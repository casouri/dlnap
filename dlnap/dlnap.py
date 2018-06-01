#!/usr/bin/python

# @file dlnap.py
# @author cherezov.pavel@gmail.com
# @brief Python over the network media player to playback on DLNA UPnP devices.

# Change log:
#   0.1  initial version.
#   0.2  device renamed to DlnapDevice; DLNAPlayer is disappeared.
#   0.3  debug output is added. Extract location url fixed.
#   0.4  compatible discover mode added.
#   0.5  xml parser introduced for device descriptions
#   0.6  xpath introduced to navigate over xml dictionary
#   0.7  device ip argument introduced
#   0.8  debug output is replaced with standard logging
#   0.9  pause/stop added. Video playback tested on Samsung TV
#   0.10 proxy (draft) is introduced.
#   0.11 sync proxy for py2 and py3 implemented, --proxy-port added
#   0.12 local files can be played as well now via proxy
#   0.13 ssdp protocol version argument added
#   0.14 fixed bug with receiving responses from device
#   0.15 Lot's of fixes and features added thanks @ttopholm and @NicoPy
#
#   1.0  moved from idea version

__version__ = "0.15"

import re
import sys
import time
import signal
import socket
import select
import logging
import traceback
import mimetypes
from contextlib import contextmanager

import os
py3 = sys.version_info[0] == 3
if py3:
    from urllib.request import urlopen
    from http.server import HTTPServer
    from http.server import BaseHTTPRequestHandler
else:
    from urllib2 import urlopen
    from BaseHTTPServer import BaseHTTPRequestHandler
    from BaseHTTPServer import HTTPServer

import shutil
import threading

SSDP_GROUP = ("239.255.255.250", 1900)
URN_AVTransport = "urn:schemas-upnp-org:service:AVTransport:1"
URN_AVTransport_Fmt = "urn:schemas-upnp-org:service:AVTransport:{}"

URN_RenderingControl = "urn:schemas-upnp-org:service:RenderingControl:1"
URN_RenderingControl_Fmt = "urn:schemas-upnp-org:service:RenderingControl:{}"

SSDP_ALL = "ssdp:all"


# =================================================================================================
# XML to DICT
#
def _get_tag_value(x, i=0):
    """ Get the nearest to 'i' position xml tag name.

   x -- xml string
   i -- position to start searching tag from
   return -- (tag, value) pair.
      e.g
         <d>
            <e>value4</e>
         </d>
      result is ('d', '<e>value4</e>')
   """
    x = x.strip()
    value = ''
    tag = ''

    # skip <? > tag
    if x[i:].startswith('<?'):
        i += 2
        while i < len(x) and x[i] != '<':
            i += 1

    # check for empty tag like '</tag>'
    if x[i:].startswith('</'):
        i += 2
        in_attr = False
        while i < len(x) and x[i] != '>':
            if x[i] == ' ':
                in_attr = True
            if not in_attr:
                tag += x[i]
            i += 1
        return (tag.strip(), '', x[i + 1:])

    # not an xml, treat like a value
    if not x[i:].startswith('<'):
        return ('', x[i:], '')

    i += 1  # <

    # read first open tag
    in_attr = False
    while i < len(x) and x[i] != '>':
        # get rid of attributes
        if x[i] == ' ':
            in_attr = True
        if not in_attr:
            tag += x[i]
        i += 1

    i += 1  # >

    # replace self-closing <tag/> by <tag>None</tag>
    empty_elmt = '<' + tag + ' />'
    closed_elmt = '<' + tag + '>None</' + tag + '>'
    if x.startswith(empty_elmt):
        x = x.replace(empty_elmt, closed_elmt)

    while i < len(x):
        value += x[i]
        if x[i] == '>' and value.endswith('</' + tag + '>'):
            # Note: will not work with xml like <a> <a></a> </a>
            close_tag_len = len(tag) + 2  # />
            value = value[:-close_tag_len]
            break
        i += 1
    return (tag.strip(), value[:-1], x[i + 1:])


def _xml2dict(s, ignoreUntilXML=False):
    """ Convert xml to dictionary.

   <?xml version="1.0"?>
   <a any_tag="tag value">
      <b> <bb>value1</bb> </b>
      <b> <bb>value2</bb> </b>
      </c>
      <d>
         <e>value4</e>
      </d>
      <g>value</g>
   </a>

   =>

   { 'a':
     {
         'b': [ {'bb':value1}, {'bb':value2} ],
         'c': [],
         'd':
         {
           'e': [value4]
         },
         'g': [value]
     }
   }
   """
    if ignoreUntilXML:
        s = ''.join(re.findall(".*?(<.*)", s, re.M))

    d = {}
    while s:
        tag, value, s = _get_tag_value(s)
        value = value.strip()
        isXml, dummy, dummy2 = _get_tag_value(value)
        if tag not in d:
            d[tag] = []
        if not isXml:
            if not value:
                continue
            d[tag].append(value.strip())
        else:
            if tag not in d:
                d[tag] = []
            d[tag].append(_xml2dict(value))
    return d


s = """
   hello
   this is a bad
   strings

   <?xml version="1.0"?>
   <a any_tag="tag value">
      <b><bb>value1</bb></b>
      <b><bb>value2</bb> <v>value3</v></b>
      </c>
      <d>
         <e>value4</e>
      </d>
      <g>value</g>
   </a>
"""


def _xpath(d, path):
    """ Return value from xml dictionary at path.

   d -- xml dictionary
   path -- string path like root/device/serviceList/service@serviceType=URN_AVTransport/controlURL
   return -- value at path or None if path not found
   """

    for p in path.split('/'):
        tag_attr = p.split('@')
        tag = tag_attr[0]
        if tag not in d:
            return None

        attr = tag_attr[1] if len(tag_attr) > 1 else ''
        if attr:
            a, aval = attr.split('=')
            for s in d[tag]:
                if s[a] == [aval]:
                    d = s
                    break
        else:
            d = d[tag][0]
    return d


#
# XML to DICT
# =================================================================================================


def _get_port(location):
    """ Extract port number from url.

   location -- string like http://anyurl:port/whatever/path
   return -- port number
   """
    port = re.findall('http://.*?:(\d+).*', location)
    return int(port[0]) if port else 80


def _get_control_url(xml, urn):
    """ Extract AVTransport contol url from device description xml

   xml -- device description xml
   return -- control url or empty string if wasn't found
   """
    return _xpath(
        xml,
        'root/device/serviceList/service@serviceType={}/controlURL'.format(
            urn))


@contextmanager
def _send_udp(to, packet):
    """ Send UDP message to group

   to -- (host, port) group to send the packet to
   packet -- message to send
   """
    sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM, socket.IPPROTO_UDP)
    sock.sendto(packet.encode(), to)
    yield sock
    sock.close()


def _unescape_xml(xml):
    """ Replace escaped xml symbols with real ones.
   """
    return xml.replace('&lt;', '<').replace('&gt;', '>').replace('&quot;', '"')


def _send_tcp(to, payload):
    """ Send TCP message to group

   to -- (host, port) group to send to payload to
   payload -- message to send
   """
    try:
        sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        sock.settimeout(5)
        sock.connect(to)
        sock.sendall(payload.encode('utf-8'))

        data = sock.recv(2048)
        if py3:
            data = data.decode('utf-8')
        data = _xml2dict(_unescape_xml(data), True)

        errorDescription = _xpath(
            data,
            's:Envelope/s:Body/s:Fault/detail/UPnPError/errorDescription')
        if errorDescription is not None:
            logging.error(errorDescription)
    except Exception as e:
        data = ''
    finally:
        sock.close()
    return data


def _get_location_url(raw):
    """ Extract device description url from discovery response

    raw -- raw discovery response
    return -- location url string
    """
    t = re.findall('\n(?i)location:\s*(.*)\r\s*', raw, re.M)
    if len(t) > 0:
        return t[0]
    return ''


def _get_friendly_name(xml):
    """ Extract device name from description xml

   xml -- device description xml
   return -- device name
   """
    name = _xpath(xml, 'root/device/friendlyName')
    return name if name is not None else 'Unknown'


def _get_serve_ip(target_ip, target_port=80):
    """ Find ip address of network interface used to communicate with target
    
    target-ip -- ip address of target
    return -- ip address of interface connected to target
    """
    s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    s.connect((target_ip, target_port))
    my_ip = s.getsockname()[0]
    s.close()
    return my_ip


class DlnapDevice:
    """ Represents DLNA/UPnP device.
   """

    def __init__(self, raw, ip):
        self.__logger = logging.getLogger(self.__class__.__name__)
        self.__logger.info(
            '=> New DlnapDevice (ip = {}) initialization..'.format(ip))

        self.ip = ip
        self.ssdp_version = 1

        self.port = None
        self.name = 'Unknown'
        self.control_url = None
        self.rendering_control_url = None
        self.has_av_transport = False

        try:
            self.__raw = raw.decode()
            self.location = _get_location_url(self.__raw)
            self.__logger.info('location: {}'.format(self.location))

            self.port = _get_port(self.location)
            self.__logger.info('port: {}'.format(self.port))

            raw_desc_xml = urlopen(self.location).read().decode()

            self.__desc_xml = _xml2dict(raw_desc_xml)
            self.__logger.debug('description xml: {}'.format(self.__desc_xml))

            self.name = _get_friendly_name(self.__desc_xml)
            self.__logger.info('friendlyName: {}'.format(self.name))

            self.control_url = _get_control_url(self.__desc_xml,
                                                URN_AVTransport)
            self.__logger.info('control_url: {}'.format(self.control_url))

            self.rendering_control_url = _get_control_url(
                self.__desc_xml, URN_RenderingControl)
            self.__logger.info('rendering_control_url: {}'.format(
                self.rendering_control_url))

            self.has_av_transport = self.control_url is not None
            self.__logger.info('=> Initialization completed'.format(ip))
        except Exception as e:
            self.__logger.warning(
                'DlnapDevice (ip = {}) init exception:\n{}'.format(
                    ip, traceback.format_exc()))

    def __repr__(self):
        return '{} @ {}'.format(self.name, self.ip)

    def __eq__(self, d):
        return self.name == d.name and self.ip == d.ip

    def _payload_from_template(self, action, data, urn):
        """ Assembly payload from template.
      """
        fields = ''
        for tag, value in data.items():
            fields += '<{tag}>{value}</{tag}>'.format(tag=tag, value=value)

        payload = """<?xml version="1.0" encoding="utf-8"?>
         <s:Envelope xmlns:s="http://schemas.xmlsoap.org/soap/envelope/" s:encodingStyle="http://schemas.xmlsoap.org/soap/encoding/">
            <s:Body>
               <u:{action} xmlns:u="{urn}">
                  {fields}
               </u:{action}>
            </s:Body>
         </s:Envelope>""".format(
            action=action, urn=urn, fields=fields)
        return payload

    def _create_packet(self, action, data):
        """ Create packet to send to device control url.

      action -- control action
      data -- dictionary with XML fields value
      """
        if action in ["SetVolume", "SetMute", "GetVolume"]:
            url = self.rendering_control_url
            urn = URN_RenderingControl_Fmt.format(self.ssdp_version)
        else:
            url = self.control_url
            urn = URN_AVTransport_Fmt.format(self.ssdp_version)
        payload = self._payload_from_template(
            action=action, data=data, urn=urn)

        packet = "\r\n".join([
            'POST {} HTTP/1.1'.format(url),
            'User-Agent: {}/{}'.format(__file__, __version__),
            'Accept: */*',
            'Content-Type: text/xml; charset="utf-8"',
            'HOST: {}:{}'.format(self.ip, self.port),
            'Content-Length: {}'.format(len(payload)),
            'SOAPACTION: "{}#{}"'.format(urn, action),
            'Connection: close',
            '',
            payload,
        ])

        self.__logger.debug(packet)
        return packet

    def set_current_media(self, url, instance_id=0):
        """ Set media to playback.

      url -- media url
      instance_id -- device instance id
      """
        packet = self._create_packet('SetAVTransportURI', {
            'InstanceID': instance_id,
            'CurrentURI': url,
            'CurrentURIMetaData': ''
        })
        _send_tcp((self.ip, self.port), packet)

    def play(self, instance_id=0):
        """ Play media that was already set as current.

      instance_id -- device instance id
      """
        packet = self._create_packet('Play', {
            'InstanceID': instance_id,
            'Speed': 1
        })
        _send_tcp((self.ip, self.port), packet)

    def pause(self, instance_id=0):
        """ Pause media that is currently playing back.

      instance_id -- device instance id
      """
        packet = self._create_packet('Pause', {
            'InstanceID': instance_id,
            'Speed': 1
        })
        _send_tcp((self.ip, self.port), packet)

    def stop(self, instance_id=0):
        """ Stop media that is currently playing back.

      instance_id -- device instance id
      """
        packet = self._create_packet('Stop', {
            'InstanceID': instance_id,
            'Speed': 1
        })
        _send_tcp((self.ip, self.port), packet)

    def seek(self, position, instance_id=0):
        """
      Seek position
      """
        packet = self._create_packet('Seek', {
            'InstanceID': instance_id,
            'Unit': 'REL_TIME',
            'Target': position
        })
        _send_tcp((self.ip, self.port), packet)

    def volume(self, volume=10, instance_id=0):
        """ Stop media that is currently playing back.

      instance_id -- device instance id
      """
        packet = self._create_packet(
            'SetVolume', {
                'InstanceID': instance_id,
                'DesiredVolume': volume,
                'Channel': 'Master'
            })

        _send_tcp((self.ip, self.port), packet)

    def get_volume(self, instance_id=0):
        """
      get volume
      """
        packet = self._create_packet('GetVolume', {
            'InstanceID': instance_id,
            'Channel': 'Master'
        })
        _send_tcp((self.ip, self.port), packet)

    def mute(self, instance_id=0):
        """ Stop media that is currently playing back.

      instance_id -- device instance id
      """
        packet = self._create_packet('SetMute', {
            'InstanceID': instance_id,
            'DesiredMute': '1',
            'Channel': 'Master'
        })
        _send_tcp((self.ip, self.port), packet)

    def unmute(self, instance_id=0):
        """ Stop media that is currently playing back.

      instance_id -- device instance id
      """
        packet = self._create_packet('SetMute', {
            'InstanceID': instance_id,
            'DesiredMute': '0',
            'Channel': 'Master'
        })
        _send_tcp((self.ip, self.port), packet)

    def info(self, instance_id=0):
        """ Transport info.

      instance_id -- device instance id
      """
        packet = self._create_packet('GetTransportInfo',
                                     {'InstanceID': instance_id})
        return _send_tcp((self.ip, self.port), packet)

    def media_info(self, instance_id=0):
        """ Media info.

      instance_id -- device instance id
      """
        packet = self._create_packet('GetMediaInfo',
                                     {'InstanceID': instance_id})
        return _send_tcp((self.ip, self.port), packet)

    def position_info(self, instance_id=0):
        """ Position info.
      instance_id -- device instance id
      """
        packet = self._create_packet('GetPositionInfo',
                                     {'InstanceID': instance_id})
        return _send_tcp((self.ip, self.port), packet)

    def set_next(self, url):
        pass

    def next(self):
        pass


#
# Signal of Ctrl+C
# =================================================================================================
# def signal_handler(signal, frame):
#     print(' Got Ctrl + C, exit now!')
#     sys.exit(1)

# signal.signal(signal.SIGINT, signal_handler)


def paired(li):
    paired_list = []
    current_command = None
    current_tuple = ()
    if len(li) % 2 != 0:
        li.append('')
    for element in li:
        # element is command
        if element.startswith('--') or element.startswith('-'):
            # last command doesn't have argument
            if current_command:
                paired_list.append((current_command, ''))
            current_command = element
        # element is arg
        else:
            # what should happend
            if current_command:
                paired_list.append((current_command, element))
                current_command = None
            # no command but an argument, opps
            else:
                print(
                    'Something is wrong, are you sure you typed command before argument?'
                )

    return paired_list


class Cli():
    # setup
    device = ''
    url = ''
    vol = 10
    position = '00:00:00'
    timeout = 1
    action = ''
    logLevel = logging.WARN
    compatibleOnly = True
    ip = ''
    ssdp_version = 1
    devices = []
    device_index = 0

    def discover(self,
                 name='',
                 ip='',
                 timeout=1,
                 st=SSDP_ALL,
                 mx=3,
                 ssdp_version=1):
        """ Discover UPnP devices in the local network.

    name -- name or part of the name to filter devices
    timeout -- timeout to perform discover
    st -- st field of discovery packet
    mx -- mx field of discovery packet
    return -- list of DlnapDevice
    """
        st = st.format(ssdp_version)
        payload = "\r\n".join([
            'M-SEARCH * HTTP/1.1', 'User-Agent: {}/{}'.format(
                __file__, __version__), 'HOST: {}:{}'.format(*SSDP_GROUP),
            'Accept: */*', 'MAN: "ssdp:discover"', 'ST: {}'.format(st),
            'MX: {}'.format(mx), '', ''
        ])
        with _send_udp(SSDP_GROUP, payload) as sock:
            start = time.time()
            try:
                while True:
                    if time.time() - start > timeout:
                        # timed out
                        break
                    r, w, x = select.select([sock], [], [sock], 1)
                    if sock in r:
                        data, addr = sock.recvfrom(1024)
                        if ip and addr[0] != ip:
                            continue

                        d = DlnapDevice(data, addr[0])
                        d.ssdp_version = ssdp_version
                        if d not in self.devices:
                            if not name or name is None or name.lower(
                            ) in d.name.lower():

                                self.devices.append(d)
                                print('{} {}'.format(self.devices.index(d), d))
                                if not ip:
                                    pass
                                elif d.has_av_transport:
                                    # no need in further searching by ip
                                    break

                    elif sock in x:
                        raise Exception('Getting response failed')
                    else:
                        # Nothing to read
                        pass
            except KeyboardInterrupt:
                pass

    def usage(self):
        print(
            '{} [--search <timeout>] [--index <index of device>] [--ip <device ip>] [-d[evice] <name>] [--all] [-t[imeout] <seconds>] [--play <url>] [--pause] [--stop]'.
            format(__file__))
        print(
            ' --search <timeout> - search for devices, press Ctrl-C to stop searching.'
        )
        print(
            ' --index <index of device> - use the <index>th device of the device list.'
        )
        print(
            ' --ip <device ip> - ip address for faster access to the known device'
        )
        print(
            ' --device <device name or part of the name> - discover devices with this name as substring'
        )
        print(
            ' --all - flag to discover all upnp devices, not only devices with AVTransport ability'
        )
        print(
            ' --play <url> - set current url for play and start playback it. In case of url is empty - continue playing recent media.'
        )
        print(' --pause - pause current playback')
        print(' --stop - stop current playback')
        print(' --mute - mute playback')
        print(' --unmute - unmute playback')
        print(' --volume <vol> - set current volume for playback')
        print(
            ' --seek <position in HH:MM:SS> - set current position for playback'
        )
        print(
            ' --ssdp-version <version> - discover devices by protocol version, default 1'
        )
        print(' --help - this help')

    def version(self):
        print(__version__)

    def process_command(self, paired_command_list):
        for opt, arg in paired_command_list:
            if opt in ('-h', '--help'):
                self.usage()
            elif opt in ('-s', '--search'):
                self.action = 'search'
                self.timeout = float(arg)
            elif opt in ('-v', '--version'):
                self.version()
            elif opt in ('--log'):
                if arg.lower() == 'debug':
                    self.logLevel = logging.DEBUG
                elif arg.lower() == 'info':
                    self.logLevel = logging.INFO
                elif arg.lower() == 'warn':
                    self.logLevel = logging.WARN
            elif opt in ('--all'):
                self.compatibleOnly = False
            elif opt in ('-d', '--device'):
                self.device = arg
            elif opt in ('--ssdp-version'):
                self.ssdp_version = int(arg)
            elif opt in ('--index', 'I'):
                self.device_index = int(arg)
            elif opt in ('-i', '--ip'):
                self.ip = arg
                self.compatibleOnly = False
                self.timeout = 10
            elif opt in ('--list'):
                self.action = 'list'
            elif opt in ('--play'):
                self.action = 'play'
                self.url = arg
            elif opt in ('--pause'):
                self.action = 'pause'
            elif opt in ('--stop'):
                self.action = 'stop'
            elif opt in ('--volume'):
                self.action = 'volume'
                self.vol = arg
            elif opt in ('--seek'):
                self.action = 'seek'
                self.position = arg
            elif opt in ('--mute'):
                self.action = 'mute'
            elif opt in ('--unmute'):
                self.action = 'unmute'
            elif opt in ('--info'):
                self.action = 'info'
            elif opt in ('--media-info'):
                self.action = 'media-info'

    def run(self):
        run = True
        while run:
            command = input('Command: ')
            command_list = command.split(' ')

            paired_command_list = paired(command_list)
            # print(paired_command_list)
            self.action = None
            self.process_command(paired_command_list)

            logging.basicConfig(level=self.logLevel)

            st = URN_AVTransport_Fmt if self.compatibleOnly else SSDP_ALL

            # print(self.action)
            if self.action == 'search':
                self.discover(
                    name=self.device,
                    ip=self.ip,
                    timeout=self.timeout,
                    st=st,
                    ssdp_version=self.ssdp_version)

            if self.action == 'list':
                print('Discovered devices:')
                for d in self.devices:
                    print('{} {} {}'.format(
                        self.device_index, '[a]'
                        if d.has_av_transport else '[x]', d))

            if not self.devices:
                print('No compatible devices found.')
                continue
            else:
                d = self.devices[self.device_index]

            if self.url != '' and self.url.lower().replace(
                    'https://', '').replace('www.', '').startswith('youtube.'):
                import subprocess
                process = subprocess.Popen(
                    ['youtube-dl', '-g', url], stdout=subprocess.PIPE)
                url, err = process.communicate()

            if self.action == 'play':
                try:
                    if self.url != '':
                        d.stop()
                        d.set_current_media(url=self.url)
                        d.play()
                    else:
                        d.play()
                except Exception as e:
                    print('Device is unable to play media.')
                    logging.warn('Play exception:\n{}'.format(
                        traceback.format_exc()))
            elif self.action == 'pause':
                d.pause()
            elif self.action == 'stop':
                d.stop()
            elif self.action == 'volume':
                d.volume(self.vol)
            elif self.action == 'seek':
                d.seek(self.position)
            elif self.action == 'mute':
                d.mute()
            elif self.action == 'unmute':
                d.unmute()
            elif self.action == 'info':
                print(d.info())
            elif self.action == 'media-info':
                print(d.media_info())


cli = Cli()
cli.run()
