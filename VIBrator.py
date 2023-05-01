#!/usr/bin/python3
import os
import sys
import gzip
import zlib
import math
import struct
import zipfile
import tarfile
import hashlib
import argparse
from io import BytesIO
import xml.etree.ElementTree as ET

class hexdump:
    def __init__(self, buf, off=0):
        self.buf = buf
        self.off = off

    def __iter__(self):
        last_bs, last_line = None, None
        for i in range(0, len(self.buf), 16):
            bs = bytearray(self.buf[i : i + 16])
            line = "{:08x}  {:23}  {:23}  |{:16}|".format(
                self.off + i,
                " ".join(("{:02x}".format(x) for x in bs[:8])),
                " ".join(("{:02x}".format(x) for x in bs[8:])),
                "".join((chr(x) if 32 <= x < 127 else "." for x in bs)),
            )
            if bs == last_bs:
                line = "*"
            if bs != last_bs or line != last_line:
                yield line
            last_bs, last_line = bs, line
        yield "{:08x}".format(self.off + len(self.buf))

    def __str__(self):
        return "\n".join(self)

    def __repr__(self):
        return "\n".join(self)

## Region for ar file format
AR_MAGIC = b"!<arch>\n"
AR_FMT = '16s12s6s6s8s10s2s'

def read_until(data, offset, delimiter):
    start = offset
    end = start
    current = data[start]
    while current != int.from_bytes(delimiter, "big"):
        end += 1
        current = data[end]
    return data[start:end].decode()

def lookup_name(data, offset):
    return read_until(data, offset, b'\n')

def padding(n, padding_size):
    remainder = n % padding_size
    return padding_size - remainder if remainder else 0

def pad(n, padding_size):
    return n + padding(n, padding_size)

class ArchiveEntry:
    name = "" #16 bytes (15 max for string)
    date = "" #12 bytes
    uid = ""  #6 bytes
    gid = ""  #6 bytes
    mode = "" #8 bytes
    size = "" #10 bytes
    magic = b"`\n"
    data = []

def create_entry_struct(entry):
    return struct.pack(AR_FMT, 
        entry.name.ljust(16, ' ').encode(),
        entry.date.ljust(12, ' ').encode(),
        entry.uid.ljust(6, ' ').encode(),
        entry.gid.ljust(6, ' ').encode(),
        entry.mode.ljust(8, ' ').encode(),
        entry.size.ljust(10, ' ').encode(),
        entry.magic
    )

class Archive:
    def __init__(self, data=[]):
        self.data = data
        self.string_table_offset = 0
        self.string_table = []
        self.entries = []

    def add_entry(self, entry):
        self.entries.append(entry)
    
    def load(self):
        index = len(AR_MAGIC)
        hdr_len = struct.calcsize(AR_FMT)
        if self.data[0:index] != AR_MAGIC:
            raise Exception("File is not a valid archive file")
        while True:
            new_index = index + hdr_len
            buffer = self.data[index:new_index]
            index = new_index
            if len(buffer) < hdr_len:
                break
            name, timestamp, owner, group, mode, size, _ = struct.unpack(AR_FMT, buffer)
            name = name.decode().rstrip()
            size = int(size.decode().rstrip())
            if name == '/':
                index += pad(size, 2)
            elif name == '//':
                self.string_table = bytearray(self.data[index:index + size])
                index += pad(size, 2)
            elif name.startswith('/'):
                lookup_offset = int(name[1:])
                expanded_name = lookup_name(self.string_table, lookup_offset)
                entry = ArchiveEntry()
                entry.name = expanded_name.rstrip('/')
                entry.date = timestamp.decode().rstrip()
                entry.uid = owner.decode().rstrip()
                entry.gid = group.decode().rstrip()
                entry.mode = mode.decode().rstrip()
                entry.size = str(size)
                entry.data = bytearray(self.data[index:index+size])
                index += pad(size, 2)
                self.entries.append(entry)
            else:
                entry = ArchiveEntry()
                entry.name = name.rstrip('/')
                entry.date = timestamp.decode().rstrip()
                entry.uid = owner.decode().rstrip()
                entry.gid = group.decode().rstrip()
                entry.mode = mode.decode().rstrip()
                entry.size = str(size)
                entry.data = self.data[index:index+size]
                hexdump(entry.data)
                index += pad(size, 2)
                self.entries.append(entry)

    def create(self):
        self.data += bytearray(AR_MAGIC)
        for entry in self.entries:
            if len(entry.name) > 15:
                name = entry.name + "/\n"
                self.string_table += bytearray(name.encode())
                self.string_table_offset += len(name)
        if self.string_table_offset != 0:
            string_table = ArchiveEntry()
            string_table.name = "//"
            string_table.date = "0"
            string_table.uid = "0"
            string_table.gid = "0"
            string_table.mode = "0"
            string_table.size = str(len(self.string_table))
            entry_struct = create_entry_struct(string_table)
            self.data += entry_struct
            self.data += self.string_table
            if padding(len(self.string_table), 2) != 0:
                self.data += b'\n'
        name_index = 0
        for entry in self.entries:
            if len(entry.name) > 15:
                file_name = entry.name
                entry.name = "/" + str(name_index)
                name_index += len(file_name) + 2
            else:
                entry.name += "/"
            entry_struct = create_entry_struct(entry)
            self.data += entry_struct
            self.data += bytearray(entry.data)
            if padding(len(entry.data), 2) != 0:
                self.data += b'\n'
        return bytearray(self.data)

def create_entry(path, filename):
    entry = ArchiveEntry()
    entry.name = filename
    with open(os.path.join(path, filename), 'rb') as f:
        entry.data = f.read()
    stat = os.stat(os.path.join(path, filename))
    entry.date = str(int(stat.st_mtime))
    entry.uid = str(stat.st_uid)
    entry.gid = str(stat.st_gid)
    entry.mode = "{0:o}".format(stat.st_mode)
    entry.size = str(stat.st_size)
    return entry

## Payload class region
GZIP_MAGIC = b'\x1f\x8b'
VTAR_FMT = '100s8s8s8s12s12s8sc100s6s2s32s32s8s8s151sIIII'

class VtarEntry:
    def __init__(self, name="", mode="", uid="", gid="", size=0, mtime="", chksum="", type="", linkname="", version="", uname="", gname="", devmajor="", devminor="", prefix="", offset=0, textoffset=0, textsize=0, numfixuppgs=0, content=[]):
        self.name = name.replace('\x00', '')
        self.mode = mode.replace('\x00', '')
        self.uid = uid.replace('\x00', '')
        self.gid = gid.replace('\x00', '')
        self.size = size
        self.mtime = mtime.replace('\x00', '')
        self.chksum = chksum.replace('\x00', '')
        self.type = type.replace('\x00', '')
        self.linkname = linkname.replace('\x00', '')
        self.version = version.replace('\x00', '')
        self.uname = uname.replace('\x00', '')
        self.gname = gname.replace('\x00', '')
        self.devmajor = devmajor.replace('\x00', '')
        self.devminor = devminor.replace('\x00', '')
        self.prefix = prefix.replace('\x00', '')
        self.offset = offset
        self.textoffset = textoffset
        self.textsize = textsize
        self.numfixuppgs = numfixuppgs
        self.content = content

    def is_file(self):
        return self.type == '0'
    
    def is_dir(self):
        return self.type == '5'

def calculate_chksum(data):
    chksum = 0
    for i in range(512):
        if i > 0x93 and i < 0x9C:
            chksum += int(ord(' '))
            continue
        chksum += int(data[i])
    return oct(chksum)[2:]

def create_vtar(entry):
    return struct.pack(VTAR_FMT, 
        entry.name.ljust(100, '\x00').encode(),
        entry.mode.rjust(7, '0').ljust(8, '\x00').encode(),
        entry.uid.rjust(7, '0').ljust(8, '\x00').encode(),
        entry.gid.rjust(7, '0').ljust(8, '\x00').encode(),
        str(format(entry.size, 'o')).rjust(11, '0').ljust(12, '\x00').encode(),
        entry.mtime.ljust(12, '\x00').encode(),
        entry.chksum.rjust(6, '0').ljust(7, '\x00').ljust(8, ' ').encode(),
        entry.type.encode(),
        entry.linkname.ljust(100, '\x00').encode(),
        'visor '.ljust(6, ' ').encode(),
        entry.version.ljust(2, '\x00').encode(),
        entry.uname.ljust(32, '\x00').encode(),
        entry.gname.ljust(32, '\x00').encode(),
        entry.devmajor.ljust(8, '\x00').encode(),
        entry.devminor.ljust(8, '\x00').encode(),
        entry.prefix.ljust(151, '\x00').encode(),
        entry.offset,
        entry.textoffset,
        entry.textsize,
        entry.numfixuppgs
        )

class Payload:
    def __init__(self, data=[], tarfmt = False):
        self.astar = tarfmt
        self.filename = ""
        magic = data[0:2]
        if magic == GZIP_MAGIC:
            compression = data[2:3]
            flags = data[3:4]
            timestamp = data[4:8]
            compression_flags = data[8:9]
            os = data[9:10]
            if flags == b'\x08':
                self.filename = read_until(data, 10, b'\x00')
            self.data = zlib.decompress(data, 16+zlib.MAX_WBITS)
        else:
            self.data = data
        self.contents = load(self.data)
        if self.contents is None:
            self.contents = []
        self.sha256 = ""
        self.sha1 = ""
        self.gzippedsha256 = ""

    def __iter__(self):
        return iter(self.contents)

    def add_entry(self, entry):
        self.contents.append(entry)

    def create_payload(self):
        first_offset = struct.calcsize(VTAR_FMT) * len(self.contents)
        payload = bytearray()
        for entry in self.contents:
            if len(entry.content) > 0:
                entry.offset = first_offset
                first_offset += len(entry.content)
            vtar = create_vtar(entry)
            chksum = calculate_chksum(vtar)
            entry.chksum = chksum
            vtar = create_vtar(entry)
            payload += vtar
        for entry in self.contents:
            if len(entry.content) > 0:
                payload += bytearray(entry.content)
        hash256 = hashlib.sha256()
        hash256.update(payload)
        self.sha256 = hash256.hexdigest()
        hash1 = hashlib.sha1()
        hash1.update(payload)
        self.sha1 = hash1.hexdigest()
        return payload

def alignup(x, base=512):
    return base * math.ceil(x / base)

def load(data):
    lookup_data = None
    header_size = struct.calcsize(VTAR_FMT)
    chunk_start = 0
    contents = []
    while True:
        chunk_end = chunk_start + header_size
        buffer = data[chunk_start:chunk_end]
        if len(buffer) < header_size:
            break
        name, mode, owner, group, size, mtime, chksum, t, linkname, magic, version, uname, gname, devmajor, devminor, prefix, offset, textoffset, textsize, numfixuppgs = struct.unpack(VTAR_FMT, buffer)
        if not (magic == b'visor ' or magic == b'ustar '):
            break
        name = name.decode().rstrip('\0')
        content = []
        if t == b'0':
            size = int(size.decode().rstrip('\0'), 8)
            if offset:
                content = data[offset:offset+size]
                chunk_start = chunk_end
            else:
                content = data[chunk_end:chunk_end+size]
                chunk_start = alignup(chunk_end + size)
        else:
            size = 0
            chunk_start = chunk_end
        contents.append(VtarEntry(
            name, 
            mode.decode(), 
            owner.decode(), 
            group.decode(), 
            size, 
            mtime.decode(), 
            chksum.decode(), 
            t.decode(), 
            linkname.decode(), 
            version.decode(),
            uname.decode(), 
            gname.decode(), 
            devmajor.decode(), 
            devminor.decode(), 
            prefix.decode(), 
            offset, 
            textoffset, 
            textsize, 
            numfixuppgs, 
            content))
    return contents

def parse_args():
    parser = argparse.ArgumentParser(description='ESXi VIB extraction/creation tool')
    parser.add_argument('-v', '--vib', help='.vib file', required=True)
    parser.add_argument('-c', '--create', action='store_true', help='Creates a VIB from the data directory')
    parser.add_argument('-x', '--extract', action='store_true', help='Save vib file to disk')
    parser.add_argument('-d', '--data', help='Specifies the directory containing the content to create VIB')
    parser.add_argument('-o', '--output', help='Output folder to save the VIB (create) or VIB contents (extract)')
    parser.add_argument('-t', '--tar', action='store_true', help='Output payload as a standard tar vs VMware vtar')
    return parser.parse_args()

def gunziphash(obj, hash='sha1'):
    algo = hashlib.new(hash)
    decompressed = gzip.decompress(obj.getbuffer())
    algo.update(decompressed)
    return algo.hexdigest()

def main():
    args = parse_args()
    is_root = os.geteuid() == 0
    script_dir = os.path.realpath(os.path.dirname(__file__))
    if args.data is not None:
        data_dir = args.data
    else:
        data_dir = os.path.join(script_dir, 'data')
    if args.output is not None:
        out_dir = args.output
    else:
        out_dir = os.path.join(script_dir, 'out')
    if args.create:
        if not os.path.exists(out_dir):
            raise Exception("Output directory doesn't exist")
        if not os.path.exists(data_dir):
            raise Exception("Data directory doesn't exist")
        if not os.path.exists(os.path.join(data_dir, 'descriptor.xml')):
            raise Exception("Descriptor file is missing")
        if not os.path.exists(os.path.join(data_dir, 'sig.pkcs7')):
            raise Exception("Signature file is missing")
        if os.path.exists(data_dir):
            payload_names = [filename for filename in os.listdir(data_dir) if filename != 'descriptor.xml' and filename != 'sig.pkcs7']
            vib_contents = []
            descriptor_file = create_entry(data_dir, "descriptor.xml")
            vib_contents.append(descriptor_file)
            pkcs_file = create_entry(data_dir, "sig.pkcs7")
            vib_contents.append(pkcs_file)
            for name in payload_names:
                payload = Payload()
                payload_gzipped = BytesIO()
                payload_dir = os.path.join(data_dir, name)
                if args.tar:
                    with tarfile.open(fileobj=payload_gzipped, mode='w:gz', format=tarfile.GNU_FORMAT) as tar:
                        for entry in os.listdir(payload_dir):
                            p = os.path.join(payload_dir, entry)
                            tar.add(p, arcname=entry)
                    payload.sha256 = gunziphash(payload_gzipped, "sha256")
                    payload.sha1 = gunziphash(payload_gzipped, "sha1")
                else:
                    for root, dirs, files in os.walk(payload_dir):
                        relative = os.path.relpath(root, payload_dir)
                        if relative != '.':
                            stat = os.stat(root)
                            relative += '/'
                            entry = VtarEntry()
                            entry.name = relative
                            print(relative)
                            entry.mode = "{0:o}".format(stat.st_mode & 0o777)
                            entry.uid = str(stat.st_uid)
                            entry.gid = str(stat.st_gid)
                            entry.mtime = str(int(stat.st_mtime))
                            entry.type = '5'
                            entry.version = ' '
                            entry.uname = 'rsh'
                            entry.gname = 'rsh'
                            payload.add_entry(entry)
                            for file in files:
                                fstat = os.stat(os.path.join(root, file))
                                file_entry = VtarEntry()
                                file_entry.name = relative + file
                                file_entry.mode = "{0:o}".format(fstat.st_mode & 0o777)
                                file_entry.uid = str(fstat.st_uid)
                                file_entry.gid = str(fstat.st_gid)
                                file_entry.size = fstat.st_size
                                file_entry.mtime = str(int(fstat.st_mtime))
                                file_entry.type = '0'
                                file_entry.version = ' '
                                file_entry.uname = 'rsh'
                                file_entry.gname = 'rsh'
                                with open(os.path.join(root, file), 'rb') as f:
                                    file_entry.content = f.read()
                                payload.add_entry(file_entry)
                    vtar = payload.create_payload()
                    with gzip.GzipFile(filename="{}.vtar".format(name), fileobj=payload_gzipped, mode='wb') as f:
                        f.write(vtar)
                file = ArchiveEntry()
                file.name = name
                fstat = os.stat(os.path.join(data_dir, name))
                file.date = str(int(fstat.st_mtime))
                file.mode = "100644"
                file.gid = "0"
                file.uid = "0"
                file.data = payload_gzipped.getbuffer()
                file.size = str(len(file.data))
                payload.gzippedsha256 = hashlib.sha256(payload_gzipped.getbuffer()).hexdigest()
                xmlTree = ET.parse(os.path.join(data_dir, "descriptor.xml"))
                rootElement = xmlTree.getroot()
                for element in rootElement.findall('payloads'):
                    for payloadelement in element.findall('payload'):
                        if payloadelement.get('name') == name:
                            payloadelement.set('size', str(file.size))
                            for chksum in payloadelement.findall('checksum'):
                                checksum_type = chksum.get('checksum-type')
                                if checksum_type == "sha-1":
                                    chksum.text = payload.sha1
                                elif checksum_type == "sha-256":
                                    if chksum.get('verify-process') is not None:
                                        chksum.text = payload.sha256
                                    else:
                                        chksum.text = payload.gzippedsha256
                xmlTree.write(os.path.join(data_dir, "descriptor.xml"),encoding='UTF-8',xml_declaration=False)
                print("GZIP sha256: {}".format(payload.gzippedsha256))
                print("Payload sha256: {}".format(payload.sha256))
                print("Payload sha1: {}".format(payload.sha1))
                vib_contents.append(file)
            archive = Archive()
            for entry in vib_contents:
                if entry.name == "descriptor.xml":
                    with open(os.path.join(data_dir, "descriptor.xml"), 'rb') as f:
                        entry.data = f.read()
                archive.add_entry(entry)
            outdata = archive.create()
            with open(os.path.join(out_dir, args.vib), 'wb') as f:
                f.write(outdata)
    else:
        data = []
        with open(args.vib, 'rb') as f:
            data = f.read()
        archive = Archive(data)
        archive.load()
        for entry in archive.entries:
            if entry.name == 'descriptor.xml' or entry.name == 'sig.pkcs7':
                if args.extract:
                    path = os.path.join(out_dir, entry.name)
                    with open(path, 'wb') as savefile:
                        savefile.write(entry.data)
                    os.chmod(path, int(entry.mode, 8))
                    if is_root:
                        os.chown(path, int(entry.uid), int(entry.gid))
            else:
                content = entry.data
                payload = Payload(content)
                if payload.filename != "":
                    payload_dirname = payload.filename.rstrip('.vtar')
                else:
                    payload_dirname = entry.name
                for item in payload:
                    print("---------------------------------")
                    print(item.name)
                    if args.extract:
                        payload_dir = os.path.join(out_dir, payload_dirname)
                        if not os.path.exists(payload_dir):
                            os.mkdir(payload_dir)
                        if item.is_file():
                            path = os.path.join(payload_dir, item.name)
                            with open(path, 'wb') as savefile:
                                savefile.write(item.content)
                            os.chmod(path, int(item.mode, 8))
                            if is_root:
                                os.chown(path, int(item.uid), int(item.gid))
                        else:
                            path = os.path.join(payload_dir, item.name)
                            mode = int(item.mode, 8)
                            try:
                                os.mkdir(path, mode=mode)
                                if is_root:
                                    os.chown(path, int(item.uid), int(item.gid))
                            except OSError:
                                pass

if __name__ == '__main__':
    sys.exit(main())
