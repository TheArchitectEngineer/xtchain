/**
 * PROJECT:     XTchain
 * LICENSE:     See COPYING.md in the top level directory
 * FILE:        tools/mkxthv.c
 * DESCRIPTION: Builds XTHV1 registry hives from YAML
 * DEVELOPERS:  Aiken Harris <harraiken91@gmail.com>
 */

#define YAML_MAX_BINARY 0x7ffff000u
#define YAML_MAX_DEPTH 192

#include "xtchain.h"


#define HIVE_PAGE_SIZE              4096u
#define HIVE_MAP_ENTRIES            84u
#define HIVE_CELL_NIL               UINT32_MAX
#define HIVE_LOGICAL_LIMIT          0x7ffff000u
#define HIVE_CELL_LIMIT             0x100000u
#define HIVE_BIG_DATA_CHUNK         0x3fd8u
#define HIVE_VALUE_LIMIT            (HIVE_BIG_DATA_CHUNK * UINT16_MAX)
#define HIVE_INDEX_ENTRIES          1014u
#define HIVE_TRAVERSAL_LIMIT        64u
#define HIVE_KEY_COMPRESSED         0x20u
#define HIVE_KEY_FLAGS              0xf078u


typedef struct
{
    unsigned char PageNumber[8], Generation[8], Hash[32];
} HIVE_PAGE_DESCRIPTOR;

typedef struct
{
    unsigned char Magic[8], HiveId[16], Generation[8], FirstLogicalPage[8];
    unsigned char Level[4], UsedEntries[4], Reserved[16];
    HIVE_PAGE_DESCRIPTOR Entries[HIVE_MAP_ENTRIES];
} HIVE_MAP_NODE;

typedef struct
{
    unsigned char Magic[8], Major[2], Minor[2], HeaderBytes[4], PageBytes[4], SlotId[4];
    unsigned char HiveId[16], Generation[8], LogicalBytes[8], FilePageLimit[8];
    unsigned char RootCell[4], CellFormat[4];
    HIVE_PAGE_DESCRIPTOR MapRoot;
    unsigned char CommitTime[8], RequiredFeatures[8], ReadOnlyFeatures[8], CompatibleFeatures[8];
    unsigned char WriterId[16], HashAlgorithm[4], Reserved[4], ReservedBytes[3888], Hash[32];
} HIVE_SUPERBLOCK;

typedef struct
{
    unsigned char Domain[8], HiveId[16], PageNumber[8], Generation[8], FirstLogicalPage[8], Level[4];
} HIVE_HASH_CONTEXT;

typedef struct
{
    unsigned char Signature[4], FileOffset[4], Size[4], Reserved[8], Timestamp[8], Spare[4];
} HIVE_BIN_HEADER;

typedef struct
{
    unsigned char Signature[2], Flags[2], LastWriteTime[8], AccessBits[4], Parent[4];
    unsigned char SubKeyCount[4], VolatileCount[4], SubKeyList[4], VolatileList[4];
    unsigned char ValueCount[4], ValueList[4], Security[4], Class[4];
    unsigned char MaxNameLength[4], MaxClassLength[4], MaxValueNameLength[4], MaxValueDataLength[4];
    unsigned char WorkVar[4], NameLength[2], ClassLength[2];
} HIVE_KEY_NODE;

typedef struct
{
    unsigned char Signature[2], NameLength[2], DataLength[4], Data[4], Type[4], Flags[2], Reserved[2];
} HIVE_VALUE_NODE;

typedef struct
{
    uint32_t State[5];
    uint64_t Bytes;
    unsigned char Block[64];
    size_t Used;
} HIVE_SHA1_CONTEXT;

typedef struct
{
    YAML_BUFFER Bytes;
    uint16_t *Characters;
    size_t Length;
    int Compressed;
} HIVE_NAME;

typedef struct
{
    HIVE_NAME Name;
    YAML_BUFFER Data;
    uint32_t Type, Cell;
} HIVE_VALUE;

typedef struct HIVE_SECURITY
{
    YAML_BUFFER Descriptor;
    uint32_t Cell, References;
    struct HIVE_SECURITY *Next;
} HIVE_SECURITY;

typedef struct HIVE_KEY
{
    HIVE_NAME Name;
    YAML_BUFFER Class;
    HIVE_SECURITY *Security;
    uint64_t Timestamp;
    uint32_t Flags, AccessBits, Cell;
    HIVE_VALUE *Values;
    struct HIVE_KEY **Children;
    size_t ValueCount, ChildCount;
    unsigned TraversalCost;
} HIVE_KEY;

typedef struct HIVE_BIN
{
    unsigned char *Data;
    uint32_t Offset, Size, Used;
    struct HIVE_BIN *Next;
} HIVE_BIN;

typedef struct HIVE_SOURCE_KEY
{
    YAML_NODE *Record;
    HIVE_NAME Name;
    size_t Hash, ChildCount, IndexSize;
    struct HIVE_SOURCE_KEY **Index;
} HIVE_SOURCE_KEY;

typedef struct
{
    HIVE_BIN *Bins, *LastBin;
    HIVE_SECURITY *Security, *LastSecurity;
    uint32_t LogicalBytes;
    uint64_t Timestamp, NextPage;
    unsigned char HiveId[16], WriterId[16];
    const char *InputDirectory;
    const char *OutputPath;
    YAML_NODE *Strings;
} HIVE_BUILD_CONTEXT;

static FILE *HiveOutput;
static char *HiveTemporary;

static void HiveStoreInteger(unsigned char *Destination, uint64_t Value, unsigned Width);
static void HiveSha1Initialize(HIVE_SHA1_CONTEXT *Context);
static void HiveSha1Update(HIVE_SHA1_CONTEXT *Context, const void *Data, size_t Length);
static void HiveSha1Finish(HIVE_SHA1_CONTEXT *Context, unsigned char Digest[20]);
static HIVE_KEY *HiveReadKey(HIVE_BUILD_CONTEXT *Context, YAML_NODE *Node, HIVE_SECURITY *Inherited, unsigned Depth);
static void HiveBuildKey(HIVE_BUILD_CONTEXT *Context, HIVE_KEY *Key, uint32_t Parent);

static
void
HiveStoreInteger(unsigned char *Destination,
                 uint64_t Value,
                 unsigned Width)
{
    for(unsigned Index = 0; Index < Width; Index++)
    {
        Destination[Index] = (unsigned char)(Value >> (Index * 8));
    }
}

static
uint32_t
HiveRotate(uint32_t Value,
           unsigned Shift)
{
    return (Value << Shift) | (Value >> (32 - Shift));
}

static
void
HiveSha1Transform(HIVE_SHA1_CONTEXT *Context)
{
    uint32_t Words[80];
    for(unsigned Index = 0; Index < 16; Index++)
    {
        const unsigned char *Data = Context->Block + Index * 4;
        Words[Index] = (uint32_t)Data[0] << 24 | (uint32_t)Data[1] << 16 | (uint32_t)Data[2] << 8 | Data[3];
    }
    for(unsigned Index = 16; Index < 80; Index++)
    {
        Words[Index] = HiveRotate(Words[Index - 3] ^ Words[Index - 8] ^ Words[Index - 14] ^ Words[Index - 16], 1);
    }
    uint32_t First = Context->State[0], Second = Context->State[1], Third = Context->State[2];
    uint32_t Fourth = Context->State[3], Fifth = Context->State[4];
    for(unsigned Index = 0; Index < 80; Index++)
    {
        uint32_t Function, Constant;
        if(Index < 20)
        {
            Function = (Second & Third) | (~Second & Fourth);
            Constant = 0x5a827999;
        }
        else if(Index < 40)
        {
            Function = Second ^ Third ^ Fourth;
            Constant = 0x6ed9eba1;
        }
        else if(Index < 60)
        {
            Function = (Second & Third) | (Second & Fourth) | (Third & Fourth);
            Constant = 0x8f1bbcdc;
        }
        else
        {
            Function = Second ^ Third ^ Fourth;
            Constant = 0xca62c1d6;
        }
        uint32_t Next = HiveRotate(First, 5) + Function + Fifth + Constant + Words[Index];
        Fifth = Fourth;
        Fourth = Third;
        Third = HiveRotate(Second, 30);
        Second = First;
        First = Next;
    }
    Context->State[0] += First;
    Context->State[1] += Second;
    Context->State[2] += Third;
    Context->State[3] += Fourth;
    Context->State[4] += Fifth;
}

static
void
HiveSha1Initialize(HIVE_SHA1_CONTEXT *Context)
{
    memset(Context, 0, sizeof(*Context));
    Context->State[0] = 0x67452301;
    Context->State[1] = 0xefcdab89;
    Context->State[2] = 0x98badcfe;
    Context->State[3] = 0x10325476;
    Context->State[4] = 0xc3d2e1f0;
}

static
void
HiveSha1Update(HIVE_SHA1_CONTEXT *Context,
               const void *Data,
               size_t Length)
{
    const unsigned char *Bytes = Data;
    Context->Bytes += Length;
    while(Length)
    {
        size_t Count = sizeof(Context->Block) - Context->Used;
        if(Count > Length)
        {
            Count = Length;
        }
        memcpy(Context->Block + Context->Used, Bytes, Count);
        Context->Used += Count;
        Bytes += Count;
        Length -= Count;
        if(Context->Used == sizeof(Context->Block))
        {
            HiveSha1Transform(Context);
            Context->Used = 0;
        }
    }
}

static
void
HiveSha1Finish(HIVE_SHA1_CONTEXT *Context,
               unsigned char Digest[20])
{
    uint64_t Bits = Context->Bytes * 8;
    unsigned char Padding[64] = {0x80}, Length[8];
    for(unsigned Index = 0; Index < 8; Index++)
    {
        Length[7 - Index] = (unsigned char)(Bits >> (Index * 8));
    }
    size_t Count = Context->Used < 56 ? 56 - Context->Used : 120 - Context->Used;
    HiveSha1Update(Context, Padding, Count);
    HiveSha1Update(Context, Length, sizeof(Length));
    for(unsigned Index = 0; Index < 20; Index++)
    {
        Digest[Index] = (unsigned char)(Context->State[Index / 4] >> (24 - (Index % 4) * 8));
    }
}

static
uint64_t
HiveParseInteger(const char *Text,
                 uint64_t Maximum)
{
    unsigned Base = 10;
    const char *Start = Text;
    if(Text[0] == '0' && (Text[1] == 'x' || Text[1] == 'X'))
    {
        Base = 16;
        Text += 2;
    }
    if(!*Text)
    {
        YamlError("empty integer");
    }
    uint64_t Value = 0;
    for(; *Text; Text++)
    {
        unsigned Digit = *Text >= '0' && *Text <= '9' ? (unsigned)(*Text - '0') :
                         *Text >= 'a' && *Text <= 'f' ? (unsigned)(*Text - 'a' + 10) :
                         *Text >= 'A' && *Text <= 'F' ? (unsigned)(*Text - 'A' + 10) : 99;
        if(Digit >= Base || Digit > Maximum || Value > (Maximum - Digit) / Base)
        {
            YamlError("invalid or overflowing integer: %s", Start);
        }
        Value = Value * Base + Digit;
    }
    return Value;
}

static
uint64_t
HiveOptionalInteger(YAML_NODE *Node,
                    const char *Field,
                    uint64_t Default,
                    uint64_t Maximum)
{
    YAML_NODE *Value = YamlFindField(Node, Field);
    return Value ? HiveParseInteger(YamlGetScalar(Value), Maximum) : Default;
}

static
YAML_BUFFER
HiveReadFile(const char *Path,
             size_t Limit)
{
    FILE *File = fopen(Path, "rb");
    if(!File)
    {
        YamlError("cannot open %s: %s", Path, strerror(errno));
    }
    YAML_BUFFER Buffer = {0};
    unsigned char Block[8192];
    size_t Count;
    while((Count = fread(Block, 1, sizeof(Block), File)) != 0)
    {
        if(Count > Limit || Buffer.len > Limit - Count)
        {
            fclose(File);
            YamlError("file exceeds size limit: %s", Path);
        }
        YamlAppendBuffer(&Buffer, Block, Count);
    }
    if(ferror(File))
    {
        fclose(File);
        YamlError("cannot read %s", Path);
    }
    if(fclose(File))
    {
        YamlError("cannot close %s", Path);
    }
    return Buffer;
}

static
YAML_BUFFER
HiveReadBytes(HIVE_BUILD_CONTEXT *Context,
              YAML_NODE *Node)
{
    YAML_BUFFER Bytes = {0};
    if(Node->type == YAML_BINARY)
    {
        Bytes.data = Node->bytes;
        Bytes.len = Node->length;
    }
    else if(Node->type == YAML_SEQUENCE)
    {
        for(size_t Index = 0; Index < Node->count; Index++)
        {
            unsigned char Byte = (unsigned char)HiveParseInteger(YamlGetScalar(Node->values[Index]), 255);
            YamlAppendBuffer(&Bytes, &Byte, 1);
        }
    }
    else if(Node->type == YAML_MAP)
    {
        YamlValidateFields(Node, "file", "");
        const char *Name = YamlGetScalar(YamlGetField(Node, "file"));
        int Absolute = Name[0] == '/' || Name[0] == '\\' || (strlen(Name) >= 2 && Name[1] == ':');
        char *Path = Absolute ? YamlCopyString(Name) : YamlFormatString("%s/%s", Context->InputDirectory, Name);
        struct stat InputStat, OutputStat;
        if(!strcmp(Path, Context->OutputPath) ||
           (!stat(Path, &InputStat) && !stat(Context->OutputPath, &OutputStat) && InputStat.st_ino &&
            InputStat.st_ino == OutputStat.st_ino && InputStat.st_dev == OutputStat.st_dev))
        {
            YamlError("output must not replace an external input payload: %s", Path);
        }
        Bytes = HiveReadFile(Path, HIVE_VALUE_LIMIT);
    }
    else
    {
        const unsigned char *Text = (const unsigned char *)YamlGetScalar(Node);
        unsigned Value = 0, Half = 0;
        for(; *Text; Text++)
        {
            if(*Text == ' ' || *Text == '\t' || *Text == '\n' || *Text == '\r')
            {
                continue;
            }
            unsigned Digit = *Text >= '0' && *Text <= '9' ? *Text - '0' :
                             *Text >= 'a' && *Text <= 'f' ? *Text - 'a' + 10 :
                             *Text >= 'A' && *Text <= 'F' ? *Text - 'A' + 10 : 99;
            if(Digit > 15)
            {
                YamlError("binary data must be hexadecimal, a byte sequence, !!binary or {file: PATH}");
            }
            Value = Value * 16 + Digit;
            if(++Half == 2)
            {
                unsigned char Byte = (unsigned char)Value;
                YamlAppendBuffer(&Bytes, &Byte, 1);
                Half = Value = 0;
            }
        }
        if(Half)
        {
            YamlError("odd number of hexadecimal digits");
        }
    }
    return Bytes;
}

static
YAML_BUFFER
HiveEncodeString(const char *Text,
                 int Terminate)
{
    YAML_BUFFER Bytes = {0};
    const unsigned char *Cursor = (const unsigned char *)Text;
    while(*Cursor)
    {
        uint32_t Character = *Cursor++;
        if(Character >= 0x80)
        {
            unsigned Extra = Character < 0xe0 ? 1 : Character < 0xf0 ? 2 : 3;
            Character &= Extra == 1 ? 0x1f : Extra == 2 ? 0x0f : 7;
            while(Extra--)
            {
                Character = (Character << 6) | (*Cursor++ & 63);
            }
        }
        if(Character > 0xffff)
        {
            Character -= 0x10000;
            WriteUInt16(&Bytes, (uint16_t)(0xd800 | (Character >> 10)));
            WriteUInt16(&Bytes, (uint16_t)(0xdc00 | (Character & 1023)));
        }
        else
        {
            WriteUInt16(&Bytes, (uint16_t)Character);
        }
    }
    if(Terminate)
    {
        WriteUInt16(&Bytes, 0);
    }
    return Bytes;
}

static
HIVE_NAME
HiveReadName(YAML_NODE *Node,
             int KeyName)
{
    const char *Text = YamlGetScalar(Node);
    if(KeyName && strchr(Text, '\\'))
    {
        YamlError("a key name is one path component, without backslashes");
    }
    HIVE_NAME Name = {0};
    YAML_BUFFER Wide = HiveEncodeString(Text, 0);
    Name.Length = Wide.len / 2;
    Name.Characters = YamlAllocateMemory(Wide.len);
    Name.Compressed = 1;
    for(size_t Index = 0; Index < Name.Length; Index++)
    {
        Name.Characters[Index] = ReadUInt16(Wide.data + Index * 2);
        if(Name.Characters[Index] > 255)
        {
            Name.Compressed = 0;
        }
    }
    if(Name.Compressed)
    {
        for(size_t Index = 0; Index < Name.Length; Index++)
        {
            unsigned char Byte = (unsigned char)Name.Characters[Index];
            YamlAppendBuffer(&Name.Bytes, &Byte, 1);
        }
    }
    else
    {
        Name.Bytes = Wide;
    }
    if(Name.Bytes.len > UINT16_MAX)
    {
        YamlError("encoded registry name is longer than 65535 bytes");
    }
    return Name;
}

static
uint16_t
HiveUpcase(uint16_t Character)
{
    /* CellFormat 1 currently defines ASCII and Latin-1 folding, independently of host locale. */
    if((Character >= 'a' && Character <= 'z') ||
       (Character >= 0x00e0 && Character <= 0x00fe && Character != 0x00f7))
    {
        return (uint16_t)(Character - 32);
    }
    return Character == 0x00ff ? 0x0178 : Character;
}

static
int
HiveCompareNames(const HIVE_NAME *First,
                 const HIVE_NAME *Second)
{
    size_t Count = First->Length < Second->Length ? First->Length : Second->Length;
    for(size_t Index = 0; Index < Count; Index++)
    {
        unsigned Left = HiveUpcase(First->Characters[Index]), Right = HiveUpcase(Second->Characters[Index]);
        if(Left != Right)
        {
            return Left < Right ? -1 : 1;
        }
    }
    return (First->Length > Second->Length) - (First->Length < Second->Length);
}

static
int
HiveCompareKeys(const void *First,
                const void *Second)
{
    return HiveCompareNames(&(*(HIVE_KEY *const *)First)->Name, &(*(HIVE_KEY *const *)Second)->Name);
}

static
int
HiveCompareValues(const void *First,
                  const void *Second)
{
    return HiveCompareNames(&((const HIVE_VALUE *)First)->Name, &((const HIVE_VALUE *)Second)->Name);
}

static
uint32_t
HiveReadValueType(YAML_NODE *Node)
{
    static const char *Names[] = {
        "HIVE_NONE", "HIVE_SZ", "HIVE_EXPAND_SZ", "HIVE_BINARY", "HIVE_DWORD", "HIVE_DWORD_BIG_ENDIAN",
        "HIVE_LINK", "HIVE_MULTI_SZ", "HIVE_RESOURCE_LIST", "HIVE_FULL_RESOURCE_DESCRIPTOR",
        "HIVE_RESOURCE_REQUIREMENTS_LIST", "HIVE_QWORD"
    };
    const char *Name = YamlGetScalar(Node);
    for(size_t Index = 0; Index < sizeof(Names) / sizeof(Names[0]); Index++)
    {
        if(!strcmp(Name, Names[Index]))
        {
            return (uint32_t)Index;
        }
    }
    if(!strcmp(Name, "HIVE_DWORD_LITTLE_ENDIAN"))
    {
        return 4;
    }
    if(!strcmp(Name, "HIVE_QWORD_LITTLE_ENDIAN"))
    {
        return 11;
    }
    if(*Name < '0' || *Name > '9')
    {
        YamlError("unknown registry value type: %s; use a HIVE_* name or numeric type code", Name);
    }
    return (uint32_t)HiveParseInteger(Name, UINT32_MAX);
}

static
HIVE_VALUE
HiveReadValue(HIVE_BUILD_CONTEXT *Context,
              YAML_NODE *Node)
{
    YamlValidateFields(Node, "name type", "data raw");
    HIVE_VALUE Value = {0};
    Value.Name = HiveReadName(YamlGetField(Node, "name"), 0);
    Value.Type = HiveReadValueType(YamlGetField(Node, "type"));
    YAML_NODE *Data = YamlFindField(Node, "data"), *Raw = YamlFindField(Node, "raw");
    if((Data != NULL) == (Raw != NULL))
    {
        YamlError("a value requires exactly one of data and raw");
    }
    if(Raw)
    {
        Value.Data = HiveReadBytes(Context, Raw);
    }
    else if(Value.Type == 1 || Value.Type == 2 || Value.Type == 6)
    {
        Value.Data = HiveEncodeString(YamlGetScalar(Data), Value.Type != 6);
    }
    else if(Value.Type == 4 || Value.Type == 5 || Value.Type == 11)
    {
        unsigned Width = Value.Type == 11 ? 8 : 4;
        uint64_t Number = HiveParseInteger(YamlGetScalar(Data), Width == 8 ? UINT64_MAX : UINT32_MAX);
        unsigned char Bytes[8];
        HiveStoreInteger(Bytes, Number, Width);
        if(Value.Type == 5)
        {
            for(unsigned Index = 0; Index < Width / 2; Index++)
            {
                unsigned char Byte = Bytes[Index];
                Bytes[Index] = Bytes[Width - Index - 1];
                Bytes[Width - Index - 1] = Byte;
            }
        }
        YamlAppendBuffer(&Value.Data, Bytes, Width);
    }
    else if(Value.Type == 7)
    {
        if(Data->type != YAML_SEQUENCE)
        {
            YamlError("HIVE_MULTI_SZ data must be a sequence of strings");
        }
        for(size_t Index = 0; Index < Data->count; Index++)
        {
            const char *Text = YamlGetScalar(Data->values[Index]);
            if(!*Text)
            {
                YamlError("HIVE_MULTI_SZ elements cannot be empty; use raw for exact bytes");
            }
            YAML_BUFFER String = HiveEncodeString(Text, 1);
            YamlAppendBuffer(&Value.Data, String.data, String.len);
        }
        WriteUInt16(&Value.Data, 0);
        if(!Data->count)
        {
            WriteUInt16(&Value.Data, 0);
        }
    }
    else
    {
        Value.Data = HiveReadBytes(Context, Data);
    }
    if(Value.Data.len > HIVE_VALUE_LIMIT)
    {
        YamlError("value exceeds the XTHV1 big-data limit");
    }
    return Value;
}

static
YAML_BUFFER
HiveEncodeSid(const char *Text)
{
    if(strncmp(Text, "S-1-", 4))
    {
        YamlError("expected SID S-1-authority-subauthority[...]");
    }
    char *Copy = YamlCopyString(Text + 4), *Cursor = Copy, *Part;
    uint32_t SubAuthorities[15];
    unsigned Count = 0;
    Part = strchr(Cursor, '-');
    if(!Part)
    {
        YamlError("a SID requires at least one subauthority");
    }
    *Part++ = 0;
    uint64_t Authority = HiveParseInteger(Cursor, 0xffffffffffffULL);
    Cursor = Part;
    while(1)
    {
        Part = strchr(Cursor, '-');
        if(Part)
        {
            *Part++ = 0;
        }
        if(Count == 15)
        {
            YamlError("a SID can contain at most 15 subauthorities");
        }
        SubAuthorities[Count++] = (uint32_t)HiveParseInteger(Cursor, UINT32_MAX);
        if(!Part)
        {
            break;
        }
        Cursor = Part;
    }
    YAML_BUFFER Sid = {0};
    unsigned char Header[8] = {1, (unsigned char)Count};
    for(unsigned Index = 0; Index < 6; Index++)
    {
        Header[7 - Index] = (unsigned char)(Authority >> (Index * 8));
    }
    YamlAppendBuffer(&Sid, Header, sizeof(Header));
    for(unsigned Index = 0; Index < Count; Index++)
    {
        WriteUInt32(&Sid, SubAuthorities[Index]);
    }
    return Sid;
}

static
YAML_BUFFER
HiveEncodeAcl(HIVE_BUILD_CONTEXT *Context,
              YAML_NODE *Node)
{
    if(Node->type != YAML_SEQUENCE || Node->count > UINT16_MAX)
    {
        YamlError("an ACL must be an ACE sequence");
    }
    YAML_BUFFER Acl = {0};
    unsigned char Header[8] = {2};
    YamlAppendBuffer(&Acl, Header, sizeof(Header));
    for(size_t Index = 0; Index < Node->count; Index++)
    {
        YAML_NODE *Ace = Node->values[Index];
        YAML_NODE *Raw = Ace->type == YAML_MAP ? YamlFindField(Ace, "raw") : NULL;
        if(Raw)
        {
            YamlValidateFields(Ace, "raw", "");
            YAML_BUFFER Bytes = HiveReadBytes(Context, Raw);
            if(Bytes.len < 4 || Bytes.len > UINT16_MAX || ReadUInt16(Bytes.data + 2) != Bytes.len)
            {
                YamlError("raw ACE size does not match its header");
            }
            YamlAppendBuffer(&Acl, Bytes.data, Bytes.len);
        }
        else
        {
            YamlValidateFields(Ace, "type mask sid", "flags");
            const char *TypeName = YamlGetScalar(YamlGetField(Ace, "type"));
            unsigned Type;
            if(!strcmp(TypeName, "allow"))
            {
                Type = 0;
            }
            else if(!strcmp(TypeName, "deny"))
            {
                Type = 1;
            }
            else if(!strcmp(TypeName, "audit"))
            {
                Type = 2;
            }
            else
            {
                YamlError("unknown ACE type: %s; use raw for other ACE layouts", TypeName);
                Type = 0;
            }
            YAML_BUFFER Sid = HiveEncodeSid(YamlGetScalar(YamlGetField(Ace, "sid")));
            unsigned char Prefix[8] = {(unsigned char)Type};
            Prefix[1] = (unsigned char)HiveOptionalInteger(Ace, "flags", 0, 255);
            HiveStoreInteger(Prefix + 2, 8 + Sid.len, 2);
            HiveStoreInteger(Prefix + 4, HiveParseInteger(YamlGetScalar(YamlGetField(Ace, "mask")), UINT32_MAX), 4);
            YamlAppendBuffer(&Acl, Prefix, sizeof(Prefix));
            YamlAppendBuffer(&Acl, Sid.data, Sid.len);
        }
    }
    if(Acl.len > UINT16_MAX)
    {
        YamlError("ACL exceeds its 16-bit size field");
    }
    HiveStoreInteger(Acl.data + 2, Acl.len, 2);
    HiveStoreInteger(Acl.data + 4, Node->count, 2);
    return Acl;
}

static
void
HiveValidateSecurity(const YAML_BUFFER *Descriptor)
{
    const unsigned char *Data = Descriptor->data;
    size_t Length = Descriptor->len;
    if(Length < 20 || Data[0] != 1 || Data[1] || !(ReadUInt16(Data + 2) & 0x8000))
    {
        YamlError("expected a revision-1 self-relative security descriptor");
    }
    for(unsigned Index = 0; Index < 4; Index++)
    {
        size_t Offset = ReadUInt32(Data + 4 + Index * 4);
        if(!Offset)
        {
            continue;
        }
        if(Offset < 20 || Offset > Length || Length - Offset < 8)
        {
            YamlError("security descriptor component is out of bounds");
        }
        const unsigned char *Component = Data + Offset;
        if(Index < 2)
        {
            if(Component[0] != 1 || !Component[1] || Component[1] > 15 ||
               Component[1] > (Length - Offset - 8) / 4)
            {
                YamlError("invalid security descriptor SID");
            }
        }
        else
        {
            size_t AclSize = ReadUInt16(Component + 2), Position = 8;
            unsigned Count = ReadUInt16(Component + 4);
            if(Component[0] != 2 || Component[1] || AclSize < 8 || AclSize > Length - Offset)
            {
                YamlError("CellFormat 1 requires a bounded revision-2 ACL");
            }
            while(Count--)
            {
                if(Position > AclSize || AclSize - Position < 4)
                {
                    YamlError("truncated ACE header");
                }
                size_t Size = ReadUInt16(Component + Position + 2);
                if(Size < 4 || Size > AclSize - Position)
                {
                    YamlError("invalid ACE size");
                }
                Position += Size;
            }
        }
    }
}

static
YAML_BUFFER
HiveReadSecurity(HIVE_BUILD_CONTEXT *Context,
                 YAML_NODE *Node)
{
    if(Node->type != YAML_MAP || YamlFindField(Node, "file"))
    {
        YAML_BUFFER Raw = HiveReadBytes(Context, Node);
        HiveValidateSecurity(&Raw);
        return Raw;
    }
    if(YamlFindField(Node, "raw"))
    {
        YamlValidateFields(Node, "raw", "");
        YAML_BUFFER Raw = HiveReadBytes(Context, YamlGetField(Node, "raw"));
        HiveValidateSecurity(&Raw);
        return Raw;
    }
    YamlValidateFields(Node, "", "owner group dacl sacl control");
    YAML_BUFFER Descriptor = {0};
    unsigned char Header[20] = {1};
    uint16_t Control = (uint16_t)HiveOptionalInteger(Node, "control", 0, UINT16_MAX) | 0x8000;
    YamlAppendBuffer(&Descriptor, Header, sizeof(Header));
    const char *Fields[] = {"owner", "group", "sacl", "dacl"};
    for(unsigned Index = 0; Index < 4; Index++)
    {
        YAML_NODE *Field = YamlFindField(Node, Fields[Index]);
        if(!Field)
        {
            continue;
        }
        if(Index >= 2)
        {
            Control |= Index == 2 ? 0x10 : 4;
            if(Field->type == YAML_SCALAR && !strcmp(YamlGetScalar(Field), "null"))
            {
                continue;
            }
        }
        YAML_BUFFER Bytes = Index < 2 ? HiveEncodeSid(YamlGetScalar(Field)) : HiveEncodeAcl(Context, Field);
        HiveStoreInteger(Descriptor.data + 4 + Index * 4, Descriptor.len, 4);
        YamlAppendBuffer(&Descriptor, Bytes.data, Bytes.len);
    }
    HiveStoreInteger(Descriptor.data + 2, Control, 2);
    HiveValidateSecurity(&Descriptor);
    return Descriptor;
}

static
HIVE_SECURITY *
HiveInternSecurity(HIVE_BUILD_CONTEXT *Context,
                   YAML_BUFFER Descriptor)
{
    for(HIVE_SECURITY *Security = Context->Security; Security; Security = Security->Next)
    {
        if(Security->Descriptor.len == Descriptor.len &&
           !memcmp(Security->Descriptor.data, Descriptor.data, Descriptor.len))
        {
            return Security;
        }
    }
    HIVE_SECURITY *Security = YamlAllocateMemory(sizeof(*Security));
    Security->Descriptor = Descriptor;
    if(Context->LastSecurity)
    {
        Context->LastSecurity->Next = Security;
    }
    else
    {
        Context->Security = Security;
    }
    Context->LastSecurity = Security;
    return Security;
}

static
HIVE_KEY *
HiveReadKey(HIVE_BUILD_CONTEXT *Context,
            YAML_NODE *Node,
            HIVE_SECURITY *Inherited,
            unsigned Depth)
{
    if(Depth > HIVE_TRAVERSAL_LIMIT)
    {
        YamlError("registry tree exceeds the kernel traversal budget");
    }
    YamlValidateFields(Node, "name", "class timestamp flags access_bits security values subkeys");
    HIVE_KEY *Key = YamlAllocateMemory(sizeof(*Key));
    Key->Name = HiveReadName(YamlGetField(Node, "name"), 1);
    if(Depth && !Key->Name.Length)
    {
        YamlError("a subkey cannot have an empty name");
    }
    Key->Timestamp = HiveOptionalInteger(Node, "timestamp", Context->Timestamp, UINT64_MAX);
    Key->AccessBits = (uint32_t)HiveOptionalInteger(Node, "access_bits", 0, UINT32_MAX);
    Key->Flags = (uint32_t)HiveOptionalInteger(Node, "flags", 0, UINT16_MAX);
    if(Key->Flags & ~HIVE_KEY_FLAGS)
    {
        YamlError("key flags include runtime-only or undefined bits");
    }
    Key->Flags = (Key->Flags & ~HIVE_KEY_COMPRESSED) | (Key->Name.Compressed ? HIVE_KEY_COMPRESSED : 0);
    YAML_NODE *Class = YamlFindField(Node, "class");
    if(Class)
    {
        Key->Class = HiveEncodeString(YamlGetScalar(Class), 0);
        if(Key->Class.len > UINT16_MAX)
        {
            YamlError("key class is longer than 65535 bytes");
        }
    }
    YAML_NODE *Security = YamlFindField(Node, "security");
    Key->Security = Security ? HiveInternSecurity(Context, HiveReadSecurity(Context, Security)) : Inherited;
    if(Key->Security->References == UINT32_MAX)
    {
        YamlError("security reference count overflow");
    }
    Key->Security->References++;
    YAML_NODE *Values = YamlFindField(Node, "values");
    if(Values)
    {
        if(Values->type != YAML_SEQUENCE || Values->count > (HIVE_CELL_LIMIT - 4) / 4)
        {
            YamlError("value list exceeds one cell");
        }
        Key->ValueCount = Values->count;
        Key->Values = YamlAllocateMemory(Key->ValueCount * sizeof(*Key->Values));
        for(size_t Index = 0; Index < Key->ValueCount; Index++)
        {
            Key->Values[Index] = HiveReadValue(Context, Values->values[Index]);
        }
        qsort(Key->Values, Key->ValueCount, sizeof(*Key->Values), HiveCompareValues);
        for(size_t Index = 1; Index < Key->ValueCount; Index++)
        {
            if(!HiveCompareNames(&Key->Values[Index - 1].Name, &Key->Values[Index].Name))
            {
                YamlError("duplicate value name after CellFormat 1 case folding");
            }
        }
    }
    if((Key->Flags & 0x40) && Key->ValueCount)
    {
        YamlError("predefined-handle keys cannot have values");
    }
    YAML_NODE *Children = YamlFindField(Node, "subkeys");
    if(Children)
    {
        if(Children->type != YAML_SEQUENCE || Children->count > HIVE_LOGICAL_LIMIT / 80)
        {
            YamlError("invalid subkey sequence");
        }
        Key->ChildCount = Children->count;
        Key->Children = YamlAllocateMemory(Key->ChildCount * sizeof(*Key->Children));
        for(size_t Index = 0; Index < Key->ChildCount; Index++)
        {
            Key->Children[Index] = HiveReadKey(Context, Children->values[Index], Key->Security, Depth + 1);
        }
        qsort(Key->Children, Key->ChildCount, sizeof(*Key->Children), HiveCompareKeys);
        for(size_t Index = 1; Index < Key->ChildCount; Index++)
        {
            if(!HiveCompareNames(&Key->Children[Index - 1]->Name, &Key->Children[Index]->Name))
            {
                YamlError("duplicate subkey name after CellFormat 1 case folding");
            }
        }
    }
    return Key;
}

static
int
HiveIdentifierStart(unsigned char Character)
{
    return (Character >= 'A' && Character <= 'Z') ||
           (Character >= 'a' && Character <= 'z') || Character == '_';
}

static
int
HiveIdentifierCharacter(unsigned char Character)
{
    return HiveIdentifierStart(Character) || (Character >= '0' && Character <= '9');
}

static
void
HiveReadDictionary(HIVE_BUILD_CONTEXT *Context,
                   YAML_NODE *Document)
{
    Context->Strings = YamlFindField(Document, "strings");
    if(!Context->Strings)
    {
        return;
    }
    if(Context->Strings->type != YAML_MAP)
    {
        YamlError("strings must be a mapping of identifiers to literal text");
    }
    for(size_t Index = 0; Index < Context->Strings->count; Index++)
    {
        const unsigned char *Name = (const unsigned char *)Context->Strings->keys[Index];
        if(!HiveIdentifierStart(*Name))
        {
            YamlError("invalid dictionary identifier: %s", Name);
        }
        for(const unsigned char *Character = Name + 1; *Character; Character++)
        {
            if(!HiveIdentifierCharacter(*Character))
            {
                YamlError("invalid dictionary identifier: %s", Name);
            }
        }
        (void)HiveEncodeString(YamlGetScalar(Context->Strings->values[Index]), 0);
    }
}

static
char *
HiveExpandText(HIVE_BUILD_CONTEXT *Context,
               YAML_NODE *Node,
               const char *Field)
{
    const char *Text = YamlGetScalar(Node);
    if(!strchr(Text, '$'))
    {
        return Node->text;
    }
    YAML_BUFFER Output = {0};
    while(*Text)
    {
        if(Text[0] == '$' && Text[1] == '$')
        {
            YamlAppendBuffer(&Output, Text, 1);
            Text += 2;
        }
        else if(Text[0] == '$' && HiveIdentifierStart((unsigned char)Text[1]))
        {
            const char *End = Text + 2;
            while(HiveIdentifierCharacter((unsigned char)*End))
            {
                End++;
            }
            char *Name = YamlAllocateMemory((size_t)(End - Text));
            memcpy(Name, Text + 1, (size_t)(End - Text - 1));
            YAML_NODE *Value = Context->Strings ? YamlFindField(Context->Strings, Name) : NULL;
            if(!Value)
            {
                YamlError("%s: undefined dictionary symbol $%s", Field, Name);
            }
            const char *Replacement = YamlGetScalar(Value);
            YamlAppendBuffer(&Output, Replacement, strlen(Replacement));
            Text = End;
        }
        else
        {
            YamlAppendBuffer(&Output, Text++, 1);
        }
    }
    YamlAppendBuffer(&Output, "", 1);
    Node->text = (char *)Output.data;
    return Node->text;
}

static
char *
HiveReadPath(HIVE_BUILD_CONTEXT *Context,
             YAML_NODE *Node,
             const char *Field)
{
    char *Path = HiveExpandText(Context, Node, Field);
    for(char *Character = Path; *Character; Character++)
    {
        if(*Character == '/')
        {
            *Character = '\\';
        }
        if(*Character == '\\' && (Character == Path || !Character[1] || Character[1] == '\\' || Character[1] == '/'))
        {
            YamlError("%s: expected a relative path without empty components: %s", Field, Path);
        }
    }
    return Path;
}

static
int
HiveEqualPath(const char *First,
               const char *Second)
{
    while(*First && *Second)
    {
        if(HiveUpcase((unsigned char)*First++) != HiveUpcase((unsigned char)*Second++))
        {
            return 0;
        }
    }
    return *First == *Second;
}

static
HIVE_SOURCE_KEY *
HiveCreateSourceKey(const char *Name)
{
    HIVE_SOURCE_KEY *Key = YamlAllocateMemory(sizeof(*Key));
    Key->Record = YamlCreateNode(YAML_MAP);
    YAML_NODE *NameNode = YamlCreateString(Name);
    YamlAddField(Key->Record, "name", NameNode);
    YamlAddField(Key->Record, "values", YamlCreateNode(YAML_SEQUENCE));
    YamlAddField(Key->Record, "subkeys", YamlCreateNode(YAML_SEQUENCE));
    Key->Name = HiveReadName(NameNode, 1);
    Key->Hash = 2166136261u;
    for(size_t Index = 0; Index < Key->Name.Length; Index++)
    {
        unsigned Character = HiveUpcase(Key->Name.Characters[Index]);
        Key->Hash = (Key->Hash ^ (Character & 255)) * 16777619u;
        Key->Hash = (Key->Hash ^ (Character >> 8)) * 16777619u;
    }
    return Key;
}

static
HIVE_SOURCE_KEY *
HiveFindSourceChild(HIVE_SOURCE_KEY *Parent,
                    HIVE_SOURCE_KEY *Candidate)
{
    if(Parent->IndexSize)
    {
        size_t Position = Candidate->Hash & (Parent->IndexSize - 1);
        while(Parent->Index[Position])
        {
            HIVE_SOURCE_KEY *Child = Parent->Index[Position];
            if(!HiveCompareNames(&Child->Name, &Candidate->Name))
            {
                return Child;
            }
            Position = (Position + 1) & (Parent->IndexSize - 1);
        }
    }
    if(!Parent->IndexSize || (Parent->ChildCount + 1) * 2 >= Parent->IndexSize)
    {
        size_t Size = Parent->IndexSize ? Parent->IndexSize * 2 : 16;
        HIVE_SOURCE_KEY **Index = YamlAllocateMemory(Size * sizeof(*Index));
        for(size_t Slot = 0; Slot < Parent->IndexSize; Slot++)
        {
            HIVE_SOURCE_KEY *Child = Parent->Index[Slot];
            if(Child)
            {
                size_t Position = Child->Hash & (Size - 1);
                while(Index[Position])
                {
                    Position = (Position + 1) & (Size - 1);
                }
                Index[Position] = Child;
            }
        }
        Parent->Index = Index;
        Parent->IndexSize = Size;
    }
    size_t Position = Candidate->Hash & (Parent->IndexSize - 1);
    while(Parent->Index[Position])
    {
        Position = (Position + 1) & (Parent->IndexSize - 1);
    }
    Parent->Index[Position] = Candidate;
    Parent->ChildCount++;
    YamlAppendItem(YamlGetField(Parent->Record, "subkeys"), Candidate->Record);
    return Candidate;
}

static
void
HivePrepareValues(HIVE_BUILD_CONTEXT *Context,
                  YAML_NODE *Values,
                  const char *Location)
{
    if(!Values)
    {
        return;
    }
    if(Values->type != YAML_SEQUENCE)
    {
        YamlError("%s.values: expected a sequence", Location);
    }
    for(size_t Index = 0; Index < Values->count; Index++)
    {
        YAML_NODE *Value = Values->values[Index];
        YamlValidateFields(Value, "name type", "data raw");
        HiveExpandText(Context, YamlGetField(Value, "name"), YamlFormatString("%s.values[%zu].name", Location, Index));
        uint32_t Type = HiveReadValueType(YamlGetField(Value, "type"));
        YAML_NODE *Data = YamlFindField(Value, "data");
        if(Data && (Type == 1 || Type == 2 || Type == 6))
        {
            HiveExpandText(Context, Data, YamlFormatString("%s.values[%zu].data", Location, Index));
        }
        else if(Data && Type == 7)
        {
            if(Data->type != YAML_SEQUENCE)
            {
                YamlError("%s.values[%zu].data: HIVE_MULTI_SZ requires a sequence", Location, Index);
            }
            for(size_t Element = 0; Element < Data->count; Element++)
            {
                HiveExpandText(Context, Data->values[Element], YamlFormatString("%s.values[%zu].data[%zu]", Location, Index, Element));
            }
        }
    }
}

static
void
HiveMergeMetadata(HIVE_BUILD_CONTEXT *Context,
                   HIVE_SOURCE_KEY *Key,
                   YAML_NODE *Source,
                   const char *Location)
{
    const char *Fields[] = {"class", "timestamp", "flags", "access_bits", "security"};
    for(size_t Index = 0; Index < sizeof(Fields) / sizeof(Fields[0]); Index++)
    {
        YAML_NODE *Value = YamlFindField(Source, Fields[Index]);
        if(!Value)
        {
            continue;
        }
        if(!Index)
        {
            HiveExpandText(Context, Value, YamlFormatString("%s.class", Location));
        }
        YAML_NODE *Previous = YamlFindField(Key->Record, Fields[Index]);
        if(Previous)
        {
            int Equal;
            if(Index == 4)
            {
                YAML_BUFFER First = HiveReadSecurity(Context, Previous), Second = HiveReadSecurity(Context, Value);
                Equal = First.len == Second.len && !memcmp(First.data, Second.data, First.len);
            }
            else if(!Index)
            {
                Equal = !strcmp(YamlGetScalar(Previous), YamlGetScalar(Value));
            }
            else
            {
                uint64_t Maximum = Index == 1 ? UINT64_MAX : Index == 2 ? UINT16_MAX : UINT32_MAX;
                Equal = HiveParseInteger(YamlGetScalar(Previous), Maximum) == HiveParseInteger(YamlGetScalar(Value), Maximum);
            }
            if(!Equal)
            {
                YamlError("%s: conflicting %s metadata for key %s", Location, Fields[Index], Key->Name.Length ? YamlGetScalar(YamlGetField(Key->Record, "name")) : "<root>");
            }
        }
        else
        {
            YamlAddField(Key->Record, Fields[Index], Value);
        }
    }
}

static
const char *
HiveResolveControlSet(HIVE_BUILD_CONTEXT *Context,
                      YAML_NODE *Entries)
{
    int HasAlias = 0, Ambiguous = 0, HasCurrent = 0;
    uint32_t Existing = 0, Current = 0;
    for(size_t Index = 0; Index < Entries->count; Index++)
    {
        YAML_NODE *Entry = Entries->values[Index];
        const char *Path = YamlGetScalar(YamlGetField(Entry, "key"));
        size_t Length = strcspn(Path, "\\");
        char *First = YamlAllocateMemory(Length + 1);
        memcpy(First, Path, Length);
        if(HiveEqualPath(First, "CurrentControlSet"))
        {
            HasAlias = 1;
        }
        char Saved = Length > 10 ? First[10] : 0;
        if(Length > 10)
        {
            First[10] = 0;
        }
        int IsControlSet = Length > 10 && HiveEqualPath(First, "ControlSet");
        if(Length > 10)
        {
            First[10] = Saved;
        }
        if(IsControlSet)
        {
            uint32_t Number = 0;
            int Valid = 1;
            for(size_t Digit = 10; Digit < Length; Digit++)
            {
                unsigned Value = (unsigned char)First[Digit] - '0';
                if(Value > 9 || Number > (UINT32_MAX - Value) / 10)
                {
                    Valid = 0;
                    break;
                }
                Number = Number * 10 + Value;
            }
            if(Valid && Number && HiveEqualPath(First, YamlFormatString("ControlSet%03u", Number)))
            {
                if(Existing && Existing != Number)
                {
                    Ambiguous = 1;
                }
                Existing = Number;
            }
        }
    }
    if(!HasAlias)
    {
        return NULL;
    }
    for(size_t Index = 0; Index < Entries->count; Index++)
    {
        YAML_NODE *Entry = Entries->values[Index];
        if(!HiveEqualPath(YamlGetScalar(YamlGetField(Entry, "key")), "Select"))
        {
            continue;
        }
        YAML_NODE *Values = YamlFindField(Entry, "values");
        for(size_t ValueIndex = 0; Values && ValueIndex < Values->count; ValueIndex++)
        {
            YAML_NODE *Value = Values->values[ValueIndex];
            if(HiveEqualPath(YamlGetScalar(YamlGetField(Value, "name")), "Current"))
            {
                HIVE_VALUE Selection = HiveReadValue(Context, Value);
                if(HasCurrent || Selection.Type != 4 || Selection.Data.len != 4 || !ReadUInt32(Selection.Data.data))
                {
                    YamlError("Select.Current: control-set alias requires one nonzero HIVE_DWORD value");
                }
                Current = ReadUInt32(Selection.Data.data);
                HasCurrent = 1;
            }
        }
    }
    if(!HasCurrent && Ambiguous)
    {
        YamlError("CurrentControlSet is ambiguous; declare Select.Current explicitly");
    }
    if(!HasCurrent)
    {
        Current = Existing ? Existing : 1;
    }
    return YamlFormatString("ControlSet%03u", Current);
}

static
YAML_NODE *
HiveReadFlatEntries(HIVE_BUILD_CONTEXT *Context,
                    YAML_NODE *Root)
{
    YamlValidateFields(Root, "type entries", "path class timestamp flags access_bits security");
    const char *Type = YamlGetScalar(YamlGetField(Root, "type"));
    if(strcmp(Type, "HKLM") && strcmp(Type, "HKCU") && strcmp(Type, "HKU") && strcmp(Type, "HBCD"))
    {
        YamlError("root.type: unsupported or unresolved root %s; select HKLM, HKCU, HKU or HBCD", Type);
    }
    YAML_NODE *PathNode = YamlFindField(Root, "path");
    const char *Path = PathNode ? HiveReadPath(Context, PathNode, "root.path") : "";
    if(strcmp(Type, "HKCU") && !*Path)
    {
        YamlError("root.path: %s requires an explicit nonempty mount path", Type);
    }
    if(!strcmp(Type, "HBCD") && !HiveEqualPath(Path, "BCD00000000"))
    {
        YamlError("root.path: HBCD requires BCD00000000");
    }
    const char *Name = strrchr(Path, '\\');
    Name = Name ? Name + 1 : *Path ? Path : "USER";
    HIVE_SOURCE_KEY *Tree = HiveCreateSourceKey(Name);
    HiveMergeMetadata(Context, Tree, Root, "root");
    YAML_NODE *Entries = YamlGetField(Root, "entries");
    if(Entries->type != YAML_SEQUENCE)
    {
        YamlError("root.entries: expected a sequence");
    }
    for(size_t Index = 0; Index < Entries->count; Index++)
    {
        YAML_NODE *Entry = Entries->values[Index];
        YamlValidateFields(Entry, "key", "class timestamp flags access_bits security values");
        const char *Location = YamlFormatString("root.entries[%zu]", Index);
        HiveReadPath(Context, YamlGetField(Entry, "key"), YamlFormatString("%s.key", Location));
        HivePrepareValues(Context, YamlFindField(Entry, "values"), Location);
    }
    const char *Alias = !strcmp(Type, "HKLM") && HiveEqualPath(Path, "SYSTEM") ? HiveResolveControlSet(Context, Entries) : NULL;
    for(size_t Index = 0; Index < Entries->count; Index++)
    {
        YAML_NODE *Entry = Entries->values[Index];
        YamlValidateFields(Entry, "key", "class timestamp flags access_bits security values");
        const char *Location = YamlFormatString("root.entries[%zu]", Index);
        const char *PathText = YamlGetScalar(YamlGetField(Entry, "key"));
        char *Components = YamlCopyString(PathText), *Component = Components;
        HIVE_SOURCE_KEY *Key = Tree;
        unsigned Depth = 0;
        while(*Component)
        {
            if(++Depth > HIVE_TRAVERSAL_LIMIT)
            {
                YamlError("%s.key: registry path exceeds the traversal budget", Location);
            }
            char *Separator = strchr(Component, '\\');
            if(Separator)
            {
                *Separator = 0;
            }
            if(Depth == 1 && Alias && HiveEqualPath(Component, "CurrentControlSet"))
            {
                Component = (char *)Alias;
            }
            YAML_ALLOCATION *Checkpoint = YamlAllocations;
            HIVE_SOURCE_KEY *Candidate = HiveCreateSourceKey(Component);
            Key = HiveFindSourceChild(Key, Candidate);
            if(Key != Candidate)
            {
                YamlReleaseAllocations(Checkpoint);
            }
            if(!Separator)
            {
                break;
            }
            Component = Separator + 1;
        }
        HiveMergeMetadata(Context, Key, Entry, Location);
        YAML_NODE *Values = YamlFindField(Entry, "values");
        if(Values)
        {
            YAML_NODE *Destination = YamlGetField(Key->Record, "values");
            for(size_t Value = 0; Value < Values->count; Value++)
            {
                YamlAppendItem(Destination, Values->values[Value]);
            }
        }
    }
    return Tree->Record;
}

static
uint32_t
HiveAllocateCell(HIVE_BUILD_CONTEXT *Context,
                 size_t PayloadLength,
                 unsigned char **Payload)
{
    if(PayloadLength > HIVE_CELL_LIMIT - 4)
    {
        YamlError("cell exceeds the kernel's 1 MiB cell limit");
    }
    uint32_t CellSize = ((uint32_t)PayloadLength + 4 + 7) & ~7u;
    HIVE_BIN *Bin = Context->LastBin;
    if(!Bin || Bin->Size - Bin->Used < CellSize)
    {
        uint32_t Size = (CellSize + sizeof(HIVE_BIN_HEADER) + HIVE_PAGE_SIZE - 1) & ~(HIVE_PAGE_SIZE - 1);
        if(Size > HIVE_LOGICAL_LIMIT - Context->LogicalBytes)
        {
            YamlError("hive exceeds the XTHV1 logical size limit");
        }
        Bin = YamlAllocateMemory(sizeof(*Bin));
        Bin->Data = YamlAllocateMemory(Size);
        Bin->Size = Size;
        Bin->Offset = Context->LogicalBytes;
        Bin->Used = sizeof(HIVE_BIN_HEADER);
        HIVE_BIN_HEADER *Header = (HIVE_BIN_HEADER *)Bin->Data;
        memcpy(Header->Signature, "hbin", 4);
        HiveStoreInteger(Header->FileOffset, Bin->Offset, 4);
        HiveStoreInteger(Header->Size, Size, 4);
        if(Context->LastBin)
        {
            Context->LastBin->Next = Bin;
        }
        else
        {
            Context->Bins = Bin;
        }
        Context->LastBin = Bin;
        Context->LogicalBytes += Size;
    }
    uint32_t Cell = Bin->Offset + Bin->Used;
    HiveStoreInteger(Bin->Data + Bin->Used, 0u - CellSize, 4);
    *Payload = Bin->Data + Bin->Used + 4;
    Bin->Used += CellSize;
    return Cell;
}

static
uint32_t
HiveStoreData(HIVE_BUILD_CONTEXT *Context,
              const YAML_BUFFER *Data)
{
    unsigned char *Payload;
    uint32_t Cell = HiveAllocateCell(Context, Data->len, &Payload);
    if(Data->len)
    {
        memcpy(Payload, Data->data, Data->len);
    }
    return Cell;
}

static
void
HiveBuildValue(HIVE_BUILD_CONTEXT *Context,
               HIVE_VALUE *Value)
{
    unsigned char *Payload;
    Value->Cell = HiveAllocateCell(Context, sizeof(HIVE_VALUE_NODE) + Value->Name.Bytes.len, &Payload);
    HIVE_VALUE_NODE *Node = (HIVE_VALUE_NODE *)Payload;
    memcpy(Node->Signature, "vk", 2);
    HiveStoreInteger(Node->NameLength, Value->Name.Bytes.len, 2);
    HiveStoreInteger(Node->Type, Value->Type, 4);
    HiveStoreInteger(Node->Flags, Value->Name.Compressed ? 1 : 0, 2);
    if(Value->Name.Bytes.len)
    {
        memcpy(Payload + sizeof(*Node), Value->Name.Bytes.data, Value->Name.Bytes.len);
    }
    if(Value->Data.len <= 4)
    {
        HiveStoreInteger(Node->DataLength, 0x80000000u | Value->Data.len, 4);
        if(Value->Data.len)
        {
            memcpy(Node->Data, Value->Data.data, Value->Data.len);
        }
    }
    else
    {
        uint32_t DataCell;
        if(Value->Data.len > HIVE_BIG_DATA_CHUNK)
        {
            size_t Count = (Value->Data.len + HIVE_BIG_DATA_CHUNK - 1) / HIVE_BIG_DATA_CHUNK;
            if(Count > UINT16_MAX)
            {
                YamlError("value exceeds the big-data chunk count limit");
            }
            unsigned char *Record, *List;
            DataCell = HiveAllocateCell(Context, 8, &Record);
            memcpy(Record, "db", 2);
            HiveStoreInteger(Record + 2, Count, 2);
            uint32_t ListCell = HiveAllocateCell(Context, Count * 4, &List);
            HiveStoreInteger(Record + 4, ListCell, 4);
            size_t Position = 0;
            for(size_t Index = 0; Index < Count; Index++)
            {
                size_t Length = Value->Data.len - Position;
                if(Length > HIVE_BIG_DATA_CHUNK)
                {
                    Length = HIVE_BIG_DATA_CHUNK;
                }
                YAML_BUFFER Chunk = {.data = Value->Data.data + Position, .len = Length};
                HiveStoreInteger(List + Index * 4, HiveStoreData(Context, &Chunk), 4);
                Position += Length;
            }
        }
        else
        {
            DataCell = HiveStoreData(Context, &Value->Data);
        }
        HiveStoreInteger(Node->DataLength, Value->Data.len, 4);
        HiveStoreInteger(Node->Data, DataCell, 4);
    }
}

static
uint32_t
HiveBuildIndex(HIVE_BUILD_CONTEXT *Context,
               const uint32_t *Cells,
               size_t Count,
               int Leaves,
               unsigned *Levels)
{
    size_t Groups = (Count + HIVE_INDEX_ENTRIES - 1) / HIVE_INDEX_ENTRIES;
    uint32_t *Parents = YamlAllocateMemory(Groups * sizeof(*Parents));
    for(size_t Group = 0; Group < Groups; Group++)
    {
        size_t First = Group * HIVE_INDEX_ENTRIES;
        size_t Entries = Count - First;
        if(Entries > HIVE_INDEX_ENTRIES)
        {
            Entries = HIVE_INDEX_ENTRIES;
        }
        unsigned char *Record;
        Parents[Group] = HiveAllocateCell(Context, 4 + Entries * 4, &Record);
        memcpy(Record, Leaves ? "li" : "ri", 2);
        HiveStoreInteger(Record + 2, Entries, 2);
        for(size_t Index = 0; Index < Entries; Index++)
        {
            HiveStoreInteger(Record + 4 + Index * 4, Cells[First + Index], 4);
        }
    }
    if(Groups == 1)
    {
        return Parents[0];
    }
    (*Levels)++;
    return HiveBuildIndex(Context, Parents, Groups, 0, Levels);
}

static
void
HiveBuildKey(HIVE_BUILD_CONTEXT *Context,
             HIVE_KEY *Key,
             uint32_t Parent)
{
    unsigned char *Payload;
    Key->Cell = HiveAllocateCell(Context, sizeof(HIVE_KEY_NODE) + Key->Name.Bytes.len, &Payload);
    HIVE_KEY_NODE *Node = (HIVE_KEY_NODE *)Payload;
    memcpy(Node->Signature, "nk", 2);
    HiveStoreInteger(Node->Flags, Key->Flags, 2);
    HiveStoreInteger(Node->LastWriteTime, Key->Timestamp, 8);
    HiveStoreInteger(Node->AccessBits, Key->AccessBits, 4);
    HiveStoreInteger(Node->Parent, Parent == HIVE_CELL_NIL ? Key->Cell : Parent, 4);
    HiveStoreInteger(Node->VolatileList, HIVE_CELL_NIL, 4);
    HiveStoreInteger(Node->SubKeyList, HIVE_CELL_NIL, 4);
    HiveStoreInteger(Node->ValueList, HIVE_CELL_NIL, 4);
    HiveStoreInteger(Node->Class, HIVE_CELL_NIL, 4);
    HiveStoreInteger(Node->Security, Key->Security->Cell, 4);
    HiveStoreInteger(Node->NameLength, Key->Name.Bytes.len, 2);
    HiveStoreInteger(Node->ClassLength, Key->Class.len, 2);
    if(Key->Name.Bytes.len)
    {
        memcpy(Payload + sizeof(*Node), Key->Name.Bytes.data, Key->Name.Bytes.len);
    }
    if(Key->Class.len)
    {
        HiveStoreInteger(Node->Class, HiveStoreData(Context, &Key->Class), 4);
    }
    if(Key->ValueCount)
    {
        unsigned char *List;
        uint32_t Cell = HiveAllocateCell(Context, Key->ValueCount * 4, &List);
        HiveStoreInteger(Node->ValueCount, Key->ValueCount, 4);
        HiveStoreInteger(Node->ValueList, Cell, 4);
        for(size_t Index = 0; Index < Key->ValueCount; Index++)
        {
            HIVE_VALUE *Value = &Key->Values[Index];
            HiveBuildValue(Context, Value);
            HiveStoreInteger(List + Index * 4, Value->Cell, 4);
            if(Value->Name.Length * 2 > ReadUInt32(Node->MaxValueNameLength))
            {
                HiveStoreInteger(Node->MaxValueNameLength, Value->Name.Length * 2, 4);
            }
            if(Value->Data.len > ReadUInt32(Node->MaxValueDataLength))
            {
                HiveStoreInteger(Node->MaxValueDataLength, Value->Data.len, 4);
            }
        }
    }
    if(Key->ChildCount)
    {
        uint32_t *Cells = YamlAllocateMemory(Key->ChildCount * sizeof(*Cells));
        unsigned MaximumCost = 0, IndexLevels = 0;
        for(size_t Index = 0; Index < Key->ChildCount; Index++)
        {
            HIVE_KEY *Child = Key->Children[Index];
            HiveBuildKey(Context, Child, Key->Cell);
            Cells[Index] = Child->Cell;
            if(Child->TraversalCost > MaximumCost)
            {
                MaximumCost = Child->TraversalCost;
            }
            if(Child->Name.Length * 2 > ReadUInt32(Node->MaxNameLength))
            {
                HiveStoreInteger(Node->MaxNameLength, Child->Name.Length * 2, 4);
            }
            if(Child->Class.len > ReadUInt32(Node->MaxClassLength))
            {
                HiveStoreInteger(Node->MaxClassLength, Child->Class.len, 4);
            }
        }
        uint32_t Cell = HiveBuildIndex(Context, Cells, Key->ChildCount, 1, &IndexLevels);
        Key->TraversalCost = MaximumCost + 1 + IndexLevels;
        if(Key->TraversalCost > HIVE_TRAVERSAL_LIMIT)
        {
            YamlError("key and index tree together exceed the kernel traversal budget");
        }
        HiveStoreInteger(Node->SubKeyCount, Key->ChildCount, 4);
        HiveStoreInteger(Node->SubKeyList, Cell, 4);
    }
}

static
void
HiveBuildSecurity(HIVE_BUILD_CONTEXT *Context)
{
    for(HIVE_SECURITY *Security = Context->Security; Security; Security = Security->Next)
    {
        if(!Security->References)
        {
            continue;
        }
        unsigned char *Payload;
        Security->Cell = HiveAllocateCell(Context, 20 + Security->Descriptor.len, &Payload);
        memcpy(Payload, "sk", 2);
        HiveStoreInteger(Payload + 12, Security->References, 4);
        HiveStoreInteger(Payload + 16, Security->Descriptor.len, 4);
        memcpy(Payload + 20, Security->Descriptor.data, Security->Descriptor.len);
    }
    HIVE_SECURITY *First = NULL, *Previous = NULL;
    unsigned char *PreviousPayload = NULL;
    for(HIVE_SECURITY *Security = Context->Security; Security; Security = Security->Next)
    {
        if(!Security->References)
        {
            continue;
        }
        HIVE_BIN *Bin = Context->Bins;
        while(Security->Cell >= Bin->Offset + Bin->Size)
        {
            Bin = Bin->Next;
        }
        unsigned char *Payload = Bin->Data + Security->Cell - Bin->Offset + 4;
        if(Previous)
        {
            HiveStoreInteger(PreviousPayload + 4, Security->Cell, 4);
            HiveStoreInteger(Payload + 8, Previous->Cell, 4);
        }
        else
        {
            First = Security;
        }
        Previous = Security;
        PreviousPayload = Payload;
    }
    HiveStoreInteger(PreviousPayload + 4, First->Cell, 4);
    HIVE_BIN *Bin = Context->Bins;
    while(First->Cell >= Bin->Offset + Bin->Size)
    {
        Bin = Bin->Next;
    }
    HiveStoreInteger(Bin->Data + First->Cell - Bin->Offset + 4 + 8, Previous->Cell, 4);
}

static
void
HiveWrite(const void *Data,
          size_t Length)
{
    if(Length && fwrite(Data, 1, Length, HiveOutput) != Length)
    {
        YamlError("cannot write hive: %s", strerror(errno));
    }
}

static
void
HiveHashPage(HIVE_BUILD_CONTEXT *Context,
             const char *Domain,
             uint64_t PageNumber,
             uint64_t LogicalPage,
             uint32_t Level,
             const void *Page,
             HIVE_PAGE_DESCRIPTOR *Descriptor)
{
    HIVE_HASH_CONTEXT Header = {0};
    HIVE_SHA1_CONTEXT Hash;
    memcpy(Header.Domain, Domain, 8);
    memcpy(Header.HiveId, Context->HiveId, sizeof(Header.HiveId));
    HiveStoreInteger(Header.PageNumber, PageNumber, 8);
    HiveStoreInteger(Header.Generation, 1, 8);
    HiveStoreInteger(Header.FirstLogicalPage, LogicalPage, 8);
    HiveStoreInteger(Header.Level, Level, 4);
    memset(Descriptor, 0, sizeof(*Descriptor));
    HiveStoreInteger(Descriptor->PageNumber, PageNumber, 8);
    HiveStoreInteger(Descriptor->Generation, 1, 8);
    HiveSha1Initialize(&Hash);
    HiveSha1Update(&Hash, &Header, sizeof(Header));
    HiveSha1Update(&Hash, Page, HIVE_PAGE_SIZE);
    HiveSha1Finish(&Hash, Descriptor->Hash);
}

static
HIVE_PAGE_DESCRIPTOR
HiveWriteMap(HIVE_BUILD_CONTEXT *Context,
             const HIVE_PAGE_DESCRIPTOR *Data,
             uint64_t FirstLogicalPage,
             size_t Count,
             unsigned Level)
{
    HIVE_MAP_NODE Node = {0};
    memcpy(Node.Magic, "XTHVMAP1", 8);
    memcpy(Node.HiveId, Context->HiveId, sizeof(Node.HiveId));
    HiveStoreInteger(Node.Generation, 1, 8);
    HiveStoreInteger(Node.FirstLogicalPage, FirstLogicalPage, 8);
    HiveStoreInteger(Node.Level, Level, 4);
    size_t Span = 1;
    for(unsigned Index = 0; Index < Level; Index++)
    {
        Span *= HIVE_MAP_ENTRIES;
    }
    size_t Entries = (Count + Span - 1) / Span;
    HiveStoreInteger(Node.UsedEntries, Entries, 4);
    for(size_t Index = 0; Index < Entries; Index++)
    {
        size_t Offset = Index * Span, ChildCount = Count - Offset;
        if(ChildCount > Span)
        {
            ChildCount = Span;
        }
        Node.Entries[Index] = Level ? HiveWriteMap(Context, Data + Offset, FirstLogicalPage + Offset,
                                                 ChildCount, Level - 1) : Data[Index];
    }
    HIVE_PAGE_DESCRIPTOR Descriptor;
    uint64_t PageNumber = Context->NextPage++;
    HiveHashPage(Context, "XTHVMAP1", PageNumber, FirstLogicalPage, Level, &Node, &Descriptor);
    HiveWrite(&Node, sizeof(Node));
    return Descriptor;
}

static
void
HiveCleanOutput(void)
{
    if(HiveOutput)
    {
        fclose(HiveOutput);
        HiveOutput = NULL;
    }
    if(HiveTemporary)
    {
        remove(HiveTemporary);
    }
}

static
void
HiveCreateOutput(const char *Path)
{
    for(unsigned Attempt = 0; Attempt < 100; Attempt++)
    {
        char *Candidate = YamlFormatString("%s.mkxthv-%ld-%u.tmp", Path, (long)XTCHAIN_PROCESS_ID(), Attempt);
        HiveOutput = fopen(Candidate, "wbx");
        if(HiveOutput)
        {
            HiveTemporary = Candidate;
            return;
        }
        if(errno != EEXIST)
        {
            YamlError("cannot create output temporary file: %s", strerror(errno));
        }
    }
    YamlError("cannot allocate temporary output filename");
}

static
void
HivePublishOutput(const char *Path)
{
    if(fflush(HiveOutput))
    {
        YamlError("cannot flush hive");
    }
#ifdef _WIN32
    if(_commit(_fileno(HiveOutput)))
#else
    if(fsync(fileno(HiveOutput)))
#endif
    {
        YamlError("cannot sync hive");
    }
    FILE *Finished = HiveOutput;
    HiveOutput = NULL;
    if(fclose(Finished))
    {
        YamlError("cannot close hive");
    }
#ifdef _WIN32
    if(!MoveFileExA(HiveTemporary, Path, MOVEFILE_REPLACE_EXISTING | MOVEFILE_WRITE_THROUGH))
#else
    if(rename(HiveTemporary, Path))
#endif
    {
        YamlError("cannot replace output hive");
    }
    HiveTemporary = NULL;
}

static
void
HiveWriteContainer(HIVE_BUILD_CONTEXT *Context,
                   HIVE_KEY *Root,
                   const char *Path,
                   int ExplicitId)
{
    HIVE_SHA1_CONTEXT Hash;
    HiveSha1Initialize(&Hash);
    HiveSha1Update(&Hash, "XTHVID01", 8);
    for(HIVE_BIN *Bin = Context->Bins; Bin; Bin = Bin->Next)
    {
        if(Bin->Used < Bin->Size)
        {
            HiveStoreInteger(Bin->Data + Bin->Used, Bin->Size - Bin->Used, 4);
        }
        HiveSha1Update(&Hash, Bin->Data, Bin->Size);
    }
    if(!ExplicitId)
    {
        unsigned char Digest[20];
        HiveSha1Finish(&Hash, Digest);
        memcpy(Context->HiveId, Digest, sizeof(Context->HiveId));
        unsigned Present = 0;
        for(unsigned Index = 0; Index < sizeof(Context->HiveId); Index++)
        {
            Present |= Context->HiveId[Index];
        }
        if(!Present)
        {
            Context->HiveId[15] = 1;
        }
    }
    HiveCreateOutput(Path);
    unsigned char Empty[HIVE_PAGE_SIZE] = {0};
    HiveWrite(Empty, sizeof(Empty));
    HiveWrite(Empty, sizeof(Empty));
    Context->NextPage = 2;
    size_t Count = Context->LogicalBytes / HIVE_PAGE_SIZE;
    HIVE_PAGE_DESCRIPTOR *Data = YamlAllocateMemory(Count * sizeof(*Data));
    size_t LogicalPage = 0;
    for(HIVE_BIN *Bin = Context->Bins; Bin; Bin = Bin->Next)
    {
        for(size_t Offset = 0; Offset < Bin->Size; Offset += HIVE_PAGE_SIZE)
        {
            uint64_t PageNumber = Context->NextPage++;
            HiveHashPage(Context, "XTHVDAT1", PageNumber, LogicalPage, UINT32_MAX,
                         Bin->Data + Offset, &Data[LogicalPage]);
            HiveWrite(Bin->Data + Offset, HIVE_PAGE_SIZE);
            LogicalPage++;
        }
    }
    HIVE_SUPERBLOCK Superblock = {0};
    Superblock.MapRoot = HiveWriteMap(Context, Data, 0, Count, 2);
    memcpy(Superblock.Magic, "XTHV1\r\n\032", 8);
    HiveStoreInteger(Superblock.Major, 1, 2);
    HiveStoreInteger(Superblock.HeaderBytes, 176, 4);
    HiveStoreInteger(Superblock.PageBytes, HIVE_PAGE_SIZE, 4);
    memcpy(Superblock.HiveId, Context->HiveId, sizeof(Superblock.HiveId));
    HiveStoreInteger(Superblock.Generation, 1, 8);
    HiveStoreInteger(Superblock.LogicalBytes, Context->LogicalBytes, 8);
    HiveStoreInteger(Superblock.FilePageLimit, Context->NextPage, 8);
    HiveStoreInteger(Superblock.RootCell, Root->Cell, 4);
    HiveStoreInteger(Superblock.CellFormat, 1, 4);
    HiveStoreInteger(Superblock.CommitTime, Context->Timestamp, 8);
    memcpy(Superblock.WriterId, Context->WriterId, sizeof(Superblock.WriterId));
    HiveStoreInteger(Superblock.HashAlgorithm, 1, 4);
    HiveSha1Initialize(&Hash);
    HiveSha1Update(&Hash, "XTHVSUP1", 8);
    HiveSha1Update(&Hash, &Superblock, sizeof(Superblock));
    HiveSha1Finish(&Hash, Superblock.Hash);
    if(fseek(HiveOutput, 0, SEEK_SET))
    {
        YamlError("cannot seek to the superblock");
    }
    HiveWrite(&Superblock, sizeof(Superblock));
    HivePublishOutput(Path);
}

int
main(int argc,
     char **argv)
{
    YamlProgramName = "mkxthv";
    atexit(YamlCleanup);
    atexit(HiveCleanOutput);
    if(argc != 3)
    {
        fprintf(stderr, "Usage: mkxthv INPUT.yaml OUTPUT.xhv\n");
        return 2;
    }
    struct stat InputStat, OutputStat;
    if(!strcmp(argv[1], argv[2]) ||
       (!stat(argv[1], &InputStat) && !stat(argv[2], &OutputStat) && InputStat.st_ino &&
        InputStat.st_ino == OutputStat.st_ino && InputStat.st_dev == OutputStat.st_dev))
    {
        YamlError("input and output must be different files");
    }
    HIVE_BUILD_CONTEXT Context = {0};
    Context.OutputPath = argv[2];
    YamlProgramName = YamlFormatString("mkxthv (%s)", argv[1]);
    char *Directory = YamlCopyString(argv[1]);
    char *Separator = _tcsrchrs(Directory, '/', '\\');
    if(Separator)
    {
        Separator[1] = 0;
        Context.InputDirectory = Directory;
    }
    else
    {
        Context.InputDirectory = ".";
    }
    YAML_BUFFER Source = HiveReadFile(argv[1], YAML_MAX_TEXT);
    YAML_NODE *Document = YamlReadDocument(Source.data, Source.len);
    YamlValidateFields(Document, "format version root", "strings hive_id writer_id timestamp");
    if(strcmp(YamlGetScalar(YamlGetField(Document, "format")), "xthv") ||
       HiveParseInteger(YamlGetScalar(YamlGetField(Document, "version")), UINT32_MAX) != 1)
    {
        YamlError("expected xthv YAML version 1");
    }
    HiveReadDictionary(&Context, Document);
    Context.Timestamp = HiveOptionalInteger(Document, "timestamp", 0, UINT64_MAX);
    memcpy(Context.WriterId, "XTchain:mkxthv01", 16);
    const char *Ids[] = {"hive_id", "writer_id"};
    int ExplicitId = 0;
    for(unsigned Index = 0; Index < 2; Index++)
    {
        YAML_NODE *Field = YamlFindField(Document, Ids[Index]);
        if(Field)
        {
            YAML_BUFFER Id = HiveReadBytes(&Context, Field);
            if(Id.len != 16)
            {
                YamlError("%s must contain exactly 16 bytes", Ids[Index]);
            }
            memcpy(Index ? Context.WriterId : Context.HiveId, Id.data, 16);
            if(!Index)
            {
                unsigned Present = 0;
                for(unsigned Byte = 0; Byte < 16; Byte++)
                {
                    Present |= Context.HiveId[Byte];
                }
                if(!Present)
                {
                    YamlError("hive_id cannot be zero");
                }
                ExplicitId = 1;
            }
        }
    }

    static const char DefaultSecurity[] =
        "owner: S-1-5-18\ngroup: S-1-5-32-544\ndacl:\n"
        "  - {type: allow, mask: 0xF003F, sid: S-1-5-18, flags: 2}\n"
        "  - {type: allow, mask: 0xF003F, sid: S-1-5-32-544, flags: 2}\n"
        "  - {type: allow, mask: 0x20019, sid: S-1-1-0, flags: 2}\n";
    YAML_NODE *Default = YamlReadDocument((const unsigned char *)DefaultSecurity, sizeof(DefaultSecurity) - 1);
    HIVE_SECURITY *Inherited = HiveInternSecurity(&Context, HiveReadSecurity(&Context, Default));
    YAML_NODE *Records = HiveReadFlatEntries(&Context, YamlGetField(Document, "root"));
    HIVE_KEY *Root = HiveReadKey(&Context, Records, Inherited, 0);
    HiveBuildSecurity(&Context);
    HiveBuildKey(&Context, Root, HIVE_CELL_NIL);
    HiveWriteContainer(&Context, Root, argv[2], ExplicitId);
    fprintf(stderr, "mkxthv: %u logical bytes -> %s\n", Context.LogicalBytes, argv[2]);
    return 0;
}
