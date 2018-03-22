{$optimize 7}

unit Printf;

{$LibPrefix '0/obj/'}

interface

uses CCommon;

{$segment 'PRINTF'}

type

  fmtArgPtr = ^fmtArgRecord;

  fmtArgRecord = record
    next: fmtArgPtr;
    ty: typePtr;
    tk: tokenPtr;
  end;

  {
  format arg1: printf
  format arg2: fprintf, sprintf, asprintf, dprintf
  format arg3: snprintf

  format arg1: scanf
  format arg2: fscanf, sscanf
  }
  fmt_type = (fmt_none, fmt_printf1, fmt_printf2, fmt_printf3, fmt_scanf1, fmt_scanf2);


procedure FormatCheck(fmt: fmt_type; args: fmtArgPtr);

function FormatClassify(fname: stringPtr): fmt_type;

implementation

type
    length_modifier = (default, h, hh, l, ll, j, z, t, ld);

    state_enum = (st_text, st_flag, st_width,
      st_precision_dot, st_precision, st_precision_number,
      st_length, st_length_h, st_length_l, st_format,
      { scanf }
      st_suppress, st_set, st_set_1, st_set_2,
      st_error);

    bt_set = set of baseTypeEnum;


{
  Check if a string is printf/scanf. Caller must check if
  it otherwise matches (variadic, direct call)
}
function FormatClassify {fname: stringPtr): fmt_type};
var
  l: integer;
begin

  FormatClassify := fmt_none;

  l := length(fname^);
  if (l >= 5) and (l <= 8) then case fname^[1] of
    'a': if fname^ = 'asprintf' then FormatClassify := fmt_printf2;
    'd': if fname^ = 'dprintf' then FormatClassify := fmt_printf2;
    'p': if fname^ = 'printf' then FormatClassify := fmt_printf1;
    'f':
           if fname^ = 'fprintf' then FormatClassify := fmt_printf2
      else if fname^ = 'fscanf' then FormatClassify := fmt_scanf2;
    's':
           if fname^ = 'scanf' then FormatClassify := fmt_scanf1
      else if fname^ = 'snprintf' then FormatClassify := fmt_printf3
      else if fname^ = 'sprintf' then FormatClassify := fmt_printf2
      else if fname^ = 'sscanf' then FormatClassify := fmt_scanf2;
      otherwise:
  end;
end;



procedure FormatCheck{fmt: fmt_type; args: fmtArgPtr};

var
  head: fmtArgPtr;
  s: longstringPtr;
  state: state_enum;
  has_length: length_modifier;
  printed: boolean;
  expected : integer;
  offset : integer;


  number_set : set of char;
  flag_set : set of char;
  length_set : set of char;
  format_set : set of char;

  { Write the current line. copied from Scanner.pas }
  procedure WriteLine;
  const
    RETURN       = 13;
  var
    cp: ptr;
  begin

    write(lineNumber:4, ' ');            {write the line #}
    cp := firstPtr;                      {write the characters in the line}
    while cp <> chPtr do begin
      if cp^ <> RETURN then
      write(chr(cp^));
      cp := pointer(ord4(cp) + 1);
    end; {while}
    writeln;                             {write the end of line character}

  end;

  {
    Print a warning.  offset is the location of the current % character.
  }
  procedure Warning(msg: stringPtr);
  var 
    i: integer;
    c: char;
  begin
    if not printed then begin
      WriteLine;
      Write('     "');
      for i := 1  to s^.length do begin
        c := s^.str[i];
        if (c = '"') or (ord(c) < $20) or (ord(c) > $7f) then c := '.';
        Write(c);
      end;
      WriteLn('"');
      printed := true;
    end;
    Write('     ');
    if offset <> 0 then begin
      for i := 1 to offset do Write(' ');
      Write('^ ');
    end;
    Write('Warning: ');
    WriteLn(msg^);
  end;

  procedure WarningConversionChar(c: char);
  var
    msg: stringPtr;
  begin
    if (ord(c) >= $20) and (ord(c) <= $7f) then begin
      new(msg);
      msg^ := concat('unknown conversion type character ''', c, ''' in format.');
      Warning(msg);
      dispose(msg);
    end else Warning(@'unknown conversion type character in format.');
  end;

  procedure WarningExtraArgs(i: integer);
  var
    msg: stringPtr;
  begin
    new(msg);
    msg^ := concat('extra arguments provided (', cnvis(i), ' expected).');
    Warning(msg);
    dispose(msg);
  end;



  function popType: typePtr;
  begin
    expected := expected + 1;
    popType := nil;
    if args <> nil then begin
      popType := args^.ty;
      args := args^.next;
    end;
  end;


  procedure expect_long;
  var
    ty: typePtr;
  begin
    ty := popType;
    if ty <> nil then begin
      if (ty^.kind <> scalarType) or (not (ty^.baseType in [cgLong, cgULong])) then begin
        Warning(@'expected long int.');
      end;
    end else begin
      Warning(@'argument missing; expected long int');
    end;
  end;

  { expect an int (or char) }
  procedure expect_int;
  var
    ty: typePtr;
  begin
    ty := popType;
    if ty <> nil then begin
      if (ty^.kind <> scalarType) or 
        not (ty^.baseType in [cgWord, cgUWord, cgByte, cgUByte]) then begin
        Warning(@'expected int.');
      end;
    end else begin
      Warning(@'argument missing; expected int.');
    end;
  end;


  { expect a char (or int) }
  procedure expect_char;
  var
    ty: typePtr;
  begin
    ty := popType;
    if ty <> nil then begin
      if (ty^.kind <> scalarType) or 
        not (ty^.baseType in [cgWord, cgUWord, cgByte, cgUByte]) then begin
        Warning(@'expected char.');
      end;
    end else begin
      Warning(@'argument missing; expected char.');
    end;
  end;


  { expect an extended (or float or double since they're passed as extended )}
  procedure expect_extended;
  var
    ty: typePtr;
  begin
    ty := popType;
    if ty <> nil then begin
      if (ty^.kind <> scalarType) or
        not (ty^.baseType in [cgExtended, cgReal, cgDouble]) then begin
        Warning(@'expected extended.');
      end;
    end else begin
      Warning(@'argument missing; expected extended.');
    end;
  end;

  { expect a pointer of some sort }
  procedure expect_pointer;
  var
    ty: typePtr;
  begin
    ty := popType;
    if ty <> nil then begin
      if (ty^.kind <> pointerType) then begin
        Warning(@'expected pointer.');
      end;
    end else begin
      Warning(@'argument missing; expected pointer.');
    end;
  end;

  { expect a pointer to a specific type }
  procedure expect_pointer_to(types: bt_set; name: stringPtr);

  var
    ty: typePtr;
    baseTy: typePtr;
    ok: boolean;

    procedure error(prefix: stringPtr);
      var
        msg: stringPtr;
      begin
        new(msg);
        msg^ := concat(prefix^, name^, '.');
        Warning(msg);
        dispose(msg);
      end;

  begin
    ok := false;
    ty := popType;
    baseTy := nil;


    if ty <> nil then
      if (ty^.kind = pointerType) or (ty^.kind = arrayType) then begin
        baseTy := ty^.pType;
        if (baseTy <> nil)
          and (baseTy^.kind = scalarType)
          and (baseTy^.baseType in types)
          then ok := true;
      end;

    if not ok then begin

      if ty = nil then
        error(@'argument missing; expected pointer to ')
      else error(@'expected pointer to ');
    end;

  end;

  procedure do_length(c: char);
  begin
    state := st_format;
    case c of
    'h': begin has_length := h; state := st_length_h; end;
    'l': begin has_length := l; state := st_length_l; end;
    'j': has_length := j;
    'z': has_length := z;
    't': has_length := t;
    'L': has_length := ld;
    end;
  end;



  procedure FormatScanf;

  label 1;

  var
    i: integer;
    c: char;
    has_suppress: boolean;
    types: bt_set;
    name: stringPtr;


    procedure do_scanf_format;

    {
      (current) ORCALib limitations, wrt size modifiers:

      - ignored for string types
      - hh not supported
      - L not supported
      - ignored for 'n'
    }
    begin

      name := nil;

      state := st_text;
      if c in format_set then begin

        case c of

          '%': has_suppress := true;
          'c', 'b', 's', '[' :
            { n.b. orca doesn't support %ls }
            begin
              types := [cgByte, cgUByte];
              name := @'char';
              if c = '[' then state := st_set_1;
            end;
          'd', 'i', 'u', 'o', 'x', 'X':
            begin
              types := [cgWord, cgUWord];
              name := @'int';
              case has_length of
                hh: begin types := [cgByte, cgUByte]; name := @'char'; end;
                l, ll, j, z, t: begin types := [cgLong, cgULong]; name := @'long'; end;
                otherwise ; 
              end;
            end;
          'n':
            begin
                { ORCALib always treats n as int * }
                { n.b. - *n is  undefined; orcalib pops a parm but doesn't store.}
                if has_suppress then Warning(@'*n is undefined.');
                types := [cgWord, cgUWord];
                name := @'int';
                has_suppress := false;
              end;
            'p':
              begin
                if not has_suppress then expect_pointer;
                has_suppress := true;
              end;
            'a', 'A', 'f', 'F', 'g', 'G', 'e', 'E':
              begin
                types := [cgReal];
                name := @'float';
                case has_length of
                ld: begin types := [cgExtended]; name := @'long double'; end;
                l: begin types := [cgDouble]; name := @'double'; end;
                otherwise ; 
              end;
            end;
        end; { case }

        if not has_suppress then begin
          expect_pointer_to(types, name);
        end;

      end {if}
      else WarningConversionChar(c);


    end;



  begin

    {
      '%'
      '*'?                         - assignment suppression
      \d*                          - maximum field width
      (h|hh|l|ll|j|z|t|L)?         - length modifier
      [%bcsdiuoxXnaAeEfFgGp] | set - format

      set: '[[' [^]]* ']'
      set: '[^[' [^]]* ']'
      set: '[' [^]]+ ']'

    }
    state := st_text;
    expected := 0;
    offset := 0;

    number_set := ['0' .. '9'];
    length_set := ['h', 'l', 'j', 't', 'z', 'L']; 
    flag_set := ['#', '0', '-', '+', ' '];
    format_set := ['%', '[', 'b', 'c', 's', 'd', 'i', 'o', 'x', 'X', 'u', 
      'f', 'F', 'e', 'E', 'a', 'A', 'g', 'G', 'n', 'p'];


    for i := 1 to s^.length do begin
      c := s^.str[i];
      case state of
      st_text:  if c = '%' then begin
        state := st_suppress;
        offset := i;
        has_length := default;
        has_suppress := false;
        end;
      st_suppress: { suppress? width? length? format }
        if c = '*' then begin
          state := st_width;
          has_suppress := true;
        end
        else if c in number_set then state := st_width
        else if c in length_set then do_length(c)
        else do_scanf_format;

      st_width: {width? length? format }
        if c in number_set then state := st_width
        else if c in length_set then do_length(c)
        else do_scanf_format;

      st_length_h: { h? format }
        if c = 'h' then begin
          has_length := hh;
          state := st_format;
        end else do_scanf_format;

      st_length_l: { l? format }
        if c = 'l' then begin
          has_length := ll;
          state := st_format;
        end else do_scanf_format;    

      st_format: { format }
        do_scanf_format;

        { first char of a [set]. ']' does not end the set.   }
      st_set_1:
        if c = '^' then state := st_set_2
        else state := st_set;

      st_set_2:
        state := st_set;

      st_set:
        if c = ']' then state := st_text;

      st_error: goto 1;
      end; { case }
    end; { for }

      if state <> st_text then
        Warning(@'incomplete format specifier.');

      if args <> nil then begin
        offset := 0;
        WarningExtraArgs(expected);
      end;

1:

  end; {FormatScanf}



  procedure FormatPrintf;

  label 1;

  var

    i : integer;
    c : char;

    has_flag : boolean;
    has_width: boolean;
    has_precision : boolean;

    procedure do_printf_format;
    begin
      state := st_text;
      if c in format_set then begin
        case c of
           { %b: orca-specific - pascal string }
          'p': expect_pointer;

          'b', 's': expect_pointer_to([cgByte, cgUByte], @'char');

          'n': expect_pointer_to([cgWord, cgUWord], @'int');

          'c': expect_char;

          'd', 'i', 'o', 'x', 'X', 'u':
            if has_length in [l, ll, j, z, t] then begin
              expect_long;
            end else begin
              expect_int;
            end;
          'f', 'F', 'e', 'E', 'a', 'A', 'g', 'G':
            begin
              expect_extended;
            end;
          '%': ;
        end;

      end else WarningConversionChar(c);


    end; 

    begin

      state := st_text;
      expected := 0;
      offset := 0;

      number_set := ['0' .. '9'];
      length_set := ['h', 'l', 'j', 't', 'z', 'L']; 
      flag_set := ['#', '0', '-', '+', ' '];
      format_set := ['%', 'b', 'c', 's', 'd', 'i', 'o', 'x', 'X', 'u', 
        'f', 'F', 'e', 'E', 'a', 'A', 'g', 'G', 'n', 'p'];

      if s^.length = 0 then Warning('format string is empty.');

      for i := 1 to s^.length do begin
        c := s^.str[i];
        case state of
        st_text:
          if c = '%' then begin
            state := st_flag;
            offset := i;
            has_length := default;
            has_flag := false;
            has_width := false;
            has_precision := false;
          end;

        st_flag: { flags* width? precision? length? format }
          if c in flag_set then begin
            state := st_flag;
            has_flag := true;
          end
          else if c in number_set then begin
            state := st_width;
            has_width := true;
          end
          else if c = '*' then begin
            { * for the width }
            has_width := true;
            expect_int;
            state := st_precision;
          end
          else if c = '.' then state := st_precision_dot
          else if c in length_set then do_length(c)
          else do_printf_format;

        st_width: { width? precision? length? format }
          if c in number_set then state := st_width
          else if c = '.' then state := st_precision_dot
          else if c in length_set then do_length(c)
          else do_printf_format;

        st_precision: { (. precision)? length? format }
          if c = '.' then state := st_precision_dot
          else if c in length_set then do_length(c)
          else do_printf_format;

        st_precision_dot: { * | [0-9]+ }
          begin
            has_precision := true;
            if c = '*' then begin
              expect_int;
              state := st_length;
            end
            else if c in number_set then state := st_precision_number
            else state := st_error;
          end;

        st_precision_number: { [0-9]*  length? format }
          if c in number_set then state := st_precision_number
          else if c in length_set then do_length(c)
          else do_printf_format;  

        st_length: { length? format }
          if c in length_set then do_length(c)
          else do_printf_format;

        st_length_h: { h? format }
          if c = 'h' then begin has_length := hh; state := st_format; end
          else do_printf_format;

        st_length_l: { l? format}
          if c = 'l' then begin has_length := ll; state := st_format; end
          else do_printf_format;

        st_format: do_printf_format;

        st_error: { error }
          goto 1;

        end; { case  }
      end; { for i }

      if state <> st_text then
        Warning(@'incomplete format specifier.');

      if args <> nil then begin
        offset := 0;
        WarningExtraArgs(expected);
      end;
1:

    end;





  function get_format_string(pos: integer): longstringPtr;
  var
    tk: tokenPtr;
  begin
    get_format_string := nil;

    while (args <> nil) and (pos > 1) do begin
      args := args^.next;
      pos := pos - 1;
    end;

    if (pos = 1) and (args <> nil) then begin
      tk := args^.tk;
      args := args^.next;

      if (tk <> nil) and (tk^.token.kind = stringconst) then
        get_format_string := tk^.token.sval
      else
        Warning(@'format string is not a string literal')
    end else Warning(@'format string missing');
  end;


{FormatCheck}
begin

  head := args;
  printed := false;
  offset := 0;

  case fmt of
  fmt_printf1, fmt_scanf1:
    s := get_format_string(1);
  fmt_printf2, fmt_scanf2:
    s := get_format_string(2);
  fmt_printf3:
    s := get_format_string(3);
  otherwise s := nil;
  end;

  if (s <> nil) then case fmt of
    fmt_printf1, fmt_printf2, fmt_printf3:
      FormatPrintf;
    fmt_scanf1, fmt_scanf2:
      FormatScanf;
  end;

  { clean up linked list }
  while head <> nil do begin
    args := head^.next;
    dispose(head);
    head := args;
  end;
end;

end.
