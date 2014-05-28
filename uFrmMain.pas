
{ *************************************************************************** }
{                                                                             }
{                            Mandelbrot Explorer                              }
{                                                                             }
{ This program is made for as an entry for the Borland Multithreading Contest }
{                                                                             }
{ It calculates parts of the Mandelbrot fractal using threads. All calculated }
{ parts are maintained in a tree structure and can be navigated by clicking   }
{ on rectangle and using the back, foward and up buttons. A new part will be  }
{ calculated by dragging a rectangle on a part.                               }
{                                                                             }
{  The progress of the calculations of a part is displayed in a progressbar   }
{  and by a rectangle that gradually turns white. The synchronisation of the  }
{  threads with the main thread is done by asynchronous Windows messaging.    }
{                                                                             }
{ (C) Jacco Kulman 2002                                                       }
{                                                                             }
{ *************************************************************************** }

unit uFrmMain;

interface

uses
  Windows, Messages, SysUtils, Variants, Classes, Graphics, Controls, Forms,
  Dialogs, ExtCtrls, StdCtrls, SyncObjs, ComCtrls, Contnrs, ImgList,
  ToolWin, Menus;

type
  { TFractalPart - stores the number of iterations for every pixels of the part.
                   also maintains a list of ChildParts which enlargements of parts
                   of this part.

     ChildAt - returns the Child in which the point (X, Y) lies
               inside its fViewRect }

  TFractalPart = class
  private
    fParentPart: TFractalPart;
    fChildParts: TObjectList;
    fIterations: array[0..640, 0..480] of Word;
    fLeft: Extended;
    fTop: Extended;
    fRight: Extended;
    fBottom: Extended;
    fProgress: Integer;
    fViewRect: TRect;
    fHighLight: Boolean;
    fLevel: Integer;
    fMaxIterations: Integer;
    fNode: TTreeNode;
    fVisited: Boolean;
    fName: string;
    fColorScheme: Integer;
  public
    constructor Create(aParentPart: TFractalPart; aLeft, aTop, aRight, aBottom: Extended; aViewRect: TRect);
    destructor Destroy; override;
    function ChildAt(X, Y: Integer): TFractalPart;
    function MinIterationsInRect(aRect: TRect): Integer;
  end;

  TfrmMain = class(TForm)
    pnlTop: TPanel;
    pnlMain: TPanel;
    sbProgressBox: TScrollBox;
    pnlView: TPanel;
    tbrToolBar: TToolBar;
    btnBack: TToolButton;
    btnForward: TToolButton;
    btnUp: TToolButton;
    ilImages: TImageList;
    ilDisabled: TImageList;
    ilHighLight: TImageList;
    pnlMiddle: TPanel;
    pnlRight: TPanel;
    Label1: TLabel;
    lbLeft: TLabel;
    Label3: TLabel;
    lbTop: TLabel;
    Label5: TLabel;
    lbWidth: TLabel;
    Label7: TLabel;
    lbHeight: TLabel;
    Label9: TLabel;
    lbMagnification: TLabel;
    Label11: TLabel;
    Label6: TLabel;
    lbMaxIterations: TLabel;
    Label8: TLabel;
    lbLevel: TLabel;
    pbxFractalView: TPaintBox;
    pnlLeft: TPanel;
    trvPartTree: TTreeView;
    pmColorScheme: TPopupMenu;
    miRainbow: TMenuItem;
    miIce: TMenuItem;
    miFire: TMenuItem;
    pnlButtons: TPanel;
    btnLoad: TButton;
    btnSave: TButton;
    N1: TMenuItem;
    miInfo: TMenuItem;
    pbLoadSave: TProgressBar;
    odLoad: TOpenDialog;
    sdSave: TSaveDialog;
    procedure FormCreate(Sender: TObject);
    procedure FormDestroy(Sender: TObject);
    procedure pbxFractalViewMouseDown(Sender: TObject; Button: TMouseButton; Shift: TShiftState; X, Y: Integer);
    procedure pbxFractalViewMouseMove(Sender: TObject; Shift: TShiftState; X, Y: Integer);
    procedure pbxFractalViewMouseUp(Sender: TObject; Button: TMouseButton; Shift: TShiftState; X, Y: Integer);
    procedure pbxFractalViewPaint(Sender: TObject);
    procedure btnUpClick(Sender: TObject);
    procedure btnBackClick(Sender: TObject);
    procedure btnForwardClick(Sender: TObject);
    procedure trvPartTreeCustomDrawItem(Sender: TCustomTreeView; Node: TTreeNode; State: TCustomDrawState; var DefaultDraw: Boolean);
    procedure trvPartTreeChange(Sender: TObject; Node: TTreeNode);
    procedure trvPartTreeEdited(Sender: TObject; Node: TTreeNode; var S: String);
    procedure miColorScheme(Sender: TObject);
    procedure pmColorSchemePopup(Sender: TObject);
    procedure btnSaveClick(Sender: TObject);
    procedure btnLoadClick(Sender: TObject);
    procedure miInfoClick(Sender: TObject);
  private
    fStartX: Integer;
    fStartY: Integer;
    fEndX: Integer;
    fEndY: Integer;
    fRootPart: TFractalPart;
    fFractalPart: TFractalPart;
    fPartBitmap: TBitmap;
    fDragging: Boolean;
    fChanging: Boolean;
    fBackList: TList;
    fBackIndex: Integer;
    fDragRect: TRect;
    fDragCanvas: TCanvas;
    fThreadList: TList;
    fSaveSection: TCriticalSection;
    procedure SetFractalPart(const Value: TFractalPart);
    procedure DrawDragRect(aRect: TRect);
    procedure HistoryAdd(aFractalPart: TFractalPart);
    procedure GotoFractalPart(aFractalPart: TFractalPart);
    procedure DisplayPartDetails(aFractalPart: TFractalPart);
    procedure KillThreads;
  public
    procedure DrawFractalPart(aFractalPart: TFractalPart);
    function NewFractalPart(aLeft, aTop, aRight, aBottom: Extended; aViewRect: TRect; aOnFinished: TNotifyEvent = nil): TFractalPart;
    procedure InvalidateFractalPart(aFractalPart: TFractalPart);
    procedure InitialDraw(Sender: TObject);
    property FractalPart: TFractalPart read fFractalPart write SetFractalPart;
  end;

  { TCalculateThread - calculates and stores the iterations of fFractalPart in
                       its execute method. Sends progress messages (and a finish
                       method) to fProgressHandle. The thread starts directly
                       after its creation and frees itself when finished. }

const
  P_ProgressUpdate   = WM_APP + 1;
  P_ProgressFinished = WM_APP + 2;

type
  TCalculateThread = class(TThread)
  private
    fProgress: Integer;
    fProgressHandle: HWND;
    fFractalPart: TFractalPart;
    procedure SetProgress(const Value: Integer);
  public
    constructor Create(aFractalPart: TFractalPart; aProgressHandle: HWND); virtual;
    procedure Execute; override;
    property Progress: Integer read fProgress write SetProgress;
  end;

  { TThreadProgressBar - is the receiver of the messages of the TCalculateThread.
                         When the finish message is received it frees itself. The
                         progress message is handled by updating the progressbar
                         position and by invalidating the progress rectangle of the
                         TFractalPart being calculated (if visible) }


  TThreadProgressBar = class(TProgressBar)
  private
    procedure ProgressUpdate(var Msg: TMessage); message P_ProgressUpdate;
    procedure ProgressFinished(var Msg: TMessage); message P_ProgressFinished;
  public
    constructor Create(aOwner: TComponent); override;
  end;

var
  frmMain: TfrmMain;

implementation

uses
  Math, CommCtrl, ZLib;

{$R *.dfm}

{ utility }

function ColorToRGBTriple(aColor: TColor): TRGBTriple;
begin
  // convert aColor to a TRGBTriple
  with Result do
  begin
    rgbtRed   := GetRValue(aColor);
    rgbtGreen := GetGValue(aColor);
    rgbtBlue  := GetBValue(aColor);
  end;
end;

function NormalizeRect(aRect: TRect): TRect;
var
  liTemp: Integer;
begin
  if aRect.Left > aRect.Right then
  begin
    // swap left and right
    liTemp := aRect.Left;
    aRect.Left := aRect.Right;
    aRect.Right := liTemp;
  end;
  if aRect.Top > aRect.Bottom then
  begin
    // swap top and bottom
    liTemp := aRect.Top;
    aRect.Top := aRect.Bottom;
    aRect.Bottom := liTemp;
  end;
  Result := aRect;
end;

function CalcPartRect(aLeft, aTop, aRight, aBottom: Integer): TRect;
var
  leAngle, leDist: Extended;
begin
  // correct for zero width height
  if aRight = aLeft then
    aRight := aLeft + 4;
  if aBottom = aTop then
    aBottom := aTop + 3;
  // calculate angle and radius
  leAngle := ArcTan2((aBottom - aTop), (aRight - aLeft));
  leDist := Sqrt(Sqr(aRight - aLeft) + Sqr(aBottom - aTop));
  // correct angle depending on quadrant
  if leAngle > 0 then
  begin
    if leAngle > 0.5*PI then
      leAngle := ArcTan2(3, -4)
    else
      leAngle := ArcTan2(3, 4);
  end else begin
    if leAngle < -0.5*PI then
      leAngle := ArcTan2(-3, -4)
    else
      leAngle := ArcTan2(-3, 4);
  end;
  // now recalculate end point
  aRight := aLeft + Round(Cos(leAngle) * leDist);
  aBottom := aTop + Round(Sin(leAngle) * leDist);
  // convert to normalized rectangle
  Result := NormalizeRect(Rect(aLeft, aTop, aRight, aBottom));
end;

function InterpolateColors(const aFraction: Extended; const aColors: array of TColor): TColor;
var
  liCount, liStartIndex: Integer;
  leFraction, leComplement: Extended;
  R1, R2: Byte;
  G1, G2: Byte;
  B1, B2: Byte;
begin
  Result := clBlack;
  // count the colors in the array
  liCount := High(aColors) - Low(aColors) + 1;
  if liCount < 2 then
    Exit;
  // calculate the fraction
  leFraction   := aFraction * (liCount - 1.0) - 0.00001;
  liStartIndex := Trunc(leFraction);
  leFraction   := Frac(leFraction);
  // determine the two colors to interpolate between
  R1 := GetRValue(aColors[liStartIndex]);
  G1 := GetGValue(aColors[liStartIndex]);
  B1 := GetBValue(aColors[liStartIndex]);
  R2 := GetRValue(aColors[liStartIndex + 1]);
  G2 := GetGValue(aColors[liStartIndex + 1]);
  B2 := GetBValue(aColors[liStartIndex + 1]);
  // invert the fraction
  leComplement := 1 - leFraction;
  // construct the color
  Result := RGB(Round(leComplement*R1 + leFraction*R2),
                Round(leComplement*G1 + leFraction*G2),
                Round(leComplement*B1 + leFraction*B2));
end;

{ TFractalPart }

function TFractalPart.ChildAt(X, Y: Integer): TFractalPart;
var
  liChildPart, liIndex: Integer;
  leMinDist, leDist: Extended;
begin
  // initialize variables
  leMinDist := 9E9;
  liIndex := -1;
  Result := nil;
  // iterate over all child parts
  for liChildPart := 0 to fChildParts.Count-1 do
    with TFractalPart(fChildParts[liChildPart]) do
      if (fProgress = 101) and PtInRect(fViewRect, Point(X,Y)) then
      begin
        // calculate the distance between centerpoint of fractal part and X,Y
        leDist := Sqrt(Sqr((fViewRect.Left + fViewRect.Right) div 2 - X) +
                       Sqr((fViewRect.Top + fViewRect.Bottom) div 2 - Y));
        // record the minimum index
        if  leDist < leMinDist then
        begin
          leMinDist := leDist;
          liIndex := liChildPart;
        end;
      end;
  // return the result if found
  if liIndex <> -1 then
    Result := TFractalPart(fChildParts[liIndex]);
end;

constructor TFractalPart.Create(aParentPart: TFractalPart; aLeft, aTop, aRight, aBottom: Extended; aViewRect: TRect);
begin
  fViewRect := Rect(0, 0, 640, 480);
  fLevel := 1;
  fParentPart := aParentPart;
  fChildParts := TObjectList.Create;
  fLeft := aLeft;
  fTop := aTop;
  fRight := aRight;
  fBottom := aBottom;
  fMaxIterations := 1000;
  // if there is a parent then change some fields
  if Assigned(fParentPart) then
  begin
    fColorScheme := fParentPart.fColorScheme;
    fParentPart.fChildParts.Add(Self);
    fViewRect := aViewRect;
    fLevel := fParentPart.fLevel + 1;
  end;
end;

destructor TFractalPart.Destroy;
begin
  fChildParts.Free;
  inherited Destroy;
end;

function TFractalPart.MinIterationsInRect(aRect: TRect): Integer;
var
  liX, liY: Integer;
begin
  // determine the minimum iterations inside a rectangle
  Result := fMaxIterations;
  for liX := aRect.Left to aRect.Right do
    for liY := aRect.Top to aRect.Bottom do
      if fIterations[liX, liY] < Result then
        Result := fIterations[liX, liY];
end;

{ TCalculateThread }

constructor TCalculateThread.Create(aFractalPart: TFractalPart; aProgressHandle: HWND);
begin
  inherited Create(True);
  // initialize private fields
  fProgressHandle := aProgressHandle;
  fFractalPart := aFractalPart;
  FreeOnTerminate := True;
  // force message when setting progress to 0
  fProgress := -1;
end;

procedure TCalculateThread.Execute;
var
  x, y, it: Integer;
  dx, dy, fcr, fci, fzr, fzi, t, sqrr, sqri: Extended;
begin
  Progress := 0;
  // to show first progress rectangle
  Sleep(10);
  if Assigned(fFractalPart.fParentPart) then
    fFractalPart.fMaxIterations := fFractalPart.fParentPart.MinIterationsInRect(fFractalPart.fViewRect) + 1000;
  for y := 0 to 480 do
  begin
    dy  := fFractalPart.fTop + (fFractalPart.fBottom - fFractalPart.fTop) * (y / 480);
    fci := dy;
    for x := 0 to 640 do
    begin
      dx  := fFractalPart.fLeft + (fFractalPart.fRight - fFractalPart.fLeft) * (x / 640);
      fcr := dx;
      fzr := 0;
      fzi := 0;
      sqri := 0;
      sqrr := 0;
      it  := 0;
      // iterate in mandlebrot fashion for all (X,Y)
      while True do
      begin
        t := sqrr - sqri + fcr;
        fzi := 2 * fzr * fzi + fci;
        fzr := t + fcr;
        Inc(it);
        sqrr := Sqr(fzr);
        sqri := Sqr(fzi);
        if (it > fFractalPart.fMaxIterations) or (sqrr + sqri > 4) then
          Break;
        if Terminated then
          Exit;
      end;
      fFractalPart.fIterations[x, y] := it;
    end;
    // update the progress
    Progress := Round(y / 4.8);
  end;
  Progress := 100;
  // post the finished message
  if fProgressHandle <> 0 then
    PostMessage(fProgressHandle, P_ProgressFinished, Integer(Self), Integer(fFractalPart));
end;

procedure TCalculateThread.SetProgress(const Value: Integer);
begin
  if Value <> fProgress then
  begin
    // store the progress
    fProgress := Value;
    fFractalPart.fProgress := Value;
    // post the progress message
    if fProgressHandle <> 0 then
      PostMessage(fProgressHandle, P_ProgressUpdate, fProgress, Integer(fFractalPart));
  end;
end;

{ TThreadProgressBar }

constructor TThreadProgressBar.Create(aOwner: TComponent);
begin
  inherited Create(aOwner);
  Smooth := True;
  Step := 1;
  Height := 6;
  Min := -1;
  Position := -1;
end;

var
  NameIndex: Integer;

procedure TThreadProgressBar.ProgressFinished(var Msg: TMessage);
var
  lNode: TTreeNode;
begin
  // make sure no part get 101 progress (save enabled)
  frmMain.fSaveSection.Enter;
  try
    // free the progressbar
    Free;
    // add the fractal to the parttree
    lNode := nil;
    with TFractalPart(Msg.LParam) do
    begin
      // allow saving
      fProgress := 101;
      fName := 'Part' + IntToStr(NameIndex);
      Inc(NameIndex);
      if Assigned(fParentPart) then
        lNode := fParentPart.fNode;
      fNode := frmMain.trvPartTree.Items.AddChildObject(lNode, fName, Pointer(Msg.LParam));
    end;
    // remove the thread from the list
    frmMain.fThreadList.Remove(TObject(Msg.WParam));
  finally
    frmMain.fSaveSection.Leave;
  end;
end;

procedure TThreadProgressBar.ProgressUpdate(var Msg: TMessage);
begin
  // update the position of the progress bar
  PostMessage(Handle, PBM_SETPOS, Msg.WParam, 0);
  // invalidate the progress rectangle of the part
  frmMain.InvalidateFractalPart(TFractalPart(Msg.LParam));
end;

{ TfrmMain }

procedure TfrmMain.FormCreate(Sender: TObject);
begin
  fSaveSection := TCriticalSection.Create;
  // prevent having artifacts
  pnlMiddle.DoubleBuffered := True;
  fBackList := TList.Create;
  fThreadList := TList.Create;
  // create the canvas for drawing the dragging rectangle
  fDragCanvas := TCanvas.Create;
  with fDragCanvas do
  begin
    Handle := GetWindowDC(GetDesktopWindow);
    Pen.Color := clBlack;
    Pen.Mode := pmNotXor;
    Brush.Style := bsClear;
  end;
  // create the bitmap that will contain the colors of the actual part
  fPartBitmap := TBitmap.Create;
  with fPartBitmap do
  begin
    PixelFormat := pf24bit;
    Width := 640;
    Height := 480;
    // fill it black
    Canvas.Brush.Color := clBlack;
    Canvas.FillRect(Rect(0, 0, 639, 479));
  end;
  // spawn the initial thread
  fRootPart := NewFractalPart(-1.5, -2, 1.5, 2, Rect(0, 0, 640, 480), InitialDraw); // 640:480 4:3
  fFractalPart := fRootPart;
end;

procedure TfrmMain.KillThreads;
var
  liThread: Integer;
begin
  // terminate the threads still active
  for liThread := 0 to fThreadList.Count-1 do
    TCalculateThread(fThreadList[liThread]).Terminate;
  // wait a while
  Sleep(1000);
end;

procedure TfrmMain.FormDestroy(Sender: TObject);
begin
  KillThreads;
  // free all created resources
  fThreadList.Free;
  fBackList.Free;
  fDragCanvas.Free;
  fPartBitmap.Free;
  fRootPart.Free;
  fSaveSection.Free;
end;

function TfrmMain.NewFractalPart(aLeft, aTop, aRight, aBottom: Extended; aViewRect: TRect; aOnFinished: TNotifyEvent): TFractalPart;
var
  lCalculateThread: TCalculateThread;
begin
  // create the TFractalPart that will contain the iteration data
  Result := TFractalPart.Create(fFractalPart, aLeft, aTop, aRight, aBottom, aViewRect);
  // create the progress bar that will receive the progress messages
  with TThreadProgressBar.Create(Self) do
  begin
    Parent := sbProgressBox;
    Align  := alTop;
    // create the thread that will calculate the part's iterations
    lCalculateThread := TCalculateThread.Create(Result, Handle);
    lCalculateThread.OnTerminate := aOnFinished;
    // store the thread for preliminary termination
    fThreadList.Add(lCalculateThread);
    // start calculating
    lCalculateThread.Resume;
  end;
end;

procedure TfrmMain.InitialDraw(Sender: TObject);
begin
  HistoryAdd(FractalPart);
  FractalPart.fVisited := True;
  trvPartTree.Invalidate;
  DrawFractalPart(FractalPart);
  DisplayPartDetails(FractalPart);
  btnLoad.Enabled := True;
  btnSave.Enabled := True;
end;

procedure TfrmMain.DrawDragRect(aRect: TRect);
var
  lTopLeft: TPoint;
begin
  // calculate offset and offset the rectanngle
  with pbxFractalView do
  begin
    lTopLeft := ClientToScreen(Point(Left, Top));
    OffsetRect(aRect, lTopLeft.X - Left, lTopLeft.Y - Top);
  end;
  // draw the rectangle with the NOTXOR pen
  fDragCanvas.Rectangle(aRect);
end;

procedure TfrmMain.pbxFractalViewMouseDown(Sender: TObject; Button: TMouseButton; Shift: TShiftState; X, Y: Integer);
var
  lFractalPart: TFractalPart;
  lRect: TRect;
  lTopLeft: TPoint;
begin
  if Button = mbRight then
    Exit;
  lFractalPart := fFractalPart.ChildAt(X,Y);
  if Assigned(lFractalPart) then
    GotoFractalPart(lFractalPart)
  else begin
    // initialize the drag variables
    fStartX := X;
    fStartY := Y;
    fEndX := X;
    fEndY := Y;
    // calculate and draw the dragging rectangle
    fDragRect := CalcPartRect(fStartX, fStartY, fEndX, fEndY);
    DrawDragRect(fDragRect);
    // clip the mouse
    lRect := pbxFractalView.BoundsRect;
    lTopLeft := pbxFractalView.ClientToScreen(Point(pbxFractalView.Left, pbxFractalView.Top));
    OffsetRect(lRect, lTopLeft.X, lTopLeft.Y);
    ClipCursor(@lRect);
    // set the dragging flag
    fDragging := True;
  end;
end;

procedure TfrmMain.pbxFractalViewMouseMove(Sender: TObject; Shift: TShiftState; X, Y: Integer);
var
  liChildPart: Integer;
  lFractalPart: TFractalPart;
begin
  if not fDragging then
  begin
    lFractalPart := fFractalPart.ChildAt(X, Y);
    // unhighlight all childs but highlighted
    for liChildPart := 0 to fFractalPart.fChildParts.Count-1 do
      if TFractalPart(fFractalPart.fChildParts[liChildPart]) <> lFractalPart then
        with TFractalPart(fFractalPart.fChildParts[liChildPart]) do
          if fHighLight then
          begin
            fHighLight := False;
            InvalidateFractalPart(TFractalPart(fFractalPart.fChildParts[liChildPart]));
          end;
    // highlight one
    if Assigned(lFractalPart) then
    begin
      lFractalPart.fHighLight := True;
      InvalidateFractalPart(lFractalPart);
    end;
  end else begin
    // remove the previous dragging rectangle
    DrawDragRect(fDragRect);
    // calculate the new dragging rect
    fEndX := X;
    fEndY := Y;
    fDragRect := CalcPartRect(fStartX, fStartY, fEndX, fEndY);
    // draw the new dragging rectangle
    DrawDragRect(fDragRect);
  end;
end;

procedure TfrmMain.pbxFractalViewMouseUp(Sender: TObject; Button: TMouseButton; Shift: TShiftState; X, Y: Integer);
var
  leNewLeft, leNewRight, leNewTop, leNewBottom: Extended;
begin
  if fDragging then
  begin
    // remove the dragging rectangle
    DrawDragRect(fDragRect);
    // recalculate it
    fEndX := X;
    fEndY := Y;
    fDragRect := CalcPartRect(fStartX, fStartY, fEndX, fEndY);
    // calculate the bounds of the new fractal part
    with fFractalPart do
    begin
      leNewLeft   := fLeft + (fRight - fLeft) * fDragRect.Left / 640.0;
      leNewRight  := fLeft + (fRight - fLeft) * fDragRect.Right / 640.0;
      leNewTop    := fTop  + (fBottom - fTop) * fDragRect.Top / 480.0;
      leNewBottom := fTop  + (fBottom - fTop) * fDragRect.Bottom / 480.0;
    end;
    // spawn new thread to calculate the new part
    NewFractalPart(leNewLeft, leNewTop, leNewRight, leNewBottom, fDragRect);
    // release mouse clip
    ClipCursor(nil);
    // reset the dragging flag
    fDragging := False;
  end;
end;

procedure TfrmMain.DrawFractalPart(aFractalPart: TFractalPart);
type
  TPixelRow = array[0..639] of TRGBTriple;
  PPixelRow = ^TPixelRow;
var
  x, y, it: Integer;
  f: Extended;
  r: PPixelRow;
  liIndex: Integer;
begin
  with fPartBitmap do
  begin
    // initialize the bitmap black
    Canvas.Brush.Color := clBlack;
    Canvas.FillRect(Rect(0, 0, 639, 479));
    for y := 0 to 479 do
    begin
      r := ScanLine[y];
      for x := 0 to 639 do
      begin
        it := aFractalPart.fIterations[x, y];
        f := (it mod 101) / 100.0;
        // fill each pixel with the transformed it --> TColor
        if it <= aFractalPart.fMaxIterations then
        case aFractalPart.fColorScheme of
          0: r[x] := ColorToRGBTriple(InterpolateColors(f, [clBlue, clGreen, clYellow, $0080FF, clRed, clPurple, clBlue]));
          1: r[x] := ColorToRGBTriple(InterpolateColors(f, [clYellow, $0080FF, clRed, $0080FF, clYellow]));
          2: r[x] := ColorToRGBTriple(InterpolateColors(f, [clBlue, clWhite, clBlue]));
        end;
      end;
    end;
    pbxFractalView.Invalidate;
  end;
end;

procedure TfrmMain.pbxFractalViewPaint(Sender: TObject);
var
  liChildPart: Integer;

  procedure DrawProgress(aFractalPart: TFractalPart);
  var
    liProgress: Integer;

    procedure DrawLine(x1, y1, x2, y2, percent: Integer);
    begin
      if Percent < 0 then
        Exit;
      // adjust end x using percent
      if x1 <> x2 then
        x2 := x1 + Round((x2 - x1) * (percent / 100));
      // adjust end y using percent
      if y1 <> y2 then
        y2 := y1 + Round((y2 - y1) * (percent / 100));
      if (x1 <> x2) or (y1 <> y2) then
      begin
        // draw the line
        pbxFractalView.Canvas.MoveTo(x1, y1);
        pbxFractalView.Canvas.LineTo(x2, y2);
      end;
    end;

  begin
    // draw the rectangle
    with pbxFractalView.Canvas do
    begin
      Pen.Color := clGray;
      Brush.Style := bsClear;
      Rectangle(aFractalPart.fViewRect);
      Pen.Color := clWhite;
      if aFractalPart.fHighLight then
        Pen.Color := clYellow;
    end;
    // draw progress
    liProgress := aFractalPart.fProgress;
    with aFractalPart.fViewRect do
    begin
      DrawLine(Left, Top, Right-1, Top, IfThen(liProgress >= 25, 100, liProgress * 4));
      DrawLine(Right-1, Top, Right-1, Bottom-1, IfThen(liProgress >= 50, 100, (liProgress - 25) * 4));
      DrawLine(Right-1, Bottom-1, Left, Bottom-1, IfThen(liProgress >= 75, 100, (liProgress - 50) * 4));
      DrawLine(Left, Bottom-1, Left, Top, IfThen(liProgress < 75, 0, (liProgress - 75) * 4));
    end;
  end;

begin
  // paint the bitmap of the part
  pbxFractalView.Canvas.Draw(0, 0, fPartBitmap);
  // now paint progress of child parts
  for liChildPart := 0 to fFractalPart.fChildParts.Count-1 do
    DrawProgress(TFractalPart(fFractalPart.fChildParts[liChildPart]));
end;

procedure TfrmMain.InvalidateFractalPart(aFractalPart: TFractalPart);
var
  lRect: TRect;
  lRgn1, lRgn2: HRgn;
begin
  if (aFractalPart.fParentPart = fFractalPart) then
  begin
    lRect := aFractalPart.fViewRect;
    OffsetRect(lRect, pbxFractalView.Left, pbxFractalView.Top);
    lRgn1 := CreateRectRgnIndirect(lRect);
    InflateRect(lRect, -1, -1);
    lRgn2 := CreateRectRgnIndirect(lRect);
    CombineRgn(lRgn1, lRgn1, lRgn2, RGN_XOR);
    InvalidateRgn(WindowFromDC(pbxFractalView.Canvas.Handle), lRgn1, False);
    DeleteObject(lRgn1);
    DeleteObject(lRgn2);
  end;
end;

procedure TfrmMain.DisplayPartDetails(aFractalPart: TFractalPart);
begin
  // display info about the fractal part
  lbLeft  .Caption := FloatToStrF(fFractalPart.fLeft , ffFixed, 18, 17);
  lbTop   .Caption := FloatToStrF(fFractalPart.fTop, ffFixed, 18, 17);
  lbWidth .Caption := FloatToStrF(fFractalPart.fRight - fFractalPart.fLeft, ffExponent, 14, 0);
  lbHeight.Caption := FloatToStrF(fFractalPart.fBottom - fFractalPart.fTop, ffExponent, 14, 0);
  lbMagnification.Caption := FloatToStrF(3 / (fFractalPart.fRight - fFractalPart.fLeft), ffFixed, 18, 1);
  lbMaxIterations.Caption := IntToStr(fFractalPart.fMaxIterations);
  lbLevel.Caption := IntToStr(fFractalPart.fLevel);
end;

procedure TfrmMain.SetFractalPart(const Value: TFractalPart);
begin
  if Value <> fFractalPart then
  begin
    fChanging := True;
    try
      fFractalPart := Value;
      fFractalPart.fVisited := True;
      trvPartTree.Selected := fFractalPart.fNode;
      trvPartTree.Invalidate;
      // draw the part
      DrawFractalPart(fFractalPart);
      DisplayPartDetails(fFractalPart);
      // update button state
      btnUp     .Enabled := Assigned(FractalPart.fParentPart);
      btnForward.Enabled := fBackIndex < fBackList.Count - 1;
      btnBack   .Enabled := fBackIndex > 0;
    finally
      fChanging := False;
    end;
  end;
end;

procedure TfrmMain.GotoFractalPart(aFractalPart: TFractalPart);
begin
  HistoryAdd(aFractalPart);
  FractalPart := aFractalPart;
end;

procedure TfrmMain.btnUpClick(Sender: TObject);
begin
  if Assigned(fFractalPart.fParentPart) then
    GotoFractalPart(FractalPart.fParentPart);
end;

procedure TfrmMain.btnBackClick(Sender: TObject);
begin
  if fBackIndex > 0 then
  begin
    Dec(fBackIndex);
    FractalPart := TFractalPart(fBackList[fBackIndex]);
  end;
end;

procedure TfrmMain.btnForwardClick(Sender: TObject);
begin
  if fBackIndex < fBackList.Count - 1 then
  begin
    Inc(fBackIndex);
    FractalPart := TFractalPart(fBackList[fBackIndex]);
  end;
end;

procedure TfrmMain.HistoryAdd(aFractalPart: TFractalPart);
begin
  // truncate list
  if fBackList.Count - 1 > fBackIndex then
    fBackList.Count := fBackIndex + 1;
  // add part
  fBackList.Add(aFractalPart);
  fBackIndex := fBackList.Count - 1;
end;

procedure TfrmMain.trvPartTreeCustomDrawItem(Sender: TCustomTreeView; Node: TTreeNode; State: TCustomDrawState; var DefaultDraw: Boolean);
begin
  DefaultDraw := True;
  if TFractalPart(Node.Data) = FractalPart then
    trvPartTree.Canvas.Font.Style := [fsBold]
  else
    trvPartTree.Canvas.Font.Style := [];
  if not TFractalPart(Node.Data).fVisited then
    trvPartTree.Canvas.Font.Color := clRed;
end;

procedure TfrmMain.trvPartTreeChange(Sender: TObject; Node: TTreeNode);
begin
  if not fChanging then
    if Assigned(Node) then
      GotoFractalPart(TFractalPart(Node.Data));
end;

procedure TfrmMain.trvPartTreeEdited(Sender: TObject; Node: TTreeNode; var S: String);
begin
  TFractalPart(Node.Data).fName := S;
end;

procedure TfrmMain.miColorScheme(Sender: TObject);
begin
  fFractalPart.fColorScheme := TMenuItem(Sender).Tag;
  DrawFractalPart(fFractalPart);
  pbxFractalView.Invalidate;
end;

procedure TfrmMain.pmColorSchemePopup(Sender: TObject);
begin
  pmColorScheme.Items[fFractalPart.fColorScheme].Checked := True;
end;

procedure TfrmMain.btnSaveClick(Sender: TObject);
var
  fPart: TFractalPart;
  lCS: TCompressionStream;
  lFS: TFileStream;
  lW: TWriter;

  procedure SaveTotal(aFractalPart: TFractalPart);
  var
    liChild: Integer;
  begin
    with aFractalPart do
    begin
      lW.WriteString(fName);
      lW.WriteInteger(fColorScheme);
      lW.WriteInteger(fMaxIterations);
      lW.WriteFloat(fLeft);
      lW.WriteFloat(fTop);
      lW.WriteFloat(fRight);
      lW.WriteFloat(fBottom);
      lW.Write(fViewRect, SizeOf(fViewRect));
      lW.Write(fIterations, SizeOf(fIterations));
      lW.WriteListBegin;
      for liChild := 0 to fChildParts.Count-1 do
        if TFractalPart(fChildParts[liChild]).fProgress = 101 then
          SaveTotal(TFractalPart(fChildParts[liChild]));
      lW.WriteListEnd;
    end;
  end;

begin
  if sdSave.Execute then
  begin
    Refresh;
    fSaveSection.Enter;
    fPart := TFractalPart(trvPartTree.Items.Item[0].Data);
    lFS := nil;
    lCS := nil;
    lW := nil;
    try
      lFS := TFileStream.Create(sdSave.FileName, fmCreate);
      lCS := TCompressionStream.Create(clMax, lFS);
      lW := TWriter.Create(lCS, 65536);
      SaveTotal(fPart);
    finally
      lW.Free;
      lCS.Free;
      lFS.Free;
      fSaveSection.Leave;
    end;
  end;
end;

procedure TfrmMain.btnLoadClick(Sender: TObject);
var
  lCS: TDecompressionStream;
  lFS: TFileStream;
  lR: TReader;

  procedure LoadTotal(aFractalPart: TFractalPart);
  var
    lFractalPart: TFractalPart;
    liChild, liChildCount: Integer;
    lNode: TTreeNode;
  begin
    lFractalPart := TFractalPart.Create(aFractalPart, 0, 0, 0, 0, Rect(0,0,0,0));
    if not Assigned(fRootPart) then
      fRootPart := lFractalPart;
    with lFractalPart do
    begin
      fName := lR.ReadString;
      fProgress := 101;
      lNode := nil;
      if Assigned(fParentPart) then
        lNode := fParentPart.fNode;
      fNode := frmMain.trvPartTree.Items.AddChildObject(lNode, fName, lFractalPart);
      fColorScheme := lR.ReadInteger;
      fMaxIterations := lR.ReadInteger;
      fLeft := lR.ReadFloat;
      fTop := lR.ReadFloat;
      fRight := lR.ReadFloat;
      fBottom := lR.ReadFloat;
      lR.Read(fViewRect, SizeOf(fViewRect));
      lR.Read(fIterations, SizeOf(fIterations));
      pbLoadSave.Position := Round(lR.Position / lFS.Size);
      lR.ReadListBegin;
      while not lR.EndOfList do
        LoadTotal(lFractalPart);
      lR.ReadListEnd;
    end;
  end;

begin
  if odLoad.Execute then
  begin
    Refresh;
    pbLoadSave.Position := 0;
    KillThreads;
    Refresh;
    FreeAndNil(fRootPart);
    trvPartTree.Items.Clear;
    lFS := nil;
    lCS := nil;
    lR := nil;
    trvPartTree.Items.BeginUpdate;
    try
      lFS := TFileStream.Create(odLoad.FileName, fmOpenRead);
      lCS := TDecompressionStream.Create(lFS);
      lR := TReader.Create(lCS, 65536);
      LoadTotal(nil);
    finally
      trvPartTree.Items.EndUpdate;
      lR.Free;
      lCS.Free;
      lFS.Free;
    end;
    fBackList.Clear;
    fBackIndex := 0;
    GotoFractalPart(fRootPart);
    pbLoadSave.Position := 100;
  end;
end;

procedure TfrmMain.miInfoClick(Sender: TObject);
begin
  pnlRight.Left := 1000;
  pnlRight.Visible := (Sender as TMenuItem).Checked;
end;

end.
