import Mathlib
import OAI.Analysis.LaughlinGap.Certificate13
import OAI.Analysis.LaughlinGap.SumTable14

namespace OAI

/-! Certificate14. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators ComplexOrder
open Spin
namespace Certificate14

def keys : Fin 18 → Finset (Fin 25) := ![{0,1,2,12}, {0,1,3,11}, {0,1,4,10}, {0,1,5,9}, {0,1,6,8}, {0,2,3,10}, {0,2,4,9}, {0,2,5,8}, {0,2,6,7}, {0,3,4,8}, {0,3,5,7}, {0,4,5,6}, {1,2,3,9}, {1,2,4,8}, {1,2,5,7}, {1,3,4,7}, {1,3,5,6}, {2,3,4,6}]
def fibers : Fin 18 → Finset (FourTerm 14) := ![{⟨⟨14,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨13,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨2,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩}, {⟨⟨14,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩}, {⟨⟨14,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨4,by decide⟩)⟩}, {⟨⟨14,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨5,by decide⟩)⟩}, {⟨⟨14,by decide⟩,(⟨6,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨6,by decide⟩)⟩}, {⟨⟨13,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨2,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩}, {⟨⟨13,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨2,by decide⟩,(⟨0,by decide⟩,⟨4,by decide⟩)⟩}, {⟨⟨13,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨2,by decide⟩,(⟨0,by decide⟩,⟨5,by decide⟩)⟩}, {⟨⟨13,by decide⟩,(⟨6,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨2,by decide⟩,(⟨0,by decide⟩,⟨6,by decide⟩)⟩}, {⟨⟨12,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨0,by decide⟩,⟨4,by decide⟩)⟩}, {⟨⟨12,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨0,by decide⟩,⟨5,by decide⟩)⟩}, {⟨⟨11,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨0,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨0,by decide⟩,⟨4,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨0,by decide⟩,⟨5,by decide⟩)⟩}, {⟨⟨12,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨1,by decide⟩,⟨3,by decide⟩)⟩}, {⟨⟨12,by decide⟩,(⟨4,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨1,by decide⟩,⟨4,by decide⟩)⟩}, {⟨⟨12,by decide⟩,(⟨5,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨1,by decide⟩,⟨5,by decide⟩)⟩}, {⟨⟨11,by decide⟩,(⟨4,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨1,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨1,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨1,by decide⟩,⟨4,by decide⟩)⟩}, {⟨⟨11,by decide⟩,(⟨5,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨1,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨1,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨1,by decide⟩,⟨5,by decide⟩)⟩}, {⟨⟨10,by decide⟩,(⟨4,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨3,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨3,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨2,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨2,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨2,by decide⟩,⟨4,by decide⟩)⟩}]
def columns : Matrix (Fin 7) (Fin 18) ℚ := ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![-37422000, 37422000, -37422000, 29937600, -14968800, 0, 7484400, -14968800, 14968800, 0, 3742200, -7484400, -7484400, 7484400, -3742200, -3742200, 3742200, 0], ![-29937600, 29937600, -19051200, 10886400, -5443200, -10886400, 8164800, -5443200, 5443200, 0, -1360800, 2721600, 2721600, -2721600, 1360800, 1360800, -1360800, 0], ![-6548850, 6548850, -1786050, -2381400, 2778300, -4762800, 4167450, -396900, -2778300, -3175200, 2877525, -2579850, 595350, -595350, 297675, 297675, -297675, 0], ![26195400, -26195400, 12587400, -1360800, -2041200, 13608000, -11226600, 3402000, 2041200, 5443200, -4252500, 3061800, -2381400, 2381400, -1190700, -1190700, 1190700, 0], ![-3742200, 3742200, 7484400, -14968800, 11226600, -11226600, 7484400, 3742200, -11226600, -7484400, 5613300, -3742200, 3742200, -3742200, 1871100, 1871100, -1871100, 0], ![-389188800, 389188800, -291891600, 194594400, -97297200, -97297200, 97297200, -97297200, 97297200, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
def Y : Matrix (Fin 7) (Fin 7) ℚ := ![![(15219600345752738461520645079/83886080000000000000), (-100699762768020161113872933/4194304000000000000), (-623729805467846140120843071/83886080000000000000), (-584089516007342278316570187/41943040000000000000), (190555190136371424746095857/10485760000000000000), (1571730082844728778022051/5242880000000000000), (-1139960040141741640450909137/5242880000000000000)], ![(-100699762768020161113872933/4194304000000000000), (142741640769102658893312549/41943040000000000000), (-1420959356539230918345309/5242880000000000000), (10401301871960478637221063/10485760000000000000), (-317763072506796368043537/262144000000000000), (6764197770693769340624481/2621440000000000000), (-3847922209486781646037389/327680000000000000)], ![(-623729805467846140120843071/83886080000000000000), (-1420959356539230918345309/5242880000000000000), (-80601890371374760912183311/83886080000000000000), (19362242855862308868505137/41943040000000000000), (-739855777506079978431279/2097152000000000000), (2827689580002698468430219/5242880000000000000), (11349999406573499998071603/1048576000000000000)], ![(-584089516007342278316570187/41943040000000000000), (10401301871960478637221063/10485760000000000000), (19362242855862308868505137/41943040000000000000), (-12463140124899425974493061/20971520000000000000), (810008762072598110220849/5242880000000000000), (4281511287086331709548753/2621440000000000000), (24114645682193842356171591/2621440000000000000)], ![(190555190136371424746095857/10485760000000000000), (-317763072506796368043537/262144000000000000), (-739855777506079978431279/2097152000000000000), (810008762072598110220849/5242880000000000000), (-457283495233465719845067/262144000000000000), (-2055131064044619675411429/655360000000000000), (17042174237599294094951211/655360000000000000)], ![(1571730082844728778022051/5242880000000000000), (6764197770693769340624481/2621440000000000000), (2827689580002698468430219/5242880000000000000), (4281511287086331709548753/2621440000000000000), (-2055131064044619675411429/655360000000000000), (-3397198876302593138403627/327680000000000000), (-23457664774180455687416691/327680000000000000)], ![(-1139960040141741640450909137/5242880000000000000), (-3847922209486781646037389/327680000000000000), (11349999406573499998071603/1048576000000000000), (24114645682193842356171591/2621440000000000000), (17042174237599294094951211/655360000000000000), (-23457664774180455687416691/327680000000000000), (-36053847999379672913103939/65536000000000000)]]
def Z : Matrix (Fin 7) (Fin 7) ℚ := ![![0, 0, 0, 0, 0, 0, 0], ![0, 239500800, 0, 0, 0, -74844000, 778377600], ![0, 0, 43545600, 0, -21772800, 0, 389188800], ![0, 0, 0, 11113200, -19051200, 26195400, 0], ![0, 0, -21772800, -19051200, 43545600, -44906400, -194594400], ![0, -74844000, 0, 26195400, -44906400, 85135050, -243243000], ![0, 778377600, 389188800, 0, -194594400, -243243000, 6008102100]]
def W : Matrix (Fin 7) (Fin 7) ℚ := ![![0, 0, 0, 0, 0, 0, 0], ![(123795619616625230857561/15032385536000000000000000), (-221210576158217105563/46976204800000000000000), (-315334141815200876317037/15032385536000000000000000), (-17240348303552013281301/268435456000000000000000), (-18606396763756514900187/268435456000000000000000), (1227009175825425140409/93952409600000000000000), (8772549315849100608091/939524096000000000000000)], ![(18172541700157367690841/3758096384000000000000000), (12224389970059675949/7340032000000000000000), (9334405490547223614403/3758096384000000000000000), (-17741117058979611456699/469762048000000000000000), (-3305365487436044767739/67108864000000000000000), (165804218614708974899/16777216000000000000000), (1379163013793970768619/234881024000000000000000)], ![(115960184441607400478711/51539607552000000000000000), (-2095680593639597551879/402653184000000000000000), (-98307993990097050306151/10307921510400000000000000), (37792678041424947070259/6442450944000000000000000), (-24059909713700877186417/2147483648000000000000000), (-1280999549817774216473/322122547200000000000000), (1570739546172222142769/644245094400000000000000)], ![(-7546014049689474849683/1202590842880000000000000), (380018070823728547339/46976204800000000000000), (454202347988296357073143/30064771072000000000000000), (4738827170641928393791/536870912000000000000000), (164729962789311885055943/3758096384000000000000000), (1762479627877019785193/939524096000000000000000), (-13370349786036993788321/1879048192000000000000000)], ![(20518247836704851593063/7516192768000000000000000), (-40574708656115718502263/3758096384000000000000000), (-2992397625296354207229/187904819200000000000000), (63695728067499680163649/1879048192000000000000000), (-4461035431895341426413/939524096000000000000000), (-180589651135023590029/13421772800000000000000), (132899776438208483787/46976204800000000000000)], ![(150286304219236842176377/2147483648000000000000000), (-393985324535842575939/939524096000000000000000), (-98732994944619943402209/2147483648000000000000000), (-1026462858764329411726587/1879048192000000000000000), (-178637605658047273872277/268435456000000000000000), (61431404815494079500121/469762048000000000000000), (3112634520785761278177/37580963840000000000000)]]
def M : Matrix (Fin 7) (Fin 7) ℚ := ![![0, 0, 0, 0, 0, 0, 0], ![0, (433072404967000467346093053/83886080000000000000), (88702260823986477866596629/20971520000000000000), (636782555035305004693648743/671088640000000000000), (-627715852596790913477950263/167772160000000000000), (52288304842143292837295997/83886080000000000000), (4578591140600268102605631909/83886080000000000000)], ![0, (88702260823986477866596629/20971520000000000000), (18170625719261128544184429/5242880000000000000), (130446532111511337136927407/167772160000000000000), (-128588159496263658663992319/41943040000000000000), (10715682418217387501676093/20971520000000000000), (937882217141541398521032381/20971520000000000000)], ![0, (636782555035305004693648743/671088640000000000000), (130446532111511337136927407/167772160000000000000), (187330355546167953656478081/1073741824000000000000), (-923208318902119534954448373/1342177280000000000000), (15396641498003637837573531/134217728000000000000), (1346601365370254313579902643/134217728000000000000)], ![0, (-627715852596790913477950263/167772160000000000000), (-128588159496263658663992319/41943040000000000000), (-923208318902119534954448373/1342177280000000000000), (910013346085963006779304293/335544320000000000000), (-75855532882877345372933367/167772160000000000000), (-6637103222930996266041063759/167772160000000000000)], ![0, (52288304842143292837295997/83886080000000000000), (10715682418217387501676093/20971520000000000000), (15396641498003637837573531/134217728000000000000), (-75855532882877345372933367/167772160000000000000), (1268491388742116060525487/16777216000000000000), (110604527437647460981226463/16777216000000000000)], ![0, (4578591140600268102605631909/83886080000000000000), (937882217141541398521032381/20971520000000000000), (1346601365370254313579902643/134217728000000000000), (-6637103222930996266041063759/167772160000000000000), (110604527437647460981226463/16777216000000000000), (1936388418790439053223808453/3355443200000000000)]]
def L : Matrix (Fin 7) (Fin 7) ℚ := ![![1, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0], ![0, (132738138157854811622292/162017360631126250410061), 1, 0, 0, 0, 0], ![0, (238227667428097644853591/1296138885049010003280488), (9557801666835981004170464449335712364327/38681444879414949802360013223276559109056), 1, 0, 0, 0], ![0, (-234835709912753802273831/324034721262252500820122), (-8931381324285146298510914988339160901915/9670361219853737450590003305819139777264), (-12/7), 1, 0, 0], ![0, (1778332307660554801799/14728850966466022764551), (45058207857941053305375046689725501146113/77362889758829899604720026446553118218112), (33/14), 0, 1, 0], ![0, (155718502894271608427903/14728850966466022764551), (143/16), 0, 0, 0, 1]]
def diag : Fin 7 → ℚ := ![0, (433072404967000467346093053/83886080000000000000), (146868611026528637530835675207128185367197/301646867793224146218004480000000000000), (335384473774632721168007398488458696062030883255156572440519/10140108686469352600989863306402610311084376064000000000000), 0, 0, 0]

def keyIndexTable : Fin 15 → Fin 13 → Fin 13 → Fin 18 := ![![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 0, 0, 1, 2, 3, 4, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 0, 0, 5, 6, 7, 8, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 1, 5, 0, 9, 10, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 12, 13, 14, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 2, 6, 9, 0, 11, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 12, 0, 15, 16, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 3, 7, 10, 11, 0, 0, 0, 0, 0, 0, 0, 0], ![2, 0, 13, 15, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![5, 12, 0, 0, 17, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 4, 8, 0, 11, 0, 0, 0, 0, 0, 0, 0, 0], ![3, 0, 14, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![6, 13, 0, 17, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 0, 8, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![4, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![7, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![9, 15, 17, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 4, 7, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 14, 15, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![8, 0, 0, 17, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![10, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 3, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![4, 0, 13, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![8, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 16, 17, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![11, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 2, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![3, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![7, 13, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![10, 15, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![11, 0, 17, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![6, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 15, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![11, 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![9, 13, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![10, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]]
def keyIndex (n : Fin 15) (j : Fin ((n.val+1)/2)) (x : Fin ((14-n.val+2)/2)) : Fin 18 :=
  keyIndexTable n ⟨j.val,by have := j.isLt; have := n.isLt; omega⟩ ⟨x.val,by have := x.isLt; omega⟩
def representatives : Fin 18 → FourTerm 14 := ![⟨⟨14,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨14,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨14,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨14,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨14,by decide⟩,(⟨6,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨13,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨13,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨13,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨13,by decide⟩,(⟨6,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨12,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨12,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨11,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨12,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨12,by decide⟩,(⟨4,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨12,by decide⟩,(⟨5,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨11,by decide⟩,(⟨4,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨11,by decide⟩,(⟨5,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨10,by decide⟩,(⟨4,by decide⟩,⟨2,by decide⟩)⟩]
lemma cover_0 : ∀ j : Fin 0, ∀ x : Fin 8,
  (fourTermLabels (by omega : 14 ≤ 23) ⟨0,j,x⟩).Nodup →
    (fourTermLabels (by omega : 14 ≤ 23) ⟨0,j,x⟩).toFinset=keys (keyIndex 0 j x) := by decide +kernel
lemma cover_1 : ∀ j : Fin 1, ∀ x : Fin 7,
  (fourTermLabels (by omega : 14 ≤ 23) ⟨1,j,x⟩).Nodup →
    (fourTermLabels (by omega : 14 ≤ 23) ⟨1,j,x⟩).toFinset=keys (keyIndex 1 j x) := by decide +kernel
lemma cover_2 : ∀ j : Fin 1, ∀ x : Fin 7,
  (fourTermLabels (by omega : 14 ≤ 23) ⟨2,j,x⟩).Nodup →
    (fourTermLabels (by omega : 14 ≤ 23) ⟨2,j,x⟩).toFinset=keys (keyIndex 2 j x) := by decide +kernel
lemma cover_3 : ∀ j : Fin 2, ∀ x : Fin 6,
  (fourTermLabels (by omega : 14 ≤ 23) ⟨3,j,x⟩).Nodup →
    (fourTermLabels (by omega : 14 ≤ 23) ⟨3,j,x⟩).toFinset=keys (keyIndex 3 j x) := by decide +kernel
lemma cover_4 : ∀ j : Fin 2, ∀ x : Fin 6,
  (fourTermLabels (by omega : 14 ≤ 23) ⟨4,j,x⟩).Nodup →
    (fourTermLabels (by omega : 14 ≤ 23) ⟨4,j,x⟩).toFinset=keys (keyIndex 4 j x) := by decide +kernel
lemma cover_5 : ∀ j : Fin 3, ∀ x : Fin 5,
  (fourTermLabels (by omega : 14 ≤ 23) ⟨5,j,x⟩).Nodup →
    (fourTermLabels (by omega : 14 ≤ 23) ⟨5,j,x⟩).toFinset=keys (keyIndex 5 j x) := by decide +kernel
lemma cover_6 : ∀ j : Fin 3, ∀ x : Fin 5,
  (fourTermLabels (by omega : 14 ≤ 23) ⟨6,j,x⟩).Nodup →
    (fourTermLabels (by omega : 14 ≤ 23) ⟨6,j,x⟩).toFinset=keys (keyIndex 6 j x) := by decide +kernel
lemma cover_7 : ∀ j : Fin 4, ∀ x : Fin 4,
  (fourTermLabels (by omega : 14 ≤ 23) ⟨7,j,x⟩).Nodup →
    (fourTermLabels (by omega : 14 ≤ 23) ⟨7,j,x⟩).toFinset=keys (keyIndex 7 j x) := by decide +kernel
lemma cover_8 : ∀ j : Fin 4, ∀ x : Fin 4,
  (fourTermLabels (by omega : 14 ≤ 23) ⟨8,j,x⟩).Nodup →
    (fourTermLabels (by omega : 14 ≤ 23) ⟨8,j,x⟩).toFinset=keys (keyIndex 8 j x) := by decide +kernel
lemma cover_9 : ∀ j : Fin 5, ∀ x : Fin 3,
  (fourTermLabels (by omega : 14 ≤ 23) ⟨9,j,x⟩).Nodup →
    (fourTermLabels (by omega : 14 ≤ 23) ⟨9,j,x⟩).toFinset=keys (keyIndex 9 j x) := by decide +kernel
lemma cover_10 : ∀ j : Fin 5, ∀ x : Fin 3,
  (fourTermLabels (by omega : 14 ≤ 23) ⟨10,j,x⟩).Nodup →
    (fourTermLabels (by omega : 14 ≤ 23) ⟨10,j,x⟩).toFinset=keys (keyIndex 10 j x) := by decide +kernel
lemma cover_11 : ∀ j : Fin 6, ∀ x : Fin 2,
  (fourTermLabels (by omega : 14 ≤ 23) ⟨11,j,x⟩).Nodup →
    (fourTermLabels (by omega : 14 ≤ 23) ⟨11,j,x⟩).toFinset=keys (keyIndex 11 j x) := by decide +kernel
lemma cover_12 : ∀ j : Fin 6, ∀ x : Fin 2,
  (fourTermLabels (by omega : 14 ≤ 23) ⟨12,j,x⟩).Nodup →
    (fourTermLabels (by omega : 14 ≤ 23) ⟨12,j,x⟩).toFinset=keys (keyIndex 12 j x) := by decide +kernel
lemma cover_13 : ∀ j : Fin 7, ∀ x : Fin 1,
  (fourTermLabels (by omega : 14 ≤ 23) ⟨13,j,x⟩).Nodup →
    (fourTermLabels (by omega : 14 ≤ 23) ⟨13,j,x⟩).toFinset=keys (keyIndex 13 j x) := by decide +kernel
lemma cover_14 : ∀ j : Fin 7, ∀ x : Fin 1,
  (fourTermLabels (by omega : 14 ≤ 23) ⟨14,j,x⟩).Nodup →
    (fourTermLabels (by omega : 14 ≤ 23) ⟨14,j,x⟩).toFinset=keys (keyIndex 14 j x) := by decide +kernel
lemma cover : ∀ b : FourTerm 14, (fourTermLabels (by omega : 14 ≤ 23) b).Nodup →
    (fourTermLabels (by omega : 14 ≤ 23) b).toFinset=keys (keyIndex b.1 b.2.1 b.2.2) := by
  rintro ⟨n,j,x⟩
  fin_cases n
  · exact cover_0 j x
  · exact cover_1 j x
  · exact cover_2 j x
  · exact cover_3 j x
  · exact cover_4 j x
  · exact cover_5 j x
  · exact cover_6 j x
  · exact cover_7 j x
  · exact cover_8 j x
  · exact cover_9 j x
  · exact cover_10 j x
  · exact cover_11 j x
  · exact cover_12 j x
  · exact cover_13 j x
  · exact cover_14 j x
lemma representatives_checked : ∀ a : Fin 18,
  (fourTermLabels (by omega : 14 ≤ 23) (representatives a)).Nodup ∧
  (fourTermLabels (by omega : 14 ≤ 23) (representatives a)).toFinset=keys a := by decide +kernel
lemma keys_checked : fourKeys (by omega : 14 ≤ 23) = Finset.univ.image keys :=
  fourKeys_of_index (by omega : 14 ≤ 23) keys (fun b => keyIndex b.1 b.2.1 b.2.2)
    representatives cover representatives_checked
lemma keys_injective : Function.Injective keys := by decide +kernel
lemma keys_card : ∀ a : Fin 18, (keys a).card=4 := by decide +kernel
lemma fibers_cover : ∀ b : FourTerm 14,
    (fourTermLabels (by omega : 14 ≤ 23) b).Nodup →
      b ∈ fibers (keyIndex b.1 b.2.1 b.2.2) := by
  apply checkFourTerms_sound
  decide +kernel
lemma fibers_sound : ∀ a : Fin 18, ∀ b ∈ fibers a,
    (fourTermLabels (by omega : 14 ≤ 23) b).toFinset=keys a := by
  apply checkFourFibersSound_sound
  decide +kernel
lemma fibers_checked : ∀ a : Fin 18, ∀ b : FourTerm 14,
    (fourTermLabels (by omega : 14 ≤ 23) b).toFinset=keys a ↔ b ∈ fibers a :=
  fourFibers_of_index (by omega : 14 ≤ 23) keys
    (fun b => keyIndex b.1 b.2.1 b.2.2) fibers keys_injective keys_card cover fibers_cover fibers_sound
lemma columns_checked_0 : ∀ v : Fin 18, (∑ b ∈ fibers v, fourTermEval 14 (2*(0 : Fin 7).val+1) b * Occupation.wordSign (fourTermLabels (by omega : 14 ≤ 23) b)) = columns 0 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma columns_checked_1 : ∀ v : Fin 18, (∑ b ∈ fibers v, fourTermEval 14 (2*(1 : Fin 7).val+1) b * Occupation.wordSign (fourTermLabels (by omega : 14 ≤ 23) b)) = columns 1 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma columns_checked_2 : ∀ v : Fin 18, (∑ b ∈ fibers v, fourTermEval 14 (2*(2 : Fin 7).val+1) b * Occupation.wordSign (fourTermLabels (by omega : 14 ≤ 23) b)) = columns 2 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma columns_checked_3 : ∀ v : Fin 18, (∑ b ∈ fibers v, fourTermEval 14 (2*(3 : Fin 7).val+1) b * Occupation.wordSign (fourTermLabels (by omega : 14 ≤ 23) b)) = columns 3 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma columns_checked_4 : ∀ v : Fin 18, (∑ b ∈ fibers v, fourTermEval 14 (2*(4 : Fin 7).val+1) b * Occupation.wordSign (fourTermLabels (by omega : 14 ≤ 23) b)) = columns 4 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma columns_checked_5 : ∀ v : Fin 18, (∑ b ∈ fibers v, fourTermEval 14 (2*(5 : Fin 7).val+1) b * Occupation.wordSign (fourTermLabels (by omega : 14 ≤ 23) b)) = columns 5 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma columns_checked_6 : ∀ v : Fin 18, (∑ b ∈ fibers v, fourTermEval 14 (2*(6 : Fin 7).val+1) b * Occupation.wordSign (fourTermLabels (by omega : 14 ≤ 23) b)) = columns 6 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma columns_checked : ∀ u : Fin 7, ∀ v : Fin 18, (∑ b ∈ fibers v, fourTermEval 14 (2*u.val+1) b * Occupation.wordSign (fourTermLabels (by omega : 14 ≤ 23) b)) = columns u v := by
  intro u
  fin_cases u
  · exact columns_checked_0
  · exact columns_checked_1
  · exact columns_checked_2
  · exact columns_checked_3
  · exact columns_checked_4
  · exact columns_checked_5
  · exact columns_checked_6
lemma gram_checked_0 : ∀ v : Fin 7, (∑ a : Fin 18, columns (0 : Fin 7) a * columns v a / setFactorial (keys a)) = Z 0 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma gram_checked_1 : ∀ v : Fin 7, (∑ a : Fin 18, columns (1 : Fin 7) a * columns v a / setFactorial (keys a)) = Z 1 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma gram_checked_2 : ∀ v : Fin 7, (∑ a : Fin 18, columns (2 : Fin 7) a * columns v a / setFactorial (keys a)) = Z 2 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma gram_checked_3 : ∀ v : Fin 7, (∑ a : Fin 18, columns (3 : Fin 7) a * columns v a / setFactorial (keys a)) = Z 3 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma gram_checked_4 : ∀ v : Fin 7, (∑ a : Fin 18, columns (4 : Fin 7) a * columns v a / setFactorial (keys a)) = Z 4 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma gram_checked_5 : ∀ v : Fin 7, (∑ a : Fin 18, columns (5 : Fin 7) a * columns v a / setFactorial (keys a)) = Z 5 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma gram_checked_6 : ∀ v : Fin 7, (∑ a : Fin 18, columns (6 : Fin 7) a * columns v a / setFactorial (keys a)) = Z 6 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma gram_checked : ∀ u : Fin 7, ∀ v : Fin 7, (∑ a : Fin 18, columns u a * columns v a / setFactorial (keys a)) = Z u v := by
  intro u
  fin_cases u
  · exact gram_checked_0
  · exact gram_checked_1
  · exact gram_checked_2
  · exact gram_checked_3
  · exact gram_checked_4
  · exact gram_checked_5
  · exact gram_checked_6
lemma rows_table_checked_0 : ∀ v : Fin 7, integerTableEval 14 SumTable14.sums (0 : Fin 7) v = Y 0 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma rows_table_checked_1 : ∀ v : Fin 7, integerTableEval 14 SumTable14.sums (1 : Fin 7) v = Y 1 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma rows_table_checked_2 : ∀ v : Fin 7, integerTableEval 14 SumTable14.sums (2 : Fin 7) v = Y 2 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma rows_table_checked_3 : ∀ v : Fin 7, integerTableEval 14 SumTable14.sums (3 : Fin 7) v = Y 3 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma rows_table_checked_4 : ∀ v : Fin 7, integerTableEval 14 SumTable14.sums (4 : Fin 7) v = Y 4 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma rows_table_checked_5 : ∀ v : Fin 7, integerTableEval 14 SumTable14.sums (5 : Fin 7) v = Y 5 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma rows_table_checked_6 : ∀ v : Fin 7, integerTableEval 14 SumTable14.sums (6 : Fin 7) v = Y 6 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma rows_table_checked : ∀ u : Fin 7, ∀ v : Fin 7, integerTableEval 14 SumTable14.sums u v = Y u v := by
  intro u
  fin_cases u
  · exact rows_table_checked_0
  · exact rows_table_checked_1
  · exact rows_table_checked_2
  · exact rows_table_checked_3
  · exact rows_table_checked_4
  · exact rows_table_checked_5
  · exact rows_table_checked_6
lemma rows_checked (u v : Fin 7) : exactFourEval 14 (2*u.val+1) (2*v.val+1) = Y u v := by
  rw [exactFourEval_table 14 SumTable14.sums SumTable14.sums_checked]
  exact rows_table_checked u v
lemma product_checked_0 : ∀ v : Fin 7, (Z * tableComparison 14 (1/200000) Y) (0 : Fin 7) v = W 0 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma product_checked_1 : ∀ v : Fin 7, (Z * tableComparison 14 (1/200000) Y) (1 : Fin 7) v = W 1 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma product_checked_2 : ∀ v : Fin 7, (Z * tableComparison 14 (1/200000) Y) (2 : Fin 7) v = W 2 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma product_checked_3 : ∀ v : Fin 7, (Z * tableComparison 14 (1/200000) Y) (3 : Fin 7) v = W 3 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma product_checked_4 : ∀ v : Fin 7, (Z * tableComparison 14 (1/200000) Y) (4 : Fin 7) v = W 4 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma product_checked_5 : ∀ v : Fin 7, (Z * tableComparison 14 (1/200000) Y) (5 : Fin 7) v = W 5 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma product_checked_6 : ∀ v : Fin 7, (Z * tableComparison 14 (1/200000) Y) (6 : Fin 7) v = W 6 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma product_checked : ∀ u : Fin 7, ∀ v : Fin 7, (Z * tableComparison 14 (1/200000) Y) u v = W u v := by
  intro u
  fin_cases u
  · exact product_checked_0
  · exact product_checked_1
  · exact product_checked_2
  · exact product_checked_3
  · exact product_checked_4
  · exact product_checked_5
  · exact product_checked_6
lemma compression_checked_0 : ∀ v : Fin 7, (W * Z) (0 : Fin 7) v = M 0 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma compression_checked_1 : ∀ v : Fin 7, (W * Z) (1 : Fin 7) v = M 1 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma compression_checked_2 : ∀ v : Fin 7, (W * Z) (2 : Fin 7) v = M 2 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma compression_checked_3 : ∀ v : Fin 7, (W * Z) (3 : Fin 7) v = M 3 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma compression_checked_4 : ∀ v : Fin 7, (W * Z) (4 : Fin 7) v = M 4 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma compression_checked_5 : ∀ v : Fin 7, (W * Z) (5 : Fin 7) v = M 5 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma compression_checked_6 : ∀ v : Fin 7, (W * Z) (6 : Fin 7) v = M 6 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma compression_checked : ∀ u : Fin 7, ∀ v : Fin 7, (W * Z) u v = M u v := by
  intro u
  fin_cases u
  · exact compression_checked_0
  · exact compression_checked_1
  · exact compression_checked_2
  · exact compression_checked_3
  · exact compression_checked_4
  · exact compression_checked_5
  · exact compression_checked_6
lemma ldl_checked_0 : ∀ v : Fin 7, (∑ k : Fin 7, L (0 : Fin 7) k * diag k * L v k) = M 0 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma ldl_checked_1 : ∀ v : Fin 7, (∑ k : Fin 7, L (1 : Fin 7) k * diag k * L v k) = M 1 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma ldl_checked_2 : ∀ v : Fin 7, (∑ k : Fin 7, L (2 : Fin 7) k * diag k * L v k) = M 2 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma ldl_checked_3 : ∀ v : Fin 7, (∑ k : Fin 7, L (3 : Fin 7) k * diag k * L v k) = M 3 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma ldl_checked_4 : ∀ v : Fin 7, (∑ k : Fin 7, L (4 : Fin 7) k * diag k * L v k) = M 4 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma ldl_checked_5 : ∀ v : Fin 7, (∑ k : Fin 7, L (5 : Fin 7) k * diag k * L v k) = M 5 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma ldl_checked_6 : ∀ v : Fin 7, (∑ k : Fin 7, L (6 : Fin 7) k * diag k * L v k) = M 6 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma ldl_checked : ∀ u : Fin 7, ∀ v : Fin 7, (∑ k : Fin 7, L u k * diag k * L v k) = M u v := by
  intro u
  fin_cases u
  · exact ldl_checked_0
  · exact ldl_checked_1
  · exact ldl_checked_2
  · exact ldl_checked_3
  · exact ldl_checked_4
  · exact ldl_checked_5
  · exact ldl_checked_6
lemma diag_checked : ∀ u : Fin 7, 0 ≤ diag u := by decide +kernel
lemma certificate : FourCertificate (fun a : Fin 8 => (exactRows a).toReal) (1/200000) 14 (by omega) := by
  have hh := fourCertificate_of_tables exactRows (1/200000) (by omega : 14 ≤ 23) Y Z
  suffices FourCertificate (fun a : Fin 8 => (exactRows a).toReal) ((1/200000:ℚ):ℝ) 14 (by omega) by simpa using this
  apply hh
  · intro u v
    rw [exactFourEval_eq (by omega)]
    exact rows_checked u v
  · intro u v
    rw [rationalCreatedGram_of_columns (by omega : 14 ≤ 23) keys columns keys_checked keys_injective]
    · exact gram_checked u v
    · intro i a
      rw [fourColumn_eq_fiber (by omega : 14 ≤ 23) (2*i.val+1) (keys a) (fibers a) (fibers_checked a)]
      exact columns_checked i a
  · rw [Matrix.ext product_checked, Matrix.ext compression_checked]
    apply rational_ldl_positive M L diag diag_checked
    ext u v
    rw [Matrix.mul_apply]
    simpa only [Matrix.mul_diagonal,Matrix.transpose_apply] using (ldl_checked u v).symm
end Certificate14
end LaughlinGap.RealOccupation

end

end OAI
