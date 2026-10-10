import Mathlib
import OAI.Analysis.LaughlinGap.CachedIntegerRows
import OAI.Analysis.LaughlinGap.FastFourKeys
import OAI.Analysis.LaughlinGap.FourTables
import OAI.Analysis.LaughlinGap.SumTable11

namespace OAI

/-! Certificate11. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators ComplexOrder
open Spin
namespace Certificate11

def keys : Fin 9 → Finset (Fin 25) := ![{0,1,2,9}, {0,1,3,8}, {0,1,4,7}, {0,1,5,6}, {0,2,3,7}, {0,2,4,6}, {0,3,4,5}, {1,2,3,6}, {1,2,4,5}]
def fibers : Fin 9 → Finset (FourTerm 11) := ![{⟨⟨11,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨2,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩}, {⟨⟨11,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩}, {⟨⟨11,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨4,by decide⟩)⟩}, {⟨⟨11,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨5,by decide⟩)⟩}, {⟨⟨10,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨2,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩}, {⟨⟨10,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨2,by decide⟩,(⟨0,by decide⟩,⟨4,by decide⟩)⟩}, {⟨⟨9,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨0,by decide⟩,⟨4,by decide⟩)⟩}, {⟨⟨9,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨1,by decide⟩,⟨3,by decide⟩)⟩}, {⟨⟨9,by decide⟩,(⟨4,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨1,by decide⟩,⟨4,by decide⟩)⟩}]
def columns : Matrix (Fin 6) (Fin 9) ℚ := ![![226800, -226800, 340200, -340200, -113400, 0, 113400, 113400, -113400], ![90720, -90720, 75600, -75600, 15120, 0, -15120, -15120, 15120], ![28350, -28350, 4725, 16875, 23625, -21600, 19575, -2025, 2025], ![-62370, 62370, -25515, -4725, -36855, 30240, -23625, 6615, -6615], ![45360, -45360, -11340, 56700, 56700, -45360, 34020, -11340, 11340], ![1247400, -1247400, 1247400, -1247400, 0, 0, 0, 0, 0]]
def Y : Matrix (Fin 6) (Fin 6) ℚ := ![![(32839215004495137244466187/167772160000000000000), (-19588648001353140318042429/167772160000000000000), (769969819896078911998041/20971520000000000000), (-3060745927175333645962119/167772160000000000000), (1516286817957572396027451/20971520000000000000), (-19272986732194004208033657/20971520000000000000)], ![(-19588648001353140318042429/167772160000000000000), (24152328740360168247036519/838860800000000000000), (-2148675818210730931634253/167772160000000000000), (1994515423197492856394763/209715200000000000000), (8693018793801331618221/4194304000000000000), (-1927558817628006250840779/10485760000000000000)], ![(769969819896078911998041/20971520000000000000), (-2148675818210730931634253/167772160000000000000), (149319433910496770223741/46976204800000000000), (-342271579617331143233409/167772160000000000000), (65139956566813006253523/10485760000000000000), (2877018097116172834790361/20971520000000000000)], ![(-3060745927175333645962119/167772160000000000000), (1994515423197492856394763/209715200000000000000), (-342271579617331143233409/167772160000000000000), (-652126880335913571881601/104857600000000000000), (966055836873933781002981/104857600000000000000), (-511525534633041298988871/5242880000000000000)], ![(1516286817957572396027451/20971520000000000000), (8693018793801331618221/4194304000000000000), (65139956566813006253523/10485760000000000000), (966055836873933781002981/104857600000000000000), (-1172769771227963717819691/13107200000000000000), (521725615312896324070587/2621440000000000000)], ![(-19272986732194004208033657/20971520000000000000), (-1927558817628006250840779/10485760000000000000), (2877018097116172834790361/20971520000000000000), (-511525534633041298988871/5242880000000000000), (521725615312896324070587/2621440000000000000), (-1369918693771740518109957/131072000000000000)]]
def Z : Matrix (Fin 6) (Fin 6) ℚ := ![![7257600, 0, 0, 0, -453600, 9979200], ![0, 241920, 0, -60480, 0, 2494800], ![0, 0, 54000, -75600, 113400, 0], ![0, -60480, -75600, 120960, -158760, -623700], ![-453600, 0, 113400, -158760, 266490, -623700], ![9979200, 2494800, 0, -623700, -623700, 39449025]]
def W : Matrix (Fin 6) (Fin 6) ℚ := ![![(5964695117267475742980919/1503238553600000000000000), (1744624323817160701107537/1503238553600000000000000), (-161316238397235909250131/134217728000000000000000), (414064887714404869068081/751619276800000000000000), (-64800521002176063679207/187904819200000000000000), (15384382826163865762517/134217728000000000000000)], ![(512866081553008807390337/11274289152000000000000000), (-194897946662990208889687/3758096384000000000000000), (1871635346680482439661/50331648000000000000000), (-303975974406062929067597/5637144576000000000000000), (-19233547957227911298713/1409286144000000000000000), (9276944501934800833223/469762048000000000000000)], ![(-453817708231818879037087/36077725286400000000000000), (2031865538239284389204363/36077725286400000000000000), (-18408098023015419984551/375809638400000000000000), (-24170116272712712981741/721554505728000000000000), (98529294091720413115079/4509715660800000000000000), (-20089466216411214407027/4509715660800000000000000)], ![(1125259631410696923698261/180388626432000000000000000), (-11884283407719108217754297/180388626432000000000000000), (47737752682324330195009/805306368000000000000000), (5445674245348976488075063/90194313216000000000000000), (-204256955604377082203567/7516192768000000000000000), (29302929491660890850513/22548578304000000000000000)], ![(-8250049885990027717041051/30064771072000000000000000), (687492143573648402361607/15032385536000000000000000), (-59580937878949130564481/2147483648000000000000000), (-157502369657418727928627/1503238553600000000000000), (253426915913230802550397/3758096384000000000000000), (-4434231130321885021193/268435456000000000000000)], ![(8906646648378166256760477/1503238553600000000000000), (3189808830527522704705809/3006477107200000000000000), (-1362718846099888865026021/1073741824000000000000000), (302744511597940335001331/1503238553600000000000000), (-1444335560239755819933/2348810240000000000000), (678823330108464950298901/1879048192000000000000000)]]
def M : Matrix (Fin 6) (Fin 6) ℚ := ![![(5049552047366104719126260283/167772160000000000000), (8949117860231088857789367/16777216000000000000), (-39099590117542931979883869/268435456000000000000), (94714773618178746703399743/1342177280000000000000), (-1467660859958626572675955383/671088640000000000000), (7866011844464725027258136361/167772160000000000000)], ![(8949117860231088857789367/16777216000000000000), (1677004120298631639678687/41943040000000000000), (3044749629574206508033791/671088640000000000000), (-54853329812992078349810277/3355443200000000000000), (-39947051071179721194006141/1677721600000000000000), (38445358108099205386269927/33554432000000000000)], ![(-39099590117542931979883869/268435456000000000000), (3044749629574206508033791/671088640000000000000), (35550514566479531937111777/15032385536000000000000), (-47729513084776357969246941/10737418240000000000000), (75537373571788313927688669/5368709120000000000000), (-10300586047406982406675233/67108864000000000000)], ![(94714773618178746703399743/1342177280000000000000), (-54853329812992078349810277/3355443200000000000000), (-47729513084776357969246941/10737418240000000000000), (110703982169080563836793939/10737418240000000000000), (-368973410717799312717796119/26843545600000000000000), (-48018585876798273237896373/671088640000000000000)], ![(-1467660859958626572675955383/671088640000000000000), (-39947051071179721194006141/1677721600000000000000), (75537373571788313927688669/5368709120000000000000), (-368973410717799312717796119/26843545600000000000000), (2231147286200171863965309741/13421772800000000000000), (-8731261072446911549418855933/2684354560000000000000)], ![(7866011844464725027258136361/167772160000000000000), (38445358108099205386269927/33554432000000000000), (-10300586047406982406675233/67108864000000000000), (-48018585876798273237896373/671088640000000000000), (-8731261072446911549418855933/2684354560000000000000), (204769681017405795043351689717/2684354560000000000000)]]
def L : Matrix (Fin 6) (Fin 6) ℚ := ![![1, 0, 0, 0, 0, 0], ![(1104829365460628254048070/62340148732914873075632843), 1, 0, 0, 0, 0], ![(-2413554945527341480239745/498721189863318984605062744), (4136195598756701681574722903125928982590421004929/17739236837277564358431182008444017483217516030648), 1, 0, 0, 0], ![(1169318192817021564239503/498721189863318984605062744), (-51127415237893867219062037832436524732154842072813/88696184186387821792155910042220087416087580153240), (-7/5), 1, 0, 0], ![(-18119269876032426823159943/249360594931659492302531372), (86860107573890735313069180965644508634398841103509/177392368372775643584311820084440174832175160306480), (21/10), 0, 1, 0], ![(97111257339070679348865881/62340148732914873075632843), (165/16), 0, 0, 0, 1]]
def diag : Fin 6 → ℚ := ![(5049552047366104719126260283/167772160000000000000), (19956641441937259903235079759499519668619705534479/653683837977649459501547839815680000000000000), (2458274422641393096494813566379712462387217062728478526502330063469129/10416525283295689221835547659184268682830082450037544058880000000000000), 0, 0, 0]

def keyIndexTable : Fin 12 → Fin 13 → Fin 13 → Fin 9 := ![![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 0, 0, 1, 2, 3, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 0, 0, 4, 5, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 1, 4, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 7, 8, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 2, 5, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 3, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![2, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![4, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 3, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![3, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![5, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 2, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![3, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![5, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![6, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]]
def keyIndex (n : Fin 12) (j : Fin ((n.val+1)/2)) (x : Fin ((11-n.val+2)/2)) : Fin 9 :=
  keyIndexTable n ⟨j.val,by have := j.isLt; have := n.isLt; omega⟩ ⟨x.val,by have := x.isLt; omega⟩
def representatives : Fin 9 → FourTerm 11 := ![⟨⟨11,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨11,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨11,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨11,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨10,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨10,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨9,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨9,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨9,by decide⟩,(⟨4,by decide⟩,⟨1,by decide⟩)⟩]
lemma cover_0 : ∀ j : Fin 0, ∀ x : Fin 6,
  (fourTermLabels (by omega : 11 ≤ 23) ⟨0,j,x⟩).Nodup →
    (fourTermLabels (by omega : 11 ≤ 23) ⟨0,j,x⟩).toFinset=keys (keyIndex 0 j x) := by decide +kernel
lemma cover_1 : ∀ j : Fin 1, ∀ x : Fin 6,
  (fourTermLabels (by omega : 11 ≤ 23) ⟨1,j,x⟩).Nodup →
    (fourTermLabels (by omega : 11 ≤ 23) ⟨1,j,x⟩).toFinset=keys (keyIndex 1 j x) := by decide +kernel
lemma cover_2 : ∀ j : Fin 1, ∀ x : Fin 5,
  (fourTermLabels (by omega : 11 ≤ 23) ⟨2,j,x⟩).Nodup →
    (fourTermLabels (by omega : 11 ≤ 23) ⟨2,j,x⟩).toFinset=keys (keyIndex 2 j x) := by decide +kernel
lemma cover_3 : ∀ j : Fin 2, ∀ x : Fin 5,
  (fourTermLabels (by omega : 11 ≤ 23) ⟨3,j,x⟩).Nodup →
    (fourTermLabels (by omega : 11 ≤ 23) ⟨3,j,x⟩).toFinset=keys (keyIndex 3 j x) := by decide +kernel
lemma cover_4 : ∀ j : Fin 2, ∀ x : Fin 4,
  (fourTermLabels (by omega : 11 ≤ 23) ⟨4,j,x⟩).Nodup →
    (fourTermLabels (by omega : 11 ≤ 23) ⟨4,j,x⟩).toFinset=keys (keyIndex 4 j x) := by decide +kernel
lemma cover_5 : ∀ j : Fin 3, ∀ x : Fin 4,
  (fourTermLabels (by omega : 11 ≤ 23) ⟨5,j,x⟩).Nodup →
    (fourTermLabels (by omega : 11 ≤ 23) ⟨5,j,x⟩).toFinset=keys (keyIndex 5 j x) := by decide +kernel
lemma cover_6 : ∀ j : Fin 3, ∀ x : Fin 3,
  (fourTermLabels (by omega : 11 ≤ 23) ⟨6,j,x⟩).Nodup →
    (fourTermLabels (by omega : 11 ≤ 23) ⟨6,j,x⟩).toFinset=keys (keyIndex 6 j x) := by decide +kernel
lemma cover_7 : ∀ j : Fin 4, ∀ x : Fin 3,
  (fourTermLabels (by omega : 11 ≤ 23) ⟨7,j,x⟩).Nodup →
    (fourTermLabels (by omega : 11 ≤ 23) ⟨7,j,x⟩).toFinset=keys (keyIndex 7 j x) := by decide +kernel
lemma cover_8 : ∀ j : Fin 4, ∀ x : Fin 2,
  (fourTermLabels (by omega : 11 ≤ 23) ⟨8,j,x⟩).Nodup →
    (fourTermLabels (by omega : 11 ≤ 23) ⟨8,j,x⟩).toFinset=keys (keyIndex 8 j x) := by decide +kernel
lemma cover_9 : ∀ j : Fin 5, ∀ x : Fin 2,
  (fourTermLabels (by omega : 11 ≤ 23) ⟨9,j,x⟩).Nodup →
    (fourTermLabels (by omega : 11 ≤ 23) ⟨9,j,x⟩).toFinset=keys (keyIndex 9 j x) := by decide +kernel
lemma cover_10 : ∀ j : Fin 5, ∀ x : Fin 1,
  (fourTermLabels (by omega : 11 ≤ 23) ⟨10,j,x⟩).Nodup →
    (fourTermLabels (by omega : 11 ≤ 23) ⟨10,j,x⟩).toFinset=keys (keyIndex 10 j x) := by decide +kernel
lemma cover_11 : ∀ j : Fin 6, ∀ x : Fin 1,
  (fourTermLabels (by omega : 11 ≤ 23) ⟨11,j,x⟩).Nodup →
    (fourTermLabels (by omega : 11 ≤ 23) ⟨11,j,x⟩).toFinset=keys (keyIndex 11 j x) := by decide +kernel
lemma cover : ∀ b : FourTerm 11, (fourTermLabels (by omega : 11 ≤ 23) b).Nodup →
    (fourTermLabels (by omega : 11 ≤ 23) b).toFinset=keys (keyIndex b.1 b.2.1 b.2.2) := by
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
lemma representatives_checked : ∀ a : Fin 9,
  (fourTermLabels (by omega : 11 ≤ 23) (representatives a)).Nodup ∧
  (fourTermLabels (by omega : 11 ≤ 23) (representatives a)).toFinset=keys a := by decide +kernel
lemma keys_checked : fourKeys (by omega : 11 ≤ 23) = Finset.univ.image keys :=
  fourKeys_of_index (by omega : 11 ≤ 23) keys (fun b => keyIndex b.1 b.2.1 b.2.2)
    representatives cover representatives_checked
lemma keys_injective : Function.Injective keys := by decide +kernel
lemma keys_card : ∀ a : Fin 9, (keys a).card=4 := by decide +kernel
lemma fibers_cover : ∀ b : FourTerm 11,
    (fourTermLabels (by omega : 11 ≤ 23) b).Nodup →
      b ∈ fibers (keyIndex b.1 b.2.1 b.2.2) := by
  apply checkFourTerms_sound
  decide +kernel
lemma fibers_sound : ∀ a : Fin 9, ∀ b ∈ fibers a,
    (fourTermLabels (by omega : 11 ≤ 23) b).toFinset=keys a := by
  apply checkFourFibersSound_sound
  decide +kernel
lemma fibers_checked : ∀ a : Fin 9, ∀ b : FourTerm 11,
    (fourTermLabels (by omega : 11 ≤ 23) b).toFinset=keys a ↔ b ∈ fibers a :=
  fourFibers_of_index (by omega : 11 ≤ 23) keys
    (fun b => keyIndex b.1 b.2.1 b.2.2) fibers keys_injective keys_card cover fibers_cover fibers_sound
lemma columns_checked_0 : ∀ v : Fin 9, (∑ b ∈ fibers v, fourTermEval 11 (2*(0 : Fin 6).val+1) b * Occupation.wordSign (fourTermLabels (by omega : 11 ≤ 23) b)) = columns 0 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma columns_checked_1 : ∀ v : Fin 9, (∑ b ∈ fibers v, fourTermEval 11 (2*(1 : Fin 6).val+1) b * Occupation.wordSign (fourTermLabels (by omega : 11 ≤ 23) b)) = columns 1 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma columns_checked_2 : ∀ v : Fin 9, (∑ b ∈ fibers v, fourTermEval 11 (2*(2 : Fin 6).val+1) b * Occupation.wordSign (fourTermLabels (by omega : 11 ≤ 23) b)) = columns 2 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma columns_checked_3 : ∀ v : Fin 9, (∑ b ∈ fibers v, fourTermEval 11 (2*(3 : Fin 6).val+1) b * Occupation.wordSign (fourTermLabels (by omega : 11 ≤ 23) b)) = columns 3 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma columns_checked_4 : ∀ v : Fin 9, (∑ b ∈ fibers v, fourTermEval 11 (2*(4 : Fin 6).val+1) b * Occupation.wordSign (fourTermLabels (by omega : 11 ≤ 23) b)) = columns 4 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma columns_checked_5 : ∀ v : Fin 9, (∑ b ∈ fibers v, fourTermEval 11 (2*(5 : Fin 6).val+1) b * Occupation.wordSign (fourTermLabels (by omega : 11 ≤ 23) b)) = columns 5 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma columns_checked : ∀ u : Fin 6, ∀ v : Fin 9, (∑ b ∈ fibers v, fourTermEval 11 (2*u.val+1) b * Occupation.wordSign (fourTermLabels (by omega : 11 ≤ 23) b)) = columns u v := by
  intro u
  fin_cases u
  · exact columns_checked_0
  · exact columns_checked_1
  · exact columns_checked_2
  · exact columns_checked_3
  · exact columns_checked_4
  · exact columns_checked_5
lemma gram_checked_0 : ∀ v : Fin 6, (∑ a : Fin 9, columns (0 : Fin 6) a * columns v a / setFactorial (keys a)) = Z 0 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma gram_checked_1 : ∀ v : Fin 6, (∑ a : Fin 9, columns (1 : Fin 6) a * columns v a / setFactorial (keys a)) = Z 1 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma gram_checked_2 : ∀ v : Fin 6, (∑ a : Fin 9, columns (2 : Fin 6) a * columns v a / setFactorial (keys a)) = Z 2 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma gram_checked_3 : ∀ v : Fin 6, (∑ a : Fin 9, columns (3 : Fin 6) a * columns v a / setFactorial (keys a)) = Z 3 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma gram_checked_4 : ∀ v : Fin 6, (∑ a : Fin 9, columns (4 : Fin 6) a * columns v a / setFactorial (keys a)) = Z 4 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma gram_checked_5 : ∀ v : Fin 6, (∑ a : Fin 9, columns (5 : Fin 6) a * columns v a / setFactorial (keys a)) = Z 5 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma gram_checked : ∀ u : Fin 6, ∀ v : Fin 6, (∑ a : Fin 9, columns u a * columns v a / setFactorial (keys a)) = Z u v := by
  intro u
  fin_cases u
  · exact gram_checked_0
  · exact gram_checked_1
  · exact gram_checked_2
  · exact gram_checked_3
  · exact gram_checked_4
  · exact gram_checked_5
lemma rows_table_checked_0 : ∀ v : Fin 6, integerTableEval 11 SumTable11.sums (0 : Fin 6) v = Y 0 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma rows_table_checked_1 : ∀ v : Fin 6, integerTableEval 11 SumTable11.sums (1 : Fin 6) v = Y 1 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma rows_table_checked_2 : ∀ v : Fin 6, integerTableEval 11 SumTable11.sums (2 : Fin 6) v = Y 2 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma rows_table_checked_3 : ∀ v : Fin 6, integerTableEval 11 SumTable11.sums (3 : Fin 6) v = Y 3 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma rows_table_checked_4 : ∀ v : Fin 6, integerTableEval 11 SumTable11.sums (4 : Fin 6) v = Y 4 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma rows_table_checked_5 : ∀ v : Fin 6, integerTableEval 11 SumTable11.sums (5 : Fin 6) v = Y 5 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma rows_table_checked : ∀ u : Fin 6, ∀ v : Fin 6, integerTableEval 11 SumTable11.sums u v = Y u v := by
  intro u
  fin_cases u
  · exact rows_table_checked_0
  · exact rows_table_checked_1
  · exact rows_table_checked_2
  · exact rows_table_checked_3
  · exact rows_table_checked_4
  · exact rows_table_checked_5
lemma rows_checked (u v : Fin 6) : exactFourEval 11 (2*u.val+1) (2*v.val+1) = Y u v := by
  rw [exactFourEval_table 11 SumTable11.sums SumTable11.sums_checked]
  exact rows_table_checked u v
lemma product_checked_0 : ∀ v : Fin 6, (Z * tableComparison 11 (1/200000) Y) (0 : Fin 6) v = W 0 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma product_checked_1 : ∀ v : Fin 6, (Z * tableComparison 11 (1/200000) Y) (1 : Fin 6) v = W 1 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma product_checked_2 : ∀ v : Fin 6, (Z * tableComparison 11 (1/200000) Y) (2 : Fin 6) v = W 2 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma product_checked_3 : ∀ v : Fin 6, (Z * tableComparison 11 (1/200000) Y) (3 : Fin 6) v = W 3 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma product_checked_4 : ∀ v : Fin 6, (Z * tableComparison 11 (1/200000) Y) (4 : Fin 6) v = W 4 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma product_checked_5 : ∀ v : Fin 6, (Z * tableComparison 11 (1/200000) Y) (5 : Fin 6) v = W 5 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma product_checked : ∀ u : Fin 6, ∀ v : Fin 6, (Z * tableComparison 11 (1/200000) Y) u v = W u v := by
  intro u
  fin_cases u
  · exact product_checked_0
  · exact product_checked_1
  · exact product_checked_2
  · exact product_checked_3
  · exact product_checked_4
  · exact product_checked_5
lemma compression_checked_0 : ∀ v : Fin 6, (W * Z) (0 : Fin 6) v = M 0 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma compression_checked_1 : ∀ v : Fin 6, (W * Z) (1 : Fin 6) v = M 1 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma compression_checked_2 : ∀ v : Fin 6, (W * Z) (2 : Fin 6) v = M 2 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma compression_checked_3 : ∀ v : Fin 6, (W * Z) (3 : Fin 6) v = M 3 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma compression_checked_4 : ∀ v : Fin 6, (W * Z) (4 : Fin 6) v = M 4 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma compression_checked_5 : ∀ v : Fin 6, (W * Z) (5 : Fin 6) v = M 5 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma compression_checked : ∀ u : Fin 6, ∀ v : Fin 6, (W * Z) u v = M u v := by
  intro u
  fin_cases u
  · exact compression_checked_0
  · exact compression_checked_1
  · exact compression_checked_2
  · exact compression_checked_3
  · exact compression_checked_4
  · exact compression_checked_5
lemma ldl_checked_0 : ∀ v : Fin 6, (∑ k : Fin 6, L (0 : Fin 6) k * diag k * L v k) = M 0 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma ldl_checked_1 : ∀ v : Fin 6, (∑ k : Fin 6, L (1 : Fin 6) k * diag k * L v k) = M 1 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma ldl_checked_2 : ∀ v : Fin 6, (∑ k : Fin 6, L (2 : Fin 6) k * diag k * L v k) = M 2 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma ldl_checked_3 : ∀ v : Fin 6, (∑ k : Fin 6, L (3 : Fin 6) k * diag k * L v k) = M 3 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma ldl_checked_4 : ∀ v : Fin 6, (∑ k : Fin 6, L (4 : Fin 6) k * diag k * L v k) = M 4 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma ldl_checked_5 : ∀ v : Fin 6, (∑ k : Fin 6, L (5 : Fin 6) k * diag k * L v k) = M 5 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma ldl_checked : ∀ u : Fin 6, ∀ v : Fin 6, (∑ k : Fin 6, L u k * diag k * L v k) = M u v := by
  intro u
  fin_cases u
  · exact ldl_checked_0
  · exact ldl_checked_1
  · exact ldl_checked_2
  · exact ldl_checked_3
  · exact ldl_checked_4
  · exact ldl_checked_5
lemma diag_checked : ∀ u : Fin 6, 0 ≤ diag u := by decide +kernel
lemma certificate : FourCertificate (fun a : Fin 8 => (exactRows a).toReal) (1/200000) 11 (by omega) := by
  have hh := fourCertificate_of_tables exactRows (1/200000) (by omega : 11 ≤ 23) Y Z
  suffices FourCertificate (fun a : Fin 8 => (exactRows a).toReal) ((1/200000:ℚ):ℝ) 11 (by omega) by simpa using this
  apply hh
  · intro u v
    rw [exactFourEval_eq (by omega)]
    exact rows_checked u v
  · intro u v
    rw [rationalCreatedGram_of_columns (by omega : 11 ≤ 23) keys columns keys_checked keys_injective]
    · exact gram_checked u v
    · intro i a
      rw [fourColumn_eq_fiber (by omega : 11 ≤ 23) (2*i.val+1) (keys a) (fibers a) (fibers_checked a)]
      exact columns_checked i a
  · rw [Matrix.ext product_checked, Matrix.ext compression_checked]
    apply rational_ldl_positive M L diag diag_checked
    ext u v
    rw [Matrix.mul_apply]
    simpa only [Matrix.mul_diagonal,Matrix.transpose_apply] using (ldl_checked u v).symm
end Certificate11
end LaughlinGap.RealOccupation

end

end OAI
