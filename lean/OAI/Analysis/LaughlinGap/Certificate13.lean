import Mathlib
import OAI.Analysis.LaughlinGap.CachedIntegerRows
import OAI.Analysis.LaughlinGap.FastFourKeys
import OAI.Analysis.LaughlinGap.FourTables
import OAI.Analysis.LaughlinGap.SumTable13

namespace OAI

/-! Certificate13. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators ComplexOrder
open Spin
namespace Certificate13

def keys : Fin 15 → Finset (Fin 25) := ![{0,1,2,11}, {0,1,3,10}, {0,1,4,9}, {0,1,5,8}, {0,1,6,7}, {0,2,3,9}, {0,2,4,8}, {0,2,5,7}, {0,3,4,7}, {0,3,5,6}, {1,2,3,8}, {1,2,4,7}, {1,2,5,6}, {1,3,4,6}, {2,3,4,5}]
def fibers : Fin 15 → Finset (FourTerm 13) := ![{⟨⟨13,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨12,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨2,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩}, {⟨⟨13,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩}, {⟨⟨13,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨4,by decide⟩)⟩}, {⟨⟨13,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨5,by decide⟩)⟩}, {⟨⟨13,by decide⟩,(⟨6,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨1,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨0,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨1,by decide⟩,(⟨0,by decide⟩,⟨6,by decide⟩)⟩}, {⟨⟨12,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨11,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨2,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩}, {⟨⟨12,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨2,by decide⟩,(⟨0,by decide⟩,⟨4,by decide⟩)⟩}, {⟨⟨12,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨0,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨2,by decide⟩,(⟨0,by decide⟩,⟨5,by decide⟩)⟩}, {⟨⟨11,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨0,by decide⟩,⟨4,by decide⟩)⟩}, {⟨⟨11,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨0,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨0,by decide⟩,⟨5,by decide⟩)⟩}, {⟨⟨11,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨10,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨1,by decide⟩,⟨3,by decide⟩)⟩}, {⟨⟨11,by decide⟩,(⟨4,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨1,by decide⟩,⟨4,by decide⟩)⟩}, {⟨⟨11,by decide⟩,(⟨5,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨2,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨1,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨3,by decide⟩,(⟨1,by decide⟩,⟨5,by decide⟩)⟩}, {⟨⟨10,by decide⟩,(⟨4,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨9,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨1,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨1,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨4,by decide⟩,(⟨1,by decide⟩,⟨4,by decide⟩)⟩}, {⟨⟨9,by decide⟩,(⟨4,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨8,by decide⟩,(⟨3,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨3,by decide⟩,⟨2,by decide⟩)⟩,⟨⟨7,by decide⟩,(⟨2,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨6,by decide⟩,(⟨2,by decide⟩,⟨3,by decide⟩)⟩,⟨⟨5,by decide⟩,(⟨2,by decide⟩,⟨4,by decide⟩)⟩}]
def columns : Matrix (Fin 7) (Fin 15) ℚ := ![![9355500, -9355500, 14968800, -14968800, 16839900, -5613300, 0, -1871100, 7484400, -5613300, 5613300, -5613300, 7484400, -1871100, 1871100], ![4677750, -4677750, 4762800, -4762800, 4337550, -85050, 0, 425250, -340200, -85050, 85050, -85050, -340200, 425250, -425250], ![3274425, -3274425, 1701000, -491400, 42525, 1573425, -1209600, 448875, 396900, -240975, -363825, 363825, -207900, -155925, 155925], ![-467775, 467775, -340200, 340200, -411075, -127575, 0, 70875, 56700, -127575, 127575, -127575, 56700, 70875, -70875], ![-3742200, 3742200, -1973160, 340200, 510300, -1769040, 1632960, -850500, -646380, 680400, 136080, -136080, 170100, -34020, 34020], ![9355500, -9355500, 3742200, 1247400, -3742200, 5613300, -4989600, 2494800, 1871100, -1871100, -623700, 623700, -623700, 0, 0], ![97297200, -97297200, 97297200, -97297200, 97297200, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
def Y : Matrix (Fin 7) (Fin 7) ℚ := ![![(-251839151268331040358014961/41943040000000000000), (-46874153992556821049553357/41943040000000000000), (-25859766171309160725669177/8388608000000000000), (50582089306178241712160139/20971520000000000000), (-13552253472962587859513433/5242880000000000000), (19383207361412165471625381/1310720000000000000), (-610255650447424138062274083/2621440000000000000)], ![(-46874153992556821049553357/41943040000000000000), (44870346217788652708105509/83886080000000000000), (13655425844208758783924331/41943040000000000000), (-3161342093808007008219357/20971520000000000000), (-744703562398457224684467/5242880000000000000), (-3596861348652718123622667/5242880000000000000), (21361606258273238908704897/2621440000000000000)], ![(-25859766171309160725669177/8388608000000000000), (13655425844208758783924331/41943040000000000000), (-10382017631950642371404427/41943040000000000000), (195751427625490755693087/10485760000000000000), (1996722594805280378163651/5242880000000000000), (-2146289399351278589700567/2621440000000000000), (16056239782467396663247239/2621440000000000000)], ![(50582089306178241712160139/20971520000000000000), (-3161342093808007008219357/20971520000000000000), (195751427625490755693087/10485760000000000000), (-196134629690386723946157/20971520000000000000), (-139848552795666216461211/524288000000000000), (1701017595534794460591789/2621440000000000000), (-92309060511862267120047/65536000000000000)], ![(-13552253472962587859513433/5242880000000000000), (-744703562398457224684467/5242880000000000000), (1996722594805280378163651/5242880000000000000), (-139848552795666216461211/524288000000000000), (-471610220949050484117933/655360000000000000), (155671217561575490113647/163840000000000000), (-36284315401494109563471/65536000000000000)], ![(19383207361412165471625381/1310720000000000000), (-3596861348652718123622667/5242880000000000000), (-2146289399351278589700567/2621440000000000000), (1701017595534794460591789/2621440000000000000), (155671217561575490113647/163840000000000000), (-808423367051529180056853/81920000000000000), (3299431615695312593637141/163840000000000000)], ![(-610255650447424138062274083/2621440000000000000), (21361606258273238908704897/2621440000000000000), (16056239782467396663247239/2621440000000000000), (-92309060511862267120047/65536000000000000), (-36284315401494109563471/65536000000000000), (3299431615695312593637141/163840000000000000), (-29496262650250696000860159/32768000000000000)]]
def Z : Matrix (Fin 7) (Fin 7) ℚ := ![![958003200, 0, 0, 0, 0, -29937600, 972972000], ![0, 21772800, 0, 0, -2721600, 0, 291891600], ![0, 0, 4838400, -907200, -4082400, 12474000, 48648600], ![0, 0, -907200, 453600, 0, 0, -24324300], ![0, -2721600, -4082400, 0, 5851440, -16839900, -36486450], ![-29937600, 0, 12474000, 0, -16839900, 52390800, -30405375], ![972972000, 291891600, 48648600, -24324300, -36486450, -30405375, (12411474075/2)]]
def W : Matrix (Fin 7) (Fin 7) ℚ := ![![(8831729987737786013738573/2147483648000000000000000), (34748628211019859443241/1073741824000000000000000), (2175442601701750730797569/2147483648000000000000000), (-1128958923458752922056081/939524096000000000000000), (48438050204416062501949/75161927680000000000000), (-8573098207642290777219/18790481920000000000000), (92608358609211905476251/939524096000000000000000)], ![(704355043989103561462739/30064771072000000000000000), (-94799695758939067836079/2147483648000000000000000), (-3067525806525348938659353/30064771072000000000000000), (69083236828150945907529/1879048192000000000000000), (-4910735017771293411479/751619276800000000000000), (458868912964094577561/939524096000000000000000), (10221836670894438945003/1879048192000000000000000)], ![(248813601151941368981393/60129542144000000000000000), (-76203924028572529522213/4294967296000000000000000), (6348203556056114499720509/60129542144000000000000000), (-734561681117907727253339/11274289152000000000000000), (-481053601353272974503703/4509715660800000000000000), (66163226149991696581643/1879048192000000000000000), (-1720323125791409334903/3758096384000000000000000)], ![(-224556771463107840590339/60129542144000000000000000), (462797852877355205514539/90194313216000000000000000), (-308497566527027712898347/60129542144000000000000000), (-1290010974934108149769/5637144576000000000000000), (53121711501985771085789/4509715660800000000000000), (-3670859581048323286559/1879048192000000000000000), (-3968443850398932428773/11274289152000000000000000)], ![(1886323207959888622067/1202590842880000000000000), (234754241029267043867483/15032385536000000000000000), (-871281239927680314391539/7516192768000000000000000), (631207934101804270913409/7516192768000000000000000), (84946132005814233951163/751619276800000000000000), (-79523751661899341155899/1879048192000000000000000), (834644129363458012941/939524096000000000000000)], ![(-611000071363531735703093/4294967296000000000000000), (-479049630298473675900877/15032385536000000000000000), (2717215308549307723810983/7516192768000000000000000), (-1751995012933833209080121/7516192768000000000000000), (-54563777660804950852039/150323855360000000000000), (10777185928957969598559/75161927680000000000000), (-7396399577159528967533/939524096000000000000000)], ![(35259962251620035869883411/7516192768000000000000000), (-783658293849616354379353/939524096000000000000000), (-120022021767360028330443/1879048192000000000000000), (-1343991723371246071176483/1879048192000000000000000), (-2433044524619679829573/37580963840000000000000), (-165388004737776008739681/469762048000000000000000), (1287911404311002548883/6710886400000000000000)]]
def M : Matrix (Fin 7) (Fin 7) ℚ := ![![(679383827619707163253971626307/167772160000000000000), (9302050916298637474435869411/335544320000000000000), (330800053606043496481081053/134217728000000000000), (-518308919087766906124880811/134217728000000000000), (304844664596175032853703311/83886080000000000000), (-12435058782401141646184436253/83886080000000000000), (6149178943024853651772080367/1310720000000000000)], ![(9302050916298637474435869411/335544320000000000000), (86502352716019080426588039/134217728000000000000), (-308176606888633430456770863/1342177280000000000000), (-30981537341857890960211431/1342177280000000000000), (2447253932672797413599853/8388608000000000000), (-168098909438954386585025487/83886080000000000000), (1595240264012864128510203639/41943040000000000000)], ![(330800053606043496481081053/134217728000000000000), (-308176606888633430456770863/1342177280000000000000), (3818086724212768479176683371/2684354560000000000000), (-306545151431943830292769053/2684354560000000000000), (-265606313568676921717740837/167772160000000000000), (81336626278502226196173741/16777216000000000000), (465464830069039455237485331/83886080000000000000)], ![(-518308919087766906124880811/134217728000000000000), (-30981537341857890960211431/1342177280000000000000), (-306545151431943830292769053/2684354560000000000000), (35198751633344272173271779/2684354560000000000000), (81636177339639777191864319/671088640000000000000), (-32508298712591186910006483/134217728000000000000), (-827898465330432286082750601/167772160000000000000)], ![(304844664596175032853703311/83886080000000000000), (2447253932672797413599853/8388608000000000000), (-265606313568676921717740837/167772160000000000000), (81636177339639777191864319/671088640000000000000), (2378767750254200009443536657/1342177280000000000000), (-7570433753960369609446538013/1342177280000000000000), (361901366398657158054228819/335544320000000000000)], ![(-12435058782401141646184436253/83886080000000000000), (-168098909438954386585025487/83886080000000000000), (81336626278502226196173741/16777216000000000000), (-32508298712591186910006483/134217728000000000000), (-7570433753960369609446538013/1342177280000000000000), (30376681419317532547754017809/1342177280000000000000), (-55173586526011810923123519891/335544320000000000000)], ![(6149178943024853651772080367/1310720000000000000), (1595240264012864128510203639/41943040000000000000), (465464830069039455237485331/83886080000000000000), (-827898465330432286082750601/167772160000000000000), (361901366398657158054228819/335544320000000000000), (-55173586526011810923123519891/335544320000000000000), (92933407695426524496291761883/16777216000000000000)]]
def L : Matrix (Fin 7) (Fin 7) ℚ := ![![1, 0, 0, 0, 0, 0, 0], ![(3480004083912696398965907/508330585574042022636716518), 1, 0, 0, 0, 0, 0], ![(618780496831357082830305/1016661171148084045273433036), (-32439708799189059971384216868547739288924048209841/59844370252069954335025159500493333113384925260918), 1, 0, 0, 0, 0], ![(-35043130034465600186935/36746789318605447419521676), (882835082009016384226944621005887338723325380011/119688740504139908670050319000986666226769850521836), (-106549992448321565050494614978843827137059325811169374408783674627429082/1246542322781118734185307686555808314832555582764943797608745762542928169), 1, 0, 0, 0], ![(228091780468518543100414/254165292787021011318358259), (1734381888231324175347366547981226345362857291983/2955277543312096510371612814839176943870860506712), (-5580588624576168262055319665629851567015559428170067263472363431755578027/4986169291124474936741230746223233259330222331059775190434983050171712676), (-27/10), 1, 0, 0], ![(-489694558938355943299838/13377120673001105858860961), (-6428252053499638508494999902277043915781628724595/2955277543312096510371612814839176943870860506712), (34103597150187694934782509067737981798428418727705966610108887638506310165/9972338582248949873482461492446466518660444662119550380869966100343425352), (33/4), 0, 1, 0], ![(294461243811141514188861312/254165292787021011318358259), (259539191018482024500615363967589464260599164175879/19948123417356651445008386500164444371128308420306), (22854973380164975703331094912962000920899225386495830810684098207583538089/4986169291124474936741230746223233259330222331059775190434983050171712676), (-429/8), 0, 0, 1]]
def diag : Fin 7 → ℚ := ![(679383827619707163253971626307/167772160000000000000), (2423696995208833150568518959769979991092089473067179/5330232520988866879283176595783680000000000000), (1246542322781118734185307686555808314832555582764943797608745762542928169/968385345392507784518570087166501500967603570839388160000000000000), (2513845326467649635666674520447585664534112472365505536452626526778469811923314148719593/8169339766578339736356832454612145372086636267208335672008676229401334048358400000000000), 0, 0, 0]

def keyIndexTable : Fin 14 → Fin 13 → Fin 13 → Fin 15 := ![![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 0, 0, 1, 2, 3, 4, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 0, 0, 5, 6, 7, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 1, 5, 0, 8, 9, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 10, 11, 12, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 2, 6, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 10, 0, 13, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 3, 7, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![2, 0, 11, 13, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![5, 10, 0, 0, 14, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 4, 0, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![3, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![6, 11, 0, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 4, 7, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![4, 0, 12, 13, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![7, 12, 0, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![8, 13, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 3, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![4, 0, 11, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![9, 0, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 2, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![3, 0, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![7, 11, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![9, 13, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![6, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 13, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![8, 11, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![9, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]]
def keyIndex (n : Fin 14) (j : Fin ((n.val+1)/2)) (x : Fin ((13-n.val+2)/2)) : Fin 15 :=
  keyIndexTable n ⟨j.val,by have := j.isLt; have := n.isLt; omega⟩ ⟨x.val,by have := x.isLt; omega⟩
def representatives : Fin 15 → FourTerm 13 := ![⟨⟨13,by decide⟩,(⟨2,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨13,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨13,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨13,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨13,by decide⟩,(⟨6,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨12,by decide⟩,(⟨3,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨12,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨12,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨11,by decide⟩,(⟨4,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨11,by decide⟩,(⟨5,by decide⟩,⟨0,by decide⟩)⟩, ⟨⟨11,by decide⟩,(⟨3,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨11,by decide⟩,(⟨4,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨11,by decide⟩,(⟨5,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨10,by decide⟩,(⟨4,by decide⟩,⟨1,by decide⟩)⟩, ⟨⟨9,by decide⟩,(⟨4,by decide⟩,⟨2,by decide⟩)⟩]
lemma cover_0 : ∀ j : Fin 0, ∀ x : Fin 7,
  (fourTermLabels (by omega : 13 ≤ 23) ⟨0,j,x⟩).Nodup →
    (fourTermLabels (by omega : 13 ≤ 23) ⟨0,j,x⟩).toFinset=keys (keyIndex 0 j x) := by decide +kernel
lemma cover_1 : ∀ j : Fin 1, ∀ x : Fin 7,
  (fourTermLabels (by omega : 13 ≤ 23) ⟨1,j,x⟩).Nodup →
    (fourTermLabels (by omega : 13 ≤ 23) ⟨1,j,x⟩).toFinset=keys (keyIndex 1 j x) := by decide +kernel
lemma cover_2 : ∀ j : Fin 1, ∀ x : Fin 6,
  (fourTermLabels (by omega : 13 ≤ 23) ⟨2,j,x⟩).Nodup →
    (fourTermLabels (by omega : 13 ≤ 23) ⟨2,j,x⟩).toFinset=keys (keyIndex 2 j x) := by decide +kernel
lemma cover_3 : ∀ j : Fin 2, ∀ x : Fin 6,
  (fourTermLabels (by omega : 13 ≤ 23) ⟨3,j,x⟩).Nodup →
    (fourTermLabels (by omega : 13 ≤ 23) ⟨3,j,x⟩).toFinset=keys (keyIndex 3 j x) := by decide +kernel
lemma cover_4 : ∀ j : Fin 2, ∀ x : Fin 5,
  (fourTermLabels (by omega : 13 ≤ 23) ⟨4,j,x⟩).Nodup →
    (fourTermLabels (by omega : 13 ≤ 23) ⟨4,j,x⟩).toFinset=keys (keyIndex 4 j x) := by decide +kernel
lemma cover_5 : ∀ j : Fin 3, ∀ x : Fin 5,
  (fourTermLabels (by omega : 13 ≤ 23) ⟨5,j,x⟩).Nodup →
    (fourTermLabels (by omega : 13 ≤ 23) ⟨5,j,x⟩).toFinset=keys (keyIndex 5 j x) := by decide +kernel
lemma cover_6 : ∀ j : Fin 3, ∀ x : Fin 4,
  (fourTermLabels (by omega : 13 ≤ 23) ⟨6,j,x⟩).Nodup →
    (fourTermLabels (by omega : 13 ≤ 23) ⟨6,j,x⟩).toFinset=keys (keyIndex 6 j x) := by decide +kernel
lemma cover_7 : ∀ j : Fin 4, ∀ x : Fin 4,
  (fourTermLabels (by omega : 13 ≤ 23) ⟨7,j,x⟩).Nodup →
    (fourTermLabels (by omega : 13 ≤ 23) ⟨7,j,x⟩).toFinset=keys (keyIndex 7 j x) := by decide +kernel
lemma cover_8 : ∀ j : Fin 4, ∀ x : Fin 3,
  (fourTermLabels (by omega : 13 ≤ 23) ⟨8,j,x⟩).Nodup →
    (fourTermLabels (by omega : 13 ≤ 23) ⟨8,j,x⟩).toFinset=keys (keyIndex 8 j x) := by decide +kernel
lemma cover_9 : ∀ j : Fin 5, ∀ x : Fin 3,
  (fourTermLabels (by omega : 13 ≤ 23) ⟨9,j,x⟩).Nodup →
    (fourTermLabels (by omega : 13 ≤ 23) ⟨9,j,x⟩).toFinset=keys (keyIndex 9 j x) := by decide +kernel
lemma cover_10 : ∀ j : Fin 5, ∀ x : Fin 2,
  (fourTermLabels (by omega : 13 ≤ 23) ⟨10,j,x⟩).Nodup →
    (fourTermLabels (by omega : 13 ≤ 23) ⟨10,j,x⟩).toFinset=keys (keyIndex 10 j x) := by decide +kernel
lemma cover_11 : ∀ j : Fin 6, ∀ x : Fin 2,
  (fourTermLabels (by omega : 13 ≤ 23) ⟨11,j,x⟩).Nodup →
    (fourTermLabels (by omega : 13 ≤ 23) ⟨11,j,x⟩).toFinset=keys (keyIndex 11 j x) := by decide +kernel
lemma cover_12 : ∀ j : Fin 6, ∀ x : Fin 1,
  (fourTermLabels (by omega : 13 ≤ 23) ⟨12,j,x⟩).Nodup →
    (fourTermLabels (by omega : 13 ≤ 23) ⟨12,j,x⟩).toFinset=keys (keyIndex 12 j x) := by decide +kernel
lemma cover_13 : ∀ j : Fin 7, ∀ x : Fin 1,
  (fourTermLabels (by omega : 13 ≤ 23) ⟨13,j,x⟩).Nodup →
    (fourTermLabels (by omega : 13 ≤ 23) ⟨13,j,x⟩).toFinset=keys (keyIndex 13 j x) := by decide +kernel
lemma cover : ∀ b : FourTerm 13, (fourTermLabels (by omega : 13 ≤ 23) b).Nodup →
    (fourTermLabels (by omega : 13 ≤ 23) b).toFinset=keys (keyIndex b.1 b.2.1 b.2.2) := by
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
lemma representatives_checked : ∀ a : Fin 15,
  (fourTermLabels (by omega : 13 ≤ 23) (representatives a)).Nodup ∧
  (fourTermLabels (by omega : 13 ≤ 23) (representatives a)).toFinset=keys a := by decide +kernel
lemma keys_checked : fourKeys (by omega : 13 ≤ 23) = Finset.univ.image keys :=
  fourKeys_of_index (by omega : 13 ≤ 23) keys (fun b => keyIndex b.1 b.2.1 b.2.2)
    representatives cover representatives_checked
lemma keys_injective : Function.Injective keys := by decide +kernel
lemma keys_card : ∀ a : Fin 15, (keys a).card=4 := by decide +kernel
lemma fibers_cover : ∀ b : FourTerm 13,
    (fourTermLabels (by omega : 13 ≤ 23) b).Nodup →
      b ∈ fibers (keyIndex b.1 b.2.1 b.2.2) := by
  apply checkFourTerms_sound
  decide +kernel
lemma fibers_sound : ∀ a : Fin 15, ∀ b ∈ fibers a,
    (fourTermLabels (by omega : 13 ≤ 23) b).toFinset=keys a := by
  apply checkFourFibersSound_sound
  decide +kernel
lemma fibers_checked : ∀ a : Fin 15, ∀ b : FourTerm 13,
    (fourTermLabels (by omega : 13 ≤ 23) b).toFinset=keys a ↔ b ∈ fibers a :=
  fourFibers_of_index (by omega : 13 ≤ 23) keys
    (fun b => keyIndex b.1 b.2.1 b.2.2) fibers keys_injective keys_card cover fibers_cover fibers_sound
lemma columns_checked_0 : ∀ v : Fin 15, (∑ b ∈ fibers v, fourTermEval 13 (2*(0 : Fin 7).val+1) b * Occupation.wordSign (fourTermLabels (by omega : 13 ≤ 23) b)) = columns 0 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma columns_checked_1 : ∀ v : Fin 15, (∑ b ∈ fibers v, fourTermEval 13 (2*(1 : Fin 7).val+1) b * Occupation.wordSign (fourTermLabels (by omega : 13 ≤ 23) b)) = columns 1 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma columns_checked_2 : ∀ v : Fin 15, (∑ b ∈ fibers v, fourTermEval 13 (2*(2 : Fin 7).val+1) b * Occupation.wordSign (fourTermLabels (by omega : 13 ≤ 23) b)) = columns 2 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma columns_checked_3 : ∀ v : Fin 15, (∑ b ∈ fibers v, fourTermEval 13 (2*(3 : Fin 7).val+1) b * Occupation.wordSign (fourTermLabels (by omega : 13 ≤ 23) b)) = columns 3 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma columns_checked_4 : ∀ v : Fin 15, (∑ b ∈ fibers v, fourTermEval 13 (2*(4 : Fin 7).val+1) b * Occupation.wordSign (fourTermLabels (by omega : 13 ≤ 23) b)) = columns 4 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma columns_checked_5 : ∀ v : Fin 15, (∑ b ∈ fibers v, fourTermEval 13 (2*(5 : Fin 7).val+1) b * Occupation.wordSign (fourTermLabels (by omega : 13 ≤ 23) b)) = columns 5 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma columns_checked_6 : ∀ v : Fin 15, (∑ b ∈ fibers v, fourTermEval 13 (2*(6 : Fin 7).val+1) b * Occupation.wordSign (fourTermLabels (by omega : 13 ≤ 23) b)) = columns 6 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma columns_checked : ∀ u : Fin 7, ∀ v : Fin 15, (∑ b ∈ fibers v, fourTermEval 13 (2*u.val+1) b * Occupation.wordSign (fourTermLabels (by omega : 13 ≤ 23) b)) = columns u v := by
  intro u
  fin_cases u
  · exact columns_checked_0
  · exact columns_checked_1
  · exact columns_checked_2
  · exact columns_checked_3
  · exact columns_checked_4
  · exact columns_checked_5
  · exact columns_checked_6
lemma gram_checked_0 : ∀ v : Fin 7, (∑ a : Fin 15, columns (0 : Fin 7) a * columns v a / setFactorial (keys a)) = Z 0 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma gram_checked_1 : ∀ v : Fin 7, (∑ a : Fin 15, columns (1 : Fin 7) a * columns v a / setFactorial (keys a)) = Z 1 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma gram_checked_2 : ∀ v : Fin 7, (∑ a : Fin 15, columns (2 : Fin 7) a * columns v a / setFactorial (keys a)) = Z 2 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma gram_checked_3 : ∀ v : Fin 7, (∑ a : Fin 15, columns (3 : Fin 7) a * columns v a / setFactorial (keys a)) = Z 3 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma gram_checked_4 : ∀ v : Fin 7, (∑ a : Fin 15, columns (4 : Fin 7) a * columns v a / setFactorial (keys a)) = Z 4 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma gram_checked_5 : ∀ v : Fin 7, (∑ a : Fin 15, columns (5 : Fin 7) a * columns v a / setFactorial (keys a)) = Z 5 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma gram_checked_6 : ∀ v : Fin 7, (∑ a : Fin 15, columns (6 : Fin 7) a * columns v a / setFactorial (keys a)) = Z 6 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma gram_checked : ∀ u : Fin 7, ∀ v : Fin 7, (∑ a : Fin 15, columns u a * columns v a / setFactorial (keys a)) = Z u v := by
  intro u
  fin_cases u
  · exact gram_checked_0
  · exact gram_checked_1
  · exact gram_checked_2
  · exact gram_checked_3
  · exact gram_checked_4
  · exact gram_checked_5
  · exact gram_checked_6
lemma rows_table_checked_0 : ∀ v : Fin 7, integerTableEval 13 SumTable13.sums (0 : Fin 7) v = Y 0 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma rows_table_checked_1 : ∀ v : Fin 7, integerTableEval 13 SumTable13.sums (1 : Fin 7) v = Y 1 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma rows_table_checked_2 : ∀ v : Fin 7, integerTableEval 13 SumTable13.sums (2 : Fin 7) v = Y 2 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma rows_table_checked_3 : ∀ v : Fin 7, integerTableEval 13 SumTable13.sums (3 : Fin 7) v = Y 3 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma rows_table_checked_4 : ∀ v : Fin 7, integerTableEval 13 SumTable13.sums (4 : Fin 7) v = Y 4 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma rows_table_checked_5 : ∀ v : Fin 7, integerTableEval 13 SumTable13.sums (5 : Fin 7) v = Y 5 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma rows_table_checked_6 : ∀ v : Fin 7, integerTableEval 13 SumTable13.sums (6 : Fin 7) v = Y 6 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma rows_table_checked : ∀ u : Fin 7, ∀ v : Fin 7, integerTableEval 13 SumTable13.sums u v = Y u v := by
  intro u
  fin_cases u
  · exact rows_table_checked_0
  · exact rows_table_checked_1
  · exact rows_table_checked_2
  · exact rows_table_checked_3
  · exact rows_table_checked_4
  · exact rows_table_checked_5
  · exact rows_table_checked_6
lemma rows_checked (u v : Fin 7) : exactFourEval 13 (2*u.val+1) (2*v.val+1) = Y u v := by
  rw [exactFourEval_table 13 SumTable13.sums SumTable13.sums_checked]
  exact rows_table_checked u v
lemma product_checked_0 : ∀ v : Fin 7, (Z * tableComparison 13 (1/200000) Y) (0 : Fin 7) v = W 0 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma product_checked_1 : ∀ v : Fin 7, (Z * tableComparison 13 (1/200000) Y) (1 : Fin 7) v = W 1 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma product_checked_2 : ∀ v : Fin 7, (Z * tableComparison 13 (1/200000) Y) (2 : Fin 7) v = W 2 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma product_checked_3 : ∀ v : Fin 7, (Z * tableComparison 13 (1/200000) Y) (3 : Fin 7) v = W 3 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma product_checked_4 : ∀ v : Fin 7, (Z * tableComparison 13 (1/200000) Y) (4 : Fin 7) v = W 4 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma product_checked_5 : ∀ v : Fin 7, (Z * tableComparison 13 (1/200000) Y) (5 : Fin 7) v = W 5 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma product_checked_6 : ∀ v : Fin 7, (Z * tableComparison 13 (1/200000) Y) (6 : Fin 7) v = W 6 v := by
  apply Arithmetic.checkVector_sound
  decide +kernel
lemma product_checked : ∀ u : Fin 7, ∀ v : Fin 7, (Z * tableComparison 13 (1/200000) Y) u v = W u v := by
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
lemma certificate : FourCertificate (fun a : Fin 8 => (exactRows a).toReal) (1/200000) 13 (by omega) := by
  have hh := fourCertificate_of_tables exactRows (1/200000) (by omega : 13 ≤ 23) Y Z
  suffices FourCertificate (fun a : Fin 8 => (exactRows a).toReal) ((1/200000:ℚ):ℝ) 13 (by omega) by simpa using this
  apply hh
  · intro u v
    rw [exactFourEval_eq (by omega)]
    exact rows_checked u v
  · intro u v
    rw [rationalCreatedGram_of_columns (by omega : 13 ≤ 23) keys columns keys_checked keys_injective]
    · exact gram_checked u v
    · intro i a
      rw [fourColumn_eq_fiber (by omega : 13 ≤ 23) (2*i.val+1) (keys a) (fibers a) (fibers_checked a)]
      exact columns_checked i a
  · rw [Matrix.ext product_checked, Matrix.ext compression_checked]
    apply rational_ldl_positive M L diag diag_checked
    ext u v
    rw [Matrix.mul_apply]
    simpa only [Matrix.mul_diagonal,Matrix.transpose_apply] using (ldl_checked u v).symm
end Certificate13
end LaughlinGap.RealOccupation

end

end OAI
