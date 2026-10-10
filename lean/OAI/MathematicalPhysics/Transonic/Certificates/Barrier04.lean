import OAI.MathematicalPhysics.Transonic.Certificates.BarrierData04

namespace OAI

section
noncomputable section
namespace SepticProfile.ExteriorCertificates.C04
open SepticProfile.ExteriorJet SepticProfile.FixedInterval
def cell0 : Box := ⟨250000000000000000000000000000000000000000000000000000000000,250000000000000000000000000000000000000000000000000000000002⟩
def resval0 : Box := ⟨105445031723244910522220464337992165626010623376651583616,472261443477029980164135621283348306617380830814548435⟩
def polyval0 : Box := ⟨3721324186786210821605031021679744627013852255900169607660,17386722310288166979678440618401490543604223386680790987⟩
theorem cell0_lo : Holds Q cell0 (0/1:ℝ) := by norm_num [Holds,Q,cell0]
theorem cell0_hi : Holds Q cell0 (1/2:ℝ) := by norm_num [Holds,Q,cell0]
def resval0Tail4 : Box := ⟨49531867078614120800383851268443109509087539947677,1813938813096424104604340794879294360507039392910⟩
def resval0Tail8 : Box := ⟨5480133397288859645819356828773015206191434440,349085259595009354084937059678378784666123463⟩
def resval0Tail12 : Box := ⟨4561162612621615893159907305923016126026948,435198757417200448675525002373714588606237⟩
def resval0Tail16 : Box := ⟨16720034265404393085459887483212832967662,24615148526156254260658754368310433351313⟩
def resval0Tail20 : Box := ⟨208596354893088159379816707489141324367,358055085306245665266467665080509569959201⟩
def resval0Tail24 : Box := ⟨7601925866101394786798550134495223062,5728270353318947705565689635291911313894938⟩
def resval0Tail28 : Box := ⟨736481816272692793491616363826669359,91652295469203090836867834281406996180570577⟩
def resval0Tail32 : Box := ⟨177233120129768900670318732263428690,1466436723524484444347410849515536707867938944⟩
def resval0Tail36 : Box := ⟨-419931284835400164292508627378744260,23462987574790255315262782289574026666141401908⟩
def resval0Tail40 : Box := ⟨-134627541068051758124696067751906816863,375407801069748665167497101322651443438933252086⟩
def resval0Tail44 : Box := ⟨-34503454288740997649101597319069094991868,6006524784767541929204832443600700622896067824137⟩
def resval0Tail48 : Box := ⟨-8833019317980547400632022220254407186680316,96104388275316503796920103945553705750447842270208⟩
def resval0Tail52 : Box := ⟨-2261254099153404572587712072106550544031050126,1537668092479193240350665564561333137426025502580955⟩
def resval0Tail56 : Box := ⟨-578881071788379388031114800412318650382448881423,24602146778653027772623265272127899061385744371586827⟩
def resval0Tail60 : Box := ⟨-148193553971322445882893043409724887576126470636470,393495416999326373031553080463221411685412598599023915⟩
def resval0Tail64 : Box := ⟨-37937545829383455217814595378956328981453105728438406,6260360219675860121533246325558484876965940345216818355⟩
def resval0Tail68 : Box := ⟨-9711920187931690921254055944501806542903002753566445420,91060786407250978665617512864032450864272317623390689954⟩
def resval0Tail72 : Box := ⟨723157684922663937511732828501339255346955068281752882586,2811987939899607447155091321595305634075764827416690078⟩
def resval0Tail76 : Box := ⟨-22604685193013117762851858298888788304876718152215,621098203346570514727125760859073886495447016081⟩
def resval0Tail80 : Box := ⟨-1117150378533507309814954215346064441709934093,60835051006253554300490551242846784632623933⟩
def resval0Tail84 : Box := ⟨-578036473204939448458380201249612529920122,48937282549552415665394000164698730005956⟩
def resval0Tail88 : Box := ⟨-1463727057719935948104106061539911621753,324385060320615817859971750075667984819⟩
def resval0Tail92 : Box := ⟨-13349067673823070032299177054486927260,2352154576428963625070906485317864655986⟩
def resval0Tail96 : Box := ⟨-368099424039641035162188553942665307,37598744620043727000525943982428486297970⟩
def resval0Tail100 : Box := ⟨-27571277964112190322421861879914319,601578574148186272186848567862530173137090⟩
def resval0Tail104 : Box := ⟨-5263095484553909716777413700342479,9625257049819454299942176809788039280504333⟩
def resval0Tail108 : Box := ⟨-4185434537628412545294104688732219,154004112760623187208557976873872463236738824⟩
def resval0Tail112 : Box := ⟨-443984029791853105229630298871755303,2464065803756106837934430419379429146876721253⟩
def resval0Tail116 : Box := ⟨-112950735491020745567334481895942718613,39425052754210707190652209132505831640394524661⟩
def resval0Tail120 : Box := ⟨-28913442072600101366563361541673942897062,630800816961044035636845839876807699700820755142⟩
def resval0Tail124 : Box := ⟨-7401828045414508651459519817527921458808937,10092806132163356647315984599564964785121544213249⟩
def resval0Tail128 : Box := ⟨-1894867768816068746700985965631346747812941215,161483121676106130091419374876383786172287542343108⟩
def resval0Tail132 : Box := ⟨-485086145734831876772125026332093926260413207487,2583275178561411371086295766323037473387193363097038⟩
def resval0Tail136 : Box := ⟨-124182062643012986531637974900160983955080146486087,41215982178642525950237988540068333056538644938321225⟩
def resval0Tail140 : Box := ⟨-31790720205651240362986531495057377753259287859170387,629651963773788059045521514191787080382300221029252362⟩
def resval0Tail144 : Box := ⟨-8223673852481725308049856273572356643722281675560915263,2399502111143598033676649708283172040806351459525162669⟩
def resval0Tail148 : Box := ⟨47176680949179944411898268646085192131782946,1089760826226478673935603940648890897253990⟩
def resval0Tail152 : Box := ⟨768801086244068242630898591888957902388,37181225717658572594185588926536516050⟩
def resval0Tail156 : Box := ⟨223370305827160465353155653027000544,17189255702589262533806500338161613⟩
def resval0Tail160 : Box := ⟨357933155754254955109064837054058,41124685147885644346947262525447⟩
def resval0Tail164 : Box := ⟨2187095205201080206842208339764,23432084438275585044846676161526⟩
def resval0Tail168 : Box := ⟨41705478829815633058416019160,369561408674115105596989621567120⟩
def resval0Tail172 : Box := ⟨2196469202275747795043570090,5912844344734827687948695927420394⟩
def resval0Tail176 : Box := ⟨296315479529860628803485146,94605499695181501972958924413845866⟩
def resval0Tail180 : Box := ⟨103449373100443884060300139,1513687993315978519221424478114890133⟩
def resval0Tail184 : Box := ⟨1473059867659496160509394018,24219007891241090711836429287253619873⟩
def resval0Tail188 : Box := ⟨357296507352319430539280021653,387504125924978681867268087160304206833⟩
def resval0Tail192 : Box := ⟨91430357195952338043364259625611,6200065929084010817029797742932737579932⟩
def resval0Tail196 : Box := ⟨23405999139052233653913459671362189,99201032922223478215317484790956089992945⟩
def resval0Tail200 : Box := ⟨5991933860081984279514750659983811962,1587210909317702979247713201442177264424496⟩
def resval0Tail204 : Box := ⟨1533935024881372218356172148049945315061,25393936485011225764328248153204210422995793⟩
def resval0Tail208 : Box := ⟨392687372876588109851935632405233599630784,405934839354406337400246871891040079198082782⟩
def resval0Tail212 : Box := ⟨100528005890058209405018333578978943236825103,6400712442156315202921776162166165478052743421⟩
def resval0Tail216 : Box := ⟨25737313450281089789589962777846832924980589752,78283556479644232713984203582087623100969333405⟩
theorem resval0H216 : resval0Tail216=hornerBox Q residualBox cell0 216 4 :=
  hornerChunk_step Q residualBox cell0 resval0Tail216 zero 216 4 0 (by decide +kernel) rfl
theorem resval0H212 : resval0Tail212=hornerBox Q residualBox cell0 212 8 :=
  hornerChunk_step Q residualBox cell0 resval0Tail212 resval0Tail216 212 4 4 (by decide +kernel) resval0H216
theorem resval0H208 : resval0Tail208=hornerBox Q residualBox cell0 208 12 :=
  hornerChunk_step Q residualBox cell0 resval0Tail208 resval0Tail212 208 4 8 (by decide +kernel) resval0H212
theorem resval0H204 : resval0Tail204=hornerBox Q residualBox cell0 204 16 :=
  hornerChunk_step Q residualBox cell0 resval0Tail204 resval0Tail208 204 4 12 (by decide +kernel) resval0H208
theorem resval0H200 : resval0Tail200=hornerBox Q residualBox cell0 200 20 :=
  hornerChunk_step Q residualBox cell0 resval0Tail200 resval0Tail204 200 4 16 (by decide +kernel) resval0H204
theorem resval0H196 : resval0Tail196=hornerBox Q residualBox cell0 196 24 :=
  hornerChunk_step Q residualBox cell0 resval0Tail196 resval0Tail200 196 4 20 (by decide +kernel) resval0H200
theorem resval0H192 : resval0Tail192=hornerBox Q residualBox cell0 192 28 :=
  hornerChunk_step Q residualBox cell0 resval0Tail192 resval0Tail196 192 4 24 (by decide +kernel) resval0H196
theorem resval0H188 : resval0Tail188=hornerBox Q residualBox cell0 188 32 :=
  hornerChunk_step Q residualBox cell0 resval0Tail188 resval0Tail192 188 4 28 (by decide +kernel) resval0H192
theorem resval0H184 : resval0Tail184=hornerBox Q residualBox cell0 184 36 :=
  hornerChunk_step Q residualBox cell0 resval0Tail184 resval0Tail188 184 4 32 (by decide +kernel) resval0H188
theorem resval0H180 : resval0Tail180=hornerBox Q residualBox cell0 180 40 :=
  hornerChunk_step Q residualBox cell0 resval0Tail180 resval0Tail184 180 4 36 (by decide +kernel) resval0H184
theorem resval0H176 : resval0Tail176=hornerBox Q residualBox cell0 176 44 :=
  hornerChunk_step Q residualBox cell0 resval0Tail176 resval0Tail180 176 4 40 (by decide +kernel) resval0H180
theorem resval0H172 : resval0Tail172=hornerBox Q residualBox cell0 172 48 :=
  hornerChunk_step Q residualBox cell0 resval0Tail172 resval0Tail176 172 4 44 (by decide +kernel) resval0H176
theorem resval0H168 : resval0Tail168=hornerBox Q residualBox cell0 168 52 :=
  hornerChunk_step Q residualBox cell0 resval0Tail168 resval0Tail172 168 4 48 (by decide +kernel) resval0H172
theorem resval0H164 : resval0Tail164=hornerBox Q residualBox cell0 164 56 :=
  hornerChunk_step Q residualBox cell0 resval0Tail164 resval0Tail168 164 4 52 (by decide +kernel) resval0H168
theorem resval0H160 : resval0Tail160=hornerBox Q residualBox cell0 160 60 :=
  hornerChunk_step Q residualBox cell0 resval0Tail160 resval0Tail164 160 4 56 (by decide +kernel) resval0H164
theorem resval0H156 : resval0Tail156=hornerBox Q residualBox cell0 156 64 :=
  hornerChunk_step Q residualBox cell0 resval0Tail156 resval0Tail160 156 4 60 (by decide +kernel) resval0H160
theorem resval0H152 : resval0Tail152=hornerBox Q residualBox cell0 152 68 :=
  hornerChunk_step Q residualBox cell0 resval0Tail152 resval0Tail156 152 4 64 (by decide +kernel) resval0H156
theorem resval0H148 : resval0Tail148=hornerBox Q residualBox cell0 148 72 :=
  hornerChunk_step Q residualBox cell0 resval0Tail148 resval0Tail152 148 4 68 (by decide +kernel) resval0H152
theorem resval0H144 : resval0Tail144=hornerBox Q residualBox cell0 144 76 :=
  hornerChunk_step Q residualBox cell0 resval0Tail144 resval0Tail148 144 4 72 (by decide +kernel) resval0H148
theorem resval0H140 : resval0Tail140=hornerBox Q residualBox cell0 140 80 :=
  hornerChunk_step Q residualBox cell0 resval0Tail140 resval0Tail144 140 4 76 (by decide +kernel) resval0H144
theorem resval0H136 : resval0Tail136=hornerBox Q residualBox cell0 136 84 :=
  hornerChunk_step Q residualBox cell0 resval0Tail136 resval0Tail140 136 4 80 (by decide +kernel) resval0H140
theorem resval0H132 : resval0Tail132=hornerBox Q residualBox cell0 132 88 :=
  hornerChunk_step Q residualBox cell0 resval0Tail132 resval0Tail136 132 4 84 (by decide +kernel) resval0H136
theorem resval0H128 : resval0Tail128=hornerBox Q residualBox cell0 128 92 :=
  hornerChunk_step Q residualBox cell0 resval0Tail128 resval0Tail132 128 4 88 (by decide +kernel) resval0H132
theorem resval0H124 : resval0Tail124=hornerBox Q residualBox cell0 124 96 :=
  hornerChunk_step Q residualBox cell0 resval0Tail124 resval0Tail128 124 4 92 (by decide +kernel) resval0H128
theorem resval0H120 : resval0Tail120=hornerBox Q residualBox cell0 120 100 :=
  hornerChunk_step Q residualBox cell0 resval0Tail120 resval0Tail124 120 4 96 (by decide +kernel) resval0H124
theorem resval0H116 : resval0Tail116=hornerBox Q residualBox cell0 116 104 :=
  hornerChunk_step Q residualBox cell0 resval0Tail116 resval0Tail120 116 4 100 (by decide +kernel) resval0H120
theorem resval0H112 : resval0Tail112=hornerBox Q residualBox cell0 112 108 :=
  hornerChunk_step Q residualBox cell0 resval0Tail112 resval0Tail116 112 4 104 (by decide +kernel) resval0H116
theorem resval0H108 : resval0Tail108=hornerBox Q residualBox cell0 108 112 :=
  hornerChunk_step Q residualBox cell0 resval0Tail108 resval0Tail112 108 4 108 (by decide +kernel) resval0H112
theorem resval0H104 : resval0Tail104=hornerBox Q residualBox cell0 104 116 :=
  hornerChunk_step Q residualBox cell0 resval0Tail104 resval0Tail108 104 4 112 (by decide +kernel) resval0H108
theorem resval0H100 : resval0Tail100=hornerBox Q residualBox cell0 100 120 :=
  hornerChunk_step Q residualBox cell0 resval0Tail100 resval0Tail104 100 4 116 (by decide +kernel) resval0H104
theorem resval0H96 : resval0Tail96=hornerBox Q residualBox cell0 96 124 :=
  hornerChunk_step Q residualBox cell0 resval0Tail96 resval0Tail100 96 4 120 (by decide +kernel) resval0H100
theorem resval0H92 : resval0Tail92=hornerBox Q residualBox cell0 92 128 :=
  hornerChunk_step Q residualBox cell0 resval0Tail92 resval0Tail96 92 4 124 (by decide +kernel) resval0H96
theorem resval0H88 : resval0Tail88=hornerBox Q residualBox cell0 88 132 :=
  hornerChunk_step Q residualBox cell0 resval0Tail88 resval0Tail92 88 4 128 (by decide +kernel) resval0H92
theorem resval0H84 : resval0Tail84=hornerBox Q residualBox cell0 84 136 :=
  hornerChunk_step Q residualBox cell0 resval0Tail84 resval0Tail88 84 4 132 (by decide +kernel) resval0H88
theorem resval0H80 : resval0Tail80=hornerBox Q residualBox cell0 80 140 :=
  hornerChunk_step Q residualBox cell0 resval0Tail80 resval0Tail84 80 4 136 (by decide +kernel) resval0H84
theorem resval0H76 : resval0Tail76=hornerBox Q residualBox cell0 76 144 :=
  hornerChunk_step Q residualBox cell0 resval0Tail76 resval0Tail80 76 4 140 (by decide +kernel) resval0H80
theorem resval0H72 : resval0Tail72=hornerBox Q residualBox cell0 72 148 :=
  hornerChunk_step Q residualBox cell0 resval0Tail72 resval0Tail76 72 4 144 (by decide +kernel) resval0H76
theorem resval0H68 : resval0Tail68=hornerBox Q residualBox cell0 68 152 :=
  hornerChunk_step Q residualBox cell0 resval0Tail68 resval0Tail72 68 4 148 (by decide +kernel) resval0H72
theorem resval0H64 : resval0Tail64=hornerBox Q residualBox cell0 64 156 :=
  hornerChunk_step Q residualBox cell0 resval0Tail64 resval0Tail68 64 4 152 (by decide +kernel) resval0H68
theorem resval0H60 : resval0Tail60=hornerBox Q residualBox cell0 60 160 :=
  hornerChunk_step Q residualBox cell0 resval0Tail60 resval0Tail64 60 4 156 (by decide +kernel) resval0H64
theorem resval0H56 : resval0Tail56=hornerBox Q residualBox cell0 56 164 :=
  hornerChunk_step Q residualBox cell0 resval0Tail56 resval0Tail60 56 4 160 (by decide +kernel) resval0H60
theorem resval0H52 : resval0Tail52=hornerBox Q residualBox cell0 52 168 :=
  hornerChunk_step Q residualBox cell0 resval0Tail52 resval0Tail56 52 4 164 (by decide +kernel) resval0H56
theorem resval0H48 : resval0Tail48=hornerBox Q residualBox cell0 48 172 :=
  hornerChunk_step Q residualBox cell0 resval0Tail48 resval0Tail52 48 4 168 (by decide +kernel) resval0H52
theorem resval0H44 : resval0Tail44=hornerBox Q residualBox cell0 44 176 :=
  hornerChunk_step Q residualBox cell0 resval0Tail44 resval0Tail48 44 4 172 (by decide +kernel) resval0H48
theorem resval0H40 : resval0Tail40=hornerBox Q residualBox cell0 40 180 :=
  hornerChunk_step Q residualBox cell0 resval0Tail40 resval0Tail44 40 4 176 (by decide +kernel) resval0H44
theorem resval0H36 : resval0Tail36=hornerBox Q residualBox cell0 36 184 :=
  hornerChunk_step Q residualBox cell0 resval0Tail36 resval0Tail40 36 4 180 (by decide +kernel) resval0H40
theorem resval0H32 : resval0Tail32=hornerBox Q residualBox cell0 32 188 :=
  hornerChunk_step Q residualBox cell0 resval0Tail32 resval0Tail36 32 4 184 (by decide +kernel) resval0H36
theorem resval0H28 : resval0Tail28=hornerBox Q residualBox cell0 28 192 :=
  hornerChunk_step Q residualBox cell0 resval0Tail28 resval0Tail32 28 4 188 (by decide +kernel) resval0H32
theorem resval0H24 : resval0Tail24=hornerBox Q residualBox cell0 24 196 :=
  hornerChunk_step Q residualBox cell0 resval0Tail24 resval0Tail28 24 4 192 (by decide +kernel) resval0H28
theorem resval0H20 : resval0Tail20=hornerBox Q residualBox cell0 20 200 :=
  hornerChunk_step Q residualBox cell0 resval0Tail20 resval0Tail24 20 4 196 (by decide +kernel) resval0H24
theorem resval0H16 : resval0Tail16=hornerBox Q residualBox cell0 16 204 :=
  hornerChunk_step Q residualBox cell0 resval0Tail16 resval0Tail20 16 4 200 (by decide +kernel) resval0H20
theorem resval0H12 : resval0Tail12=hornerBox Q residualBox cell0 12 208 :=
  hornerChunk_step Q residualBox cell0 resval0Tail12 resval0Tail16 12 4 204 (by decide +kernel) resval0H16
theorem resval0H8 : resval0Tail8=hornerBox Q residualBox cell0 8 212 :=
  hornerChunk_step Q residualBox cell0 resval0Tail8 resval0Tail12 8 4 208 (by decide +kernel) resval0H12
theorem resval0H4 : resval0Tail4=hornerBox Q residualBox cell0 4 216 :=
  hornerChunk_step Q residualBox cell0 resval0Tail4 resval0Tail8 4 4 212 (by decide +kernel) resval0H8
theorem resval0H0 : resval0=hornerBox Q residualBox cell0 0 220 :=
  hornerChunk_step Q residualBox cell0 resval0 resval0Tail4 0 4 216 (by decide +kernel) resval0H4
theorem resval0_eq : resval0=hornerBox Q residualBox cell0 0 220 := resval0H0
def polyval0Tail5 : Box := ⟨1875034295062678220263016776859719557643281669531367,53797879641068805062176273527616801483791870178876⟩
def polyval0Tail9 : Box := ⟨166279064232559997707037930545050104031928417290,9369903745210549198217520565145487288887730751⟩
def polyval0Tail13 : Box := ⟨119746009935620829778772510900646079524339592,10445487793136240629183696663721061683095072⟩
def polyval0Tail17 : Box := ⟨384647646209052905726083257592157639382343,412147842394171211222911634295641834297187⟩
def polyval0Tail21 : Box := ⟨4216627598539549561218318732502684210812,5829025753081462481921061211091228581940584⟩
def polyval0Tail25 : Box := ⟨134874257807975552006503279530167727958,93252842224961281149037627927425969996015674⟩
def polyval0Tail29 : Box := ⟨11428052722280386998156829061970681571,1492044972497987302389429630898437920517729796⟩
def polyval0Tail33 : Box := ⟨2440941843859189900361697397112512329,23872719501939952947863249916578717591301233504⟩
def polyval0Tail37 : Box := ⟨6790904417868849340723744921652309233,381963512012254783020493573800912210401779495957⟩
def polyval0Tail41 : Box := ⟨1422438446147718350087016598966821818547,6111416190863869044805531282995849777426625529626⟩
def polyval0Tail45 : Box := ⟨363757804744857402631476201361893111846911,97782658712801560710095011034932953182273230732326⟩
def polyval0Tail49 : Box := ⟨93120861786046051002542883886672606814968019,1564522452104032787042891433921864900264664182932291⟩
def polyval0Tail53 : Box := ⟨23838932484512294872935128243186971787618535273,25032336884665618094089246341135644026063087913075757⟩
def polyval0Tail57 : Box := ⟨6102766579331960679346773220208046217727742275264,400511668810999728786197021208043848825750733930226695⟩
def polyval0Tail61 : Box := ⟨1562308242570809960057861857598172715283520411441771,6406722037002472013933191796677350371377332316484860511⟩
def polyval0Tail65 : Box := ⟨399950917195510772879055334547917530600435616862588406,102132598611234902861459248335937039063138485368296657523⟩
def polyval0Tail69 : Box := ⟨102387520947105280062409985073935145826236022895687372497,1538133314781276659405315210954705789073220119211034600149⟩
def polyval0Tail73 : Box := ⟨26281250000000000000000000000000000000000000000000000000000,2⟩
theorem polyval0H73 : polyval0Tail73=hornerBox Q polyBox cell0 73 1 :=
  hornerChunk_step Q polyBox cell0 polyval0Tail73 zero 73 1 0 (by decide +kernel) rfl
theorem polyval0H69 : polyval0Tail69=hornerBox Q polyBox cell0 69 5 :=
  hornerChunk_step Q polyBox cell0 polyval0Tail69 polyval0Tail73 69 4 1 (by decide +kernel) polyval0H73
theorem polyval0H65 : polyval0Tail65=hornerBox Q polyBox cell0 65 9 :=
  hornerChunk_step Q polyBox cell0 polyval0Tail65 polyval0Tail69 65 4 5 (by decide +kernel) polyval0H69
theorem polyval0H61 : polyval0Tail61=hornerBox Q polyBox cell0 61 13 :=
  hornerChunk_step Q polyBox cell0 polyval0Tail61 polyval0Tail65 61 4 9 (by decide +kernel) polyval0H65
theorem polyval0H57 : polyval0Tail57=hornerBox Q polyBox cell0 57 17 :=
  hornerChunk_step Q polyBox cell0 polyval0Tail57 polyval0Tail61 57 4 13 (by decide +kernel) polyval0H61
theorem polyval0H53 : polyval0Tail53=hornerBox Q polyBox cell0 53 21 :=
  hornerChunk_step Q polyBox cell0 polyval0Tail53 polyval0Tail57 53 4 17 (by decide +kernel) polyval0H57
theorem polyval0H49 : polyval0Tail49=hornerBox Q polyBox cell0 49 25 :=
  hornerChunk_step Q polyBox cell0 polyval0Tail49 polyval0Tail53 49 4 21 (by decide +kernel) polyval0H53
theorem polyval0H45 : polyval0Tail45=hornerBox Q polyBox cell0 45 29 :=
  hornerChunk_step Q polyBox cell0 polyval0Tail45 polyval0Tail49 45 4 25 (by decide +kernel) polyval0H49
theorem polyval0H41 : polyval0Tail41=hornerBox Q polyBox cell0 41 33 :=
  hornerChunk_step Q polyBox cell0 polyval0Tail41 polyval0Tail45 41 4 29 (by decide +kernel) polyval0H45
theorem polyval0H37 : polyval0Tail37=hornerBox Q polyBox cell0 37 37 :=
  hornerChunk_step Q polyBox cell0 polyval0Tail37 polyval0Tail41 37 4 33 (by decide +kernel) polyval0H41
theorem polyval0H33 : polyval0Tail33=hornerBox Q polyBox cell0 33 41 :=
  hornerChunk_step Q polyBox cell0 polyval0Tail33 polyval0Tail37 33 4 37 (by decide +kernel) polyval0H37
theorem polyval0H29 : polyval0Tail29=hornerBox Q polyBox cell0 29 45 :=
  hornerChunk_step Q polyBox cell0 polyval0Tail29 polyval0Tail33 29 4 41 (by decide +kernel) polyval0H33
theorem polyval0H25 : polyval0Tail25=hornerBox Q polyBox cell0 25 49 :=
  hornerChunk_step Q polyBox cell0 polyval0Tail25 polyval0Tail29 25 4 45 (by decide +kernel) polyval0H29
theorem polyval0H21 : polyval0Tail21=hornerBox Q polyBox cell0 21 53 :=
  hornerChunk_step Q polyBox cell0 polyval0Tail21 polyval0Tail25 21 4 49 (by decide +kernel) polyval0H25
theorem polyval0H17 : polyval0Tail17=hornerBox Q polyBox cell0 17 57 :=
  hornerChunk_step Q polyBox cell0 polyval0Tail17 polyval0Tail21 17 4 53 (by decide +kernel) polyval0H21
theorem polyval0H13 : polyval0Tail13=hornerBox Q polyBox cell0 13 61 :=
  hornerChunk_step Q polyBox cell0 polyval0Tail13 polyval0Tail17 13 4 57 (by decide +kernel) polyval0H17
theorem polyval0H9 : polyval0Tail9=hornerBox Q polyBox cell0 9 65 :=
  hornerChunk_step Q polyBox cell0 polyval0Tail9 polyval0Tail13 9 4 61 (by decide +kernel) polyval0H13
theorem polyval0H5 : polyval0Tail5=hornerBox Q polyBox cell0 5 69 :=
  hornerChunk_step Q polyBox cell0 polyval0Tail5 polyval0Tail9 5 4 65 (by decide +kernel) polyval0H9
theorem polyval0H1 : polyval0=hornerBox Q polyBox cell0 1 73 :=
  hornerChunk_step Q polyBox cell0 polyval0 polyval0Tail5 1 4 69 (by decide +kernel) polyval0H5
theorem polyval0_eq : polyval0=hornerBox Q polyBox cell0 1 73 := polyval0H1
theorem polyval0_upper : 5*(polyval0.center+polyval0.radius)<Q := by decide +kernel
theorem resval0_pos : 0<(resval0).center-(resval0).radius := by decide +kernel
theorem polyval0_pos : 0<(polyval0).center-(polyval0).radius := by decide +kernel
def cell1 : Box := ⟨625000000000000000000000000000000000000000000000000000000000,125000000000000000000000000000000000000000000000000000000002⟩
def resval1 : Box := ⟨105240141525858941270478774418636116197121121526168200952,403857998288626264351157875911068124230374078416558623⟩
def polyval1 : Box := ⟨3703937994913543467521058525859035718365577157316720485262,11486732482729141124306829007549317568922324487523630089⟩
theorem cell1_lo : Holds Q cell1 (1/2:ℝ) := by norm_num [Holds,Q,cell1]
theorem cell1_hi : Holds Q cell1 (3/4:ℝ) := by norm_num [Holds,Q,cell1]
def resval1Tail4 : Box := ⟨48124872375155990121640769774188294329105225443215,3196653092028188833742061115812994691532801239606⟩
def resval1Tail8 : Box := ⟨5161198090025894212253092690868526198794142039,5974551971028312926460637580505562579167236324607⟩
def resval1Tail12 : Box := ⟨-313904696262999661919145421692524028741752901,18881665567193168605506819614910548955569294568820⟩
def resval1Tail16 : Box := ⟨-2084962066888367929635324698330587650951476926,59674307156819176899336951235364421681287975370756⟩
def resval1Tail20 : Box := ⟨-13664106511927618656377974566613736816247148179,188593204856126687896121769185166799486599893646441⟩
def resval1Tail24 : Box := ⟨-89549089635779120577375435525491628431345373056,596001296027361996195303612975340324617244401678953⟩
def resval1Tail28 : Box := ⟨-586868913879100709456000616349669294475067292537,1883354567505291314104910422631807110310326927146543⟩
def resval1Tail32 : Box := ⟨-3846104114001934789032924258536259259991448155752,5950339176420661529326397325581751235031078404836278⟩
def resval1Tail36 : Box := ⟨-25205827921523938997437263472012197691729062667112,18792959996978153434959781201056085540960478453991519⟩
def resval1Tail40 : Box := ⟨-165188913866499711451823671505344156455716737423920,59309508014211493027990138113184862727301789977996861⟩
def resval1Tail44 : Box := ⟨-1082582065915492867797797633735881239285814660715409,186886830447516187672481525158249221675062898123563875⟩
def resval1Tail48 : Box := ⟨-7094809827183773239150763988775068642085415589864472,586981358116501534986513453609870015920770678484056482⟩
def resval1Tail52 : Box := ⟨-46496545683431518546939344360800753440761004346952208,1831077515965746656644827322453595487311176223673867966⟩
def resval1Tail56 : Box := ⟨-304719761790931471503881093981200812817714911321353746,5629341470087946479574890149239152412296457632740801612⟩
def resval1Tail60 : Box := ⟨-1997011430871475902327787118647577319497454244301242871,16757552462472452561680831585019613522542012951166231534⟩
def resval1Tail64 : Box := ⟨-13087614110991672011608872019272712299071127689676929768,46186069302662330170527997814060367603053246271214444597⟩
def resval1Tail68 : Box := ⟨-85770945872785220942214447484947585443636329353769961057,101563125130838804445423191939569778087466633430566426224⟩
def resval1Tail72 : Box := ⟨725713999692668643402696075087371782093879265598595137670,1962765105402960882151545532161049411212069454109466709⟩
def resval1Tail76 : Box := ⟨-22111178261421856851755257833615347522091711872214,463819405538785858836682651801991015987471687441⟩
def resval1Tail80 : Box := ⟨-1068833370045587913383370553148339387843880752,58782267524320723201518122567847740112556634354⟩
def resval1Tail84 : Box := ⟨-3144390349370980332301350140239105026940327,185646608536867284262774594777201026224816410998⟩
def resval1Tail88 : Box := ⟨-17066274729994341203050087556841602829727093,586726103452434181346772282978307669812134780984⟩
def resval1Tail92 : Box := ⟨-111836796688797391311571608558468995457710699,1854286324961790404735285030053553537052807237807⟩
def resval1Tail96 : Box := ⟨-732933553353828443972035979030328750513232936,5860081009743738111534722600564880041439402337698⟩
def resval1Tail100 : Box := ⟨-4803353333199616744984942725215149963558871096,18518262936592379820520758255456665390451456873859⟩
def resval1Tail104 : Box := ⟨-31479256404310027466091276760330785282140086672,58510557412990039159042641289934221217759571950326⟩
def resval1Tail108 : Box := ⟨-206302454771260248332922311209592350324245500675,184815443068252842297279649199636019991187477714054⟩
def resval1Tail112 : Box := ⟨-1352023767588920684021579882576557006337487322812,583408060848388484358882237113569338742876891565749⟩
def resval1Tail116 : Box := ⟨-8860622963270742454554802490514741782415987834148,1839270014835373891588206247870940031794414102078059⟩
def resval1Tail120 : Box := ⟨-58068978652091138777660931759122160134761610013381,5782936493896711658426837178446358738993859895030758⟩
def resval1Tail124 : Box := ⟨-380560858494344922150463302498159375584027218900781,18079900881906809902865391705397064449643004083773396⟩
def resval1Tail128 : Box := ⟨-2494043642228571223388680156719405396876839285492548,55850131734841767645730342528689694254208963763174358⟩
def resval1Tail132 : Box := ⟨-16344964413715955821882103923551627691829790560245590,168051441716288892646559771701756656517204669461132344⟩
def resval1Tail136 : Box := ⟨-107118358788130602378501034721308426386483941212144691,475665344540947951419441467378494511873725148333936891⟩
def resval1Tail140 : Box := ⟨-702010929774105956847245254020630424292724431511138365,1139873407092619692301006972390397138514619951586527800⟩
def resval1Tail144 : Box := ⟨-4636057914187913161943830351746084684818702209452925217,1212276786089926584086850350728841297605558547208759516⟩
def resval1Tail148 : Box := ⟨46492203381741999328053488748483585177569111,852051585611399638437266999518646214363918⟩
def resval1Tail152 : Box := ⟨740014127645010815789168019057245788702,2394193998509644569371322842706339182978⟩
def resval1Tail156 : Box := ⟨302091827926102326315410924981861824,7482901366941953753134893024415109339579⟩
def resval1Tail160 : Box := ⟨601511607630383985993057976065693774,23649343395863426011516143447706551126824⟩
def resval1Tail164 : Box := ⟨3939910439174272722349761201910386542,74741563922886036023292450280551564605165⟩
def resval1Tail168 : Box := ⟨25820584234725657223662159873747399329,236206882882640692756400044149776311852198⟩
def resval1Tail172 : Box := ⟨169217780604056661032524106383312582047,746442783299772576227966353781809836917074⟩
def resval1Tail176 : Box := ⟨1108985646954796862031843811479675078531,2358553635051513428612958861241475336438891⟩
def resval1Tail180 : Box := ⟨7267848335881442214943128420309316828085,7450431298562980314562657654747028845015353⟩
def resval1Tail184 : Box := ⟨47630570854032170830197286297477580936166,23522381547739901046473927700999756575868078⟩
def resval1Tail188 : Box := ⟨312151709148984954904954058681055560953393,74180726097765174201085339276529214363579252⟩
def resval1Tail192 : Box := ⟨2045717441078787577827142179830304865282457,233388563035094357308657096833782793340187906⟩
def resval1Tail196 : Box := ⟨13406813821853944759742388498636022689141840,730681776325063650734801058748113068191057060⟩
def resval1Tail200 : Box := ⟨87862895062902160553827842897157590853579608,2263824500956985649393995675286582959241773339⟩
def resval1Tail204 : Box := ⟨575818269084253674417904271411570803937523875,6856675229447749880511205110327487335151282749⟩
def resval1Tail208 : Box := ⟨3773682608278486613154959370864812684180174634,19716667214247974685045905114201717072666207463⟩
def resval1Tail212 : Box := ⟨24731206362230000509806011984709874335469693314,49509899264746798643216542591915683236066332997⟩
def resval1Tail216 : Box := ⟨162079380722393325156079277037006633288256883127,72559882831455039320729855447128997164997996078⟩
theorem resval1H216 : resval1Tail216=hornerBox Q residualBox cell1 216 4 :=
  hornerChunk_step Q residualBox cell1 resval1Tail216 zero 216 4 0 (by decide +kernel) rfl
theorem resval1H212 : resval1Tail212=hornerBox Q residualBox cell1 212 8 :=
  hornerChunk_step Q residualBox cell1 resval1Tail212 resval1Tail216 212 4 4 (by decide +kernel) resval1H216
theorem resval1H208 : resval1Tail208=hornerBox Q residualBox cell1 208 12 :=
  hornerChunk_step Q residualBox cell1 resval1Tail208 resval1Tail212 208 4 8 (by decide +kernel) resval1H212
theorem resval1H204 : resval1Tail204=hornerBox Q residualBox cell1 204 16 :=
  hornerChunk_step Q residualBox cell1 resval1Tail204 resval1Tail208 204 4 12 (by decide +kernel) resval1H208
theorem resval1H200 : resval1Tail200=hornerBox Q residualBox cell1 200 20 :=
  hornerChunk_step Q residualBox cell1 resval1Tail200 resval1Tail204 200 4 16 (by decide +kernel) resval1H204
theorem resval1H196 : resval1Tail196=hornerBox Q residualBox cell1 196 24 :=
  hornerChunk_step Q residualBox cell1 resval1Tail196 resval1Tail200 196 4 20 (by decide +kernel) resval1H200
theorem resval1H192 : resval1Tail192=hornerBox Q residualBox cell1 192 28 :=
  hornerChunk_step Q residualBox cell1 resval1Tail192 resval1Tail196 192 4 24 (by decide +kernel) resval1H196
theorem resval1H188 : resval1Tail188=hornerBox Q residualBox cell1 188 32 :=
  hornerChunk_step Q residualBox cell1 resval1Tail188 resval1Tail192 188 4 28 (by decide +kernel) resval1H192
theorem resval1H184 : resval1Tail184=hornerBox Q residualBox cell1 184 36 :=
  hornerChunk_step Q residualBox cell1 resval1Tail184 resval1Tail188 184 4 32 (by decide +kernel) resval1H188
theorem resval1H180 : resval1Tail180=hornerBox Q residualBox cell1 180 40 :=
  hornerChunk_step Q residualBox cell1 resval1Tail180 resval1Tail184 180 4 36 (by decide +kernel) resval1H184
theorem resval1H176 : resval1Tail176=hornerBox Q residualBox cell1 176 44 :=
  hornerChunk_step Q residualBox cell1 resval1Tail176 resval1Tail180 176 4 40 (by decide +kernel) resval1H180
theorem resval1H172 : resval1Tail172=hornerBox Q residualBox cell1 172 48 :=
  hornerChunk_step Q residualBox cell1 resval1Tail172 resval1Tail176 172 4 44 (by decide +kernel) resval1H176
theorem resval1H168 : resval1Tail168=hornerBox Q residualBox cell1 168 52 :=
  hornerChunk_step Q residualBox cell1 resval1Tail168 resval1Tail172 168 4 48 (by decide +kernel) resval1H172
theorem resval1H164 : resval1Tail164=hornerBox Q residualBox cell1 164 56 :=
  hornerChunk_step Q residualBox cell1 resval1Tail164 resval1Tail168 164 4 52 (by decide +kernel) resval1H168
theorem resval1H160 : resval1Tail160=hornerBox Q residualBox cell1 160 60 :=
  hornerChunk_step Q residualBox cell1 resval1Tail160 resval1Tail164 160 4 56 (by decide +kernel) resval1H164
theorem resval1H156 : resval1Tail156=hornerBox Q residualBox cell1 156 64 :=
  hornerChunk_step Q residualBox cell1 resval1Tail156 resval1Tail160 156 4 60 (by decide +kernel) resval1H160
theorem resval1H152 : resval1Tail152=hornerBox Q residualBox cell1 152 68 :=
  hornerChunk_step Q residualBox cell1 resval1Tail152 resval1Tail156 152 4 64 (by decide +kernel) resval1H156
theorem resval1H148 : resval1Tail148=hornerBox Q residualBox cell1 148 72 :=
  hornerChunk_step Q residualBox cell1 resval1Tail148 resval1Tail152 148 4 68 (by decide +kernel) resval1H152
theorem resval1H144 : resval1Tail144=hornerBox Q residualBox cell1 144 76 :=
  hornerChunk_step Q residualBox cell1 resval1Tail144 resval1Tail148 144 4 72 (by decide +kernel) resval1H148
theorem resval1H140 : resval1Tail140=hornerBox Q residualBox cell1 140 80 :=
  hornerChunk_step Q residualBox cell1 resval1Tail140 resval1Tail144 140 4 76 (by decide +kernel) resval1H144
theorem resval1H136 : resval1Tail136=hornerBox Q residualBox cell1 136 84 :=
  hornerChunk_step Q residualBox cell1 resval1Tail136 resval1Tail140 136 4 80 (by decide +kernel) resval1H140
theorem resval1H132 : resval1Tail132=hornerBox Q residualBox cell1 132 88 :=
  hornerChunk_step Q residualBox cell1 resval1Tail132 resval1Tail136 132 4 84 (by decide +kernel) resval1H136
theorem resval1H128 : resval1Tail128=hornerBox Q residualBox cell1 128 92 :=
  hornerChunk_step Q residualBox cell1 resval1Tail128 resval1Tail132 128 4 88 (by decide +kernel) resval1H132
theorem resval1H124 : resval1Tail124=hornerBox Q residualBox cell1 124 96 :=
  hornerChunk_step Q residualBox cell1 resval1Tail124 resval1Tail128 124 4 92 (by decide +kernel) resval1H128
theorem resval1H120 : resval1Tail120=hornerBox Q residualBox cell1 120 100 :=
  hornerChunk_step Q residualBox cell1 resval1Tail120 resval1Tail124 120 4 96 (by decide +kernel) resval1H124
theorem resval1H116 : resval1Tail116=hornerBox Q residualBox cell1 116 104 :=
  hornerChunk_step Q residualBox cell1 resval1Tail116 resval1Tail120 116 4 100 (by decide +kernel) resval1H120
theorem resval1H112 : resval1Tail112=hornerBox Q residualBox cell1 112 108 :=
  hornerChunk_step Q residualBox cell1 resval1Tail112 resval1Tail116 112 4 104 (by decide +kernel) resval1H116
theorem resval1H108 : resval1Tail108=hornerBox Q residualBox cell1 108 112 :=
  hornerChunk_step Q residualBox cell1 resval1Tail108 resval1Tail112 108 4 108 (by decide +kernel) resval1H112
theorem resval1H104 : resval1Tail104=hornerBox Q residualBox cell1 104 116 :=
  hornerChunk_step Q residualBox cell1 resval1Tail104 resval1Tail108 104 4 112 (by decide +kernel) resval1H108
theorem resval1H100 : resval1Tail100=hornerBox Q residualBox cell1 100 120 :=
  hornerChunk_step Q residualBox cell1 resval1Tail100 resval1Tail104 100 4 116 (by decide +kernel) resval1H104
theorem resval1H96 : resval1Tail96=hornerBox Q residualBox cell1 96 124 :=
  hornerChunk_step Q residualBox cell1 resval1Tail96 resval1Tail100 96 4 120 (by decide +kernel) resval1H100
theorem resval1H92 : resval1Tail92=hornerBox Q residualBox cell1 92 128 :=
  hornerChunk_step Q residualBox cell1 resval1Tail92 resval1Tail96 92 4 124 (by decide +kernel) resval1H96
theorem resval1H88 : resval1Tail88=hornerBox Q residualBox cell1 88 132 :=
  hornerChunk_step Q residualBox cell1 resval1Tail88 resval1Tail92 88 4 128 (by decide +kernel) resval1H92
theorem resval1H84 : resval1Tail84=hornerBox Q residualBox cell1 84 136 :=
  hornerChunk_step Q residualBox cell1 resval1Tail84 resval1Tail88 84 4 132 (by decide +kernel) resval1H88
theorem resval1H80 : resval1Tail80=hornerBox Q residualBox cell1 80 140 :=
  hornerChunk_step Q residualBox cell1 resval1Tail80 resval1Tail84 80 4 136 (by decide +kernel) resval1H84
theorem resval1H76 : resval1Tail76=hornerBox Q residualBox cell1 76 144 :=
  hornerChunk_step Q residualBox cell1 resval1Tail76 resval1Tail80 76 4 140 (by decide +kernel) resval1H80
theorem resval1H72 : resval1Tail72=hornerBox Q residualBox cell1 72 148 :=
  hornerChunk_step Q residualBox cell1 resval1Tail72 resval1Tail76 72 4 144 (by decide +kernel) resval1H76
theorem resval1H68 : resval1Tail68=hornerBox Q residualBox cell1 68 152 :=
  hornerChunk_step Q residualBox cell1 resval1Tail68 resval1Tail72 68 4 148 (by decide +kernel) resval1H72
theorem resval1H64 : resval1Tail64=hornerBox Q residualBox cell1 64 156 :=
  hornerChunk_step Q residualBox cell1 resval1Tail64 resval1Tail68 64 4 152 (by decide +kernel) resval1H68
theorem resval1H60 : resval1Tail60=hornerBox Q residualBox cell1 60 160 :=
  hornerChunk_step Q residualBox cell1 resval1Tail60 resval1Tail64 60 4 156 (by decide +kernel) resval1H64
theorem resval1H56 : resval1Tail56=hornerBox Q residualBox cell1 56 164 :=
  hornerChunk_step Q residualBox cell1 resval1Tail56 resval1Tail60 56 4 160 (by decide +kernel) resval1H60
theorem resval1H52 : resval1Tail52=hornerBox Q residualBox cell1 52 168 :=
  hornerChunk_step Q residualBox cell1 resval1Tail52 resval1Tail56 52 4 164 (by decide +kernel) resval1H56
theorem resval1H48 : resval1Tail48=hornerBox Q residualBox cell1 48 172 :=
  hornerChunk_step Q residualBox cell1 resval1Tail48 resval1Tail52 48 4 168 (by decide +kernel) resval1H52
theorem resval1H44 : resval1Tail44=hornerBox Q residualBox cell1 44 176 :=
  hornerChunk_step Q residualBox cell1 resval1Tail44 resval1Tail48 44 4 172 (by decide +kernel) resval1H48
theorem resval1H40 : resval1Tail40=hornerBox Q residualBox cell1 40 180 :=
  hornerChunk_step Q residualBox cell1 resval1Tail40 resval1Tail44 40 4 176 (by decide +kernel) resval1H44
theorem resval1H36 : resval1Tail36=hornerBox Q residualBox cell1 36 184 :=
  hornerChunk_step Q residualBox cell1 resval1Tail36 resval1Tail40 36 4 180 (by decide +kernel) resval1H40
theorem resval1H32 : resval1Tail32=hornerBox Q residualBox cell1 32 188 :=
  hornerChunk_step Q residualBox cell1 resval1Tail32 resval1Tail36 32 4 184 (by decide +kernel) resval1H36
theorem resval1H28 : resval1Tail28=hornerBox Q residualBox cell1 28 192 :=
  hornerChunk_step Q residualBox cell1 resval1Tail28 resval1Tail32 28 4 188 (by decide +kernel) resval1H32
theorem resval1H24 : resval1Tail24=hornerBox Q residualBox cell1 24 196 :=
  hornerChunk_step Q residualBox cell1 resval1Tail24 resval1Tail28 24 4 192 (by decide +kernel) resval1H28
theorem resval1H20 : resval1Tail20=hornerBox Q residualBox cell1 20 200 :=
  hornerChunk_step Q residualBox cell1 resval1Tail20 resval1Tail24 20 4 196 (by decide +kernel) resval1H24
theorem resval1H16 : resval1Tail16=hornerBox Q residualBox cell1 16 204 :=
  hornerChunk_step Q residualBox cell1 resval1Tail16 resval1Tail20 16 4 200 (by decide +kernel) resval1H20
theorem resval1H12 : resval1Tail12=hornerBox Q residualBox cell1 12 208 :=
  hornerChunk_step Q residualBox cell1 resval1Tail12 resval1Tail16 12 4 204 (by decide +kernel) resval1H16
theorem resval1H8 : resval1Tail8=hornerBox Q residualBox cell1 8 212 :=
  hornerChunk_step Q residualBox cell1 resval1Tail8 resval1Tail12 8 4 208 (by decide +kernel) resval1H12
theorem resval1H4 : resval1Tail4=hornerBox Q residualBox cell1 4 216 :=
  hornerChunk_step Q residualBox cell1 resval1Tail4 resval1Tail8 4 4 212 (by decide +kernel) resval1H8
theorem resval1H0 : resval1=hornerBox Q residualBox cell1 0 220 :=
  hornerChunk_step Q residualBox cell1 resval1 resval1Tail4 0 4 216 (by decide +kernel) resval1H4
theorem resval1_eq : resval1=hornerBox Q residualBox cell1 0 220 := resval1H0
def polyval1Tail5 : Box := ⟨1825549416660781933261977930391297567872155943378543,119668514349611144755334659161438411034680868525271⟩
def polyval1Tail9 : Box := ⟨160626918206505069718486515878254196467037277138,264974907529423031020888948079901177260041499953370⟩
def polyval1Tail13 : Box := ⟨14969745217548416954164521725603998497998839081,837426984652890378178675754839071828068829715243915⟩
def polyval1Tail17 : Box := ⟨97375360812699106596281454498416519014314717144,2646632396699287788421040399740461316506238021526776⟩
def polyval1Tail21 : Box := ⟨638156877733339926619518336848929836234416292018,8364334948760452198344340600570956834092119249777301⟩
def polyval1Tail25 : Box := ⟨4182224889573265385744954012639407363743731887632,26433263639831439068282645594386759984247446072739669⟩
def polyval1Tail29 : Box := ⟨27408629035556703110197768880596188113797440058061,83527975832304551864857073928035622360403228992290020⟩
def polyval1Tail33 : Box := ⟨179625191247363922720687086845866336984757409435381,263896651624839862159736702017330831881324041819855323⟩
def polyval1Tail37 : Box := ⟨1177191653358712390820723325788481764670623323598720,833434251123410786197030918338637139230838599452974542⟩
def polyval1Tail41 : Box := ⟨7714843219451652351043830988619120226996212906669474,2630069469754042068906166461857523207359580757248351550⟩
def polyval1Tail45 : Box := ⟨50559996522998344645141312098062615943502052539418498,8286141042010512673560666929794248842577416319769034891⟩
def polyval1Tail49 : Box := ⟨331349993213121953482211651182384646219319379997992251,26016742177954517810712074399635820381432328416330276790⟩
def polyval1Tail53 : Box := ⟨2171535315521516328716781838375444679047187054720590467,81101447348909542887273038643262181599681499079097171654⟩
def polyval1Tail57 : Box := ⟨14231373843801831886322376013153034383096160105357413137,248952373836375358561390950598133459146108096782072143764⟩
def polyval1Tail61 : Box := ⟨93266731622744595506892105413044568003274655836996177587,738523878329423810758050753100952476486929945978711875361⟩
def polyval1Tail65 : Box := ⟨611232852367619711467993327774303091344652639886572721852,2017636235879747986739845968961506743209409976399735727014⟩
def polyval1Tail69 : Box := ⟨4005775662416372341941591054450517519382552190640807241055,4302748894164523934420206445434156637822286906743681132884⟩
def polyval1Tail73 : Box := ⟨26281250000000000000000000000000000000000000000000000000000,2⟩
theorem polyval1H73 : polyval1Tail73=hornerBox Q polyBox cell1 73 1 :=
  hornerChunk_step Q polyBox cell1 polyval1Tail73 zero 73 1 0 (by decide +kernel) rfl
theorem polyval1H69 : polyval1Tail69=hornerBox Q polyBox cell1 69 5 :=
  hornerChunk_step Q polyBox cell1 polyval1Tail69 polyval1Tail73 69 4 1 (by decide +kernel) polyval1H73
theorem polyval1H65 : polyval1Tail65=hornerBox Q polyBox cell1 65 9 :=
  hornerChunk_step Q polyBox cell1 polyval1Tail65 polyval1Tail69 65 4 5 (by decide +kernel) polyval1H69
theorem polyval1H61 : polyval1Tail61=hornerBox Q polyBox cell1 61 13 :=
  hornerChunk_step Q polyBox cell1 polyval1Tail61 polyval1Tail65 61 4 9 (by decide +kernel) polyval1H65
theorem polyval1H57 : polyval1Tail57=hornerBox Q polyBox cell1 57 17 :=
  hornerChunk_step Q polyBox cell1 polyval1Tail57 polyval1Tail61 57 4 13 (by decide +kernel) polyval1H61
theorem polyval1H53 : polyval1Tail53=hornerBox Q polyBox cell1 53 21 :=
  hornerChunk_step Q polyBox cell1 polyval1Tail53 polyval1Tail57 53 4 17 (by decide +kernel) polyval1H57
theorem polyval1H49 : polyval1Tail49=hornerBox Q polyBox cell1 49 25 :=
  hornerChunk_step Q polyBox cell1 polyval1Tail49 polyval1Tail53 49 4 21 (by decide +kernel) polyval1H53
theorem polyval1H45 : polyval1Tail45=hornerBox Q polyBox cell1 45 29 :=
  hornerChunk_step Q polyBox cell1 polyval1Tail45 polyval1Tail49 45 4 25 (by decide +kernel) polyval1H49
theorem polyval1H41 : polyval1Tail41=hornerBox Q polyBox cell1 41 33 :=
  hornerChunk_step Q polyBox cell1 polyval1Tail41 polyval1Tail45 41 4 29 (by decide +kernel) polyval1H45
theorem polyval1H37 : polyval1Tail37=hornerBox Q polyBox cell1 37 37 :=
  hornerChunk_step Q polyBox cell1 polyval1Tail37 polyval1Tail41 37 4 33 (by decide +kernel) polyval1H41
theorem polyval1H33 : polyval1Tail33=hornerBox Q polyBox cell1 33 41 :=
  hornerChunk_step Q polyBox cell1 polyval1Tail33 polyval1Tail37 33 4 37 (by decide +kernel) polyval1H37
theorem polyval1H29 : polyval1Tail29=hornerBox Q polyBox cell1 29 45 :=
  hornerChunk_step Q polyBox cell1 polyval1Tail29 polyval1Tail33 29 4 41 (by decide +kernel) polyval1H33
theorem polyval1H25 : polyval1Tail25=hornerBox Q polyBox cell1 25 49 :=
  hornerChunk_step Q polyBox cell1 polyval1Tail25 polyval1Tail29 25 4 45 (by decide +kernel) polyval1H29
theorem polyval1H21 : polyval1Tail21=hornerBox Q polyBox cell1 21 53 :=
  hornerChunk_step Q polyBox cell1 polyval1Tail21 polyval1Tail25 21 4 49 (by decide +kernel) polyval1H25
theorem polyval1H17 : polyval1Tail17=hornerBox Q polyBox cell1 17 57 :=
  hornerChunk_step Q polyBox cell1 polyval1Tail17 polyval1Tail21 17 4 53 (by decide +kernel) polyval1H21
theorem polyval1H13 : polyval1Tail13=hornerBox Q polyBox cell1 13 61 :=
  hornerChunk_step Q polyBox cell1 polyval1Tail13 polyval1Tail17 13 4 57 (by decide +kernel) polyval1H17
theorem polyval1H9 : polyval1Tail9=hornerBox Q polyBox cell1 9 65 :=
  hornerChunk_step Q polyBox cell1 polyval1Tail9 polyval1Tail13 9 4 61 (by decide +kernel) polyval1H13
theorem polyval1H5 : polyval1Tail5=hornerBox Q polyBox cell1 5 69 :=
  hornerChunk_step Q polyBox cell1 polyval1Tail5 polyval1Tail9 5 4 65 (by decide +kernel) polyval1H9
theorem polyval1H1 : polyval1=hornerBox Q polyBox cell1 1 73 :=
  hornerChunk_step Q polyBox cell1 polyval1 polyval1Tail5 1 4 69 (by decide +kernel) polyval1H5
theorem polyval1_eq : polyval1=hornerBox Q polyBox cell1 1 73 := polyval1H1
theorem polyval1_upper : 5*(polyval1.center+polyval1.radius)<Q := by decide +kernel
theorem resval1_pos : 0<(resval1).center-(resval1).radius := by decide +kernel
theorem polyval1_pos : 0<(polyval1).center-(polyval1).radius := by decide +kernel
def cell2 : Box := ⟨812500000000000000000000000000000000000000000000000000000000,62500000000000000000000000000000000000000000000000000000002⟩
def resval2 : Box := ⟨105139228462323462790142383402708622752527311438959256419,389713113576216481447056767250524596019078920593254274⟩
def polyval2 : Box := ⟨3695345425084552259085691824437941444535668439758815620126,10289259590894950319062002487976155811925122481866273675⟩
theorem cell2_lo : Holds Q cell2 (3/4:ℝ) := by norm_num [Holds,Q,cell2]
theorem cell2_hi : Holds Q cell2 (7/8:ℝ) := by norm_num [Holds,Q,cell2]
def resval2Tail4 : Box := ⟨-147449890085324448364377736055756638324279984099878,33877879604898077579589536428486950546142889475920936⟩
def resval2Tail8 : Box := ⟨-447225417646759111213413647038687525737559182370059,57677702935241656677829606997897465275443664582318371⟩
def resval2Tail12 : Box := ⟨-1026214002261132365529221154294450927739321668793154,98132356012490997014641304356432591783338137737406594⟩
def resval2Tail16 : Box := ⟨-2354748122266106748804114170953326979678727392196031,166805394650026627100322230980510519251879068941001778⟩
def resval2Tail20 : Box := ⟨-5403199220677685773450104593429772310879688518766338,283176536220957276630646488072777927771655302991379224⟩
def resval2Tail24 : Box := ⟨-12398167575587130410602918564954594924928324540153854,479906120791317255542554122004746859340063174864716708⟩
def resval2Tail28 : Box := ⟨-28448804671883987284766331801887468345557429155867593,811400576898645119286381690222892459282465740438241537⟩
def resval2Tail32 : Box := ⟨-65278556877440881757636721800237706757289156301802590,1367467410183320143667193290213993099519487483478479572⟩
def resval2Tail36 : Box := ⟨-149788015248764596244156152187707797183530057972485817,2294413351298872705022155475144080778666179442442359161⟩
def resval2Tail40 : Box := ⟨-343703209528484177074295447476787942128423740048418033,3825996414536123230634956208129070018949426563745442192⟩
def resval2Tail44 : Box := ⟨-788660534983324779444667775644553106124852347328756281,6324662938639595645908134451869186914348966201746864804⟩
def resval2Tail48 : Box := ⟨-1809658514080990605566734022133987316178151782501313417,10325357290983350108663592781105373918788278944718207571⟩
def resval2Tail52 : Box := ⟨-4152437953111298574652272613301666794643724278705349995,16549363270355398378249958940904623339563557045139630822⟩
def resval2Tail56 : Box := ⟨-9528173862788485309005767248648682657211129085263678652,25788185075703633643333100373735483512586734246628042341⟩
def resval2Tail60 : Box := ⟨-21863324192838798550169653827405237974627838106134267595,38384825000022602484273171760990630652211500019383300157⟩
def resval2Tail64 : Box := ⟨-50167529646985153078595562925347314302753567441534797285,52613153022342834764819340752976261596458054170108776820⟩
def resval2Tail68 : Box := ⟨-115114256543751554273684555605144422121715403942672497112,60225016320564712465131570148593812689211933381063447458⟩
def resval2Tail72 : Box := ⟨726990674950459055733887200905441228563222628667867642522,1538556181219649071143342445458121679453571101710007225⟩
def resval2Tail76 : Box := ⟨-23947291661552361504596834659305399449909759227104,388686228458157817308460078723770849255885845081397⟩
def resval2Tail80 : Box := ⟨-4757515725543396803142896532009925783758565304050,661533644259924382806917551499173868228877741961650⟩
def resval2Tail84 : Box := ⟨-10914184651124726975254250503446856340668800714863,1125747306447318789185684254605527398761767189560079⟩
def resval2Tail88 : Box := ⟨-25043659921482513787391314599297836654440840449544,1914050661337435717252252599616761382888371085225136⟩
def resval2Tail92 : Box := ⟨-57465120147428620534383439860745337570247983859720,3250544184255365899066216132642376773307007826199453⟩
def resval2Tail96 : Box := ⟨-131859322642104752376826853014558312895454733921893,5511458507775970356623524692632972929348215726527533⟩
def resval2Tail100 : Box := ⟨-302564075791217329619283349880074529087305852613639,9324687000173978159896546351458034925533472975734872⟩
def resval2Tail104 : Box := ⟨-694262780401709240771037951246353682649379247673408,15729402528700098603820050438319277601247047621188802⟩
def resval2Tail108 : Box := ⟨-1593053659760036994433602563605969558475070632362240,26424994281131676839856956742051642834084201056968146⟩
def resval2Tail112 : Box := ⟨-3655416989812464003607774290615557835946430043502549,44142135848959905783953894347904752504076348609202704⟩
def resval2Tail116 : Box := ⟨-8387710788990218863422643479518667452400674582920308,73152804174613124180578493317726747009533322755218088⟩
def resval2Tail120 : Box := ⟨-19246420442815832220164035828896438006266169986373562,119858098212294244055623554983915442087176952627262719⟩
def resval2Tail124 : Box := ⟨-44162788772815321409786605088449099771789000556356565,193143378828738561667207402257441427473635756183255551⟩
def resval2Tail128 : Box := ⟨-101335825952005382995463475987551204147424036981394827,303498019319116964946963111015672848186344126000363023⟩
def resval2Tail132 : Box := ⟨-232524935737221649522841087665130377589860769833013891,458103731580782363983229667392929211511738209321609481⟩
def resval2Tail136 : Box := ⟨-533551142768896747764877973516777478037414845094318356,644630873617783485245088805949045502084457667707423516⟩
def resval2Tail140 : Box := ⟨-1224285175668236018403588746840934788604774328451983756,785641364443066865793442580151613179169987844291460576⟩
def resval2Tail144 : Box := ⟨-2836600398332521940064683514103466800354898924397990476,615534205074132091575762156922596716948732765529571437⟩
def resval2Tail148 : Box := ⟨46362965118763244933773929277755197192368263,36910837914375708773385699849304348172208431⟩
def resval2Tail152 : Box := ⟨465285813051584663530297342944835026500907,61652589461788919001492276313648556284213305⟩
def resval2Tail156 : Box := ⟨1065976875035356090042454333000688759860589,104903117116296355551349283372542982878821950⟩
def resval2Tail160 : Box := ⟨2445987433656958045838980565735034693167175,178332608206045501340652665302779465645859068⟩
def resval2Tail164 : Box := ⟨5612556718302585369590794948071627223708133,302787746379940035963500138480246064799902528⟩
def resval2Tail168 : Box := ⟨12878558772121316094959526412217780262096330,513238742973148904238419160911498630490231110⟩
def resval2Tail172 : Box := ⟨29551109123971162694951208226039946989166285,867981780483953316726328921565275906761134957⟩
def resval2Tail176 : Box := ⟨67807901948411260510114257759811301217790364,1463343583196969272722723771872199547456501766⟩
def resval2Tail180 : Box := ⟨155591844196319469072614690182189479616839662,2456484991770143947503947874922578171270556255⟩
def resval2Tail184 : Box := ⟨357020661085045786984084018641603005194870177,4099067102396267896499985066279753884976943189⟩
def resval2Tail188 : Box := ⟨819218726405572658347237927571315724337024705,6782670269520899997813655198393332207089356233⟩
def resval2Tail192 : Box := ⟨1879777264581618631817412690034941508483356443,11088709752209231847086195472168736346050443005⟩
def resval2Tail196 : Box := ⟨4313332264683342977005835164536851028504019241,17810334049675392369794161470081061560023742478⟩
def resval2Tail200 : Box := ⟨9897361552406693374916692656557783749401433516,27844636458261103471955823375473678554408223404⟩
def resval2Tail204 : Box := ⟨22710461352842179983987429271338136405375276263,41675721009379945781143557132275768703821881337⟩
def resval2Tail208 : Box := ⟨52111368482197780028209542779029158091171478978,57728616089094963161613814851978326284084748464⟩
def resval2Tail212 : Box := ⟨119574617321503354793041530516452320784019557637,67807547124904973907469488553466144277681838515⟩
def resval2Tail216 : Box := ⟨274376361193581884078097855061180607822110583836,45289951641336223007860259347376484630333673357⟩
theorem resval2H216 : resval2Tail216=hornerBox Q residualBox cell2 216 4 :=
  hornerChunk_step Q residualBox cell2 resval2Tail216 zero 216 4 0 (by decide +kernel) rfl
theorem resval2H212 : resval2Tail212=hornerBox Q residualBox cell2 212 8 :=
  hornerChunk_step Q residualBox cell2 resval2Tail212 resval2Tail216 212 4 4 (by decide +kernel) resval2H216
theorem resval2H208 : resval2Tail208=hornerBox Q residualBox cell2 208 12 :=
  hornerChunk_step Q residualBox cell2 resval2Tail208 resval2Tail212 208 4 8 (by decide +kernel) resval2H212
theorem resval2H204 : resval2Tail204=hornerBox Q residualBox cell2 204 16 :=
  hornerChunk_step Q residualBox cell2 resval2Tail204 resval2Tail208 204 4 12 (by decide +kernel) resval2H208
theorem resval2H200 : resval2Tail200=hornerBox Q residualBox cell2 200 20 :=
  hornerChunk_step Q residualBox cell2 resval2Tail200 resval2Tail204 200 4 16 (by decide +kernel) resval2H204
theorem resval2H196 : resval2Tail196=hornerBox Q residualBox cell2 196 24 :=
  hornerChunk_step Q residualBox cell2 resval2Tail196 resval2Tail200 196 4 20 (by decide +kernel) resval2H200
theorem resval2H192 : resval2Tail192=hornerBox Q residualBox cell2 192 28 :=
  hornerChunk_step Q residualBox cell2 resval2Tail192 resval2Tail196 192 4 24 (by decide +kernel) resval2H196
theorem resval2H188 : resval2Tail188=hornerBox Q residualBox cell2 188 32 :=
  hornerChunk_step Q residualBox cell2 resval2Tail188 resval2Tail192 188 4 28 (by decide +kernel) resval2H192
theorem resval2H184 : resval2Tail184=hornerBox Q residualBox cell2 184 36 :=
  hornerChunk_step Q residualBox cell2 resval2Tail184 resval2Tail188 184 4 32 (by decide +kernel) resval2H188
theorem resval2H180 : resval2Tail180=hornerBox Q residualBox cell2 180 40 :=
  hornerChunk_step Q residualBox cell2 resval2Tail180 resval2Tail184 180 4 36 (by decide +kernel) resval2H184
theorem resval2H176 : resval2Tail176=hornerBox Q residualBox cell2 176 44 :=
  hornerChunk_step Q residualBox cell2 resval2Tail176 resval2Tail180 176 4 40 (by decide +kernel) resval2H180
theorem resval2H172 : resval2Tail172=hornerBox Q residualBox cell2 172 48 :=
  hornerChunk_step Q residualBox cell2 resval2Tail172 resval2Tail176 172 4 44 (by decide +kernel) resval2H176
theorem resval2H168 : resval2Tail168=hornerBox Q residualBox cell2 168 52 :=
  hornerChunk_step Q residualBox cell2 resval2Tail168 resval2Tail172 168 4 48 (by decide +kernel) resval2H172
theorem resval2H164 : resval2Tail164=hornerBox Q residualBox cell2 164 56 :=
  hornerChunk_step Q residualBox cell2 resval2Tail164 resval2Tail168 164 4 52 (by decide +kernel) resval2H168
theorem resval2H160 : resval2Tail160=hornerBox Q residualBox cell2 160 60 :=
  hornerChunk_step Q residualBox cell2 resval2Tail160 resval2Tail164 160 4 56 (by decide +kernel) resval2H164
theorem resval2H156 : resval2Tail156=hornerBox Q residualBox cell2 156 64 :=
  hornerChunk_step Q residualBox cell2 resval2Tail156 resval2Tail160 156 4 60 (by decide +kernel) resval2H160
theorem resval2H152 : resval2Tail152=hornerBox Q residualBox cell2 152 68 :=
  hornerChunk_step Q residualBox cell2 resval2Tail152 resval2Tail156 152 4 64 (by decide +kernel) resval2H156
theorem resval2H148 : resval2Tail148=hornerBox Q residualBox cell2 148 72 :=
  hornerChunk_step Q residualBox cell2 resval2Tail148 resval2Tail152 148 4 68 (by decide +kernel) resval2H152
theorem resval2H144 : resval2Tail144=hornerBox Q residualBox cell2 144 76 :=
  hornerChunk_step Q residualBox cell2 resval2Tail144 resval2Tail148 144 4 72 (by decide +kernel) resval2H148
theorem resval2H140 : resval2Tail140=hornerBox Q residualBox cell2 140 80 :=
  hornerChunk_step Q residualBox cell2 resval2Tail140 resval2Tail144 140 4 76 (by decide +kernel) resval2H144
theorem resval2H136 : resval2Tail136=hornerBox Q residualBox cell2 136 84 :=
  hornerChunk_step Q residualBox cell2 resval2Tail136 resval2Tail140 136 4 80 (by decide +kernel) resval2H140
theorem resval2H132 : resval2Tail132=hornerBox Q residualBox cell2 132 88 :=
  hornerChunk_step Q residualBox cell2 resval2Tail132 resval2Tail136 132 4 84 (by decide +kernel) resval2H136
theorem resval2H128 : resval2Tail128=hornerBox Q residualBox cell2 128 92 :=
  hornerChunk_step Q residualBox cell2 resval2Tail128 resval2Tail132 128 4 88 (by decide +kernel) resval2H132
theorem resval2H124 : resval2Tail124=hornerBox Q residualBox cell2 124 96 :=
  hornerChunk_step Q residualBox cell2 resval2Tail124 resval2Tail128 124 4 92 (by decide +kernel) resval2H128
theorem resval2H120 : resval2Tail120=hornerBox Q residualBox cell2 120 100 :=
  hornerChunk_step Q residualBox cell2 resval2Tail120 resval2Tail124 120 4 96 (by decide +kernel) resval2H124
theorem resval2H116 : resval2Tail116=hornerBox Q residualBox cell2 116 104 :=
  hornerChunk_step Q residualBox cell2 resval2Tail116 resval2Tail120 116 4 100 (by decide +kernel) resval2H120
theorem resval2H112 : resval2Tail112=hornerBox Q residualBox cell2 112 108 :=
  hornerChunk_step Q residualBox cell2 resval2Tail112 resval2Tail116 112 4 104 (by decide +kernel) resval2H116
theorem resval2H108 : resval2Tail108=hornerBox Q residualBox cell2 108 112 :=
  hornerChunk_step Q residualBox cell2 resval2Tail108 resval2Tail112 108 4 108 (by decide +kernel) resval2H112
theorem resval2H104 : resval2Tail104=hornerBox Q residualBox cell2 104 116 :=
  hornerChunk_step Q residualBox cell2 resval2Tail104 resval2Tail108 104 4 112 (by decide +kernel) resval2H108
theorem resval2H100 : resval2Tail100=hornerBox Q residualBox cell2 100 120 :=
  hornerChunk_step Q residualBox cell2 resval2Tail100 resval2Tail104 100 4 116 (by decide +kernel) resval2H104
theorem resval2H96 : resval2Tail96=hornerBox Q residualBox cell2 96 124 :=
  hornerChunk_step Q residualBox cell2 resval2Tail96 resval2Tail100 96 4 120 (by decide +kernel) resval2H100
theorem resval2H92 : resval2Tail92=hornerBox Q residualBox cell2 92 128 :=
  hornerChunk_step Q residualBox cell2 resval2Tail92 resval2Tail96 92 4 124 (by decide +kernel) resval2H96
theorem resval2H88 : resval2Tail88=hornerBox Q residualBox cell2 88 132 :=
  hornerChunk_step Q residualBox cell2 resval2Tail88 resval2Tail92 88 4 128 (by decide +kernel) resval2H92
theorem resval2H84 : resval2Tail84=hornerBox Q residualBox cell2 84 136 :=
  hornerChunk_step Q residualBox cell2 resval2Tail84 resval2Tail88 84 4 132 (by decide +kernel) resval2H88
theorem resval2H80 : resval2Tail80=hornerBox Q residualBox cell2 80 140 :=
  hornerChunk_step Q residualBox cell2 resval2Tail80 resval2Tail84 80 4 136 (by decide +kernel) resval2H84
theorem resval2H76 : resval2Tail76=hornerBox Q residualBox cell2 76 144 :=
  hornerChunk_step Q residualBox cell2 resval2Tail76 resval2Tail80 76 4 140 (by decide +kernel) resval2H80
theorem resval2H72 : resval2Tail72=hornerBox Q residualBox cell2 72 148 :=
  hornerChunk_step Q residualBox cell2 resval2Tail72 resval2Tail76 72 4 144 (by decide +kernel) resval2H76
theorem resval2H68 : resval2Tail68=hornerBox Q residualBox cell2 68 152 :=
  hornerChunk_step Q residualBox cell2 resval2Tail68 resval2Tail72 68 4 148 (by decide +kernel) resval2H72
theorem resval2H64 : resval2Tail64=hornerBox Q residualBox cell2 64 156 :=
  hornerChunk_step Q residualBox cell2 resval2Tail64 resval2Tail68 64 4 152 (by decide +kernel) resval2H68
theorem resval2H60 : resval2Tail60=hornerBox Q residualBox cell2 60 160 :=
  hornerChunk_step Q residualBox cell2 resval2Tail60 resval2Tail64 60 4 156 (by decide +kernel) resval2H64
theorem resval2H56 : resval2Tail56=hornerBox Q residualBox cell2 56 164 :=
  hornerChunk_step Q residualBox cell2 resval2Tail56 resval2Tail60 56 4 160 (by decide +kernel) resval2H60
theorem resval2H52 : resval2Tail52=hornerBox Q residualBox cell2 52 168 :=
  hornerChunk_step Q residualBox cell2 resval2Tail52 resval2Tail56 52 4 164 (by decide +kernel) resval2H56
theorem resval2H48 : resval2Tail48=hornerBox Q residualBox cell2 48 172 :=
  hornerChunk_step Q residualBox cell2 resval2Tail48 resval2Tail52 48 4 168 (by decide +kernel) resval2H52
theorem resval2H44 : resval2Tail44=hornerBox Q residualBox cell2 44 176 :=
  hornerChunk_step Q residualBox cell2 resval2Tail44 resval2Tail48 44 4 172 (by decide +kernel) resval2H48
theorem resval2H40 : resval2Tail40=hornerBox Q residualBox cell2 40 180 :=
  hornerChunk_step Q residualBox cell2 resval2Tail40 resval2Tail44 40 4 176 (by decide +kernel) resval2H44
theorem resval2H36 : resval2Tail36=hornerBox Q residualBox cell2 36 184 :=
  hornerChunk_step Q residualBox cell2 resval2Tail36 resval2Tail40 36 4 180 (by decide +kernel) resval2H40
theorem resval2H32 : resval2Tail32=hornerBox Q residualBox cell2 32 188 :=
  hornerChunk_step Q residualBox cell2 resval2Tail32 resval2Tail36 32 4 184 (by decide +kernel) resval2H36
theorem resval2H28 : resval2Tail28=hornerBox Q residualBox cell2 28 192 :=
  hornerChunk_step Q residualBox cell2 resval2Tail28 resval2Tail32 28 4 188 (by decide +kernel) resval2H32
theorem resval2H24 : resval2Tail24=hornerBox Q residualBox cell2 24 196 :=
  hornerChunk_step Q residualBox cell2 resval2Tail24 resval2Tail28 24 4 192 (by decide +kernel) resval2H28
theorem resval2H20 : resval2Tail20=hornerBox Q residualBox cell2 20 200 :=
  hornerChunk_step Q residualBox cell2 resval2Tail20 resval2Tail24 20 4 196 (by decide +kernel) resval2H24
theorem resval2H16 : resval2Tail16=hornerBox Q residualBox cell2 16 204 :=
  hornerChunk_step Q residualBox cell2 resval2Tail16 resval2Tail20 16 4 200 (by decide +kernel) resval2H20
theorem resval2H12 : resval2Tail12=hornerBox Q residualBox cell2 12 208 :=
  hornerChunk_step Q residualBox cell2 resval2Tail12 resval2Tail16 12 4 204 (by decide +kernel) resval2H16
theorem resval2H8 : resval2Tail8=hornerBox Q residualBox cell2 8 212 :=
  hornerChunk_step Q residualBox cell2 resval2Tail8 resval2Tail12 8 4 208 (by decide +kernel) resval2H12
theorem resval2H4 : resval2Tail4=hornerBox Q residualBox cell2 4 216 :=
  hornerChunk_step Q residualBox cell2 resval2Tail4 resval2Tail8 4 4 212 (by decide +kernel) resval2H8
theorem resval2H0 : resval2=hornerBox Q residualBox cell2 0 220 :=
  hornerChunk_step Q residualBox cell2 resval2 resval2Tail4 0 4 216 (by decide +kernel) resval2H4
theorem resval2_eq : resval2=hornerBox Q residualBox cell2 0 220 := resval2H0
def polyval2Tail5 : Box := ⟨21177969692476918589169129179192726571104889029368398,2972057300746676324646001108696560004169596378043112277⟩
def polyval2Tail9 : Box := ⟨44460297333357195520394773777414614880201198741481127,5058775532043115134418459114841566250210634085969103339⟩
def polyval2Tail13 : Box := ⟨102018133487234742454844962566744662670771206798672815,8603876624964510865140034866923681822533672282073086009⟩
def polyval2Tail17 : Box := ⟨234090556673904537385165317635920568345351829413093210,14617781550850988524826907561921756365381046855687614192⟩
def polyval2Tail21 : Box := ⟨537143612694205220971289961554649186160517482274386193,24799494518259793367301723940579163255924634903549425295⟩
def polyval2Tail25 : Box := ⟨1232528405921613567461671550750115544010938141522870285,41990657676705443158467723109366942949552255218712300895⟩
def polyval2Tail29 : Box := ⟨2828156633538001467047850482642107730393670909890344621,70908690594467172996643709337651842815096750492666213534⟩
def polyval2Tail33 : Box := ⟨6489481220389568419119058421268948727456091381058116518,119302324796232336856395058091907211690627551910800181069⟩
def polyval2Tail37 : Box := ⟨14890747566942710543174548410430057248251344915235313005,199704520006603030398788322755720292220423900677692183008⟩
def polyval2Tail41 : Box := ⟨34168272558634413295386487998704926766898126652989474481,331921779911687683704101022245331958031361483174469666555⟩
def polyval2Tail45 : Box := ⟨78402433752412902550387651693033715121863059190230886845,546131033518907092997147099459615710593063727362166658189⟩
def polyval2Tail49 : Box := ⟨179902030685134693530706228281749831733417722592439041859,885524492406629863646535207775830302516365362546102459712⟩
def polyval2Tail53 : Box := ⟨412802754909876659947168066050498541190289267148874229541,1404767856745211897637696018339048300971548201193053520541⟩
def polyval2Tail57 : Box := ⟨947216181008146681379134183339236277404433801824985505953,2153479039874503367875269884583319088730411058076068325618⟩
def polyval2Tail61 : Box := ⟨2173479907515493799189862664710398968338008989288756290978,3116169248975694126814548123727727155532222781936314027885⟩
def polyval2Tail65 : Box := ⟨4987261623159072201176517849425136715900633433956035412874,4036646308950605230173002359158441688906354539313226968584⟩
def polyval2Tail69 : Box := ⟨11443758224973014419075446172639372290405978614474133940931,3950630344118234841582694561555081469427873718261805046988⟩
def polyval2Tail73 : Box := ⟨26281250000000000000000000000000000000000000000000000000000,2⟩
theorem polyval2H73 : polyval2Tail73=hornerBox Q polyBox cell2 73 1 :=
  hornerChunk_step Q polyBox cell2 polyval2Tail73 zero 73 1 0 (by decide +kernel) rfl
theorem polyval2H69 : polyval2Tail69=hornerBox Q polyBox cell2 69 5 :=
  hornerChunk_step Q polyBox cell2 polyval2Tail69 polyval2Tail73 69 4 1 (by decide +kernel) polyval2H73
theorem polyval2H65 : polyval2Tail65=hornerBox Q polyBox cell2 65 9 :=
  hornerChunk_step Q polyBox cell2 polyval2Tail65 polyval2Tail69 65 4 5 (by decide +kernel) polyval2H69
theorem polyval2H61 : polyval2Tail61=hornerBox Q polyBox cell2 61 13 :=
  hornerChunk_step Q polyBox cell2 polyval2Tail61 polyval2Tail65 61 4 9 (by decide +kernel) polyval2H65
theorem polyval2H57 : polyval2Tail57=hornerBox Q polyBox cell2 57 17 :=
  hornerChunk_step Q polyBox cell2 polyval2Tail57 polyval2Tail61 57 4 13 (by decide +kernel) polyval2H61
theorem polyval2H53 : polyval2Tail53=hornerBox Q polyBox cell2 53 21 :=
  hornerChunk_step Q polyBox cell2 polyval2Tail53 polyval2Tail57 53 4 17 (by decide +kernel) polyval2H57
theorem polyval2H49 : polyval2Tail49=hornerBox Q polyBox cell2 49 25 :=
  hornerChunk_step Q polyBox cell2 polyval2Tail49 polyval2Tail53 49 4 21 (by decide +kernel) polyval2H53
theorem polyval2H45 : polyval2Tail45=hornerBox Q polyBox cell2 45 29 :=
  hornerChunk_step Q polyBox cell2 polyval2Tail45 polyval2Tail49 45 4 25 (by decide +kernel) polyval2H49
theorem polyval2H41 : polyval2Tail41=hornerBox Q polyBox cell2 41 33 :=
  hornerChunk_step Q polyBox cell2 polyval2Tail41 polyval2Tail45 41 4 29 (by decide +kernel) polyval2H45
theorem polyval2H37 : polyval2Tail37=hornerBox Q polyBox cell2 37 37 :=
  hornerChunk_step Q polyBox cell2 polyval2Tail37 polyval2Tail41 37 4 33 (by decide +kernel) polyval2H41
theorem polyval2H33 : polyval2Tail33=hornerBox Q polyBox cell2 33 41 :=
  hornerChunk_step Q polyBox cell2 polyval2Tail33 polyval2Tail37 33 4 37 (by decide +kernel) polyval2H37
theorem polyval2H29 : polyval2Tail29=hornerBox Q polyBox cell2 29 45 :=
  hornerChunk_step Q polyBox cell2 polyval2Tail29 polyval2Tail33 29 4 41 (by decide +kernel) polyval2H33
theorem polyval2H25 : polyval2Tail25=hornerBox Q polyBox cell2 25 49 :=
  hornerChunk_step Q polyBox cell2 polyval2Tail25 polyval2Tail29 25 4 45 (by decide +kernel) polyval2H29
theorem polyval2H21 : polyval2Tail21=hornerBox Q polyBox cell2 21 53 :=
  hornerChunk_step Q polyBox cell2 polyval2Tail21 polyval2Tail25 21 4 49 (by decide +kernel) polyval2H25
theorem polyval2H17 : polyval2Tail17=hornerBox Q polyBox cell2 17 57 :=
  hornerChunk_step Q polyBox cell2 polyval2Tail17 polyval2Tail21 17 4 53 (by decide +kernel) polyval2H21
theorem polyval2H13 : polyval2Tail13=hornerBox Q polyBox cell2 13 61 :=
  hornerChunk_step Q polyBox cell2 polyval2Tail13 polyval2Tail17 13 4 57 (by decide +kernel) polyval2H17
theorem polyval2H9 : polyval2Tail9=hornerBox Q polyBox cell2 9 65 :=
  hornerChunk_step Q polyBox cell2 polyval2Tail9 polyval2Tail13 9 4 61 (by decide +kernel) polyval2H13
theorem polyval2H5 : polyval2Tail5=hornerBox Q polyBox cell2 5 69 :=
  hornerChunk_step Q polyBox cell2 polyval2Tail5 polyval2Tail9 5 4 65 (by decide +kernel) polyval2H9
theorem polyval2H1 : polyval2=hornerBox Q polyBox cell2 1 73 :=
  hornerChunk_step Q polyBox cell2 polyval2 polyval2Tail5 1 4 69 (by decide +kernel) polyval2H5
theorem polyval2_eq : polyval2=hornerBox Q polyBox cell2 1 73 := polyval2H1
theorem polyval2_upper : 5*(polyval2.center+polyval2.radius)<Q := by decide +kernel
theorem resval2_pos : 0<(resval2).center-(resval2).radius := by decide +kernel
theorem polyval2_pos : 0<(polyval2).center-(polyval2).radius := by decide +kernel
def cell3 : Box := ⟨906250000000000000000000000000000000000000000000000000000000,31250000000000000000000000000000000000000000000000000000002⟩
def resval3 : Box := ⟨104954696287013794017164498673824572190455327386744570910,1959787903820309326602477116780645230498138065664429685⟩
def polyval3 : Box := ⟨3712995638416492479523579564080645525441162385956712598403,235559964768728462271706231600105828937586343607857720442⟩
theorem cell3_lo : Holds Q cell3 (7/8:ℝ) := by norm_num [Holds,Q,cell3]
theorem cell3_hi : Holds Q cell3 (15/16:ℝ) := by norm_num [Holds,Q,cell3]
def resval3Tail4 : Box := ⟨-199497148195635511506672768362009983551323536492944878,2056106982726396083740285000643307192545809615210845247⟩
def resval3Tail8 : Box := ⟨-295833391650301267843059360037161193579476461014902579,2624192307927234946639257253486954010324273297218216808⟩
def resval3Tail12 : Box := ⟨-438586360654005421255313274212804460207826571446228999,3341498667808738838006321194807026270326956604224759953⟩
def resval3Tail16 : Box := ⟨-650224071781010895230871398258391731720627671575683534,4243240667489798225561477208249735644993698269182345311⟩
def resval3Tail20 : Box := ⟨-963986529104924368150252112425028297962595294847842160,5370790856630435666863829925007630986873589122449000165⟩
def resval3Tail24 : Box := ⟨-1429153531259464551506810725839286351415344249516494093,6771458236672437965985550946256815033015855473424492332⟩
def resval3Tail28 : Box := ⟨-2118784603564812722731654917512225284637539928393535609,8497221180596869522992891389136493326592606879232835981⟩
def resval3Tail32 : Box := ⟨-3141193789268447853160452580733283216833887990417986636,10601631989908243656519862101581336250783118557623745697⟩
def resval3Tail36 : Box := ⟨-4656961545377229101527018665569329656587243177857639942,13133652385765954202777462693374155695245836048316242750⟩
def resval3Tail40 : Box := ⟨-6904155645924990749601787785363051430862840524791905756,16126474963287842060833205005780783714242087050964122732⟩
def resval3Tail44 : Box := ⟨-10235722309211534171185646341733542462984469888726665740,19578310433610632960649870902080217760559647130284917166⟩
def resval3Tail48 : Box := ⟨-15174920231285434860424739096047415478011516691411522532,23420486185180610472915859312732551175089365450853609018⟩
def resval3Tail52 : Box := ⟨-22497504042156308599811157662790448324382908429675926664,27465726672105790033560480226132781996337328228785919027⟩
def resval3Tail56 : Box := ⟨-33353564988325842684501903559631503191073579936249885137,31325749344313774787616649852636556308548542088419008647⟩
def resval3Tail60 : Box := ⟨-49448165242948575352606590184097333065956690668489200984,34281682541817855453184692168778334197646948283229540128⟩
def resval3Tail64 : Box := ⟨-73309136420411688539923411896807026766274420030381652460,35082356010706118570448772172236336010012963101612221682⟩
def resval3Tail68 : Box := ⟨-108684073182904872140577556494433865303190975763112782422,31632830073255321158742812741433803348207366316281622846⟩
def resval3Tail72 : Box := ⟨727627055707765767193711786447988721824077807023541874658,1345809040886080875532326307863581359229423379862917562⟩
def resval3Tail76 : Box := ⟨-2388215619195024629375469479713010429272163346154761,25326469826109223075378213421192380890341734878811516⟩
def resval3Tail80 : Box := ⟨-3508380722333995496742688498637205716128051181098680,32340873188346468385008973889454556087042748998095063⟩
def resval3Tail84 : Box := ⟨-5201331209968821597506698449983418655569815557826399,41206898619821538232812453790942453497498626633828037⟩
def resval3Tail88 : Box := ⟨-7711208238712087898043090401518993949437818179752533,52366021392701935736764549720829343428392296823816448⟩
def resval3Tail92 : Box := ⟨-11432214197913501214253701761728302715571710269157682,66340058811948501165885852654473535945004657161781930⟩
def resval3Tail96 : Box := ⟨-16948773450426826346398913726569301443823264135590402,83730410430547305667518351239131171938257373534810839⟩
def resval3Tail100 : Box := ⟨-25127321488283666003975673109306802937378851523160655,105205735199588347739416101665410105201163759422618695⟩
def resval3Tail104 : Box := ⟨-37252388028094255811814359465364432127752972354876083,131468741909612021547251887948809717749255741027981508⟩
def resval3Tail108 : Box := ⟨-55228346341760859374690688300188564422383685224807930,163187613591029631346853833613432753492253225622504122⟩
def resval3Tail112 : Box := ⟨-81878515743612842532451792861932578271212981315379696,200869303518715208822800187875769878210560039540849823⟩
def resval3Tail116 : Box := ⟨-121388594525195191123073607348778040173550775730106109,244639278722724436998221796192401856020059503275447162⟩
def resval3Tail120 : Box := ⟨-179964069291909541955366667497641184959671516097344248,293873021101683756796271657422313346038984682592112629⟩
def resval3Tail124 : Box := ⟨-266804853971523821810923884720079429348027139259873336,346595394048911347474152754387761007395080319656175340⟩
def resval3Tail128 : Box := ⟨-395550236126864121185995090083405811873753075739816732,398519860747550502622433646959848341723532177945057528⟩
def resval3Tail132 : Box := ⟨-586421075070539696735061627617924826474206254492528633,441533055670435093547575394753854119249388834508293344⟩
def resval3Tail136 : Box := ⟨-869395707245786389589715358840625120572728155704298004,461330256456688226893756129634963238618284025481077098⟩
def resval3Tail140 : Box := ⟨-1288918407579362366358469665882951069012238100678244790,433757314222785537662629829627752181654594159631615454⟩
def resval3Tail144 : Box := ⟨-1935458118347009949541766172106136707260083560795522927,316379640851907111346458219983570798770105890106861094⟩
def resval3Tail148 : Box := ⟨469016797380425345183074356974986703300470086,4136343649312881717987273752196987194965054184⟩
def resval3Tail152 : Box := ⟨627146397671239481628580112471906285555014595,5274399445961246057160677202918320386168568765⟩
def resval3Tail156 : Box := ⟨929771768663967540128872700588373199716153228,6710004237769237109546534364217635675464598111⟩
def resval3Tail160 : Box := ⟨1378428604596178710285810601798544039548483659,8511553821952047455861071880027218671090270743⟩
def resval3Tail164 : Box := ⟨2043582610720092991845313770679474669659611393,10759378145946442320105128126292398057074216348⟩
def resval3Tail168 : Box := ⟨3029703441232594035475860975159988137063031813,13544219248128352780294728178942031128788191258⟩
def resval3Tail172 : Box := ⟨4491672073184361646453485919829716666448185617,16963905158814828639192617714995916676965842147⟩
def resval3Tail176 : Box := ⟨6659106544373969039450632950370058723282058922,21115959321824528431074295239356022169087180645⟩
def resval3Tail180 : Box := ⟨9872425957820836356884764645451190862077361910,26083459802321084239943729674267870327132400126⟩
def resval3Tail184 : Box := ⟨14636316995858705809603306570988877517292654213,31909953210100028180129824775447731764680169334⟩
def resval3Tail188 : Box := ⟨21699000440064894013867041673381018310088960521,38556927742013359630582524486284361884551243420⟩
def resval3Tail192 : Box := ⟨32169747364119050710640837978312628408378180522,45833857758659821997498745155389131887604395918⟩
def resval3Tail196 : Box := ⟨47693102192874540275733981241503776251058474669,53285549961721730379806814788041653118016696141⟩
def resval3Tail200 : Box := ⟨70707176249603218581774705676752839882936590542,60013553579604113741752325232377204148848144902⟩
def resval3Tail204 : Box := ⟨104826579595809805105918330287590312746585876982,64396408060228363828404961190317925872347088099⟩
def resval3Tail208 : Box := ⟨155410134764344121859931629457748662537441031654,63655499191732111273721452098154191638916565271⟩
def resval3Tail212 : Box := ⟨230402538002903331807625894823950844410529159855,53186309159136189900551405902299355259015706941⟩
def resval3Tail216 : Box := ⟨341582826987427056329286388776390756113974469062,25534363529166105980250361531455510449919988363⟩
theorem resval3H216 : resval3Tail216=hornerBox Q residualBox cell3 216 4 :=
  hornerChunk_step Q residualBox cell3 resval3Tail216 zero 216 4 0 (by decide +kernel) rfl
theorem resval3H212 : resval3Tail212=hornerBox Q residualBox cell3 212 8 :=
  hornerChunk_step Q residualBox cell3 resval3Tail212 resval3Tail216 212 4 4 (by decide +kernel) resval3H216
theorem resval3H208 : resval3Tail208=hornerBox Q residualBox cell3 208 12 :=
  hornerChunk_step Q residualBox cell3 resval3Tail208 resval3Tail212 208 4 8 (by decide +kernel) resval3H212
theorem resval3H204 : resval3Tail204=hornerBox Q residualBox cell3 204 16 :=
  hornerChunk_step Q residualBox cell3 resval3Tail204 resval3Tail208 204 4 12 (by decide +kernel) resval3H208
theorem resval3H200 : resval3Tail200=hornerBox Q residualBox cell3 200 20 :=
  hornerChunk_step Q residualBox cell3 resval3Tail200 resval3Tail204 200 4 16 (by decide +kernel) resval3H204
theorem resval3H196 : resval3Tail196=hornerBox Q residualBox cell3 196 24 :=
  hornerChunk_step Q residualBox cell3 resval3Tail196 resval3Tail200 196 4 20 (by decide +kernel) resval3H200
theorem resval3H192 : resval3Tail192=hornerBox Q residualBox cell3 192 28 :=
  hornerChunk_step Q residualBox cell3 resval3Tail192 resval3Tail196 192 4 24 (by decide +kernel) resval3H196
theorem resval3H188 : resval3Tail188=hornerBox Q residualBox cell3 188 32 :=
  hornerChunk_step Q residualBox cell3 resval3Tail188 resval3Tail192 188 4 28 (by decide +kernel) resval3H192
theorem resval3H184 : resval3Tail184=hornerBox Q residualBox cell3 184 36 :=
  hornerChunk_step Q residualBox cell3 resval3Tail184 resval3Tail188 184 4 32 (by decide +kernel) resval3H188
theorem resval3H180 : resval3Tail180=hornerBox Q residualBox cell3 180 40 :=
  hornerChunk_step Q residualBox cell3 resval3Tail180 resval3Tail184 180 4 36 (by decide +kernel) resval3H184
theorem resval3H176 : resval3Tail176=hornerBox Q residualBox cell3 176 44 :=
  hornerChunk_step Q residualBox cell3 resval3Tail176 resval3Tail180 176 4 40 (by decide +kernel) resval3H180
theorem resval3H172 : resval3Tail172=hornerBox Q residualBox cell3 172 48 :=
  hornerChunk_step Q residualBox cell3 resval3Tail172 resval3Tail176 172 4 44 (by decide +kernel) resval3H176
theorem resval3H168 : resval3Tail168=hornerBox Q residualBox cell3 168 52 :=
  hornerChunk_step Q residualBox cell3 resval3Tail168 resval3Tail172 168 4 48 (by decide +kernel) resval3H172
theorem resval3H164 : resval3Tail164=hornerBox Q residualBox cell3 164 56 :=
  hornerChunk_step Q residualBox cell3 resval3Tail164 resval3Tail168 164 4 52 (by decide +kernel) resval3H168
theorem resval3H160 : resval3Tail160=hornerBox Q residualBox cell3 160 60 :=
  hornerChunk_step Q residualBox cell3 resval3Tail160 resval3Tail164 160 4 56 (by decide +kernel) resval3H164
theorem resval3H156 : resval3Tail156=hornerBox Q residualBox cell3 156 64 :=
  hornerChunk_step Q residualBox cell3 resval3Tail156 resval3Tail160 156 4 60 (by decide +kernel) resval3H160
theorem resval3H152 : resval3Tail152=hornerBox Q residualBox cell3 152 68 :=
  hornerChunk_step Q residualBox cell3 resval3Tail152 resval3Tail156 152 4 64 (by decide +kernel) resval3H156
theorem resval3H148 : resval3Tail148=hornerBox Q residualBox cell3 148 72 :=
  hornerChunk_step Q residualBox cell3 resval3Tail148 resval3Tail152 148 4 68 (by decide +kernel) resval3H152
theorem resval3H144 : resval3Tail144=hornerBox Q residualBox cell3 144 76 :=
  hornerChunk_step Q residualBox cell3 resval3Tail144 resval3Tail148 144 4 72 (by decide +kernel) resval3H148
theorem resval3H140 : resval3Tail140=hornerBox Q residualBox cell3 140 80 :=
  hornerChunk_step Q residualBox cell3 resval3Tail140 resval3Tail144 140 4 76 (by decide +kernel) resval3H144
theorem resval3H136 : resval3Tail136=hornerBox Q residualBox cell3 136 84 :=
  hornerChunk_step Q residualBox cell3 resval3Tail136 resval3Tail140 136 4 80 (by decide +kernel) resval3H140
theorem resval3H132 : resval3Tail132=hornerBox Q residualBox cell3 132 88 :=
  hornerChunk_step Q residualBox cell3 resval3Tail132 resval3Tail136 132 4 84 (by decide +kernel) resval3H136
theorem resval3H128 : resval3Tail128=hornerBox Q residualBox cell3 128 92 :=
  hornerChunk_step Q residualBox cell3 resval3Tail128 resval3Tail132 128 4 88 (by decide +kernel) resval3H132
theorem resval3H124 : resval3Tail124=hornerBox Q residualBox cell3 124 96 :=
  hornerChunk_step Q residualBox cell3 resval3Tail124 resval3Tail128 124 4 92 (by decide +kernel) resval3H128
theorem resval3H120 : resval3Tail120=hornerBox Q residualBox cell3 120 100 :=
  hornerChunk_step Q residualBox cell3 resval3Tail120 resval3Tail124 120 4 96 (by decide +kernel) resval3H124
theorem resval3H116 : resval3Tail116=hornerBox Q residualBox cell3 116 104 :=
  hornerChunk_step Q residualBox cell3 resval3Tail116 resval3Tail120 116 4 100 (by decide +kernel) resval3H120
theorem resval3H112 : resval3Tail112=hornerBox Q residualBox cell3 112 108 :=
  hornerChunk_step Q residualBox cell3 resval3Tail112 resval3Tail116 112 4 104 (by decide +kernel) resval3H116
theorem resval3H108 : resval3Tail108=hornerBox Q residualBox cell3 108 112 :=
  hornerChunk_step Q residualBox cell3 resval3Tail108 resval3Tail112 108 4 108 (by decide +kernel) resval3H112
theorem resval3H104 : resval3Tail104=hornerBox Q residualBox cell3 104 116 :=
  hornerChunk_step Q residualBox cell3 resval3Tail104 resval3Tail108 104 4 112 (by decide +kernel) resval3H108
theorem resval3H100 : resval3Tail100=hornerBox Q residualBox cell3 100 120 :=
  hornerChunk_step Q residualBox cell3 resval3Tail100 resval3Tail104 100 4 116 (by decide +kernel) resval3H104
theorem resval3H96 : resval3Tail96=hornerBox Q residualBox cell3 96 124 :=
  hornerChunk_step Q residualBox cell3 resval3Tail96 resval3Tail100 96 4 120 (by decide +kernel) resval3H100
theorem resval3H92 : resval3Tail92=hornerBox Q residualBox cell3 92 128 :=
  hornerChunk_step Q residualBox cell3 resval3Tail92 resval3Tail96 92 4 124 (by decide +kernel) resval3H96
theorem resval3H88 : resval3Tail88=hornerBox Q residualBox cell3 88 132 :=
  hornerChunk_step Q residualBox cell3 resval3Tail88 resval3Tail92 88 4 128 (by decide +kernel) resval3H92
theorem resval3H84 : resval3Tail84=hornerBox Q residualBox cell3 84 136 :=
  hornerChunk_step Q residualBox cell3 resval3Tail84 resval3Tail88 84 4 132 (by decide +kernel) resval3H88
theorem resval3H80 : resval3Tail80=hornerBox Q residualBox cell3 80 140 :=
  hornerChunk_step Q residualBox cell3 resval3Tail80 resval3Tail84 80 4 136 (by decide +kernel) resval3H84
theorem resval3H76 : resval3Tail76=hornerBox Q residualBox cell3 76 144 :=
  hornerChunk_step Q residualBox cell3 resval3Tail76 resval3Tail80 76 4 140 (by decide +kernel) resval3H80
theorem resval3H72 : resval3Tail72=hornerBox Q residualBox cell3 72 148 :=
  hornerChunk_step Q residualBox cell3 resval3Tail72 resval3Tail76 72 4 144 (by decide +kernel) resval3H76
theorem resval3H68 : resval3Tail68=hornerBox Q residualBox cell3 68 152 :=
  hornerChunk_step Q residualBox cell3 resval3Tail68 resval3Tail72 68 4 148 (by decide +kernel) resval3H72
theorem resval3H64 : resval3Tail64=hornerBox Q residualBox cell3 64 156 :=
  hornerChunk_step Q residualBox cell3 resval3Tail64 resval3Tail68 64 4 152 (by decide +kernel) resval3H68
theorem resval3H60 : resval3Tail60=hornerBox Q residualBox cell3 60 160 :=
  hornerChunk_step Q residualBox cell3 resval3Tail60 resval3Tail64 60 4 156 (by decide +kernel) resval3H64
theorem resval3H56 : resval3Tail56=hornerBox Q residualBox cell3 56 164 :=
  hornerChunk_step Q residualBox cell3 resval3Tail56 resval3Tail60 56 4 160 (by decide +kernel) resval3H60
theorem resval3H52 : resval3Tail52=hornerBox Q residualBox cell3 52 168 :=
  hornerChunk_step Q residualBox cell3 resval3Tail52 resval3Tail56 52 4 164 (by decide +kernel) resval3H56
theorem resval3H48 : resval3Tail48=hornerBox Q residualBox cell3 48 172 :=
  hornerChunk_step Q residualBox cell3 resval3Tail48 resval3Tail52 48 4 168 (by decide +kernel) resval3H52
theorem resval3H44 : resval3Tail44=hornerBox Q residualBox cell3 44 176 :=
  hornerChunk_step Q residualBox cell3 resval3Tail44 resval3Tail48 44 4 172 (by decide +kernel) resval3H48
theorem resval3H40 : resval3Tail40=hornerBox Q residualBox cell3 40 180 :=
  hornerChunk_step Q residualBox cell3 resval3Tail40 resval3Tail44 40 4 176 (by decide +kernel) resval3H44
theorem resval3H36 : resval3Tail36=hornerBox Q residualBox cell3 36 184 :=
  hornerChunk_step Q residualBox cell3 resval3Tail36 resval3Tail40 36 4 180 (by decide +kernel) resval3H40
theorem resval3H32 : resval3Tail32=hornerBox Q residualBox cell3 32 188 :=
  hornerChunk_step Q residualBox cell3 resval3Tail32 resval3Tail36 32 4 184 (by decide +kernel) resval3H36
theorem resval3H28 : resval3Tail28=hornerBox Q residualBox cell3 28 192 :=
  hornerChunk_step Q residualBox cell3 resval3Tail28 resval3Tail32 28 4 188 (by decide +kernel) resval3H32
theorem resval3H24 : resval3Tail24=hornerBox Q residualBox cell3 24 196 :=
  hornerChunk_step Q residualBox cell3 resval3Tail24 resval3Tail28 24 4 192 (by decide +kernel) resval3H28
theorem resval3H20 : resval3Tail20=hornerBox Q residualBox cell3 20 200 :=
  hornerChunk_step Q residualBox cell3 resval3Tail20 resval3Tail24 20 4 196 (by decide +kernel) resval3H24
theorem resval3H16 : resval3Tail16=hornerBox Q residualBox cell3 16 204 :=
  hornerChunk_step Q residualBox cell3 resval3Tail16 resval3Tail20 16 4 200 (by decide +kernel) resval3H20
theorem resval3H12 : resval3Tail12=hornerBox Q residualBox cell3 12 208 :=
  hornerChunk_step Q residualBox cell3 resval3Tail12 resval3Tail16 12 4 204 (by decide +kernel) resval3H16
theorem resval3H8 : resval3Tail8=hornerBox Q residualBox cell3 8 212 :=
  hornerChunk_step Q residualBox cell3 resval3Tail8 resval3Tail12 8 4 208 (by decide +kernel) resval3H12
theorem resval3H4 : resval3Tail4=hornerBox Q residualBox cell3 4 216 :=
  hornerChunk_step Q residualBox cell3 resval3Tail4 resval3Tail8 4 4 212 (by decide +kernel) resval3H8
theorem resval3H0 : resval3=hornerBox Q residualBox cell3 0 220 :=
  hornerChunk_step Q residualBox cell3 resval3 resval3Tail4 0 4 216 (by decide +kernel) resval3H4
theorem resval3_eq : resval3=hornerBox Q residualBox cell3 0 220 := resval3H0
def polyval3Tail5 : Box := ⟨32523866296156828481863120254996270058480865507645544302,293613139123529736227726540791829144771909420000983809315⟩
def polyval3Tail9 : Box := ⟨48215445239304845278483919151691659838430159435309903664,373979053958066505911407327891438211924477128515279402789⟩
def polyval3Tail13 : Box := ⟨71481573161095169287456580195922974019618146795568050947,475065363909527635804102302018696181687707015518523665463⟩
def polyval3Tail17 : Box := ⟨105974657963182303140064607874796472834516320424403875278,601551269303053613781136747067015533798242792399293346117⟩
def polyval3Tail21 : Box := ⟨157112212753349101603051303841982014743173356912509502062,758807178245564770620036551578117635499818439721620886786⟩
def polyval3Tail25 : Box := ⟨232925945416398551681810360810686967527567902406304874016,952766759936783064006009110120060083948075331829610431586⟩
def polyval3Tail29 : Box := ⟨345323225338932514268215262608943055575623891236472615191,1189601360103558554542119191917637412000142180833244651698⟩
def polyval3Tail33 : Box := ⟨511957264980957356515476025152743258540070594602980754674,1475061354901691427385597718596090867621253494629665032523⟩
def polyval3Tail37 : Box := ⟨758999748451707795154075251423767996564979739332377842334,1813271901378006194014136793002919357456359301997332786188⟩
def polyval3Tail41 : Box := ⟨1125251378493834774313590402593585136628540883587915677344,2204652717175106183594504182357514150524414390020321529078⟩
def polyval3Tail45 : Box := ⟨1668235947884293926051373384689841447389674795624207691192,2642452344733181918244628340246659355988983952600648329864⟩
def polyval3Tail49 : Box := ⟨2473235075293584003831228387326856807134319499326056625297,3107115896459085565201173850780949776021179204246395595456⟩
def polyval3Tail53 : Box := ⟨3666682608907980195468547798775608908803798931030785444701,3557295293013658380099636041764667688022958692993530824773⟩
def polyval3Tail57 : Box := ⟨5436022434249321351657721011691330669918442762643711279922,3915693433016584948308016521376737925900007387787915523232⟩
def polyval3Tail61 : Box := ⟨8059148570391992809152685641145684211303466810104683575295,4047005524958892895619059007814274771489124725526232419456⟩
def polyval3Tail65 : Box := ⟨11948051441152608326905780871936658080036091358303355898771,3723828357228903231309769347186730467267124114778938883008⟩
def polyval3Tail69 : Box := ⟨17713525471143398419203181713696888465094502572404663954285,2574322741096138366174905686142337313536669226255154871736⟩
def polyval3Tail73 : Box := ⟨26281250000000000000000000000000000000000000000000000000000,2⟩
theorem polyval3H73 : polyval3Tail73=hornerBox Q polyBox cell3 73 1 :=
  hornerChunk_step Q polyBox cell3 polyval3Tail73 zero 73 1 0 (by decide +kernel) rfl
theorem polyval3H69 : polyval3Tail69=hornerBox Q polyBox cell3 69 5 :=
  hornerChunk_step Q polyBox cell3 polyval3Tail69 polyval3Tail73 69 4 1 (by decide +kernel) polyval3H73
theorem polyval3H65 : polyval3Tail65=hornerBox Q polyBox cell3 65 9 :=
  hornerChunk_step Q polyBox cell3 polyval3Tail65 polyval3Tail69 65 4 5 (by decide +kernel) polyval3H69
theorem polyval3H61 : polyval3Tail61=hornerBox Q polyBox cell3 61 13 :=
  hornerChunk_step Q polyBox cell3 polyval3Tail61 polyval3Tail65 61 4 9 (by decide +kernel) polyval3H65
theorem polyval3H57 : polyval3Tail57=hornerBox Q polyBox cell3 57 17 :=
  hornerChunk_step Q polyBox cell3 polyval3Tail57 polyval3Tail61 57 4 13 (by decide +kernel) polyval3H61
theorem polyval3H53 : polyval3Tail53=hornerBox Q polyBox cell3 53 21 :=
  hornerChunk_step Q polyBox cell3 polyval3Tail53 polyval3Tail57 53 4 17 (by decide +kernel) polyval3H57
theorem polyval3H49 : polyval3Tail49=hornerBox Q polyBox cell3 49 25 :=
  hornerChunk_step Q polyBox cell3 polyval3Tail49 polyval3Tail53 49 4 21 (by decide +kernel) polyval3H53
theorem polyval3H45 : polyval3Tail45=hornerBox Q polyBox cell3 45 29 :=
  hornerChunk_step Q polyBox cell3 polyval3Tail45 polyval3Tail49 45 4 25 (by decide +kernel) polyval3H49
theorem polyval3H41 : polyval3Tail41=hornerBox Q polyBox cell3 41 33 :=
  hornerChunk_step Q polyBox cell3 polyval3Tail41 polyval3Tail45 41 4 29 (by decide +kernel) polyval3H45
theorem polyval3H37 : polyval3Tail37=hornerBox Q polyBox cell3 37 37 :=
  hornerChunk_step Q polyBox cell3 polyval3Tail37 polyval3Tail41 37 4 33 (by decide +kernel) polyval3H41
theorem polyval3H33 : polyval3Tail33=hornerBox Q polyBox cell3 33 41 :=
  hornerChunk_step Q polyBox cell3 polyval3Tail33 polyval3Tail37 33 4 37 (by decide +kernel) polyval3H37
theorem polyval3H29 : polyval3Tail29=hornerBox Q polyBox cell3 29 45 :=
  hornerChunk_step Q polyBox cell3 polyval3Tail29 polyval3Tail33 29 4 41 (by decide +kernel) polyval3H33
theorem polyval3H25 : polyval3Tail25=hornerBox Q polyBox cell3 25 49 :=
  hornerChunk_step Q polyBox cell3 polyval3Tail25 polyval3Tail29 25 4 45 (by decide +kernel) polyval3H29
theorem polyval3H21 : polyval3Tail21=hornerBox Q polyBox cell3 21 53 :=
  hornerChunk_step Q polyBox cell3 polyval3Tail21 polyval3Tail25 21 4 49 (by decide +kernel) polyval3H25
theorem polyval3H17 : polyval3Tail17=hornerBox Q polyBox cell3 17 57 :=
  hornerChunk_step Q polyBox cell3 polyval3Tail17 polyval3Tail21 17 4 53 (by decide +kernel) polyval3H21
theorem polyval3H13 : polyval3Tail13=hornerBox Q polyBox cell3 13 61 :=
  hornerChunk_step Q polyBox cell3 polyval3Tail13 polyval3Tail17 13 4 57 (by decide +kernel) polyval3H17
theorem polyval3H9 : polyval3Tail9=hornerBox Q polyBox cell3 9 65 :=
  hornerChunk_step Q polyBox cell3 polyval3Tail9 polyval3Tail13 9 4 61 (by decide +kernel) polyval3H13
theorem polyval3H5 : polyval3Tail5=hornerBox Q polyBox cell3 5 69 :=
  hornerChunk_step Q polyBox cell3 polyval3Tail5 polyval3Tail9 5 4 65 (by decide +kernel) polyval3H9
theorem polyval3H1 : polyval3=hornerBox Q polyBox cell3 1 73 :=
  hornerChunk_step Q polyBox cell3 polyval3 polyval3Tail5 1 4 69 (by decide +kernel) polyval3H5
theorem polyval3_eq : polyval3=hornerBox Q polyBox cell3 1 73 := polyval3H1
theorem polyval3_upper : 5*(polyval3.center+polyval3.radius)<Q := by decide +kernel
theorem resval3_pos : 0<(resval3).center-(resval3).radius := by decide +kernel
theorem polyval3_pos : 0<(polyval3).center-(polyval3).radius := by decide +kernel
def cell4 : Box := ⟨953125000000000000000000000000000000000000000000000000000000,15625000000000000000000000000000000000000000000000000000002⟩
def resval4 : Box := ⟨101368232584358310180486637621511062438522931182704398604,9729019292098064467834131880984593145359203913463259248⟩
def polyval4 : Box := ⟨4517094703299761670074593278165715769413047067575660078756,1847298112746050171112323591419408797954510429379712436219⟩
theorem cell4_lo : Holds Q cell4 (15/16:ℝ) := by norm_num [Holds,Q,cell4]
theorem cell4_hi : Holds Q cell4 (31/32:ℝ) := by norm_num [Holds,Q,cell4]
def resval4Tail4 : Box := ⟨-4478628793679290786900112266356539228407141406204169921,10373906059294914123575901833714296492870577810904145790⟩
def resval4Tail8 : Box := ⟨-5426879492891850161482093670267946746800939957160644723,11436905878495981839386536116950735030976656314024821177⟩
def resval4Tail12 : Box := ⟨-6575832377533490601851605924688634432372278866459181580,12571496827391199583791407884194503773972933431910440910⟩
def resval4Tail16 : Box := ⟨-7968036046184533003174444228626570827398423391593711383,13772054182827141433978709617427924457496346613074775103⟩
def resval4Tail20 : Box := ⟨-9654990393333573512516155848117536794035123723114148052,15028949497558089030144847320917484236113116669875916756⟩
def resval4Tail24 : Box := ⟨-11699098617908607038850920004405020224163066241536744334,16327320873398700640100623583700969057834800060775929849⟩
def resval4Tail28 : Box := ⟨-14175975624590385563412293231495418487689594818482166385,17645532326519607020924511978062972021338194279922799932⟩
def resval4Tail32 : Box := ⟨-17177245142746317116301167785084366724861608825180286918,18953248393776524902925934647867653055239217460858840942⟩
def resval4Tail36 : Box := ⟨-20813929037954848352352744471949318759360308368327338720,20209034587726620280385158830178155446859493372054659594⟩
def resval4Tail40 : Box := ⟨-25220554192297939074595259006169430072849931208700173960,21357374308258704091058212656546011704425795158106934099⟩
def resval4Tail44 : Box := ⟨-30560128873637077025990966153937611121483931926745631053,22324968439147020643453461256051652843842558785819891301⟩
def resval4Tail48 : Box := ⟨-37030172677907101984112913264497249468106507892759235973,23016154151531425125840457432836311353699814931433923770⟩
def resval4Tail52 : Box := ⟨-44870023101850286821076778374288102891422103867313279069,23307243253224836470955332715758361101297929315714902810⟩
def resval4Tail56 : Box := ⟨-54369689028259980949832368717788849299520022948924857417,23039536366224007867968568991680745652566764263645936748⟩
def resval4Tail60 : Box := ⟨-65880578628624427072364874872263873099314529669592440898,22010715589097977300250512737527740261799373463163251381⟩
def resval4Tail64 : Box := ⟨-79828498524175546713104634035327695710697045504009113372,19964253047172691517586723585162114998997479539589670900⟩
def resval4Tail68 : Box := ⟨-96729376664473512816671745225203936652273456333234840166,16576390736716450389814459687000339686867883346883504182⟩
def resval4Tail72 : Box := ⟨727901473602338148616066116101131451973904419064632782399,1338218187519239361012909869690897708668309947656700301⟩
def resval4Tail76 : Box := ⟨-55853727584438645243772663605231459648183707289542448,132359822356309786099418412160159010421105472849061713⟩
def resval4Tail80 : Box := ⟨-67652516415726621486471431058761732083788883579993612,146022313343194510946507715172304393883983772664810136⟩
def resval4Tail84 : Box := ⟨-81975581229407369955605834232587701617667060290988953,160633192351734349479499674366097401073036180034135603⟩
def resval4Tail88 : Box := ⟨-99331057824710379118001786157646845391176869740986183,176129638105393043105721205169039427116869146654128912⟩
def resval4Tail92 : Box := ⟨-120360952623508784285424523307228288401499886893288943,192400180794792224248664395321685936667519142846455099⟩
def resval4Tail96 : Box := ⟨-145843195810956761260042620587139298165819599228554534,209269268589125517709768789170754274682311019189499217⟩
def resval4Tail100 : Box := ⟨-176720417217756346171492734544088806696484256631262839,226478218731811314378509100397497056482364571246698417⟩
def resval4Tail104 : Box := ⟨-214134815737983503840697554537063746099262736984692810,243661393432629681140728504639319067922616631854764974⟩
def resval4Tail108 : Box := ⟨-259470411133303397629173159374829033700826477425394304,260316489031700853548270839452732642426300417437963357⟩
def resval4Tail112 : Box := ⟨-314404241186377620222224606896253559754390847841304732,275767578000646278185841551367178894721855896632100391⟩
def resval4Tail116 : Box := ⟨-380968398069857482262537093869393463489835762346442327,289119239867831829943550688234880673145882223122555225⟩
def resval4Tail120 : Box := ⟨-461625198757661746185545388979053261324868265777734424,299199747332519752935871512513501297162384044453337336⟩
def resval4Tail124 : Box := ⟨-559358270154931201174360003309661061541975027241856698,304490823337754028455652307243464739100235611850884534⟩
def resval4Tail128 : Box := ⟨-677782918334511756796330464640088501272937963635221583,303040936302454729836923253634031753494774441325981297⟩
def resval4Tail132 : Box := ⟨-821279864618446358084174995666887041438857023077631205,292358432940369906328454947126932901133169706370755261⟩
def resval4Tail136 : Box := ⟨-995157295625240486125276040153020147439769010909813406,269279995464555013506315413155193279621460511448158606⟩
def resval4Tail140 : Box := ⟨-1205847258343567574430748714974148728919491295081427991,229808916586174013739026329820537870660807211854859363⟩
def resval4Tail144 : Box := ⟨-1484533444533376178488416683176532375754747766277603502,166606462954540020034196584159883216537536568458629035⟩
def resval4Tail148 : Box := ⟨14487958338073975093229016617571910500427562465,30824164688527250279059721016175372123312451669⟩
def resval4Tail152 : Box := ⟨17499642787420948097717649650074692103507481556,33895444165963548626194528754454610244865579872⟩
def resval4Tail156 : Box := ⟨21204582296275727104376937353365114660603406354,37149969392426983412955538227134847349509314167⟩
def resval4Tail160 : Box := ⟨25693914683191768588168105555390870728405864465,40562491388046925477827912144842169013171034604⟩
def resval4Tail164 : Box := ⟨31133706975652452602098832382620498332656758521,44094552319539370504428130914011486313965200365⟩
def resval4Tail168 : Box := ⟨37725185982651968087577034283676625912082775851,47689815104183154352717598919062619549755975125⟩
def resval4Tail172 : Box := ⟨45712181287588404409907622858938277882457538881,51268959563165639419576024529083263159330473534⟩
def resval4Tail176 : Box := ⟨55390144902937191020446227817832800871737451165,54723319489015208828329189512125643440157619462⟩
def resval4Tail180 : Box := ⟨67117080523160441332575656010210886333696628674,57906969864709330576904390292315922955273133061⟩
def resval4Tail184 : Box := ⟨81326786666584985837373717599457658538415908779,60626908657626303293792104151530717463113167793⟩
def resval4Tail188 : Box := ⟨98544903591715107067238200025744148692500112939,62630898613410901666720880872179838345459701906⟩
def resval4Tail192 : Box := ⟨119408357589645884401971698543026667171631499813,63592438248285477997326459450751362113800070001⟩
def resval4Tail196 : Box := ⟨144688921928738627446132081918352246137038853755,63092214067686701552054255853067837362968830152⟩
def resval4Tail200 : Box := ⟨175321766009416442241826912549141388498392177988,60595243412770693593381363907971729608975780411⟩
def resval4Tail204 : Box := ⟨212440048808984436461196292236526113251128258629,55422743777084866104912889019644887463811300123⟩
def resval4Tail208 : Box := ⟨257416836284553156758830069183691487703591345562,46717553294822420707749558682382312596566526025⟩
def resval4Tail212 : Box := ⟨311915893341582715023750705292995568993949791991,33401670307549282899213053485323018807580722125⟩
def resval4Tail216 : Box := ⟨377953864880095838462486187369710950820751063690,14124088978102788502762325899736791628766282443⟩
theorem resval4H216 : resval4Tail216=hornerBox Q residualBox cell4 216 4 :=
  hornerChunk_step Q residualBox cell4 resval4Tail216 zero 216 4 0 (by decide +kernel) rfl
theorem resval4H212 : resval4Tail212=hornerBox Q residualBox cell4 212 8 :=
  hornerChunk_step Q residualBox cell4 resval4Tail212 resval4Tail216 212 4 4 (by decide +kernel) resval4H216
theorem resval4H208 : resval4Tail208=hornerBox Q residualBox cell4 208 12 :=
  hornerChunk_step Q residualBox cell4 resval4Tail208 resval4Tail212 208 4 8 (by decide +kernel) resval4H212
theorem resval4H204 : resval4Tail204=hornerBox Q residualBox cell4 204 16 :=
  hornerChunk_step Q residualBox cell4 resval4Tail204 resval4Tail208 204 4 12 (by decide +kernel) resval4H208
theorem resval4H200 : resval4Tail200=hornerBox Q residualBox cell4 200 20 :=
  hornerChunk_step Q residualBox cell4 resval4Tail200 resval4Tail204 200 4 16 (by decide +kernel) resval4H204
theorem resval4H196 : resval4Tail196=hornerBox Q residualBox cell4 196 24 :=
  hornerChunk_step Q residualBox cell4 resval4Tail196 resval4Tail200 196 4 20 (by decide +kernel) resval4H200
theorem resval4H192 : resval4Tail192=hornerBox Q residualBox cell4 192 28 :=
  hornerChunk_step Q residualBox cell4 resval4Tail192 resval4Tail196 192 4 24 (by decide +kernel) resval4H196
theorem resval4H188 : resval4Tail188=hornerBox Q residualBox cell4 188 32 :=
  hornerChunk_step Q residualBox cell4 resval4Tail188 resval4Tail192 188 4 28 (by decide +kernel) resval4H192
theorem resval4H184 : resval4Tail184=hornerBox Q residualBox cell4 184 36 :=
  hornerChunk_step Q residualBox cell4 resval4Tail184 resval4Tail188 184 4 32 (by decide +kernel) resval4H188
theorem resval4H180 : resval4Tail180=hornerBox Q residualBox cell4 180 40 :=
  hornerChunk_step Q residualBox cell4 resval4Tail180 resval4Tail184 180 4 36 (by decide +kernel) resval4H184
theorem resval4H176 : resval4Tail176=hornerBox Q residualBox cell4 176 44 :=
  hornerChunk_step Q residualBox cell4 resval4Tail176 resval4Tail180 176 4 40 (by decide +kernel) resval4H180
theorem resval4H172 : resval4Tail172=hornerBox Q residualBox cell4 172 48 :=
  hornerChunk_step Q residualBox cell4 resval4Tail172 resval4Tail176 172 4 44 (by decide +kernel) resval4H176
theorem resval4H168 : resval4Tail168=hornerBox Q residualBox cell4 168 52 :=
  hornerChunk_step Q residualBox cell4 resval4Tail168 resval4Tail172 168 4 48 (by decide +kernel) resval4H172
theorem resval4H164 : resval4Tail164=hornerBox Q residualBox cell4 164 56 :=
  hornerChunk_step Q residualBox cell4 resval4Tail164 resval4Tail168 164 4 52 (by decide +kernel) resval4H168
theorem resval4H160 : resval4Tail160=hornerBox Q residualBox cell4 160 60 :=
  hornerChunk_step Q residualBox cell4 resval4Tail160 resval4Tail164 160 4 56 (by decide +kernel) resval4H164
theorem resval4H156 : resval4Tail156=hornerBox Q residualBox cell4 156 64 :=
  hornerChunk_step Q residualBox cell4 resval4Tail156 resval4Tail160 156 4 60 (by decide +kernel) resval4H160
theorem resval4H152 : resval4Tail152=hornerBox Q residualBox cell4 152 68 :=
  hornerChunk_step Q residualBox cell4 resval4Tail152 resval4Tail156 152 4 64 (by decide +kernel) resval4H156
theorem resval4H148 : resval4Tail148=hornerBox Q residualBox cell4 148 72 :=
  hornerChunk_step Q residualBox cell4 resval4Tail148 resval4Tail152 148 4 68 (by decide +kernel) resval4H152
theorem resval4H144 : resval4Tail144=hornerBox Q residualBox cell4 144 76 :=
  hornerChunk_step Q residualBox cell4 resval4Tail144 resval4Tail148 144 4 72 (by decide +kernel) resval4H148
theorem resval4H140 : resval4Tail140=hornerBox Q residualBox cell4 140 80 :=
  hornerChunk_step Q residualBox cell4 resval4Tail140 resval4Tail144 140 4 76 (by decide +kernel) resval4H144
theorem resval4H136 : resval4Tail136=hornerBox Q residualBox cell4 136 84 :=
  hornerChunk_step Q residualBox cell4 resval4Tail136 resval4Tail140 136 4 80 (by decide +kernel) resval4H140
theorem resval4H132 : resval4Tail132=hornerBox Q residualBox cell4 132 88 :=
  hornerChunk_step Q residualBox cell4 resval4Tail132 resval4Tail136 132 4 84 (by decide +kernel) resval4H136
theorem resval4H128 : resval4Tail128=hornerBox Q residualBox cell4 128 92 :=
  hornerChunk_step Q residualBox cell4 resval4Tail128 resval4Tail132 128 4 88 (by decide +kernel) resval4H132
theorem resval4H124 : resval4Tail124=hornerBox Q residualBox cell4 124 96 :=
  hornerChunk_step Q residualBox cell4 resval4Tail124 resval4Tail128 124 4 92 (by decide +kernel) resval4H128
theorem resval4H120 : resval4Tail120=hornerBox Q residualBox cell4 120 100 :=
  hornerChunk_step Q residualBox cell4 resval4Tail120 resval4Tail124 120 4 96 (by decide +kernel) resval4H124
theorem resval4H116 : resval4Tail116=hornerBox Q residualBox cell4 116 104 :=
  hornerChunk_step Q residualBox cell4 resval4Tail116 resval4Tail120 116 4 100 (by decide +kernel) resval4H120
theorem resval4H112 : resval4Tail112=hornerBox Q residualBox cell4 112 108 :=
  hornerChunk_step Q residualBox cell4 resval4Tail112 resval4Tail116 112 4 104 (by decide +kernel) resval4H116
theorem resval4H108 : resval4Tail108=hornerBox Q residualBox cell4 108 112 :=
  hornerChunk_step Q residualBox cell4 resval4Tail108 resval4Tail112 108 4 108 (by decide +kernel) resval4H112
theorem resval4H104 : resval4Tail104=hornerBox Q residualBox cell4 104 116 :=
  hornerChunk_step Q residualBox cell4 resval4Tail104 resval4Tail108 104 4 112 (by decide +kernel) resval4H108
theorem resval4H100 : resval4Tail100=hornerBox Q residualBox cell4 100 120 :=
  hornerChunk_step Q residualBox cell4 resval4Tail100 resval4Tail104 100 4 116 (by decide +kernel) resval4H104
theorem resval4H96 : resval4Tail96=hornerBox Q residualBox cell4 96 124 :=
  hornerChunk_step Q residualBox cell4 resval4Tail96 resval4Tail100 96 4 120 (by decide +kernel) resval4H100
theorem resval4H92 : resval4Tail92=hornerBox Q residualBox cell4 92 128 :=
  hornerChunk_step Q residualBox cell4 resval4Tail92 resval4Tail96 92 4 124 (by decide +kernel) resval4H96
theorem resval4H88 : resval4Tail88=hornerBox Q residualBox cell4 88 132 :=
  hornerChunk_step Q residualBox cell4 resval4Tail88 resval4Tail92 88 4 128 (by decide +kernel) resval4H92
theorem resval4H84 : resval4Tail84=hornerBox Q residualBox cell4 84 136 :=
  hornerChunk_step Q residualBox cell4 resval4Tail84 resval4Tail88 84 4 132 (by decide +kernel) resval4H88
theorem resval4H80 : resval4Tail80=hornerBox Q residualBox cell4 80 140 :=
  hornerChunk_step Q residualBox cell4 resval4Tail80 resval4Tail84 80 4 136 (by decide +kernel) resval4H84
theorem resval4H76 : resval4Tail76=hornerBox Q residualBox cell4 76 144 :=
  hornerChunk_step Q residualBox cell4 resval4Tail76 resval4Tail80 76 4 140 (by decide +kernel) resval4H80
theorem resval4H72 : resval4Tail72=hornerBox Q residualBox cell4 72 148 :=
  hornerChunk_step Q residualBox cell4 resval4Tail72 resval4Tail76 72 4 144 (by decide +kernel) resval4H76
theorem resval4H68 : resval4Tail68=hornerBox Q residualBox cell4 68 152 :=
  hornerChunk_step Q residualBox cell4 resval4Tail68 resval4Tail72 68 4 148 (by decide +kernel) resval4H72
theorem resval4H64 : resval4Tail64=hornerBox Q residualBox cell4 64 156 :=
  hornerChunk_step Q residualBox cell4 resval4Tail64 resval4Tail68 64 4 152 (by decide +kernel) resval4H68
theorem resval4H60 : resval4Tail60=hornerBox Q residualBox cell4 60 160 :=
  hornerChunk_step Q residualBox cell4 resval4Tail60 resval4Tail64 60 4 156 (by decide +kernel) resval4H64
theorem resval4H56 : resval4Tail56=hornerBox Q residualBox cell4 56 164 :=
  hornerChunk_step Q residualBox cell4 resval4Tail56 resval4Tail60 56 4 160 (by decide +kernel) resval4H60
theorem resval4H52 : resval4Tail52=hornerBox Q residualBox cell4 52 168 :=
  hornerChunk_step Q residualBox cell4 resval4Tail52 resval4Tail56 52 4 164 (by decide +kernel) resval4H56
theorem resval4H48 : resval4Tail48=hornerBox Q residualBox cell4 48 172 :=
  hornerChunk_step Q residualBox cell4 resval4Tail48 resval4Tail52 48 4 168 (by decide +kernel) resval4H52
theorem resval4H44 : resval4Tail44=hornerBox Q residualBox cell4 44 176 :=
  hornerChunk_step Q residualBox cell4 resval4Tail44 resval4Tail48 44 4 172 (by decide +kernel) resval4H48
theorem resval4H40 : resval4Tail40=hornerBox Q residualBox cell4 40 180 :=
  hornerChunk_step Q residualBox cell4 resval4Tail40 resval4Tail44 40 4 176 (by decide +kernel) resval4H44
theorem resval4H36 : resval4Tail36=hornerBox Q residualBox cell4 36 184 :=
  hornerChunk_step Q residualBox cell4 resval4Tail36 resval4Tail40 36 4 180 (by decide +kernel) resval4H40
theorem resval4H32 : resval4Tail32=hornerBox Q residualBox cell4 32 188 :=
  hornerChunk_step Q residualBox cell4 resval4Tail32 resval4Tail36 32 4 184 (by decide +kernel) resval4H36
theorem resval4H28 : resval4Tail28=hornerBox Q residualBox cell4 28 192 :=
  hornerChunk_step Q residualBox cell4 resval4Tail28 resval4Tail32 28 4 188 (by decide +kernel) resval4H32
theorem resval4H24 : resval4Tail24=hornerBox Q residualBox cell4 24 196 :=
  hornerChunk_step Q residualBox cell4 resval4Tail24 resval4Tail28 24 4 192 (by decide +kernel) resval4H28
theorem resval4H20 : resval4Tail20=hornerBox Q residualBox cell4 20 200 :=
  hornerChunk_step Q residualBox cell4 resval4Tail20 resval4Tail24 20 4 196 (by decide +kernel) resval4H24
theorem resval4H16 : resval4Tail16=hornerBox Q residualBox cell4 16 204 :=
  hornerChunk_step Q residualBox cell4 resval4Tail16 resval4Tail20 16 4 200 (by decide +kernel) resval4H20
theorem resval4H12 : resval4Tail12=hornerBox Q residualBox cell4 12 208 :=
  hornerChunk_step Q residualBox cell4 resval4Tail12 resval4Tail16 12 4 204 (by decide +kernel) resval4H16
theorem resval4H8 : resval4Tail8=hornerBox Q residualBox cell4 8 212 :=
  hornerChunk_step Q residualBox cell4 resval4Tail8 resval4Tail12 8 4 208 (by decide +kernel) resval4H12
theorem resval4H4 : resval4Tail4=hornerBox Q residualBox cell4 4 216 :=
  hornerChunk_step Q residualBox cell4 resval4Tail4 resval4Tail8 4 4 212 (by decide +kernel) resval4H8
theorem resval4H0 : resval4=hornerBox Q residualBox cell4 0 220 :=
  hornerChunk_step Q residualBox cell4 resval4 resval4Tail4 0 4 216 (by decide +kernel) resval4H4
theorem resval4_eq : resval4=hornerBox Q residualBox cell4 0 220 := resval4H0
def polyval4Tail5 : Box := ⟨1003506927789575896981798321745070684721937663459733015273,2028688144665337533902594885336737326105344017883193702023⟩
def polyval4Tail9 : Box := ⟨1215962435517399773310949550921778412368271899669144014676,2226823480526369508948688671435080798978677046813904947346⟩
def polyval4Tail13 : Box := ⟨1473400165870132962063700189028656291184836640672757119177,2435577198519982887902098046640074821616513416579447324944⟩
def polyval4Tail17 : Box := ⟨1785341377041473171922019765732262866383782569235008327566,2652954935487009039877253102145775282769263083777322168016⟩
def polyval4Tail21 : Box := ⟨2163325284203554769748298606342579953612405761497921157788,2875965640643704155472853541370177521462161778552482434117⟩
def polyval4Tail25 : Box := ⟨2621334129963245012303559771460427001796059201179282414917,3100332752341152365813213721740365773062558350120956389249⟩
def polyval4Tail29 : Box := ⟨3176310410221050034499117147896740858830927084492824628421,3320133712629665634167565669704582749072897270512176136233⟩
def polyval4Tail33 : Box := ⟨3848783604789854525664605533661449052341700232312760751865,3527351201632860315664462805459466838308845442136588373876⟩
def polyval4Tail37 : Box := ⟨4663629596412238446594598685552337733688228257786882220242,3711315781959779772222247573793700370433467105493241145477⟩
def polyval4Tail41 : Box := ⟨5650990870327122018952941959844561972573218152925916698894,3858015124200146311505907907185462775566240155043069148483⟩
def polyval4Tail45 : Box := ⟨6847391534071936603226199714652208025712668120446758243648,3949239478885456804048526179977727681286032421757722446116⟩
def polyval4Tail49 : Box := ⟨8297088403925499356148983953910474809938529615997551656242,3961526355287135493990544740337261054218874131214409154156⟩
def polyval4Tail53 : Box := ⟨10053708136887701556762547166719236840184519080539954804757,3864859204576269268848938749038037059522019337291786216098⟩
def polyval4Tail57 : Box := ⟨12182230968384118885718241771768833709609709528226594419015,3621064970357853073634154146951200972934533472635720789207⟩
def polyval4Tail61 : Box := ⟨14761394437396008229405403438758582835609336180110095255271,3181843282441769936774039185387383159818047973333484315523⟩
def polyval4Tail65 : Box := ⟨17886606016740929760454553516835162074004632342646179485629,2486345367493164367061039453466005042923104102359278480374⟩
def polyval4Tail69 : Box := ⟨21673472419510066300320402802977412236372403945501354998320,1458202868121239194097720226543475289729847349284943964255⟩
def polyval4Tail73 : Box := ⟨26281250000000000000000000000000000000000000000000000000000,2⟩
theorem polyval4H73 : polyval4Tail73=hornerBox Q polyBox cell4 73 1 :=
  hornerChunk_step Q polyBox cell4 polyval4Tail73 zero 73 1 0 (by decide +kernel) rfl
theorem polyval4H69 : polyval4Tail69=hornerBox Q polyBox cell4 69 5 :=
  hornerChunk_step Q polyBox cell4 polyval4Tail69 polyval4Tail73 69 4 1 (by decide +kernel) polyval4H73
theorem polyval4H65 : polyval4Tail65=hornerBox Q polyBox cell4 65 9 :=
  hornerChunk_step Q polyBox cell4 polyval4Tail65 polyval4Tail69 65 4 5 (by decide +kernel) polyval4H69
theorem polyval4H61 : polyval4Tail61=hornerBox Q polyBox cell4 61 13 :=
  hornerChunk_step Q polyBox cell4 polyval4Tail61 polyval4Tail65 61 4 9 (by decide +kernel) polyval4H65
theorem polyval4H57 : polyval4Tail57=hornerBox Q polyBox cell4 57 17 :=
  hornerChunk_step Q polyBox cell4 polyval4Tail57 polyval4Tail61 57 4 13 (by decide +kernel) polyval4H61
theorem polyval4H53 : polyval4Tail53=hornerBox Q polyBox cell4 53 21 :=
  hornerChunk_step Q polyBox cell4 polyval4Tail53 polyval4Tail57 53 4 17 (by decide +kernel) polyval4H57
theorem polyval4H49 : polyval4Tail49=hornerBox Q polyBox cell4 49 25 :=
  hornerChunk_step Q polyBox cell4 polyval4Tail49 polyval4Tail53 49 4 21 (by decide +kernel) polyval4H53
theorem polyval4H45 : polyval4Tail45=hornerBox Q polyBox cell4 45 29 :=
  hornerChunk_step Q polyBox cell4 polyval4Tail45 polyval4Tail49 45 4 25 (by decide +kernel) polyval4H49
theorem polyval4H41 : polyval4Tail41=hornerBox Q polyBox cell4 41 33 :=
  hornerChunk_step Q polyBox cell4 polyval4Tail41 polyval4Tail45 41 4 29 (by decide +kernel) polyval4H45
theorem polyval4H37 : polyval4Tail37=hornerBox Q polyBox cell4 37 37 :=
  hornerChunk_step Q polyBox cell4 polyval4Tail37 polyval4Tail41 37 4 33 (by decide +kernel) polyval4H41
theorem polyval4H33 : polyval4Tail33=hornerBox Q polyBox cell4 33 41 :=
  hornerChunk_step Q polyBox cell4 polyval4Tail33 polyval4Tail37 33 4 37 (by decide +kernel) polyval4H37
theorem polyval4H29 : polyval4Tail29=hornerBox Q polyBox cell4 29 45 :=
  hornerChunk_step Q polyBox cell4 polyval4Tail29 polyval4Tail33 29 4 41 (by decide +kernel) polyval4H33
theorem polyval4H25 : polyval4Tail25=hornerBox Q polyBox cell4 25 49 :=
  hornerChunk_step Q polyBox cell4 polyval4Tail25 polyval4Tail29 25 4 45 (by decide +kernel) polyval4H29
theorem polyval4H21 : polyval4Tail21=hornerBox Q polyBox cell4 21 53 :=
  hornerChunk_step Q polyBox cell4 polyval4Tail21 polyval4Tail25 21 4 49 (by decide +kernel) polyval4H25
theorem polyval4H17 : polyval4Tail17=hornerBox Q polyBox cell4 17 57 :=
  hornerChunk_step Q polyBox cell4 polyval4Tail17 polyval4Tail21 17 4 53 (by decide +kernel) polyval4H21
theorem polyval4H13 : polyval4Tail13=hornerBox Q polyBox cell4 13 61 :=
  hornerChunk_step Q polyBox cell4 polyval4Tail13 polyval4Tail17 13 4 57 (by decide +kernel) polyval4H17
theorem polyval4H9 : polyval4Tail9=hornerBox Q polyBox cell4 9 65 :=
  hornerChunk_step Q polyBox cell4 polyval4Tail9 polyval4Tail13 9 4 61 (by decide +kernel) polyval4H13
theorem polyval4H5 : polyval4Tail5=hornerBox Q polyBox cell4 5 69 :=
  hornerChunk_step Q polyBox cell4 polyval4Tail5 polyval4Tail9 5 4 65 (by decide +kernel) polyval4H9
theorem polyval4H1 : polyval4=hornerBox Q polyBox cell4 1 73 :=
  hornerChunk_step Q polyBox cell4 polyval4 polyval4Tail5 1 4 69 (by decide +kernel) polyval4H5
theorem polyval4_eq : polyval4=hornerBox Q polyBox cell4 1 73 := polyval4H1
theorem polyval4_upper : 5*(polyval4.center+polyval4.radius)<Q := by decide +kernel
theorem resval4_pos : 0<(resval4).center-(resval4).radius := by decide +kernel
theorem polyval4_pos : 0<(polyval4).center-(polyval4).radius := by decide +kernel
def cell5 : Box := ⟨976562500000000000000000000000000000000000000000000000000000,7812500000000000000000000000000000000000000000000000000002⟩
def resval5 : Box := ⟨87470508379350588026739956595278265332093531848354030274,16089976846245479371474485809154497083387522674085343296⟩
def polyval5 : Box := ⟨8449315023933833052932170436752290655705992499417836653840,3695152110701948325450766339166321491465410836329618126550⟩
theorem cell5_lo : Holds Q cell5 (31/32:ℝ) := by norm_num [Holds,Q,cell5]
theorem cell5_hi : Holds Q cell5 (63/64:ℝ) := by norm_num [Holds,Q,cell5]
def resval5Tail4 : Box := ⟨-19330947362216435185825282260866454719818633518759292325,16167695131832386083682122267821072186925074739047137088⟩
def resval5Tail8 : Box := ⟨-21254652949867246593000187238163837575868330322304743010,16552154634576669880360946234745415939466152405454413087⟩
def resval5Tail12 : Box := ⟨-23369738068195691571339381777920708947448635422467625616,16895262092450106101032706208517160422565568972396429455⟩
def resval5Tail16 : Box := ⟨-25695298744064955889556160144037330139927748046789097099,17187725275054541478684002764102511690514898776895450588⟩
def resval5Tail20 : Box := ⟨-28252279748277483227170489110020534355671967201800281989,17418991621083245390743269467234125560032418167943901382⟩
def resval5Tail24 : Box := ⟨-31063710094411495291801026955346889103503598302971095580,17577100021120481735408153321658952232712075230326418569⟩
def resval5Tail28 : Box := ⟨-34154910450668145834843915450585368663625432819035240752,17648517344478743284403201818349520911100241062078160342⟩
def resval5Tail32 : Box := ⟨-37553721186157646774119734117768941991782358712466154078,17617957183361779477660424567910112059754731998784220852⟩
def resval5Tail36 : Box := ⟨-41290753110438251723627579144377915269483280564279094416,17468178946078312395489192175332616505633487285848626364⟩
def resval5Tail40 : Box := ⟨-45399663164554897249364421015196261753705250738684783196,17179765238873677467687165323610260997649019883884867570⟩
def resval5Tail44 : Box := ⟨-49917457546541862420958694296682014095102571079478494682,16730875264086967206387869465475324827904928381696253138⟩
def resval5Tail48 : Box := ⟨-54884825001437618427966285020219789099057022450586574656,16096971728955288050954970608181403438021823102505426935⟩
def resval5Tail52 : Box := ⟨-60346503277531577321307468412929629884106316875033426576,15250518502303690205073425380885472580060752624238495569⟩
def resval5Tail56 : Box := ⟨-66351682049268459494877130870567343954134202653151524251,14160645973190343617112681106526605180525522605550399986⟩
def resval5Tail60 : Box := ⟨-72954445935665634428018558561289411206203394006503563485,12792780753692861080822442080927581968646121901040648636⟩
def resval5Tail64 : Box := ⟨-80214261602597522825250969501614486386603494105265802391,11108236024320330252726168316331360449034015677191680615⟩
def resval5Tail68 : Box := ⟨-88196485575385411827441976099855567015615784597883666428,9063755654786295136137655800538738294475820597584069213⟩
def resval5Tail72 : Box := ⟨727882861691124663251841228563768923958116828442727965740,1367265260454182497619486393199388078354872857116792898⟩
def resval5Tail76 : Box := ⟨-246439585524522154686489548403161801798936578479797742,209344903029870523226632051958233527166156459803199159⟩
def resval5Tail80 : Box := ⟨-270939361882372549276527830167552119909183514907564555,214456801181063008988550156436795545257830006682084652⟩
def resval5Tail84 : Box := ⟨-297900977683355329660585803846792273323737898557771286,219055565005336364290497930591346467379174255365624657⟩
def resval5Tail88 : Box := ⟨-327545588888128641473388367659383734158357033776832395,223023385369635036087887106158088296512441393846602111⟩
def resval5Tail92 : Box := ⟨-360140183609233473104929618688931216556227403520038564,226226697132800941955921374652159831862664211732479940⟩
def resval5Tail96 : Box := ⟨-395978319507735799178066179581687666795480773770435613,228514041861999799754033159875818164945249381647480304⟩
def resval5Tail100 : Box := ⟨-435382766645955603288281807069317872379759819852497222,229713987992750732693858883659855646286148390146219611⟩
def resval5Tail104 : Box := ⟨-478708414460513005240100807400750131251463456860597338,229632824591153418551510034823073542418874882167510719⟩
def resval5Tail108 : Box := ⟨-526345468013546711265182340490071325008937849017603857,228052004898208910541142131962786490131273804100131346⟩
def resval5Tail112 : Box := ⟨-578722962308095285722138646712672953353820548719443197,224725313409382400298003926584543895807331855378044309⟩
def resval5Tail116 : Box := ⟨-636312626318722541629011078045431640216852713498819517,219375727543111948633180046373083820599517726606397295⟩
def resval5Tail120 : Box := ⟨-699633131538120240355565677196496333271278167102500548,211691941978181323498219014056385347160065548461571922⟩
def resval5Tail124 : Box := ⟨-769254763303498908548129662678780321466581459421874102,201324520464096965240197760733175313427843789933109343⟩
def resval5Tail128 : Box := ⟨-845804556974271702351967915450536558203870514829753052,187881636300392667290516464706273096856596016248589312⟩
def resval5Tail132 : Box := ⟨-929971945219144969437061228095118388988349401855956171,170924358706628434559861575052508900778468438525707213⟩
def resval5Tail136 : Box := ⟨-1022514967278346069687280014960889887462550613250652806,149961437927214031348025717573098535613363579071041818⟩
def resval5Tail140 : Box := ⟨-1124267131876562200150727411738050516178132708909007755,124443532683775616776296783120167004968182278370859424⟩
def resval5Tail144 : Box := ⟨-1258982655097125459937101983314926022546668959317631321,91670899853166232969148475025070723647755929798853036⟩
def resval5Tail148 : Box := ⟨79151740022772985412819015840198534557532646542,59644176251596843848832523040978580442412142354⟩
def resval5Tail152 : Box := ⟨86977818304558534611729571398843166742195320682,60793087099727019479469685850200576160215494813⟩
def resval5Tail156 : Box := ⟨95633121798370173874752569975919276671242784302,61745823418763762482282436028560491207905766843⟩
def resval5Tail160 : Box := ⟨105149729417607345168159906858761695136954393105,62461969599267206480006651558268959385363073181⟩
def resval5Tail164 : Box := ⟨115613350152159069350338175076858232919101455934,62896434677060441735449566517760243980408219493⟩
def resval5Tail168 : Box := ⟨127118222818437073686378016675447992609279346068,62998239616360982191185721445446515582957720110⟩
def resval5Tail172 : Box := ⟨139767964091092013358982807703121725034374781474,62709840267370684495548472481900332012609554953⟩
def resval5Tail176 : Box := ⟨153676501708734095948145476651186354004020679127,61966377044515538188549009977548172310174697214⟩
def resval5Tail180 : Box := ⟨168969100544691471272133320282280237230196668361,60694843630951432549499019991179006446494674753⟩
def resval5Tail184 : Box := ⟨185783490783740327814104776488153739491649093587,58813166241355013708163025542669320914156385455⟩
def resval5Tail188 : Box := ⟨204271108365537821828615828146913815406119064133,56229184105696123669809019724419541676944868051⟩
def resval5Tail192 : Box := ⟨224598458866600181300761900065980093025179265078,52839520879116556661189945800586532098173289040⟩
def resval5Tail196 : Box := ⟨246948617104396545384890821511946383871485031644,48528335628331910404878951611553655734673090761⟩
def resval5Tail200 : Box := ⟨271522875969487201474724943019012943728569826278,43165940883342915588901509896802800425084310417⟩
def resval5Tail204 : Box := ⟨298542559335631840714151083134227565591359639571,36607273963921891322061086702660673536745849270⟩
def resval5Tail208 : Box := ⟨328251015375539232190426643485089322703035816126,28690206381480180251032887158922769944346369493⟩
def resval5Tail212 : Box := ⟨360915808248672111461576677192894217070869785283,19233674563499632885380262467163505134395936618⟩
def resval5Tail216 : Box := ⟨396831748963639712632245059670291619602426823168,8035540970613992304861372430156992753868153312⟩
theorem resval5H216 : resval5Tail216=hornerBox Q residualBox cell5 216 4 :=
  hornerChunk_step Q residualBox cell5 resval5Tail216 zero 216 4 0 (by decide +kernel) rfl
theorem resval5H212 : resval5Tail212=hornerBox Q residualBox cell5 212 8 :=
  hornerChunk_step Q residualBox cell5 resval5Tail212 resval5Tail216 212 4 4 (by decide +kernel) resval5H216
theorem resval5H208 : resval5Tail208=hornerBox Q residualBox cell5 208 12 :=
  hornerChunk_step Q residualBox cell5 resval5Tail208 resval5Tail212 208 4 8 (by decide +kernel) resval5H212
theorem resval5H204 : resval5Tail204=hornerBox Q residualBox cell5 204 16 :=
  hornerChunk_step Q residualBox cell5 resval5Tail204 resval5Tail208 204 4 12 (by decide +kernel) resval5H208
theorem resval5H200 : resval5Tail200=hornerBox Q residualBox cell5 200 20 :=
  hornerChunk_step Q residualBox cell5 resval5Tail200 resval5Tail204 200 4 16 (by decide +kernel) resval5H204
theorem resval5H196 : resval5Tail196=hornerBox Q residualBox cell5 196 24 :=
  hornerChunk_step Q residualBox cell5 resval5Tail196 resval5Tail200 196 4 20 (by decide +kernel) resval5H200
theorem resval5H192 : resval5Tail192=hornerBox Q residualBox cell5 192 28 :=
  hornerChunk_step Q residualBox cell5 resval5Tail192 resval5Tail196 192 4 24 (by decide +kernel) resval5H196
theorem resval5H188 : resval5Tail188=hornerBox Q residualBox cell5 188 32 :=
  hornerChunk_step Q residualBox cell5 resval5Tail188 resval5Tail192 188 4 28 (by decide +kernel) resval5H192
theorem resval5H184 : resval5Tail184=hornerBox Q residualBox cell5 184 36 :=
  hornerChunk_step Q residualBox cell5 resval5Tail184 resval5Tail188 184 4 32 (by decide +kernel) resval5H188
theorem resval5H180 : resval5Tail180=hornerBox Q residualBox cell5 180 40 :=
  hornerChunk_step Q residualBox cell5 resval5Tail180 resval5Tail184 180 4 36 (by decide +kernel) resval5H184
theorem resval5H176 : resval5Tail176=hornerBox Q residualBox cell5 176 44 :=
  hornerChunk_step Q residualBox cell5 resval5Tail176 resval5Tail180 176 4 40 (by decide +kernel) resval5H180
theorem resval5H172 : resval5Tail172=hornerBox Q residualBox cell5 172 48 :=
  hornerChunk_step Q residualBox cell5 resval5Tail172 resval5Tail176 172 4 44 (by decide +kernel) resval5H176
theorem resval5H168 : resval5Tail168=hornerBox Q residualBox cell5 168 52 :=
  hornerChunk_step Q residualBox cell5 resval5Tail168 resval5Tail172 168 4 48 (by decide +kernel) resval5H172
theorem resval5H164 : resval5Tail164=hornerBox Q residualBox cell5 164 56 :=
  hornerChunk_step Q residualBox cell5 resval5Tail164 resval5Tail168 164 4 52 (by decide +kernel) resval5H168
theorem resval5H160 : resval5Tail160=hornerBox Q residualBox cell5 160 60 :=
  hornerChunk_step Q residualBox cell5 resval5Tail160 resval5Tail164 160 4 56 (by decide +kernel) resval5H164
theorem resval5H156 : resval5Tail156=hornerBox Q residualBox cell5 156 64 :=
  hornerChunk_step Q residualBox cell5 resval5Tail156 resval5Tail160 156 4 60 (by decide +kernel) resval5H160
theorem resval5H152 : resval5Tail152=hornerBox Q residualBox cell5 152 68 :=
  hornerChunk_step Q residualBox cell5 resval5Tail152 resval5Tail156 152 4 64 (by decide +kernel) resval5H156
theorem resval5H148 : resval5Tail148=hornerBox Q residualBox cell5 148 72 :=
  hornerChunk_step Q residualBox cell5 resval5Tail148 resval5Tail152 148 4 68 (by decide +kernel) resval5H152
theorem resval5H144 : resval5Tail144=hornerBox Q residualBox cell5 144 76 :=
  hornerChunk_step Q residualBox cell5 resval5Tail144 resval5Tail148 144 4 72 (by decide +kernel) resval5H148
theorem resval5H140 : resval5Tail140=hornerBox Q residualBox cell5 140 80 :=
  hornerChunk_step Q residualBox cell5 resval5Tail140 resval5Tail144 140 4 76 (by decide +kernel) resval5H144
theorem resval5H136 : resval5Tail136=hornerBox Q residualBox cell5 136 84 :=
  hornerChunk_step Q residualBox cell5 resval5Tail136 resval5Tail140 136 4 80 (by decide +kernel) resval5H140
theorem resval5H132 : resval5Tail132=hornerBox Q residualBox cell5 132 88 :=
  hornerChunk_step Q residualBox cell5 resval5Tail132 resval5Tail136 132 4 84 (by decide +kernel) resval5H136
theorem resval5H128 : resval5Tail128=hornerBox Q residualBox cell5 128 92 :=
  hornerChunk_step Q residualBox cell5 resval5Tail128 resval5Tail132 128 4 88 (by decide +kernel) resval5H132
theorem resval5H124 : resval5Tail124=hornerBox Q residualBox cell5 124 96 :=
  hornerChunk_step Q residualBox cell5 resval5Tail124 resval5Tail128 124 4 92 (by decide +kernel) resval5H128
theorem resval5H120 : resval5Tail120=hornerBox Q residualBox cell5 120 100 :=
  hornerChunk_step Q residualBox cell5 resval5Tail120 resval5Tail124 120 4 96 (by decide +kernel) resval5H124
theorem resval5H116 : resval5Tail116=hornerBox Q residualBox cell5 116 104 :=
  hornerChunk_step Q residualBox cell5 resval5Tail116 resval5Tail120 116 4 100 (by decide +kernel) resval5H120
theorem resval5H112 : resval5Tail112=hornerBox Q residualBox cell5 112 108 :=
  hornerChunk_step Q residualBox cell5 resval5Tail112 resval5Tail116 112 4 104 (by decide +kernel) resval5H116
theorem resval5H108 : resval5Tail108=hornerBox Q residualBox cell5 108 112 :=
  hornerChunk_step Q residualBox cell5 resval5Tail108 resval5Tail112 108 4 108 (by decide +kernel) resval5H112
theorem resval5H104 : resval5Tail104=hornerBox Q residualBox cell5 104 116 :=
  hornerChunk_step Q residualBox cell5 resval5Tail104 resval5Tail108 104 4 112 (by decide +kernel) resval5H108
theorem resval5H100 : resval5Tail100=hornerBox Q residualBox cell5 100 120 :=
  hornerChunk_step Q residualBox cell5 resval5Tail100 resval5Tail104 100 4 116 (by decide +kernel) resval5H104
theorem resval5H96 : resval5Tail96=hornerBox Q residualBox cell5 96 124 :=
  hornerChunk_step Q residualBox cell5 resval5Tail96 resval5Tail100 96 4 120 (by decide +kernel) resval5H100
theorem resval5H92 : resval5Tail92=hornerBox Q residualBox cell5 92 128 :=
  hornerChunk_step Q residualBox cell5 resval5Tail92 resval5Tail96 92 4 124 (by decide +kernel) resval5H96
theorem resval5H88 : resval5Tail88=hornerBox Q residualBox cell5 88 132 :=
  hornerChunk_step Q residualBox cell5 resval5Tail88 resval5Tail92 88 4 128 (by decide +kernel) resval5H92
theorem resval5H84 : resval5Tail84=hornerBox Q residualBox cell5 84 136 :=
  hornerChunk_step Q residualBox cell5 resval5Tail84 resval5Tail88 84 4 132 (by decide +kernel) resval5H88
theorem resval5H80 : resval5Tail80=hornerBox Q residualBox cell5 80 140 :=
  hornerChunk_step Q residualBox cell5 resval5Tail80 resval5Tail84 80 4 136 (by decide +kernel) resval5H84
theorem resval5H76 : resval5Tail76=hornerBox Q residualBox cell5 76 144 :=
  hornerChunk_step Q residualBox cell5 resval5Tail76 resval5Tail80 76 4 140 (by decide +kernel) resval5H80
theorem resval5H72 : resval5Tail72=hornerBox Q residualBox cell5 72 148 :=
  hornerChunk_step Q residualBox cell5 resval5Tail72 resval5Tail76 72 4 144 (by decide +kernel) resval5H76
theorem resval5H68 : resval5Tail68=hornerBox Q residualBox cell5 68 152 :=
  hornerChunk_step Q residualBox cell5 resval5Tail68 resval5Tail72 68 4 148 (by decide +kernel) resval5H72
theorem resval5H64 : resval5Tail64=hornerBox Q residualBox cell5 64 156 :=
  hornerChunk_step Q residualBox cell5 resval5Tail64 resval5Tail68 64 4 152 (by decide +kernel) resval5H68
theorem resval5H60 : resval5Tail60=hornerBox Q residualBox cell5 60 160 :=
  hornerChunk_step Q residualBox cell5 resval5Tail60 resval5Tail64 60 4 156 (by decide +kernel) resval5H64
theorem resval5H56 : resval5Tail56=hornerBox Q residualBox cell5 56 164 :=
  hornerChunk_step Q residualBox cell5 resval5Tail56 resval5Tail60 56 4 160 (by decide +kernel) resval5H60
theorem resval5H52 : resval5Tail52=hornerBox Q residualBox cell5 52 168 :=
  hornerChunk_step Q residualBox cell5 resval5Tail52 resval5Tail56 52 4 164 (by decide +kernel) resval5H56
theorem resval5H48 : resval5Tail48=hornerBox Q residualBox cell5 48 172 :=
  hornerChunk_step Q residualBox cell5 resval5Tail48 resval5Tail52 48 4 168 (by decide +kernel) resval5H52
theorem resval5H44 : resval5Tail44=hornerBox Q residualBox cell5 44 176 :=
  hornerChunk_step Q residualBox cell5 resval5Tail44 resval5Tail48 44 4 172 (by decide +kernel) resval5H48
theorem resval5H40 : resval5Tail40=hornerBox Q residualBox cell5 40 180 :=
  hornerChunk_step Q residualBox cell5 resval5Tail40 resval5Tail44 40 4 176 (by decide +kernel) resval5H44
theorem resval5H36 : resval5Tail36=hornerBox Q residualBox cell5 36 184 :=
  hornerChunk_step Q residualBox cell5 resval5Tail36 resval5Tail40 36 4 180 (by decide +kernel) resval5H40
theorem resval5H32 : resval5Tail32=hornerBox Q residualBox cell5 32 188 :=
  hornerChunk_step Q residualBox cell5 resval5Tail32 resval5Tail36 32 4 184 (by decide +kernel) resval5H36
theorem resval5H28 : resval5Tail28=hornerBox Q residualBox cell5 28 192 :=
  hornerChunk_step Q residualBox cell5 resval5Tail28 resval5Tail32 28 4 188 (by decide +kernel) resval5H32
theorem resval5H24 : resval5Tail24=hornerBox Q residualBox cell5 24 196 :=
  hornerChunk_step Q residualBox cell5 resval5Tail24 resval5Tail28 24 4 192 (by decide +kernel) resval5H28
theorem resval5H20 : resval5Tail20=hornerBox Q residualBox cell5 20 200 :=
  hornerChunk_step Q residualBox cell5 resval5Tail20 resval5Tail24 20 4 196 (by decide +kernel) resval5H24
theorem resval5H16 : resval5Tail16=hornerBox Q residualBox cell5 16 204 :=
  hornerChunk_step Q residualBox cell5 resval5Tail16 resval5Tail20 16 4 200 (by decide +kernel) resval5H20
theorem resval5H12 : resval5Tail12=hornerBox Q residualBox cell5 12 208 :=
  hornerChunk_step Q residualBox cell5 resval5Tail12 resval5Tail16 12 4 204 (by decide +kernel) resval5H16
theorem resval5H8 : resval5Tail8=hornerBox Q residualBox cell5 8 212 :=
  hornerChunk_step Q residualBox cell5 resval5Tail8 resval5Tail12 8 4 208 (by decide +kernel) resval5H12
theorem resval5H4 : resval5Tail4=hornerBox Q residualBox cell5 4 216 :=
  hornerChunk_step Q residualBox cell5 resval5Tail4 resval5Tail8 4 4 212 (by decide +kernel) resval5H8
theorem resval5H0 : resval5=hornerBox Q residualBox cell5 0 220 :=
  hornerChunk_step Q residualBox cell5 resval5 resval5Tail4 0 4 216 (by decide +kernel) resval5H4
theorem resval5_eq : resval5=hornerBox Q residualBox cell5 0 220 := resval5H0
def polyval5Tail5 : Box := ⟨5235276697143053393243104448840867598031617772430630254939,3765581028945367753637355296249149193736993918672214493441⟩
def polyval5Tail9 : Box := ⟨5756245644055731724358607976146460288437414769888599210022,3829844493152769916502806696818932177124158264585709387462⟩
def polyval5Tail13 : Box := ⟨6329059017807590086820816361165660800517381295098708785033,3880317163903262748844787648251760166758900090650371212671⟩
def polyval5Tail17 : Box := ⟨6958873982959880247624350235224888954646586672226325175546,3914314202157597863788479022453585353985314524848733889209⟩
def polyval5Tail21 : Box := ⟨7651362860492274066678921960290278288448182478982251798147,3928798278125660047980407664827359152302395344493909287592⟩
def polyval5Tail25 : Box := ⟨8412762433444691856121552000419679352983417029166187624014,3920338926826499195256567582079802048484973290590650953572⟩
def polyval5Tail29 : Box := ⟨9249930117289556005486323952234579990420131719888003204758,3885067517197293218887179190328675011552775869815321023936⟩
def polyval5Tail33 : Box := ⟨10170405720075286324709162384188983848954660254815110189580,3818627355882618896830343496963696078587403225798397250186⟩
def polyval5Tail37 : Box := ⟨11182479348422319468149225040007262694887254070863134183815,3716118416562319471112579901987632353832059219531927567536⟩
def polyval5Tail41 : Box := ⟨12295266070955328335914292613349679529347256046258059503392,3572036133389907087826069646187877568326604191360272821599⟩
def polyval5Tail45 : Box := ⟨13518788011615116974003219055187111572560211838948819864736,3380203639514861274210188995475602850377603699826548497131⟩
def polyval5Tail49 : Box := ⟨14864064612209611658910070886061819872536088204112447713225,3133696768219393982996729425456432799587844555356020885867⟩
def polyval5Tail53 : Box := ⟨16343211877138228319516521401638567431220807411476603990557,2824761064324370383243726545918943061071951957222948554173⟩
def polyval5Tail57 : Box := ⟨17969551494120309958299297205707915629425079582630389303497,2444719976562146158047106244431287683174179764158541019360⟩
def polyval5Tail61 : Box := ⟨19757730813704878471402066138403434486910725731336739932012,1983873316863163937915151818001037591838699917992601998148⟩
def polyval5Tail65 : Box := ⟨21723854768140004290762308311253488533927661998954607527805,1431384979173319959205179286274749840828443530232295600369⟩
def polyval5Tail69 : Box := ⟨23885630945134601106071284411072614728824694069036051951113,775158804360996897085945418096023253493916483492434832203⟩
def polyval5Tail73 : Box := ⟨26281250000000000000000000000000000000000000000000000000000,2⟩
theorem polyval5H73 : polyval5Tail73=hornerBox Q polyBox cell5 73 1 :=
  hornerChunk_step Q polyBox cell5 polyval5Tail73 zero 73 1 0 (by decide +kernel) rfl
theorem polyval5H69 : polyval5Tail69=hornerBox Q polyBox cell5 69 5 :=
  hornerChunk_step Q polyBox cell5 polyval5Tail69 polyval5Tail73 69 4 1 (by decide +kernel) polyval5H73
theorem polyval5H65 : polyval5Tail65=hornerBox Q polyBox cell5 65 9 :=
  hornerChunk_step Q polyBox cell5 polyval5Tail65 polyval5Tail69 65 4 5 (by decide +kernel) polyval5H69
theorem polyval5H61 : polyval5Tail61=hornerBox Q polyBox cell5 61 13 :=
  hornerChunk_step Q polyBox cell5 polyval5Tail61 polyval5Tail65 61 4 9 (by decide +kernel) polyval5H65
theorem polyval5H57 : polyval5Tail57=hornerBox Q polyBox cell5 57 17 :=
  hornerChunk_step Q polyBox cell5 polyval5Tail57 polyval5Tail61 57 4 13 (by decide +kernel) polyval5H61
theorem polyval5H53 : polyval5Tail53=hornerBox Q polyBox cell5 53 21 :=
  hornerChunk_step Q polyBox cell5 polyval5Tail53 polyval5Tail57 53 4 17 (by decide +kernel) polyval5H57
theorem polyval5H49 : polyval5Tail49=hornerBox Q polyBox cell5 49 25 :=
  hornerChunk_step Q polyBox cell5 polyval5Tail49 polyval5Tail53 49 4 21 (by decide +kernel) polyval5H53
theorem polyval5H45 : polyval5Tail45=hornerBox Q polyBox cell5 45 29 :=
  hornerChunk_step Q polyBox cell5 polyval5Tail45 polyval5Tail49 45 4 25 (by decide +kernel) polyval5H49
theorem polyval5H41 : polyval5Tail41=hornerBox Q polyBox cell5 41 33 :=
  hornerChunk_step Q polyBox cell5 polyval5Tail41 polyval5Tail45 41 4 29 (by decide +kernel) polyval5H45
theorem polyval5H37 : polyval5Tail37=hornerBox Q polyBox cell5 37 37 :=
  hornerChunk_step Q polyBox cell5 polyval5Tail37 polyval5Tail41 37 4 33 (by decide +kernel) polyval5H41
theorem polyval5H33 : polyval5Tail33=hornerBox Q polyBox cell5 33 41 :=
  hornerChunk_step Q polyBox cell5 polyval5Tail33 polyval5Tail37 33 4 37 (by decide +kernel) polyval5H37
theorem polyval5H29 : polyval5Tail29=hornerBox Q polyBox cell5 29 45 :=
  hornerChunk_step Q polyBox cell5 polyval5Tail29 polyval5Tail33 29 4 41 (by decide +kernel) polyval5H33
theorem polyval5H25 : polyval5Tail25=hornerBox Q polyBox cell5 25 49 :=
  hornerChunk_step Q polyBox cell5 polyval5Tail25 polyval5Tail29 25 4 45 (by decide +kernel) polyval5H29
theorem polyval5H21 : polyval5Tail21=hornerBox Q polyBox cell5 21 53 :=
  hornerChunk_step Q polyBox cell5 polyval5Tail21 polyval5Tail25 21 4 49 (by decide +kernel) polyval5H25
theorem polyval5H17 : polyval5Tail17=hornerBox Q polyBox cell5 17 57 :=
  hornerChunk_step Q polyBox cell5 polyval5Tail17 polyval5Tail21 17 4 53 (by decide +kernel) polyval5H21
theorem polyval5H13 : polyval5Tail13=hornerBox Q polyBox cell5 13 61 :=
  hornerChunk_step Q polyBox cell5 polyval5Tail13 polyval5Tail17 13 4 57 (by decide +kernel) polyval5H17
theorem polyval5H9 : polyval5Tail9=hornerBox Q polyBox cell5 9 65 :=
  hornerChunk_step Q polyBox cell5 polyval5Tail9 polyval5Tail13 9 4 61 (by decide +kernel) polyval5H13
theorem polyval5H5 : polyval5Tail5=hornerBox Q polyBox cell5 5 69 :=
  hornerChunk_step Q polyBox cell5 polyval5Tail5 polyval5Tail9 5 4 65 (by decide +kernel) polyval5H9
theorem polyval5H1 : polyval5=hornerBox Q polyBox cell5 1 73 :=
  hornerChunk_step Q polyBox cell5 polyval5 polyval5Tail5 1 4 69 (by decide +kernel) polyval5H5
theorem polyval5_eq : polyval5=hornerBox Q polyBox cell5 1 73 := polyval5H1
theorem polyval5_upper : 5*(polyval5.center+polyval5.radius)<Q := by decide +kernel
theorem resval5_pos : 0<(resval5).center-(resval5).radius := by decide +kernel
theorem polyval5_pos : 0<(polyval5).center-(polyval5).radius := by decide +kernel
def cell6 : Box := ⟨988281250000000000000000000000000000000000000000000000000000,3906250000000000000000000000000000000000000000000000000002⟩
def resval6 : Box := ⟨67649631350281480199380680782565505320109330661788253077,14939016057051835572154635024567337488849110489686671290⟩
def polyval6 : Box := ⟨14926651630069174471814422490733448307753722312218243236194,3698075876857565355266745522115258565793638972344264182898⟩
theorem cell6_lo : Holds Q cell6 (63/64:ℝ) := by norm_num [Holds,Q,cell6]
theorem cell6_hi : Holds Q cell6 (127/128:ℝ) := by norm_num [Holds,Q,cell6]
def resval6Tail4 : Box := ⟨-39201583443870144282973943780709490771940077263680999817,14452703069798758176466723018698694519889850062053144889⟩
def resval6Tail8 : Box := ⟨-41094330087267335466727896342616833323262588834590165656,14269967117771901817672167027010562051602021053477627565⟩
def resval6Tail12 : Box := ⟨-43078411615638999794417539514347939812647433993952716286,14050346872408202423296480787813051119496272809500265855⟩
def resval6Tail16 : Box := ⟨-45158286877077485204276401200275683907210879389068036872,13791166305983990183968364379949818030201132851550039150⟩
def resval6Tail20 : Box := ⟨-47338580908398999220068533426065367738380197066832911672,13489592546635817600371547152517714335342168346681005902⟩
def resval6Tail24 : Box := ⟨-49624142043318912392528086388501963406794137875598717166,13142626536970106852232014366994722179156054373510479193⟩
def resval6Tail28 : Box := ⟨-52020052698676806585111963905217011354974787902168299512,12747094072939201810538517750623140108003869174017509771⟩
def resval6Tail32 : Box := ⟨-54531640676243041991814821430056858372275115123007453712,12299636380345146848349980547343522375591123783436997744⟩
def resval6Tail36 : Box := ⟨-57164491010185469730588070130500026707298692588405271650,11796700205541277742665458890961434879707229480850793733⟩
def resval6Tail40 : Box := ⟨-59924458386545450614721919591590389929907886288600514311,11234527395893957119851638151432147532376876582054490704⟩
def resval6Tail44 : Box := ⟨-62817680162340460802380336658865041043058297562677600217,10609143944355779799860438062445399746386307613527145917⟩
def resval6Tail48 : Box := ⟨-65850590013243945765720002902342625951555948930738652092,9916348471230919887153526582325635075575802397898870084⟩
def resval6Tail52 : Box := ⟨-69029932240190855073975770548698460812603184728897904855,9151700114880258860892274783370548667197598464537191689⟩
def resval6Tail56 : Box := ⟨-72362776766722543923832734591946936202243562470242495768,8310505801715477826189878254399713695324655323099180320⟩
def resval6Tail60 : Box := ⟨-75856534860419638470257885101556524643021254326649071820,7387806864364045090306091689911639795297828860956758279⟩
def resval6Tail64 : Box := ⟨-79518975611783832754703318433274203974278083395155669956,6378364975133234398641495174977365135924426489825952907⟩
def resval6Tail68 : Box := ⟨-83358215756195350144181739414102386597704323224736023288,5276644492678276151538471719304330539995695248277848551⟩
def resval6Tail72 : Box := ⟨727705827269159894471066053425264459146118768735892167675,1326593104404663502875936415363993878750251107817990795⟩
def resval6Tail76 : Box := ⟨-504096214819520154393953197786068853570626628473543265,188039757434376102351860135396388526555955621274631884⟩
def resval6Tail80 : Box := ⟨-528411857161029770890363631203959541118206114438762523,185759879463067179298355316283473101220679313991143452⟩
def resval6Tail84 : Box := ⟨-553924188327618424542819781731878794053307354157779562,183008214986300121412515859561234893625081649174953131⟩
def resval6Tail88 : Box := ⟨-580668285261116705552287254114732229735896393386416581,179750168735044098808922791776079875952341518610775710⟩
def resval6Tail92 : Box := ⟨-608703617956057468214926383235137899737922654671811087,175949387635835932465678249756617065753065317327143943⟩
def resval6Tail96 : Box := ⟨-638092528759648242649056588070066409829763099053726700,171567384080264734347984573736532223032066047058342285⟩
def resval6Tail100 : Box := ⟨-668900369979853975919860646642342946191986381501418593,166563420750712312781421175920409332089308594642977292⟩
def resval6Tail104 : Box := ⟨-701195649209237396955777371790860987720814974585094521,160894389525207010993084059134473235739552131220080024⟩
def resval6Tail108 : Box := ⟨-735050181665727355512407513775587232499372676125927124,154514684138055423751365187537094501932218153386095672⟩
def resval6Tail112 : Box := ⟨-770539249888575907118851623856982465327460503654260046,147376066282081772800119085213839814600542871330313848⟩
def resval6Tail116 : Box := ⟨-807741771144619897525285027594274402165970323065113764,139427524822751839066506683519113100504302655517583126⟩
def resval6Tail120 : Box := ⟨-846740472917109406737949636057553889171834907517438200,130615127778122263391591100519936926516940587598190960⟩
def resval6Tail124 : Box := ⟨-887622076867338677328459778897340876298613793602729949,120881866701417868726657672891403008257586405767385734⟩
def resval6Tail128 : Box := ⟨-930477491678156199877938430137778848014405618008532844,110167493085060337751845478116330868417047010601481139⟩
def resval6Tail132 : Box := ⟨-975402015208186057766466464355498772698235774945077057,98408346386109219216541097736400533715867404411699290⟩
def resval6Tail136 : Box := ⟨-1022495546410648878192877324059951295257979567291680174,85537173252633750140460497737572478920198005127908019⟩
def resval6Tail140 : Box := ⟨-1071862842848485067898147265703319928888218969364583428,71482933268181066818707285364561328414484323924643437⟩
def resval6Tail144 : Box := ⟨-1146185086602442357309105904878894363884271465344939683,54190855092265276676287614948481122178897518257963338⟩
def resval6Tail148 : Box := ⟨182384063485013429364402845964575296610617724287,58972015577295389298149851842068607946124638729⟩
def resval6Tail152 : Box := ⟨191141706995754577512795019692085856587271416740,57858450467905428083733962779288264359804098535⟩
def resval6Tail156 : Box := ⟨200370247711392070908748955889639836100470533380,56565549081987995750274791300902301772523659015⟩
def resval6Tail160 : Box := ⟨210044353735814717497715378155991750664797192860,55079992127220065194911726991643809805411392931⟩
def resval6Tail164 : Box := ⟨220185536726426028287061411036502423392301962061,53388327431880309814984346439271651737362718475⟩
def resval6Tail168 : Box := ⟨230816347696175909395539048126775124995542335511,51476321077335429431403183332172858523745865159⟩
def resval6Tail172 : Box := ⟨241960426447065164478150823662298136537171806903,49328915422077844121883546013417806127192717517⟩
def resval6Tail176 : Box := ⟨253642554137925923040297360540593697732266419481,46930184981398452518555184393141153713075762563⟩
def resval6Tail180 : Box := ⟨265888708390441929687321535494248463001768492477,44263290038250964912811306006266257953967696529⟩
def resval6Tail184 : Box := ⟨278726121055751185574333511875248498873463383371,41310427871341495323653319522581566268133909171⟩
def resval6Tail188 : Box := ⟨292183338770086610010592941301502634316265428278,38052781480841159633961882935903830109621282509⟩
def resval6Tail192 : Box := ⟨306290286434112684108634698091663829583874217884,34470465686199608880871723413468409965912147924⟩
def resval6Tail196 : Box := ⟨321078333757117481293062578227008328937639896801,30542470464327146627458499054804361901060430003⟩
def resval6Tail200 : Box := ⟨336580365014034828042852122990885634933002169512,26246601389898181289872196457193218972784902455⟩
def resval6Tail204 : Box := ⟨352830852170415741797033231406256137562018986600,21559417032694386447402285673153290086746553053⟩
def resval6Tail208 : Box := ⟨369865931537963078081175890715735915938077612704,16456163159735561152887139492849822196808255601⟩
def resval6Tail212 : Box := ⟨387723484144895557897013665373265687824107433374,10910703580502627359716467489765638190553918321⟩
def resval6Tail216 : Box := ⟨406443834025748137255571437830311070761346105844,4895377957853738251342141285339373258890699666⟩
theorem resval6H216 : resval6Tail216=hornerBox Q residualBox cell6 216 4 :=
  hornerChunk_step Q residualBox cell6 resval6Tail216 zero 216 4 0 (by decide +kernel) rfl
theorem resval6H212 : resval6Tail212=hornerBox Q residualBox cell6 212 8 :=
  hornerChunk_step Q residualBox cell6 resval6Tail212 resval6Tail216 212 4 4 (by decide +kernel) resval6H216
theorem resval6H208 : resval6Tail208=hornerBox Q residualBox cell6 208 12 :=
  hornerChunk_step Q residualBox cell6 resval6Tail208 resval6Tail212 208 4 8 (by decide +kernel) resval6H212
theorem resval6H204 : resval6Tail204=hornerBox Q residualBox cell6 204 16 :=
  hornerChunk_step Q residualBox cell6 resval6Tail204 resval6Tail208 204 4 12 (by decide +kernel) resval6H208
theorem resval6H200 : resval6Tail200=hornerBox Q residualBox cell6 200 20 :=
  hornerChunk_step Q residualBox cell6 resval6Tail200 resval6Tail204 200 4 16 (by decide +kernel) resval6H204
theorem resval6H196 : resval6Tail196=hornerBox Q residualBox cell6 196 24 :=
  hornerChunk_step Q residualBox cell6 resval6Tail196 resval6Tail200 196 4 20 (by decide +kernel) resval6H200
theorem resval6H192 : resval6Tail192=hornerBox Q residualBox cell6 192 28 :=
  hornerChunk_step Q residualBox cell6 resval6Tail192 resval6Tail196 192 4 24 (by decide +kernel) resval6H196
theorem resval6H188 : resval6Tail188=hornerBox Q residualBox cell6 188 32 :=
  hornerChunk_step Q residualBox cell6 resval6Tail188 resval6Tail192 188 4 28 (by decide +kernel) resval6H192
theorem resval6H184 : resval6Tail184=hornerBox Q residualBox cell6 184 36 :=
  hornerChunk_step Q residualBox cell6 resval6Tail184 resval6Tail188 184 4 32 (by decide +kernel) resval6H188
theorem resval6H180 : resval6Tail180=hornerBox Q residualBox cell6 180 40 :=
  hornerChunk_step Q residualBox cell6 resval6Tail180 resval6Tail184 180 4 36 (by decide +kernel) resval6H184
theorem resval6H176 : resval6Tail176=hornerBox Q residualBox cell6 176 44 :=
  hornerChunk_step Q residualBox cell6 resval6Tail176 resval6Tail180 176 4 40 (by decide +kernel) resval6H180
theorem resval6H172 : resval6Tail172=hornerBox Q residualBox cell6 172 48 :=
  hornerChunk_step Q residualBox cell6 resval6Tail172 resval6Tail176 172 4 44 (by decide +kernel) resval6H176
theorem resval6H168 : resval6Tail168=hornerBox Q residualBox cell6 168 52 :=
  hornerChunk_step Q residualBox cell6 resval6Tail168 resval6Tail172 168 4 48 (by decide +kernel) resval6H172
theorem resval6H164 : resval6Tail164=hornerBox Q residualBox cell6 164 56 :=
  hornerChunk_step Q residualBox cell6 resval6Tail164 resval6Tail168 164 4 52 (by decide +kernel) resval6H168
theorem resval6H160 : resval6Tail160=hornerBox Q residualBox cell6 160 60 :=
  hornerChunk_step Q residualBox cell6 resval6Tail160 resval6Tail164 160 4 56 (by decide +kernel) resval6H164
theorem resval6H156 : resval6Tail156=hornerBox Q residualBox cell6 156 64 :=
  hornerChunk_step Q residualBox cell6 resval6Tail156 resval6Tail160 156 4 60 (by decide +kernel) resval6H160
theorem resval6H152 : resval6Tail152=hornerBox Q residualBox cell6 152 68 :=
  hornerChunk_step Q residualBox cell6 resval6Tail152 resval6Tail156 152 4 64 (by decide +kernel) resval6H156
theorem resval6H148 : resval6Tail148=hornerBox Q residualBox cell6 148 72 :=
  hornerChunk_step Q residualBox cell6 resval6Tail148 resval6Tail152 148 4 68 (by decide +kernel) resval6H152
theorem resval6H144 : resval6Tail144=hornerBox Q residualBox cell6 144 76 :=
  hornerChunk_step Q residualBox cell6 resval6Tail144 resval6Tail148 144 4 72 (by decide +kernel) resval6H148
theorem resval6H140 : resval6Tail140=hornerBox Q residualBox cell6 140 80 :=
  hornerChunk_step Q residualBox cell6 resval6Tail140 resval6Tail144 140 4 76 (by decide +kernel) resval6H144
theorem resval6H136 : resval6Tail136=hornerBox Q residualBox cell6 136 84 :=
  hornerChunk_step Q residualBox cell6 resval6Tail136 resval6Tail140 136 4 80 (by decide +kernel) resval6H140
theorem resval6H132 : resval6Tail132=hornerBox Q residualBox cell6 132 88 :=
  hornerChunk_step Q residualBox cell6 resval6Tail132 resval6Tail136 132 4 84 (by decide +kernel) resval6H136
theorem resval6H128 : resval6Tail128=hornerBox Q residualBox cell6 128 92 :=
  hornerChunk_step Q residualBox cell6 resval6Tail128 resval6Tail132 128 4 88 (by decide +kernel) resval6H132
theorem resval6H124 : resval6Tail124=hornerBox Q residualBox cell6 124 96 :=
  hornerChunk_step Q residualBox cell6 resval6Tail124 resval6Tail128 124 4 92 (by decide +kernel) resval6H128
theorem resval6H120 : resval6Tail120=hornerBox Q residualBox cell6 120 100 :=
  hornerChunk_step Q residualBox cell6 resval6Tail120 resval6Tail124 120 4 96 (by decide +kernel) resval6H124
theorem resval6H116 : resval6Tail116=hornerBox Q residualBox cell6 116 104 :=
  hornerChunk_step Q residualBox cell6 resval6Tail116 resval6Tail120 116 4 100 (by decide +kernel) resval6H120
theorem resval6H112 : resval6Tail112=hornerBox Q residualBox cell6 112 108 :=
  hornerChunk_step Q residualBox cell6 resval6Tail112 resval6Tail116 112 4 104 (by decide +kernel) resval6H116
theorem resval6H108 : resval6Tail108=hornerBox Q residualBox cell6 108 112 :=
  hornerChunk_step Q residualBox cell6 resval6Tail108 resval6Tail112 108 4 108 (by decide +kernel) resval6H112
theorem resval6H104 : resval6Tail104=hornerBox Q residualBox cell6 104 116 :=
  hornerChunk_step Q residualBox cell6 resval6Tail104 resval6Tail108 104 4 112 (by decide +kernel) resval6H108
theorem resval6H100 : resval6Tail100=hornerBox Q residualBox cell6 100 120 :=
  hornerChunk_step Q residualBox cell6 resval6Tail100 resval6Tail104 100 4 116 (by decide +kernel) resval6H104
theorem resval6H96 : resval6Tail96=hornerBox Q residualBox cell6 96 124 :=
  hornerChunk_step Q residualBox cell6 resval6Tail96 resval6Tail100 96 4 120 (by decide +kernel) resval6H100
theorem resval6H92 : resval6Tail92=hornerBox Q residualBox cell6 92 128 :=
  hornerChunk_step Q residualBox cell6 resval6Tail92 resval6Tail96 92 4 124 (by decide +kernel) resval6H96
theorem resval6H88 : resval6Tail88=hornerBox Q residualBox cell6 88 132 :=
  hornerChunk_step Q residualBox cell6 resval6Tail88 resval6Tail92 88 4 128 (by decide +kernel) resval6H92
theorem resval6H84 : resval6Tail84=hornerBox Q residualBox cell6 84 136 :=
  hornerChunk_step Q residualBox cell6 resval6Tail84 resval6Tail88 84 4 132 (by decide +kernel) resval6H88
theorem resval6H80 : resval6Tail80=hornerBox Q residualBox cell6 80 140 :=
  hornerChunk_step Q residualBox cell6 resval6Tail80 resval6Tail84 80 4 136 (by decide +kernel) resval6H84
theorem resval6H76 : resval6Tail76=hornerBox Q residualBox cell6 76 144 :=
  hornerChunk_step Q residualBox cell6 resval6Tail76 resval6Tail80 76 4 140 (by decide +kernel) resval6H80
theorem resval6H72 : resval6Tail72=hornerBox Q residualBox cell6 72 148 :=
  hornerChunk_step Q residualBox cell6 resval6Tail72 resval6Tail76 72 4 144 (by decide +kernel) resval6H76
theorem resval6H68 : resval6Tail68=hornerBox Q residualBox cell6 68 152 :=
  hornerChunk_step Q residualBox cell6 resval6Tail68 resval6Tail72 68 4 148 (by decide +kernel) resval6H72
theorem resval6H64 : resval6Tail64=hornerBox Q residualBox cell6 64 156 :=
  hornerChunk_step Q residualBox cell6 resval6Tail64 resval6Tail68 64 4 152 (by decide +kernel) resval6H68
theorem resval6H60 : resval6Tail60=hornerBox Q residualBox cell6 60 160 :=
  hornerChunk_step Q residualBox cell6 resval6Tail60 resval6Tail64 60 4 156 (by decide +kernel) resval6H64
theorem resval6H56 : resval6Tail56=hornerBox Q residualBox cell6 56 164 :=
  hornerChunk_step Q residualBox cell6 resval6Tail56 resval6Tail60 56 4 160 (by decide +kernel) resval6H60
theorem resval6H52 : resval6Tail52=hornerBox Q residualBox cell6 52 168 :=
  hornerChunk_step Q residualBox cell6 resval6Tail52 resval6Tail56 52 4 164 (by decide +kernel) resval6H56
theorem resval6H48 : resval6Tail48=hornerBox Q residualBox cell6 48 172 :=
  hornerChunk_step Q residualBox cell6 resval6Tail48 resval6Tail52 48 4 168 (by decide +kernel) resval6H52
theorem resval6H44 : resval6Tail44=hornerBox Q residualBox cell6 44 176 :=
  hornerChunk_step Q residualBox cell6 resval6Tail44 resval6Tail48 44 4 172 (by decide +kernel) resval6H48
theorem resval6H40 : resval6Tail40=hornerBox Q residualBox cell6 40 180 :=
  hornerChunk_step Q residualBox cell6 resval6Tail40 resval6Tail44 40 4 176 (by decide +kernel) resval6H44
theorem resval6H36 : resval6Tail36=hornerBox Q residualBox cell6 36 184 :=
  hornerChunk_step Q residualBox cell6 resval6Tail36 resval6Tail40 36 4 180 (by decide +kernel) resval6H40
theorem resval6H32 : resval6Tail32=hornerBox Q residualBox cell6 32 188 :=
  hornerChunk_step Q residualBox cell6 resval6Tail32 resval6Tail36 32 4 184 (by decide +kernel) resval6H36
theorem resval6H28 : resval6Tail28=hornerBox Q residualBox cell6 28 192 :=
  hornerChunk_step Q residualBox cell6 resval6Tail28 resval6Tail32 28 4 188 (by decide +kernel) resval6H32
theorem resval6H24 : resval6Tail24=hornerBox Q residualBox cell6 24 196 :=
  hornerChunk_step Q residualBox cell6 resval6Tail24 resval6Tail28 24 4 192 (by decide +kernel) resval6H28
theorem resval6H20 : resval6Tail20=hornerBox Q residualBox cell6 20 200 :=
  hornerChunk_step Q residualBox cell6 resval6Tail20 resval6Tail24 20 4 196 (by decide +kernel) resval6H24
theorem resval6H16 : resval6Tail16=hornerBox Q residualBox cell6 16 204 :=
  hornerChunk_step Q residualBox cell6 resval6Tail16 resval6Tail20 16 4 200 (by decide +kernel) resval6H20
theorem resval6H12 : resval6Tail12=hornerBox Q residualBox cell6 12 208 :=
  hornerChunk_step Q residualBox cell6 resval6Tail12 resval6Tail16 12 4 204 (by decide +kernel) resval6H16
theorem resval6H8 : resval6Tail8=hornerBox Q residualBox cell6 8 212 :=
  hornerChunk_step Q residualBox cell6 resval6Tail8 resval6Tail12 8 4 208 (by decide +kernel) resval6H12
theorem resval6H4 : resval6Tail4=hornerBox Q residualBox cell6 4 216 :=
  hornerChunk_step Q residualBox cell6 resval6Tail4 resval6Tail8 4 4 212 (by decide +kernel) resval6H8
theorem resval6H0 : resval6=hornerBox Q residualBox cell6 0 220 :=
  hornerChunk_step Q residualBox cell6 resval6 resval6Tail4 0 4 216 (by decide +kernel) resval6H4
theorem resval6_eq : resval6=hornerBox Q residualBox cell6 0 220 := resval6H0
def polyval6Tail5 : Box := ⟨11781972981415991391092461898928262610342650519378250936645,3625875286242801467468274659270755294532209823476628614878⟩
def polyval6Tail9 : Box := ⟨12350818322231115640816247073834391899845927592023384587751,3548076527755900728127212260519756557202626953333812849437⟩
def polyval6Tail13 : Box := ⟨12947130036535795238270467069648459088176494551414654768345,3458462915543532115491536750911946946093515045431484248218⟩
def polyval6Tail17 : Box := ⟨13572232366441190399707661321068346612183189414684746239426,3356207166709797678558875250571772491878831751791978363871⟩
def polyval6Tail21 : Box := ⟨14227515355824937782576087986615025743046029919440299560831,3240433889571251299527479397082667227281205794462397085999⟩
def polyval6Tail25 : Box := ⟨14914436161640227594808487546566930265484529771619281502428,3110216981504020054586792560232734385929415910022554775120⟩
def polyval6Tail29 : Box := ⟨15634522294054074981575878374196837535233139424233938122766,2964576911382793470054576039298869458953466821275812261051⟩
def polyval6Tail33 : Box := ⟨16389375013181295503239008454115265295969597043829943730757,2802477862237665989122594469405621841893920332733978635210⟩
def polyval6Tail37 : Box := ⟨17180672889816811538883072777517596680312987393360375641020,2622824727103154608903750858449096563069650718230706216330⟩
def polyval6Tail41 : Box := ⟨18010175538084210301613788600298438825422959835181326686251,2424459950689223352880107920329926470364228120660120206806⟩
def polyval6Tail45 : Box := ⟨18879727528300867516522154141948477818167327206145373429569,2206160209139318859371707443850359978510955807985307739534⟩
def polyval6Tail49 : Box := ⟨19791262488760699833039342502816527711996378173206941071363,1966632919757689375449932836696022535741947634614469446939⟩
def polyval6Tail53 : Box := ⟨20746807405555706379516793820380117065042102929186303023171,1704512572186753022628202621587326305630139563875573986000⟩
def polyval6Tail57 : Box := ⟨21748487129997839999626397328259285619324092281727792098426,1418356872094084484487083182588108131913013383754226975740⟩
def polyval6Tail61 : Box := ⟨22798529103664394307674304137284108485527675624962369111170,1106642687986741271270954480569797178113772290198536275034⟩
def polyval6Tail65 : Box := ⟨23899268311577285583374965526289498438965794617520994275658,767761791306664106395772983358724491560608059712177641880⟩
def polyval6Tail69 : Box := ⟨25053152501657492985695036998852286962482915188606675150384,400016376316585332516523502275343724559419191323619068681⟩
def polyval6Tail73 : Box := ⟨26281250000000000000000000000000000000000000000000000000000,2⟩
theorem polyval6H73 : polyval6Tail73=hornerBox Q polyBox cell6 73 1 :=
  hornerChunk_step Q polyBox cell6 polyval6Tail73 zero 73 1 0 (by decide +kernel) rfl
theorem polyval6H69 : polyval6Tail69=hornerBox Q polyBox cell6 69 5 :=
  hornerChunk_step Q polyBox cell6 polyval6Tail69 polyval6Tail73 69 4 1 (by decide +kernel) polyval6H73
theorem polyval6H65 : polyval6Tail65=hornerBox Q polyBox cell6 65 9 :=
  hornerChunk_step Q polyBox cell6 polyval6Tail65 polyval6Tail69 65 4 5 (by decide +kernel) polyval6H69
theorem polyval6H61 : polyval6Tail61=hornerBox Q polyBox cell6 61 13 :=
  hornerChunk_step Q polyBox cell6 polyval6Tail61 polyval6Tail65 61 4 9 (by decide +kernel) polyval6H65
theorem polyval6H57 : polyval6Tail57=hornerBox Q polyBox cell6 57 17 :=
  hornerChunk_step Q polyBox cell6 polyval6Tail57 polyval6Tail61 57 4 13 (by decide +kernel) polyval6H61
theorem polyval6H53 : polyval6Tail53=hornerBox Q polyBox cell6 53 21 :=
  hornerChunk_step Q polyBox cell6 polyval6Tail53 polyval6Tail57 53 4 17 (by decide +kernel) polyval6H57
theorem polyval6H49 : polyval6Tail49=hornerBox Q polyBox cell6 49 25 :=
  hornerChunk_step Q polyBox cell6 polyval6Tail49 polyval6Tail53 49 4 21 (by decide +kernel) polyval6H53
theorem polyval6H45 : polyval6Tail45=hornerBox Q polyBox cell6 45 29 :=
  hornerChunk_step Q polyBox cell6 polyval6Tail45 polyval6Tail49 45 4 25 (by decide +kernel) polyval6H49
theorem polyval6H41 : polyval6Tail41=hornerBox Q polyBox cell6 41 33 :=
  hornerChunk_step Q polyBox cell6 polyval6Tail41 polyval6Tail45 41 4 29 (by decide +kernel) polyval6H45
theorem polyval6H37 : polyval6Tail37=hornerBox Q polyBox cell6 37 37 :=
  hornerChunk_step Q polyBox cell6 polyval6Tail37 polyval6Tail41 37 4 33 (by decide +kernel) polyval6H41
theorem polyval6H33 : polyval6Tail33=hornerBox Q polyBox cell6 33 41 :=
  hornerChunk_step Q polyBox cell6 polyval6Tail33 polyval6Tail37 33 4 37 (by decide +kernel) polyval6H37
theorem polyval6H29 : polyval6Tail29=hornerBox Q polyBox cell6 29 45 :=
  hornerChunk_step Q polyBox cell6 polyval6Tail29 polyval6Tail33 29 4 41 (by decide +kernel) polyval6H33
theorem polyval6H25 : polyval6Tail25=hornerBox Q polyBox cell6 25 49 :=
  hornerChunk_step Q polyBox cell6 polyval6Tail25 polyval6Tail29 25 4 45 (by decide +kernel) polyval6H29
theorem polyval6H21 : polyval6Tail21=hornerBox Q polyBox cell6 21 53 :=
  hornerChunk_step Q polyBox cell6 polyval6Tail21 polyval6Tail25 21 4 49 (by decide +kernel) polyval6H25
theorem polyval6H17 : polyval6Tail17=hornerBox Q polyBox cell6 17 57 :=
  hornerChunk_step Q polyBox cell6 polyval6Tail17 polyval6Tail21 17 4 53 (by decide +kernel) polyval6H21
theorem polyval6H13 : polyval6Tail13=hornerBox Q polyBox cell6 13 61 :=
  hornerChunk_step Q polyBox cell6 polyval6Tail13 polyval6Tail17 13 4 57 (by decide +kernel) polyval6H17
theorem polyval6H9 : polyval6Tail9=hornerBox Q polyBox cell6 9 65 :=
  hornerChunk_step Q polyBox cell6 polyval6Tail9 polyval6Tail13 9 4 61 (by decide +kernel) polyval6H13
theorem polyval6H5 : polyval6Tail5=hornerBox Q polyBox cell6 5 69 :=
  hornerChunk_step Q polyBox cell6 polyval6Tail5 polyval6Tail9 5 4 65 (by decide +kernel) polyval6H9
theorem polyval6H1 : polyval6=hornerBox Q polyBox cell6 1 73 :=
  hornerChunk_step Q polyBox cell6 polyval6 polyval6Tail5 1 4 69 (by decide +kernel) polyval6H5
theorem polyval6_eq : polyval6=hornerBox Q polyBox cell6 1 73 := polyval6H1
theorem polyval6_upper : 5*(polyval6.center+polyval6.radius)<Q := by decide +kernel
theorem resval6_pos : 0<(resval6).center-(resval6).radius := by decide +kernel
theorem polyval6_pos : 0<(polyval6).center-(polyval6).radius := by decide +kernel
def cell7 : Box := ⟨996093750000000000000000000000000000000000000000000000000000,3906250000000000000000000000000000000000000000000000000002⟩
def resval7 : Box := ⟨43740153992990559159175993242977642005660988105753739040,24491611214682985903527052545831356726724515561638283118⟩
def polyval7 : Box := ⟨23500327646543940233428385513411185998602951108153223057375,6456573278425923432519899937940972144119679515274819443667⟩
theorem cell7_lo : Holds Q cell7 (127/128:ℝ) := by norm_num [Holds,Q,cell7]
theorem cell7_hi : Holds Q cell7 (1/1:ℝ) := by norm_num [Holds,Q,cell7]
def resval7Tail4 : Box := ⟨-62268658319147718234402662180930334318099718159827147831,23186335325212399862930281868573141920148156196926208101⟩
def resval7Tail8 : Box := ⟨-63251229844783957125748365505566613279464659367745793887,22203809794338393347986904814470306694288053470164176515⟩
def resval7Tail12 : Box := ⟨-64249257607915084546093072440925869527976714980642340062,21205782036024548440683641830600831813447823104511035169⟩
def resval7Tail16 : Box := ⟨-65263033034682384129218965672159371745719061647049333414,20192006609261018292273719329749907625273009286918949587⟩
def resval7Tail20 : Box := ⟨-66292804609170614733671081325148787522868472561877597547,19162235034772800479314168285173733619381784388594302225⟩
def resval7Tail24 : Box := ⟨-67338824731210405165961916889985033796823016353471131032,18116214912733010190219012585819556811324076350609338829⟩
def resval7Tail28 : Box := ⟨-68401349783191879905420433422650260884333171410965289578,17053689860751535455119905436532290240450098782790498458⟩
def resval7Tail32 : Box := ⟨-69480640192908577808885359220844637306851897737764452004,15974399451034837551941989466723957020091944076443177291⟩
def resval7Tail36 : Box := ⟨-70576960497389029016525364966259587728685510846514203476,14878079146554386344312145127900825037018644419782405231⟩
def resval7Tail40 : Box := ⟨-71690579407735503619792417016715704696477805072844543276,13764460236207911740980817614846515388349846159971439254⟩
def resval7Tail44 : Box := ⟨-72821769874985837071618882654879944056022556703987462881,12633269768957578288844230606322934737939972826513067828⟩
def resval7Tail48 : Box := ⟨-73970809157014475383984790978831842297245647660283969624,11484230486928939973575695983192210167449061663069675520⟩
def resval7Tail52 : Box := ⟨-75137978886489137700102927142256148480796609085383567258,10317060757454277588619808272123800647359982433554736822⟩
def resval7Tail56 : Box := ⟨-76323565139899748795586192891215069965423692957818500589,9131474504043661594624014242746228305719556127168486809⟩
def resval7Tail60 : Box := ⟨-77527858507675473534637302632495089269583022007523595309,7927181136266641100684882359530438386482879951223486859⟩
def resval7Tail64 : Box := ⟨-78751154163819225563509868106893829828741982828870581794,6703885478314370187613901096498016539871571249446587933⟩
def resval7Tail68 : Box := ⟨-79993724686618106258117222306905428957953071024392971107,5461284851826445881176408100859859041111085928044087928⟩
def resval7Tail72 : Box := ⟨727448747284461715598160086277103323297103520289290927290,1448251398646580315070019371587585850642889341427678410⟩
def resval7Tail76 : Box := ⟨-803578595671074813031679109262979933402328107295059882,301296177267247093846443650653585849424557957155755590⟩
def resval7Tail80 : Box := ⟨-816236102979967519520848174867915904049350203879444473,288616754896757119247170901687804492327603072346273481⟩
def resval7Tail84 : Box := ⟨-829115318516576522330048814512958573285827926080350567,275737538311840035963630950664893258322430794915379573⟩
def resval7Tail88 : Box := ⟨-842197753506899124246212139139447259499175776753215074,262655103320991429220706451017952237769803839504612073⟩
def resval7Tail92 : Box := ⟨-855486613468376371552036512795046226445965058011856107,249366243359512893086409910030747743587173496826632846⟩
def resval7Tail96 : Box := ⟨-868985155536391507370003898331405104582682683615130862,235867701291497745958594810504883259531222320939486955⟩
def resval7Tail100 : Box := ⟨-882696688240488313269339145614085547249466577695627577,222156168587400939763687574580012991343375676534689240⟩
def resval7Tail104 : Box := ⟨-896624572314798649971628933301394806316336207174179495,208228284513090603041250515793809537220088097924728757⟩
def resval7Tail108 : Box := ⟨-910772221521766396816741381928894947667176103579031179,194080635306122856193029364804450222662852967130106385⟩
def resval7Tail112 : Box := ⟨-925143103488869945234145064903249497710058002562273836,179709753339019307774904353842085829524749019740265701⟩
def resval7Tail116 : Box := ⟨-939740740558547168615202690661285356408761064206057921,165112116269342084394941953190053198640789312004209212⟩
def resval7Tail120 : Box := ⟨-954568710651531178471247071424663299560095693614760789,150284146176358074554989495017621572941871555631760795⟩
def resval7Tail124 : Box := ⟨-969630648143808473006109607518291341102306202534626301,135222208684080780377637828938434603304940722563930221⟩
def resval7Tail128 : Box := ⟨-984930244757414446353270825107110011676820094365806466,119922612070474827687256415165928377968236893043393414⟩
def resval7Tail132 : Box := ⟨-1000471250465289326306020502311728863889077543626529196,104381606362603959443016866478370544952278463370213207⟩
def resval7Tail136 : Box := ⟨-1016257474414743379393118575800870945863106625435768753,88595382416850383346790614277780428057995518310079723⟩
def resval7Tail140 : Box := ⟨-1032292820973325479894006313624438877458918659252738947,72560066778795021198310541966622035848649116535671471⟩
def resval7Tail144 : Box := ⟨-1070978451748049321435090005106161093710798947321400811,54308392780146443417543375107524161844715558444069293⟩
def resval7Tail148 : Box := ⟨316474440958667039678584682176299934133741883701,101434112490992567881593980902773309374465071630⟩
def resval7Tail152 : Box := ⟨321421459321463929240205244026704161957169998391,96440643403555881030790733687266672512283451181⟩
def resval7Tail156 : Box := ⟨326493099720979820081310416088372656281631572550,91369002274525886183602756002417973975533859540⟩
def resval7Tail160 : Box := ⟨331644765184755731539340333504692320560945140527,86217336810544197608772015250714966875985290453⟩
def resval7Tail164 : Box := ⟨336877717686880011010122002200834966646476705376,80984384308419598449892274570593001832299023643⟩
def resval7Tail168 : Box := ⟨342193239838111632289814589418934756287211820086,75668862157187975283238012187655216715737294814⟩
def resval7Tail172 : Box := ⟨347592634487453968022487538868528042076691731043,70269467507845639516151563673609862710237555231⟩
def resval7Tail176 : Box := ⟨353077225041289153704302642464310364378314782838,64784876954010453832648600462768028816637689275⟩
def resval7Tail180 : Box := ⟨358648355787748311357225295818332739746406497673,59213746207551296179528774755337611371388714932⟩
def resval7Tail184 : Box := ⟨364307392226200242034714947577509647629320533080,53554709769099365501994680002080436872977042583⟩
def resval7Tail188 : Box := ⟨370055721401939052249662384708250839220397546220,47806380593360555287048589834724927366841302107⟩
def resval7Tail192 : Box := ⟨375894752246152745592928099558696249428784587109,41967349749146861943951171838247927896492817907⟩
def resval7Tail196 : Box := ⟨381825915921256106751878051983759376254623853891,36036186074043500787771236596939742141031423921⟩
def resval7Tail200 : Box := ⟨387850666171672520072742330223268066516814045340,30011435823627087567818337637603460487574478754⟩
def resval7Tail204 : Box := ⟨393970479680150713031865413030412854511620668282,23891622315148905482712094513998628060986006636⟩
def resval7Tail208 : Box := ⟨400186856429709190507651785404752108042256317729,17675245565594983892155239950221882112629359931⟩
def resval7Tail212 : Box := ⟨406501320085006584704930474957827640062941356466,11360781922128014637774469948292968567915293735⟩
def resval7Tail216 : Box := ⟨412916027815362598868593520070157374446671736500,4946614762280266425142256179410637604375180555⟩
theorem resval7H216 : resval7Tail216=hornerBox Q residualBox cell7 216 4 :=
  hornerChunk_step Q residualBox cell7 resval7Tail216 zero 216 4 0 (by decide +kernel) rfl
theorem resval7H212 : resval7Tail212=hornerBox Q residualBox cell7 212 8 :=
  hornerChunk_step Q residualBox cell7 resval7Tail212 resval7Tail216 212 4 4 (by decide +kernel) resval7H216
theorem resval7H208 : resval7Tail208=hornerBox Q residualBox cell7 208 12 :=
  hornerChunk_step Q residualBox cell7 resval7Tail208 resval7Tail212 208 4 8 (by decide +kernel) resval7H212
theorem resval7H204 : resval7Tail204=hornerBox Q residualBox cell7 204 16 :=
  hornerChunk_step Q residualBox cell7 resval7Tail204 resval7Tail208 204 4 12 (by decide +kernel) resval7H208
theorem resval7H200 : resval7Tail200=hornerBox Q residualBox cell7 200 20 :=
  hornerChunk_step Q residualBox cell7 resval7Tail200 resval7Tail204 200 4 16 (by decide +kernel) resval7H204
theorem resval7H196 : resval7Tail196=hornerBox Q residualBox cell7 196 24 :=
  hornerChunk_step Q residualBox cell7 resval7Tail196 resval7Tail200 196 4 20 (by decide +kernel) resval7H200
theorem resval7H192 : resval7Tail192=hornerBox Q residualBox cell7 192 28 :=
  hornerChunk_step Q residualBox cell7 resval7Tail192 resval7Tail196 192 4 24 (by decide +kernel) resval7H196
theorem resval7H188 : resval7Tail188=hornerBox Q residualBox cell7 188 32 :=
  hornerChunk_step Q residualBox cell7 resval7Tail188 resval7Tail192 188 4 28 (by decide +kernel) resval7H192
theorem resval7H184 : resval7Tail184=hornerBox Q residualBox cell7 184 36 :=
  hornerChunk_step Q residualBox cell7 resval7Tail184 resval7Tail188 184 4 32 (by decide +kernel) resval7H188
theorem resval7H180 : resval7Tail180=hornerBox Q residualBox cell7 180 40 :=
  hornerChunk_step Q residualBox cell7 resval7Tail180 resval7Tail184 180 4 36 (by decide +kernel) resval7H184
theorem resval7H176 : resval7Tail176=hornerBox Q residualBox cell7 176 44 :=
  hornerChunk_step Q residualBox cell7 resval7Tail176 resval7Tail180 176 4 40 (by decide +kernel) resval7H180
theorem resval7H172 : resval7Tail172=hornerBox Q residualBox cell7 172 48 :=
  hornerChunk_step Q residualBox cell7 resval7Tail172 resval7Tail176 172 4 44 (by decide +kernel) resval7H176
theorem resval7H168 : resval7Tail168=hornerBox Q residualBox cell7 168 52 :=
  hornerChunk_step Q residualBox cell7 resval7Tail168 resval7Tail172 168 4 48 (by decide +kernel) resval7H172
theorem resval7H164 : resval7Tail164=hornerBox Q residualBox cell7 164 56 :=
  hornerChunk_step Q residualBox cell7 resval7Tail164 resval7Tail168 164 4 52 (by decide +kernel) resval7H168
theorem resval7H160 : resval7Tail160=hornerBox Q residualBox cell7 160 60 :=
  hornerChunk_step Q residualBox cell7 resval7Tail160 resval7Tail164 160 4 56 (by decide +kernel) resval7H164
theorem resval7H156 : resval7Tail156=hornerBox Q residualBox cell7 156 64 :=
  hornerChunk_step Q residualBox cell7 resval7Tail156 resval7Tail160 156 4 60 (by decide +kernel) resval7H160
theorem resval7H152 : resval7Tail152=hornerBox Q residualBox cell7 152 68 :=
  hornerChunk_step Q residualBox cell7 resval7Tail152 resval7Tail156 152 4 64 (by decide +kernel) resval7H156
theorem resval7H148 : resval7Tail148=hornerBox Q residualBox cell7 148 72 :=
  hornerChunk_step Q residualBox cell7 resval7Tail148 resval7Tail152 148 4 68 (by decide +kernel) resval7H152
theorem resval7H144 : resval7Tail144=hornerBox Q residualBox cell7 144 76 :=
  hornerChunk_step Q residualBox cell7 resval7Tail144 resval7Tail148 144 4 72 (by decide +kernel) resval7H148
theorem resval7H140 : resval7Tail140=hornerBox Q residualBox cell7 140 80 :=
  hornerChunk_step Q residualBox cell7 resval7Tail140 resval7Tail144 140 4 76 (by decide +kernel) resval7H144
theorem resval7H136 : resval7Tail136=hornerBox Q residualBox cell7 136 84 :=
  hornerChunk_step Q residualBox cell7 resval7Tail136 resval7Tail140 136 4 80 (by decide +kernel) resval7H140
theorem resval7H132 : resval7Tail132=hornerBox Q residualBox cell7 132 88 :=
  hornerChunk_step Q residualBox cell7 resval7Tail132 resval7Tail136 132 4 84 (by decide +kernel) resval7H136
theorem resval7H128 : resval7Tail128=hornerBox Q residualBox cell7 128 92 :=
  hornerChunk_step Q residualBox cell7 resval7Tail128 resval7Tail132 128 4 88 (by decide +kernel) resval7H132
theorem resval7H124 : resval7Tail124=hornerBox Q residualBox cell7 124 96 :=
  hornerChunk_step Q residualBox cell7 resval7Tail124 resval7Tail128 124 4 92 (by decide +kernel) resval7H128
theorem resval7H120 : resval7Tail120=hornerBox Q residualBox cell7 120 100 :=
  hornerChunk_step Q residualBox cell7 resval7Tail120 resval7Tail124 120 4 96 (by decide +kernel) resval7H124
theorem resval7H116 : resval7Tail116=hornerBox Q residualBox cell7 116 104 :=
  hornerChunk_step Q residualBox cell7 resval7Tail116 resval7Tail120 116 4 100 (by decide +kernel) resval7H120
theorem resval7H112 : resval7Tail112=hornerBox Q residualBox cell7 112 108 :=
  hornerChunk_step Q residualBox cell7 resval7Tail112 resval7Tail116 112 4 104 (by decide +kernel) resval7H116
theorem resval7H108 : resval7Tail108=hornerBox Q residualBox cell7 108 112 :=
  hornerChunk_step Q residualBox cell7 resval7Tail108 resval7Tail112 108 4 108 (by decide +kernel) resval7H112
theorem resval7H104 : resval7Tail104=hornerBox Q residualBox cell7 104 116 :=
  hornerChunk_step Q residualBox cell7 resval7Tail104 resval7Tail108 104 4 112 (by decide +kernel) resval7H108
theorem resval7H100 : resval7Tail100=hornerBox Q residualBox cell7 100 120 :=
  hornerChunk_step Q residualBox cell7 resval7Tail100 resval7Tail104 100 4 116 (by decide +kernel) resval7H104
theorem resval7H96 : resval7Tail96=hornerBox Q residualBox cell7 96 124 :=
  hornerChunk_step Q residualBox cell7 resval7Tail96 resval7Tail100 96 4 120 (by decide +kernel) resval7H100
theorem resval7H92 : resval7Tail92=hornerBox Q residualBox cell7 92 128 :=
  hornerChunk_step Q residualBox cell7 resval7Tail92 resval7Tail96 92 4 124 (by decide +kernel) resval7H96
theorem resval7H88 : resval7Tail88=hornerBox Q residualBox cell7 88 132 :=
  hornerChunk_step Q residualBox cell7 resval7Tail88 resval7Tail92 88 4 128 (by decide +kernel) resval7H92
theorem resval7H84 : resval7Tail84=hornerBox Q residualBox cell7 84 136 :=
  hornerChunk_step Q residualBox cell7 resval7Tail84 resval7Tail88 84 4 132 (by decide +kernel) resval7H88
theorem resval7H80 : resval7Tail80=hornerBox Q residualBox cell7 80 140 :=
  hornerChunk_step Q residualBox cell7 resval7Tail80 resval7Tail84 80 4 136 (by decide +kernel) resval7H84
theorem resval7H76 : resval7Tail76=hornerBox Q residualBox cell7 76 144 :=
  hornerChunk_step Q residualBox cell7 resval7Tail76 resval7Tail80 76 4 140 (by decide +kernel) resval7H80
theorem resval7H72 : resval7Tail72=hornerBox Q residualBox cell7 72 148 :=
  hornerChunk_step Q residualBox cell7 resval7Tail72 resval7Tail76 72 4 144 (by decide +kernel) resval7H76
theorem resval7H68 : resval7Tail68=hornerBox Q residualBox cell7 68 152 :=
  hornerChunk_step Q residualBox cell7 resval7Tail68 resval7Tail72 68 4 148 (by decide +kernel) resval7H72
theorem resval7H64 : resval7Tail64=hornerBox Q residualBox cell7 64 156 :=
  hornerChunk_step Q residualBox cell7 resval7Tail64 resval7Tail68 64 4 152 (by decide +kernel) resval7H68
theorem resval7H60 : resval7Tail60=hornerBox Q residualBox cell7 60 160 :=
  hornerChunk_step Q residualBox cell7 resval7Tail60 resval7Tail64 60 4 156 (by decide +kernel) resval7H64
theorem resval7H56 : resval7Tail56=hornerBox Q residualBox cell7 56 164 :=
  hornerChunk_step Q residualBox cell7 resval7Tail56 resval7Tail60 56 4 160 (by decide +kernel) resval7H60
theorem resval7H52 : resval7Tail52=hornerBox Q residualBox cell7 52 168 :=
  hornerChunk_step Q residualBox cell7 resval7Tail52 resval7Tail56 52 4 164 (by decide +kernel) resval7H56
theorem resval7H48 : resval7Tail48=hornerBox Q residualBox cell7 48 172 :=
  hornerChunk_step Q residualBox cell7 resval7Tail48 resval7Tail52 48 4 168 (by decide +kernel) resval7H52
theorem resval7H44 : resval7Tail44=hornerBox Q residualBox cell7 44 176 :=
  hornerChunk_step Q residualBox cell7 resval7Tail44 resval7Tail48 44 4 172 (by decide +kernel) resval7H48
theorem resval7H40 : resval7Tail40=hornerBox Q residualBox cell7 40 180 :=
  hornerChunk_step Q residualBox cell7 resval7Tail40 resval7Tail44 40 4 176 (by decide +kernel) resval7H44
theorem resval7H36 : resval7Tail36=hornerBox Q residualBox cell7 36 184 :=
  hornerChunk_step Q residualBox cell7 resval7Tail36 resval7Tail40 36 4 180 (by decide +kernel) resval7H40
theorem resval7H32 : resval7Tail32=hornerBox Q residualBox cell7 32 188 :=
  hornerChunk_step Q residualBox cell7 resval7Tail32 resval7Tail36 32 4 184 (by decide +kernel) resval7H36
theorem resval7H28 : resval7Tail28=hornerBox Q residualBox cell7 28 192 :=
  hornerChunk_step Q residualBox cell7 resval7Tail28 resval7Tail32 28 4 188 (by decide +kernel) resval7H32
theorem resval7H24 : resval7Tail24=hornerBox Q residualBox cell7 24 196 :=
  hornerChunk_step Q residualBox cell7 resval7Tail24 resval7Tail28 24 4 192 (by decide +kernel) resval7H28
theorem resval7H20 : resval7Tail20=hornerBox Q residualBox cell7 20 200 :=
  hornerChunk_step Q residualBox cell7 resval7Tail20 resval7Tail24 20 4 196 (by decide +kernel) resval7H24
theorem resval7H16 : resval7Tail16=hornerBox Q residualBox cell7 16 204 :=
  hornerChunk_step Q residualBox cell7 resval7Tail16 resval7Tail20 16 4 200 (by decide +kernel) resval7H20
theorem resval7H12 : resval7Tail12=hornerBox Q residualBox cell7 12 208 :=
  hornerChunk_step Q residualBox cell7 resval7Tail12 resval7Tail16 12 4 204 (by decide +kernel) resval7H16
theorem resval7H8 : resval7Tail8=hornerBox Q residualBox cell7 8 212 :=
  hornerChunk_step Q residualBox cell7 resval7Tail8 resval7Tail12 8 4 208 (by decide +kernel) resval7H12
theorem resval7H4 : resval7Tail4=hornerBox Q residualBox cell7 4 216 :=
  hornerChunk_step Q residualBox cell7 resval7Tail4 resval7Tail8 4 4 212 (by decide +kernel) resval7H8
theorem resval7H0 : resval7=hornerBox Q residualBox cell7 0 220 :=
  hornerChunk_step Q residualBox cell7 resval7 resval7Tail4 0 4 216 (by decide +kernel) resval7H4
theorem resval7_eq : resval7=hornerBox Q residualBox cell7 0 220 := resval7H0
def polyval7Tail5 : Box := ⟨20125986996382951520637361857012996550195385677257033464513,6138506187453398410196890299231620512126783317305460643688⟩
def polyval7Tail9 : Box := ⟨20443548874704350399534918241020827646475328985355853621691,5820942512007757196730237320608064578709435766209397766045⟩
def polyval7Tail13 : Box := ⟨20766123301970402016810762303688228676339618109001208520206,5498368084587210204135886181996760942789352489030692732083⟩
def polyval7Tail17 : Box := ⟨21093787562951276519041276147007046057591881802768198536014,5170703823606227830097476287705762812552224975196609249741⟩
def polyval7Tail21 : Box := ⟨21426621968901683193636742968830227517691569149467588368136,4837869417655820820412506215091549545978788652129823918066⟩
def polyval7Tail25 : Box := ⟨21764708098443870824721934290887703405220483336935681231084,4499783288113633185798255362241872027203064012929738212516⟩
def polyval7Tail29 : Box := ⟨22108128817411993803802913328192881346083206246309979210821,4156362569145510206610694006579703620889698103406412162945⟩
def polyval7Tail33 : Box := ⟨22456968299162651633371400408201460939291716404714770942606,3807523087394852377034061883466822485009161431088490870509⟩
def polyval7Tail37 : Box := ⟨22811312045206008324061313802733151816204586966087042863036,3453179341351495686342787342717325937620412275020418761189⟩
def polyval7Tail41 : Box := ⟨23171246906162446161655228489006459958549688893546941355542,3093244480395057848748572056726756486401332154454801674387⟩
def polyval7Tail45 : Box := ⟨23536861103049890077808896306771268116767959636452227993841,2727630283507613932595648143760597788379890437654440693328⟩
def polyval7Tail49 : Box := ⟨23908244248907020203100712751883253750307938516296706047919,2356247137650483807314134793885634128386368916755493807615⟩
def polyval7Tail53 : Box := ⟨24285487370757672511063762191925273273651135462564085319666,1979004015799831499588418966320713651323179119821915224513⟩
def polyval7Tail57 : Box := ⟨24668682931921811104047898265716261935585191249355556046793,1595808454635692920935823669796439566722636460261981125067⟩
def polyval7Tail61 : Box := ⟨25057924854678544038942875018776122065175307456861820327224,1206566531878962890431849460643925856237797463331591015082⟩
def polyval7Tail65 : Box := ⟨25453308543289980728440721148743253335944640597361205185722,811182843270309186536260573808378187997077036971879960012⟩
def polyval7Tail69 : Box := ⟨25854930934321298768923260716312668466872165783276196872249,409560476054424402359556058791038035397717821594847737486⟩
def polyval7Tail73 : Box := ⟨26281250000000000000000000000000000000000000000000000000000,2⟩
theorem polyval7H73 : polyval7Tail73=hornerBox Q polyBox cell7 73 1 :=
  hornerChunk_step Q polyBox cell7 polyval7Tail73 zero 73 1 0 (by decide +kernel) rfl
theorem polyval7H69 : polyval7Tail69=hornerBox Q polyBox cell7 69 5 :=
  hornerChunk_step Q polyBox cell7 polyval7Tail69 polyval7Tail73 69 4 1 (by decide +kernel) polyval7H73
theorem polyval7H65 : polyval7Tail65=hornerBox Q polyBox cell7 65 9 :=
  hornerChunk_step Q polyBox cell7 polyval7Tail65 polyval7Tail69 65 4 5 (by decide +kernel) polyval7H69
theorem polyval7H61 : polyval7Tail61=hornerBox Q polyBox cell7 61 13 :=
  hornerChunk_step Q polyBox cell7 polyval7Tail61 polyval7Tail65 61 4 9 (by decide +kernel) polyval7H65
theorem polyval7H57 : polyval7Tail57=hornerBox Q polyBox cell7 57 17 :=
  hornerChunk_step Q polyBox cell7 polyval7Tail57 polyval7Tail61 57 4 13 (by decide +kernel) polyval7H61
theorem polyval7H53 : polyval7Tail53=hornerBox Q polyBox cell7 53 21 :=
  hornerChunk_step Q polyBox cell7 polyval7Tail53 polyval7Tail57 53 4 17 (by decide +kernel) polyval7H57
theorem polyval7H49 : polyval7Tail49=hornerBox Q polyBox cell7 49 25 :=
  hornerChunk_step Q polyBox cell7 polyval7Tail49 polyval7Tail53 49 4 21 (by decide +kernel) polyval7H53
theorem polyval7H45 : polyval7Tail45=hornerBox Q polyBox cell7 45 29 :=
  hornerChunk_step Q polyBox cell7 polyval7Tail45 polyval7Tail49 45 4 25 (by decide +kernel) polyval7H49
theorem polyval7H41 : polyval7Tail41=hornerBox Q polyBox cell7 41 33 :=
  hornerChunk_step Q polyBox cell7 polyval7Tail41 polyval7Tail45 41 4 29 (by decide +kernel) polyval7H45
theorem polyval7H37 : polyval7Tail37=hornerBox Q polyBox cell7 37 37 :=
  hornerChunk_step Q polyBox cell7 polyval7Tail37 polyval7Tail41 37 4 33 (by decide +kernel) polyval7H41
theorem polyval7H33 : polyval7Tail33=hornerBox Q polyBox cell7 33 41 :=
  hornerChunk_step Q polyBox cell7 polyval7Tail33 polyval7Tail37 33 4 37 (by decide +kernel) polyval7H37
theorem polyval7H29 : polyval7Tail29=hornerBox Q polyBox cell7 29 45 :=
  hornerChunk_step Q polyBox cell7 polyval7Tail29 polyval7Tail33 29 4 41 (by decide +kernel) polyval7H33
theorem polyval7H25 : polyval7Tail25=hornerBox Q polyBox cell7 25 49 :=
  hornerChunk_step Q polyBox cell7 polyval7Tail25 polyval7Tail29 25 4 45 (by decide +kernel) polyval7H29
theorem polyval7H21 : polyval7Tail21=hornerBox Q polyBox cell7 21 53 :=
  hornerChunk_step Q polyBox cell7 polyval7Tail21 polyval7Tail25 21 4 49 (by decide +kernel) polyval7H25
theorem polyval7H17 : polyval7Tail17=hornerBox Q polyBox cell7 17 57 :=
  hornerChunk_step Q polyBox cell7 polyval7Tail17 polyval7Tail21 17 4 53 (by decide +kernel) polyval7H21
theorem polyval7H13 : polyval7Tail13=hornerBox Q polyBox cell7 13 61 :=
  hornerChunk_step Q polyBox cell7 polyval7Tail13 polyval7Tail17 13 4 57 (by decide +kernel) polyval7H17
theorem polyval7H9 : polyval7Tail9=hornerBox Q polyBox cell7 9 65 :=
  hornerChunk_step Q polyBox cell7 polyval7Tail9 polyval7Tail13 9 4 61 (by decide +kernel) polyval7H13
theorem polyval7H5 : polyval7Tail5=hornerBox Q polyBox cell7 5 69 :=
  hornerChunk_step Q polyBox cell7 polyval7Tail5 polyval7Tail9 5 4 65 (by decide +kernel) polyval7H9
theorem polyval7H1 : polyval7=hornerBox Q polyBox cell7 1 73 :=
  hornerChunk_step Q polyBox cell7 polyval7 polyval7Tail5 1 4 69 (by decide +kernel) polyval7H5
theorem polyval7_eq : polyval7=hornerBox Q polyBox cell7 1 73 := polyval7H1
theorem polyval7_upper : 5*(polyval7.center+polyval7.radius)<Q := by decide +kernel
theorem resval7_pos : 0<(resval7).center-(resval7).radius := by decide +kernel
theorem polyval7_pos : 0<(polyval7).center-(polyval7).radius := by decide +kernel
def pend : Box := ⟨1029949756823305122532384748219157924355880112841684610522015,7144101664741133563537232194233786842517781743431979097⟩
def zend : Box := ⟨1003681671933865696499023437500000000000000000000000000000000,5390500207759954453125000000000000000000000000000000002⟩
def betaquot : Box := ⟨428740522374591886980197893906340829717063542417146694168428,394751648397765600255475092208684799952806105351294998⟩
def crit : Box := ⟨106194863062758549200013592946358275136926067182116721948,19031891125432415186023867478354964000243733077730568913⟩
def subsonic : Box := ⟨671370547191403275455196720045482142799546631035996589848,11143337003296130238719501833026122745649386552054608704⟩
def pendTail4 : Box := ⟨26262929052691464046126533690160547997004005823441666538505,1530617936483079645565144079007422651337779602982760859⟩
def pendTail8 : Box := ⟨26262961006573597566864347042500222759451446944599564258383,1530378764765097956759715577075057085379961043646534987⟩
def pendTail12 : Box := ⟨26262961007816065571353393546646059883178234939455046035499,1530378740904628375950050765433660129189860867478928977⟩
def pendTail16 : Box := ⟨26262961007816616248482264152053894583241827546896244294456,1530378740886619044974274566036013349983493726293166970⟩
def pendTail20 : Box := ⟨26262961007816617443355654049090902085485346608286990442199,1530378740886558357130055102254045963824252673336139496⟩
def pendTail24 : Box := ⟨26262961007816617452567110070170894231023607446708533123664,1530378740886557642639269207887669870224254155983544645⟩
def pendTail28 : Box := ⟨26262961007816617452775086729896605345383050549167326091746,1530378740886557617335478557757941340156033141934701959⟩
def pendTail32 : Box := ⟨26262961007816617452786919066807797863307508963981107769877,1530378740886557614872594325869689428827024973851105955⟩
def pendTail36 : Box := ⟨26262961007816617452788296857415407880027566235446671068106,1530378740886557614246779001938759483637836703587591770⟩
def pendTail40 : Box := ⟨26262961007816617452788360699106367897612366159217741306001,1530378740886557613841202697814888287662734361264986438⟩
def pendTail44 : Box := ⟨26262961007816617452787366104122807078024717158156478704319,1530378740886557613170904164394986492610459957622590727⟩
def pendTail48 : Box := ⟨26262961007816617452779208355186166015237168214574587358740,1530378740886557610281513797395131048950940139568736377⟩
def pendTail52 : Box := ⟨26262961007816617452645104249496461802588133151640164473661,1530378740886557576161898577888732902962586008350406165⟩
def pendTail56 : Box := ⟨26262961007816617446807307813861128615946552368267306635860,1530378740886556373374537023416526696062429236142881319⟩
def pendTail60 : Box := ⟨26262961007816616623610945605979469662583110605453103049746,1530378740886410058962104707396425993546863067572779025⟩
def pendTail64 : Box := ⟨26262961007816119607024676161169184023368603075064781220613,1530378740810081677907758739619147612429554004533308843⟩
def pendTail68 : Box := ⟨26262961005660042699554575863294153982967025879461418589745,1530378481491842553225586838382004609474609518604498774⟩
def pendTail72 : Box := ⟨26262673143324030183423528192116184412007929954892030834344,1503825964954292019335915294875565984829403525680031550⟩
theorem pendH72 : pendTail72=hornerBox Q polyBox (oneBox Q) 72 2 :=
  hornerChunk_step Q polyBox (oneBox Q) pendTail72 zero 72 2 0 (by decide +kernel) rfl
theorem pendH68 : pendTail68=hornerBox Q polyBox (oneBox Q) 68 6 :=
  hornerChunk_step Q polyBox (oneBox Q) pendTail68 pendTail72 68 4 2 (by decide +kernel) pendH72
theorem pendH64 : pendTail64=hornerBox Q polyBox (oneBox Q) 64 10 :=
  hornerChunk_step Q polyBox (oneBox Q) pendTail64 pendTail68 64 4 6 (by decide +kernel) pendH68
theorem pendH60 : pendTail60=hornerBox Q polyBox (oneBox Q) 60 14 :=
  hornerChunk_step Q polyBox (oneBox Q) pendTail60 pendTail64 60 4 10 (by decide +kernel) pendH64
theorem pendH56 : pendTail56=hornerBox Q polyBox (oneBox Q) 56 18 :=
  hornerChunk_step Q polyBox (oneBox Q) pendTail56 pendTail60 56 4 14 (by decide +kernel) pendH60
theorem pendH52 : pendTail52=hornerBox Q polyBox (oneBox Q) 52 22 :=
  hornerChunk_step Q polyBox (oneBox Q) pendTail52 pendTail56 52 4 18 (by decide +kernel) pendH56
theorem pendH48 : pendTail48=hornerBox Q polyBox (oneBox Q) 48 26 :=
  hornerChunk_step Q polyBox (oneBox Q) pendTail48 pendTail52 48 4 22 (by decide +kernel) pendH52
theorem pendH44 : pendTail44=hornerBox Q polyBox (oneBox Q) 44 30 :=
  hornerChunk_step Q polyBox (oneBox Q) pendTail44 pendTail48 44 4 26 (by decide +kernel) pendH48
theorem pendH40 : pendTail40=hornerBox Q polyBox (oneBox Q) 40 34 :=
  hornerChunk_step Q polyBox (oneBox Q) pendTail40 pendTail44 40 4 30 (by decide +kernel) pendH44
theorem pendH36 : pendTail36=hornerBox Q polyBox (oneBox Q) 36 38 :=
  hornerChunk_step Q polyBox (oneBox Q) pendTail36 pendTail40 36 4 34 (by decide +kernel) pendH40
theorem pendH32 : pendTail32=hornerBox Q polyBox (oneBox Q) 32 42 :=
  hornerChunk_step Q polyBox (oneBox Q) pendTail32 pendTail36 32 4 38 (by decide +kernel) pendH36
theorem pendH28 : pendTail28=hornerBox Q polyBox (oneBox Q) 28 46 :=
  hornerChunk_step Q polyBox (oneBox Q) pendTail28 pendTail32 28 4 42 (by decide +kernel) pendH32
theorem pendH24 : pendTail24=hornerBox Q polyBox (oneBox Q) 24 50 :=
  hornerChunk_step Q polyBox (oneBox Q) pendTail24 pendTail28 24 4 46 (by decide +kernel) pendH28
theorem pendH20 : pendTail20=hornerBox Q polyBox (oneBox Q) 20 54 :=
  hornerChunk_step Q polyBox (oneBox Q) pendTail20 pendTail24 20 4 50 (by decide +kernel) pendH24
theorem pendH16 : pendTail16=hornerBox Q polyBox (oneBox Q) 16 58 :=
  hornerChunk_step Q polyBox (oneBox Q) pendTail16 pendTail20 16 4 54 (by decide +kernel) pendH20
theorem pendH12 : pendTail12=hornerBox Q polyBox (oneBox Q) 12 62 :=
  hornerChunk_step Q polyBox (oneBox Q) pendTail12 pendTail16 12 4 58 (by decide +kernel) pendH16
theorem pendH8 : pendTail8=hornerBox Q polyBox (oneBox Q) 8 66 :=
  hornerChunk_step Q polyBox (oneBox Q) pendTail8 pendTail12 8 4 62 (by decide +kernel) pendH12
theorem pendH4 : pendTail4=hornerBox Q polyBox (oneBox Q) 4 70 :=
  hornerChunk_step Q polyBox (oneBox Q) pendTail4 pendTail8 4 4 66 (by decide +kernel) pendH8
theorem pendH0 : pend=hornerBox Q polyBox (oneBox Q) 0 74 :=
  hornerChunk_step Q polyBox (oneBox Q) pend pendTail4 0 4 70 (by decide +kernel) pendH4
theorem pend_eq : pend=hornerBox Q polyBox (oneBox Q) 0 74 := pendH0
theorem zend_eq : zend=add (oneBox Q) (scale 1 256 root) := by decide +kernel
theorem betaquot_eq : betaquot=scale 3 7 (sub (oneBox Q) kap) := by decide +kernel
theorem crit_eq : crit=add (sub pend zend) (mul Q (mul Q betaquot zend) (sub (oneBox Q) (mul Q pend pend))) := by decide +kernel
theorem subsonic_eq : subsonic=sub (oneBox Q) (mul Q sig (mul Q zend zend)) := by decide +kernel
theorem crit_pos : 0<crit.center-crit.radius := by decide +kernel
theorem subsonic_pos : 0<subsonic.center-subsonic.radius := by decide +kernel
end SepticProfile.ExteriorCertificates.C04

end
end

end OAI
