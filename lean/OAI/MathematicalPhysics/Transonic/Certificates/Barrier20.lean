import OAI.MathematicalPhysics.Transonic.Certificates.BarrierData20

namespace OAI

section
noncomputable section
namespace SepticProfile.ExteriorCertificates.C20
open SepticProfile.ExteriorJet SepticProfile.FixedInterval
def cell0 : Box := ⟨250000000000000000000000000000000000000000000000000000000000,250000000000000000000000000000000000000000000000000000000002⟩
def resval0 : Box := ⟨114813681065480446671370910834591086976444609838539040316,318502966523324061830414751276310568732980356121215138⟩
def polyval0 : Box := ⟨3811039417329387267825187944453452870836838862817073818293,14961067843424120754494462493915454264239170730473516558⟩
theorem cell0_lo : Holds Q cell0 (0/1:ℝ) := by norm_num [Holds,Q,cell0]
theorem cell0_hi : Holds Q cell0 (1/2:ℝ) := by norm_num [Holds,Q,cell0]
def resval0Tail4 : Box := ⟨59297469916021792580480515366413822542218506406948,1757025252657057782638339561682044038620013496659⟩
def resval0Tail8 : Box := ⟨7210794163695990459441525083566511115971238890,387350068280367412203757636044742474682043289⟩
def resval0Tail12 : Box := ⟨6593230657914846195958525651459415237642855,537496868691757867677685050826416898380834⟩
def resval0Tail16 : Box := ⟨26536354034152278481632007923746284006878,27049320496854447862257399567572033217670⟩
def resval0Tail20 : Box := ⟨363250297498475064711098296074810665178,383721359139120957242324554282618339084407⟩
def resval0Tail24 : Box := ⟨14514006142609262854138908506853225627,6138613261559705211093177068660304849507447⟩
def resval0Tail28 : Box := ⟨1540299825295449314114760672948615132,98217761388253048530073867622929269129653193⟩
def resval0Tail32 : Box := ⟨408144269089934858095815147446311138,1571484174792316947644482213789822797111363054⟩
def resval0Tail36 : Box := ⟨-288388514646681885993512308328943546,25143746793787627492147100917433219605329269691⟩
def resval0Tail40 : Box := ⟨-141633783697975289145137889261596692756,402299948566422670383695250661857063984948119839⟩
def resval0Tail44 : Box := ⟨-36364012157583296119665668412765172014899,6436799142968208942808367966110549983645918321664⟩
def resval0Tail48 : Box := ⟨-9309587100974429854348279813381676729953444,102988777559731647288014779359111361888688482064151⟩
def resval0Tail52 : Box := ⟨-2383257988823909597423175484488677858939249437,1647818206650903561428597501522763840330665395713757⟩
def resval0Tail56 : Box := ⟨-610114120798379232655745071152756963848864345991,26364519324396652710752407521037380084774759387215381⟩
def resval0Tail60 : Box := ⟨-156189212618650311063074608809918004582650496396698,421685881795630897528617135833650353897375866222960855⟩
def resval0Tail64 : Box := ⟨-39984421259764276571838370393104335795895213404301299,6709488702045219231434789099299327297680932170226593267⟩
def resval0Tail68 : Box := ⟨-10235608029378859541167100819890929594059902147309991132,97755726047928848246526155250840850941259500142406778888⟩
def resval0Tail72 : Box := ⟨798125763088861859866539096432389796150147805718831334252,2475076668647558242014241800719808076553494751988216605⟩
def resval0Tail76 : Box := ⟨-27437482801957624621638910950853659924973302210064,603418034447400304902800147077804025633307923491⟩
def resval0Tail80 : Box := ⟨-1490687337647610531925041717991691668977438599,68743370230263313131932441925223185224826192⟩
def resval0Tail84 : Box := ⟨-847561561248714096668449603910734739775734,61490263264809563735755070459055333037179⟩
def resval0Tail88 : Box := ⟨-2357142494253678861167181973248905020057,410347389552406915227343159231531521188⟩
def resval0Tail92 : Box := ⟨-23595013066152814372304607799114931959,2612870154894178770834394106670251890681⟩
def resval0Tail96 : Box := ⟨-713628115395539176463334265010990746,41750807905685029119867955818826227465136⟩
def resval0Tail100 : Box := ⟨-58579448612143532342920606312338788,668010638476406845672773795633305266851353⟩
def resval0Tail104 : Box := ⟨-12234800923463284003998435623081786,10688169957534194951073211805170552040762303⟩
def resval0Tail108 : Box := ⟨-8136614614684906177917008082088515,171010719244780042813000789459270742899194355⟩
def resval0Tail112 : Box := ⟨-487308257172931696324717337003742849,2736171507473737314824024166275231649936402051⟩
def resval0Tail116 : Box := ⟨-122782593098650473449196820904390510446,43778744004497600993925972424491218589197037676⟩
def resval0Tail120 : Box := ⟨-31426463688227707634881734270406503016241,700459874609795876209992199102796483234386957991⟩
def resval0Tail124 : Box := ⟨-8045131753684912093916217620190447040528180,11207350451448120337363809117929974398059038956520⟩
def resval0Tail128 : Box := ⟨-2059552993035646217387806943428892041296985706,179315676392371572683482361321864343867419217755358⟩
def resval0Tail132 : Box := ⟨-527245557985327569759081356371380933580960354909,2868556529595177429182613176527461841088330225216311⟩
def resval0Tail136 : Box := ⟨-134974905196872873163882004312413788185796950715114,45770365528153952248500032232801505995884429745685229⟩
def resval0Tail140 : Box := ⟨-34554107612785203824710288818561879466518431833926812,699931631878324673596394747529989204322785168576743199⟩
def resval0Tail144 : Box := ⟨-9171751972823805862292565166387408131184338959253519599,2744553105898998590531149180768147314940267120926955140⟩
def resval0Tail148 : Box := ⟨62394065462075110829502764150944416403918240,1135320955258596493012935189532678246579496⟩
def resval0Tail152 : Box := ⟨1118151417823173942884634101256442562644,46011616973908737665836357599919086657⟩
def resval0Tail156 : Box := ⟨357116874055429871548853265727083043,23613319558953999799874056088204154⟩
def resval0Tail160 : Box := ⟨628749497594318776777046447915913,62143577374507068758499690698293⟩
def resval0Tail164 : Box := ⟨4218860571878422455369689543385,29663626817192994571620868816505⟩
def resval0Tail168 : Box := ⟨88287506913292386989494543888,465616115514228900872246173330317⟩
def resval0Tail172 : Box := ⟨5099121197158176910644520345,7449600674416159612864863611868019⟩
def resval0Tail176 : Box := ⟨753714038642492694646199479,119193590571107559929439877895364310⟩
def resval0Tail180 : Box := ⟨279658131178836857506602517,1907097445023612440559492694717009292⟩
def resval0Tail184 : Box := ⟨1974377889420290333256585635,30513559117319837608665451027421533378⟩
def resval0Tail188 : Box := ⟨445184445161628859119427079177,488216945460401770046760647989120612886⟩
def resval0Tail192 : Box := ⟨113842628859281617373848473308911,7811471020641198860654807924089344294907⟩
def resval0Tail196 : Box := ⟨29143091592514068278946264668238695,124983509008633740585612986413716026230609⟩
def resval0Tail200 : Box := ⟨7460623985874294064657805860570222030,1999729149803890153870977865930548864218391⟩
def resval0Tail204 : Box := ⟨1909919566950697614228516234548411076378,31993875847350964848880734461853994661268672⟩
def resval0Tail208 : Box := ⟨488939444462719021674367117189207183868769,511443632866929284902944549447584948607923726⟩
def resval0Tail212 : Box := ⟨125168706023948482095660761308624950699517723,8065752574865240296733238216033508751468556615⟩
def resval0Tail216 : Box := ⟨32055439236713200207151325038439776299782237958,99005651757823920472270777495663469756723632411⟩
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
def polyval0Tail5 : Box := ⟨2111473235418277119236184461307296945388411803155588,52448030818805345186668618351007457794134584514012⟩
def polyval0Tail9 : Box := ⟨205802033520998906480395965561567615080133392652,10098687717590967457290510351768153109569921471⟩
def polyval0Tail13 : Box := ⟨162819480823210370273308124033246458420435624,12390670594255521549196847362896978146990090⟩
def polyval0Tail17 : Box := ⟨574239700735770384933418134135220352017461,439514014311685519873178763249989738090863⟩
def polyval0Tail21 : Box := ⟨6907073796529228008736943069957432249088,6030819361283965593883059583615281145286841⟩
def polyval0Tail25 : Box := ⟨242228725136220108866660595079063451868,96476400427159000131008381695902463059131734⟩
def polyval0Tail29 : Box := ⟨22482637329084469942222862981569545088,1543621604518086663182703280623906955561142385⟩
def polyval0Tail33 : Box := ⟨5230451133148347866332403087707899032,24697945570092709151315281167149410622313391688⟩
def polyval0Tail37 : Box := ⟨8642532480978153516769207073038579654,395167129086674535647230020745251272288996419575⟩
def polyval0Tail41 : Box := ⟨1469296759671231779548624425675292385496,6322674064016228126768860621468727992795116580770⟩
def polyval0Tail45 : Box := ⟨375148998928953281354096445759556089033301,101162784672571514059565468145985352522566720106079⟩
def polyval0Tail49 : Box := ⟨96034975716732938809542698411621313860598091,1618604464728436468500560507552170701506429238329387⟩
def polyval0Tail53 : Box := ⟨24584929264203634107067524346823658814834691302,25897648387285252111195185248637520350076129395958347⟩
def polyval0Tail57 : Box := ⟨6293741453073704264253371371995510358732512237436,414356473814036040214410999964951752292590999221898582⟩
def polyval0Tail61 : Box := ⟨1611197808057182808968423926510319703192387612126565,6628193083097913120651304772381627092454999688224819301⟩
def polyval0Tail65 : Box := ⟨412466667622899615664251602499916826320779684884669964,105664401847771473023759062379766268404782447405186699997⟩
def polyval0Tail69 : Box := ⟨105591818764143062495963965768980647925449151349545572200,1591638271973488393032625196145508538518888418769950149075⟩
def polyval0Tail73 : Box := ⟨27281250000000000000000000000000000000000000000000000000000,2⟩
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
def resval1 : Box := ⟨114585329295938785832508804499569883282831958029615104108,240736710680018839236110737818232868876260959291365909⟩
def polyval1 : Box := ⟨3792809615566476906795042807736420867361006309645118529208,8750393437820723912865916340587222538244685821659317111⟩
theorem cell1_lo : Holds Q cell1 (1/2:ℝ) := by norm_num [Holds,Q,cell1]
theorem cell1_hi : Holds Q cell1 (3/4:ℝ) := by norm_num [Holds,Q,cell1]
def resval1Tail4 : Box := ⟨57575034563719475591835820228479486730732714000218,3106549058077881760261961366903965307782621720661⟩
def resval1Tail8 : Box := ⟨6797111369507891222245940351732766109016993583,6268955179441327037049291666233577157434722020993⟩
def resval1Tail12 : Box := ⟨-322890523627624312017641732289769254566097212,19812129607992993430164446403814003033009021065998⟩
def resval1Tail16 : Box := ⟨-2156152046962001218963755777097426049645900444,62614996120519480848159377342333377225215986556154⟩
def resval1Tail20 : Box := ⟨-14130715005675452313967336639799851206991038253,197886992587846002791130629840623962831075076498915⟩
def resval1Tail24 : Box := ⟨-92607055943252823502329922253379319377100515404,625372671531767331657756465238744488926032476929592⟩
def resval1Tail28 : Box := ⟨-606909601909658806170212556312563955719737804959,1976172242477802288924930128835030828980766115040929⟩
def resval1Tail32 : Box := ⟨-3977442767083158810271917989709271412830385563656,6243620865040404708883839550735379947253588258217648⟩
def resval1Tail36 : Box := ⟨-26066568918358131246806332331122671273590869320190,19719429317485554806583611389961773758323300881057135⟩
def resval1Tail40 : Box := ⟨-170829866063352881508973420816473764851427941895404,62234687997139137596188593814110851213458611676074995⟩
def resval1Tail44 : Box := ⟨-1119550610232790326189579030993322357755978570051154,196112703377172611255623117643198772259261754155707469⟩
def resval1Tail48 : Box := ⟨-7337086879221611403507443820252870588144435245385684,616014234364923847030693956761965637789418691301827190⟩
def resval1Tail52 : Box := ⟨-48084332571666545681764928061083281590105625987007220,1922013670372792921845509897622698195723290995572118242⟩
def resval1Tail56 : Box := ⟨-315125481941653757531459154871841812981267945814679564,5911357095265506099528237223136853112954595910373258710⟩
def resval1Tail60 : Box := ⟨-2065206358446498624140911963989582137722975436461975584,17613553391733092670867992670395618201308982401163130617⟩
def resval1Tail64 : Box := ⟨-13534536380643649621034973732707967511224177466065393005,48660062326831138076690100092530446834184709670653891806⟩
def resval1Tail68 : Box := ⟨-88699752642614808800230891132093094905616260478103754351,107865729926272739436489930088986749202963634473442847073⟩
def resval1Tail72 : Box := ⟨801015094992437064287339740509174082045098470137965010296,1511931667848563004206710167473593852308623905237422439⟩
def resval1Tail76 : Box := ⟨-26824764145444139128301424845638555128048249287145,401842277657986995360583991615341542629056385638⟩
def resval1Tail80 : Box := ⟨-1424684733061152476855694584637078047612021862,63939745317489247739197643318154130896349233315⟩
def resval1Tail84 : Box := ⟨-3578928473081003492724235582354404033651642,201944952406107208455943043576643043134235065943⟩
def resval1Tail88 : Box := ⟨-18270815639373603961937367349369745469693426,638236324990740978540595459901273352905459881869⟩
def resval1Tail92 : Box := ⟨-119725569244913328053210345900752797123720811,2017079977890330470445139469942169048512335309032⟩
def resval1Tail96 : Box := ⟨-784633354126892765385750809536396600346742361,6374562577514381606733186936865384475820858215451⟩
def resval1Tail100 : Box := ⟨-5142173145627673768888423543616595725964676521,20144103332807259787108363722153544379426978226827⟩
def resval1Tail104 : Box := ⟨-33699745926875092217621125563316598811080945408,63647866297578399273098672899234550783774252894577⟩
def resval1Tail108 : Box := ⟨-220854654906308875895328238789941127945268284676,201044341729505394608771592586189345893272183721006⟩
def resval1Tail112 : Box := ⟨-1447393066393959781544566179282099969454048302857,634650017728783758453043635646479985682970776679683⟩
def resval1Tail116 : Box := ⟨-9485635199919433695100646812511193143516806289497,2000896305091012608011527213215250432993056823706681⟩
def resval1Tail120 : Box := ⟨-62165058846192013725971623500949208584588217607686,6291634653678235219253782477160477835199880743345106⟩
def resval1Tail124 : Box := ⟨-407404929654405598078207981971080829155302835285935,19673739840793168362845930100148730396297466908386763⟩
def resval1Tail128 : Box := ⟨-2669968946983238166149422165232311662138119110615174,60796365142332653978619162966909697633810265183729297⟩
def resval1Tail132 : Box := ⟨-17497908490977521065815057639363991586701059657634421,183087048630833777714389127519890138426552815249440798⟩
def resval1Tail136 : Box := ⟨-114674293114818506951784584384452222273716199817974880,519273225712895711600392044701801954400086676869019784⟩
def resval1Tail140 : Box := ⟨-751529700712257600137244590827084815984791734851273387,1252057724836493823409975225294675007569073257058318158⟩
def resval1Tail144 : Box := ⟨-5061315820334235049811461042240074528125856984767317634,1382154272820682308666330941808830835291971523013624480⟩
def resval1Tail148 : Box := ⟨61467778793316431498104652196112246091455297,809350021282840476213183417311666851944301⟩
def resval1Tail152 : Box := ⟨1075348430433512101977685553758140055496,3025939093907715728631140251761719459443⟩
def resval1Tail156 : Box := ⟨451854324757807459724576093224427737,9469102017671517153145414938374569970648⟩
def resval1Tail160 : Box := ⟨760685511034141413323812295153795062,29926645453470584191275335421098849658994⟩
def resval1Tail164 : Box := ⟨4981448282539205112610680789955017739,94580399096596235104822377560655105842846⟩
def resval1Tail168 : Box := ⟨32646394797541321076130493803252908300,298903864945043971445005994011039714293496⟩
def resval1Tail172 : Box := ⟨213951412445919822879490548267709603948,944573047389775924457249647044123536859631⟩
def resval1Tail176 : Box := ⟨1402151976577979542187980356102355362492,2984591325719319789263881406501804601964175⟩
def resval1Tail180 : Box := ⟨9189143193697626158804907653268202769911,9428024811005681163008621620808674707281160⟩
def resval1Tail184 : Box := ⟨60221968834215533038295935131334484821425,29766034479005795881155184218442407726555665⟩
def resval1Tail188 : Box := ⟨394670694951914099120874736589639427063587,93871028695752319188896514234067333755755899⟩
def resval1Tail192 : Box := ⟨2586513866436863649059246450916756598663820,295339647170850589855859390310412648825580054⟩
def resval1Tail196 : Box := ⟨16950977275080640388581757836720564854644409,924642815632889594253713237460355443801948899⟩
def resval1Tail200 : Box := ⟨111089924669969127492959508295687297038559964,2864811445508307704351494108298808963264337833⟩
def resval1Tail204 : Box := ⟨728038930317193169863508656092026438529710711,8677278980369773665333735726684376281900580427⟩
def resval1Tail208 : Box := ⟨4771275933766022822646738196076925409024351976,24954173265473786736928693139103187116824075981⟩
def resval1Tail212 : Box := ⟨31269034070056608163388162385919153635506250398,62678064722924080610884688163121413818460793300⟩
def resval1Tail216 : Box := ⟨204930150749800747957644045459181329716312526560,91993443077722069584510083115644064115577528191⟩
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
def polyval1Tail5 : Box := ⟨2054486308027101553588971133285159989710127410060881,118304355872220643123391386860971770412181017636367⟩
def polyval1Tail9 : Box := ⟨198134644692509878494488680994959206285604609128,274434987776415172407526581164432896545583277171410⟩
def polyval1Tail13 : Box := ⟨15533320966435347689349821819219260127049031129,867325960644782798822484207780240130734709627266076⟩
def polyval1Tail17 : Box := ⟨100807663938112344180405507029437449708670295481,2741126154727500274879951598832706320264700652725241⟩
def polyval1Tail21 : Box := ⟨660649699588795458369768065672683104297730743834,8662970242152958983381306167755809018128156018725548⟩
def polyval1Tail25 : Box := ⟨4329633831469512163831464886384143886901732762008,27377022320646452179678369631388838260167690678221976⟩
def polyval1Tail29 : Box := ⟨28374688276575912701563738922735018214312189258630,86510219143159177701824443217283999621797284034644560⟩
def polyval1Tail33 : Box := ⟨185956357089249649145070133503538256325073617002132,273318735258312582296530423322718769251252076514234838⟩
def polyval1Tail37 : Box := ⟨1218683581820081352815090359005010890100235406881993,863191205968091869711042305609344263998337142244936300⟩
def polyval1Tail41 : Box := ⟨7986764721816073272720784554199792530246372283413480,2723975355337164902817949390917809782226611113887720595⟩
def polyval1Tail45 : Box := ⟨52342061280893807796075406360007535312869489971947334,8582007355201811496836529461278932871714034435350003447⟩
def polyval1Tail49 : Box := ⟨343028932810465669983640526330265702453955235746870805,26945779099529936305196612916248369996708886334787964190⟩
def polyval1Tail53 : Box := ⟨2248074414066668816414206173286085939214257243377699488,83998034922712874134178001824144444907822111823275795384⟩
def polyval1Tail57 : Box := ⟨14732980480027400706725550206368490401902706752322580635,257847315695473442551157685385175159216162069058329859090⟩
def polyval1Tail61 : Box := ⟨96554060873926125398169951842585976401602597853515286659,764934282594338501277390910539234644741512752156690013274⟩
def polyval1Tail65 : Box := ⟨632776693362467923349290487217612396181343819912348151727,2089951898355222094605788060768652726235420249231036931832⟩
def polyval1Tail69 : Box := ⟨4146965505534754789243215465935237712722749589776395095310,4458201538295380740642248074332944468951637714152984257586⟩
def polyval1Tail73 : Box := ⟨27281250000000000000000000000000000000000000000000000000000,2⟩
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
def resval2 : Box := ⟨114472912318323772637904031024830757752889070759412330238,222187659806157567239323214309782562775227709288322047⟩
def polyval2 : Box := ⟨3783802244551952434432199053763483273565266639486838125940,7460972919130241412941061703935576278232060213219095013⟩
theorem cell2_lo : Holds Q cell2 (3/4:ℝ) := by norm_num [Holds,Q,cell2]
theorem cell2_hi : Holds Q cell2 (7/8:ℝ) := by norm_num [Holds,Q,cell2]
def resval2Tail4 : Box := ⟨-137092608888911631025182224899042891230512766796286,34320307483912894079671005200341237371654600223422949⟩
def resval2Tail8 : Box := ⟨-444800349900876045201223084564868189910200453253234,58433523440279176487104645737196604869405970741585222⟩
def resval2Tail12 : Box := ⟨-1020653105865331257051190233523596750072781690995470,99423179027537601569835601913373737540926421528772468⟩
def resval2Tail16 : Box := ⟨-2341988107287678287406042776374657193870206514572465,169010755100429194906887310418751830677673799390601223⟩
def resval2Tail20 : Box := ⟨-5373920121868916160576281227094349007381960750213217,286946294863094465321997983942730569099173823838988050⟩
def resval2Tail24 : Box := ⟨-12330983827835885490804168823576111338210966313201199,486354397504280374781726551821996499366460039331352581⟩
def resval2Tail28 : Box := ⟨-28294645010365649504034879514893521678885742640472770,822440599444589886773263947303115335462827646909550317⟩
def resval2Tail32 : Box := ⟨-64924822499188518408176948951641598658827631664909291,1386391946050373280893966190976877742225030583737681094⟩
def resval2Tail36 : Box := ⟨-148976337218823527070711337000956040341382045493963649,2326905996799920800509969611302273270954795021684492810⟩
def resval2Tail40 : Box := ⟨-341840735127370143704251301010328846691076991595165476,3881905220782990858247765408558527292308461580808791743⟩
def resval2Tail44 : Box := ⟨-784386905826383170312047572835572255660640718856287166,6421137223873258088460229325752468687863415178895183260⟩
def resval2Tail48 : Box := ⟨-1799852255181465888836147930279662329891952333565741760,10492453798650158673996854339010686595507757496114865170⟩
def resval2Tail52 : Box := ⟨-4129936535680562389523786652291074717246264103178234898,16840194908090505350606017176144543454314909539596821400⟩
def resval2Tail56 : Box := ⟨-9476542165973209338321582370091547377193867245673346964,26297576282042721070649535356219794624171463276074219481⟩
def resval2Tail60 : Box := ⟨-21744850228951042960460565765135095471564037485426206603,39284216477863005150177094625855336511086273762277458102⟩
def resval2Tail64 : Box := ⟨-49895679576118662643506160527362410462767539538232397140,54217213889906841963117508758524509422245382871490151363⟩
def resval2Tail68 : Box := ⟨-114490357675328285938800075498080345390845774590165063242,63121501277302100678984076819453132377144205595042795147⟩
def resval2Tail72 : Box := ⟨802458047632613399299216688311090658854094658424861594904,1030792442378665445575501976128412333863744880167498761⟩
def resval2Tail76 : Box := ⟨-28666535647492327703158606917127061680773043398553,408119548726695257266623148493401388649699763335764⟩
def resval2Tail80 : Box := ⟨-4901466103309696749991851685902434245733402245446,694865142255615702510658827694079047016181322719304⟩
def resval2Tail84 : Box := ⟨-11243695374811135760174377355682623474265429333345,1182524855518726626961851979765685294726151955878239⟩
def resval2Tail88 : Box := ⟨-25799753857799377914553035757943868621952351776830,2010716689831678031067967671244117408984284965826556⟩
def resval2Tail92 : Box := ⟨-59200051422939682197062091948891904692251270305606,3415007092826792505149606530091659578826832352504354⟩
def resval2Tail96 : Box := ⟨-135840291658292551007080544893749565120140083597695,5791003716191279067036564971462295083967765125856285⟩
def resval2Tail100 : Box := ⟨-311698797455194994438496217947002072520355732920354,9799235420017459321866873660542115344333487167550842⟩
def resval2Tail104 : Box := ⟨-715223290151733358519482826675518505108419181295422,16533584104587122078641174141372501367251629351441683⟩
def resval2Tail108 : Box := ⟨-1641149593620111232789328790156140712192744498879732,27784554316771538846459811713063515999818597026175695⟩
def resval2Tail112 : Box := ⟨-3765777800759343496803226380448717377116278206699018,46433173976401922107302466271728034639870221057684206⟩
def resval2Tail116 : Box := ⟨-8640944432987792286347489493974319172286520647949853,76996251101894566697641513993827901574987483121194295⟩
def resval2Tail120 : Box := ⟨-19827489736363851313009126339214598105529177852893172,126265785111981897351703308132005950798535361876103816⟩
def resval2Tail124 : Box := ⟨-45496108937444116502926810762309662279473428975221423,203732568188263584536718399509079441460708538564893349⟩
def resval2Tail128 : Box := ⟨-104395259105925592794879812159037087596511021089439433,320777861055215171656900778697759738569748456787737073⟩
def resval2Tail132 : Box := ⟨-239545103489605163934249275455070399499780962943002518,485781468846955406063314579481056155730899999723727559⟩
def resval2Tail136 : Box := ⟨-549659602358079497603555247822917910862567835701112038,687715508153894775601903821766758993386989287559414154⟩
def resval2Tail140 : Box := ⟨-1261247764925259886938810051254743245012154171988576605,849659724506793332887113477287952642244121016489118635⟩
def resval2Tail144 : Box := ⟨-2999468668456951686418465829719271488953598024105749960,697277510249476674755915590854645295625058909309169132⟩
def resval2Tail148 : Box := ⟨61275833561717619792826193509763834716264762,46484910693563057663278100697734609634806448⟩
def resval2Tail152 : Box := ⟨589873456300899300160568472686143862342036,78116354761482121769548392477691278729222218⟩
def resval2Tail156 : Box := ⟨1351101069827468112538778189200624213604231,132916437115681285134339840646829931294362167⟩
def resval2Tail160 : Box := ⟨3100232427003956281088852936163082644174716,225954259475899365052121447019617949639733368⟩
def resval2Tail164 : Box := ⟨7113785662262064117659351912718497334367704,383643065163224337398621363251455683309292980⟩
def resval2Tail168 : Box := ⟨16323274996035626091986009057136669388342469,650290661272676342480631392596501521390766200⟩
def resval2Tail172 : Box := ⟨37455346456363088638113205944665609728889530,1099758598964979654635264802675794303113950024⟩
def resval2Tail176 : Box := ⟨85944945392815767345995981409427922511277399,1854091839465918035441428163364224613578162828⟩
def resval2Tail180 : Box := ⟨197209059250851654260957909279372415306349149,3112408046447346452424164358459854371880866021⟩
def resval2Tail184 : Box := ⟨452515419875488043327461623704138084081632811,5193545248570917389590951762400823748498709783⟩
def resval2Tail188 : Box := ⟨1038340763872412884914662416042204980894457991,8593589472677556566619542366891757867286679717⟩
def resval2Tail192 : Box := ⟨2382574150104774022227955676174176607943211825,14049073600377806100664749088234845882411379204⟩
def resval2Tail196 : Box := ⟨5467048755340025586153348618534842014705422114,22564616878136296035830864822980995742800554024⟩
def resval2Tail200 : Box := ⟨12544676559993135202131756511814567357740095719,35276107461130985835945207862051830629421620372⟩
def resval2Tail204 : Box := ⟨28784983825346176876311289824174364720573440328,52795162509732768414003799869170583710376798061⟩
def resval2Tail208 : Box := ⟨66049952732005395036260517581689368857898051672,73122175293213671173284976584250542716445728204⟩
def resval2Tail212 : Box := ⟨151558058358017083932069607124830777342608230244,85863447922246739194433519992424775010778449810⟩
def resval2Tail216 : Box := ⟨347768973324077284792482310734173226538362439385,57265412737706454908912897230004507319007245652⟩
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
def polyval2Tail5 : Box := ⟨22098582384527472927214522540735975091292973427011008,3079141540370318588398718154864508370059480799351364068⟩
def polyval2Tail9 : Box := ⟨46055590467976992153738129817595536186654083547012460,5241061591862926164332887332068047815476474831323920500⟩
def polyval2Tail13 : Box := ⟨105678605529134807918430201206424678447546641230869167,8913909563126307260694406689554710530104625223148870060⟩
def polyval2Tail17 : Box := ⟨242489866684840991814530168451765242187902183655690801,15144529349562653107718837747714575756932790150042946795⟩
def polyval2Tail21 : Box := ⟨556416648682654039352028884231262320159045413265458088,25693158823931958396960058952270297456253277965384632487⟩
def polyval2Tail25 : Box := ⟨1276752266659642273705333012170336420629332493026589895,43503864616234747100022607054599547934603204841528057854⟩
def polyval2Tail29 : Box := ⟨2929632595070421337716301955564684588135665753044442523,73464122820312926472492986531369947273439419441484616338⟩
def polyval2Tail33 : Box := ⟨6722327710883201980593929756818962488519801623608132738,123602046375501717871436034735823187716669082521282234424⟩
def polyval2Tail37 : Box := ⟨15425036548455639676779651407365726810913512427967821557,206902592047059825421701311827867835767872834486299144256⟩
def polyval2Tail41 : Box := ⟨35394250734903847967443353965030930064717409272952600631,343886868268524450674606847045705484363590562084421337858⟩
def polyval2Tail45 : Box := ⟨81215560245182541943613952775612527798022256446925445218,565821284168829249494145319759604805144526857599242920102⟩
def polyval2Tail49 : Box := ⟨186357023781670217080416440635628403211894898218433758444,917459267230321577094947114223811700253130463727114695552⟩
def polyval2Tail53 : Box := ⟨427614366113075150661390746399692438025067538754592749049,1455447494772022055159934611696503047386358468615955377123⟩
def polyval2Tail57 : Box := ⟨981202867462151014466536826724568269768278125795437415416,2231217533281438449292558341075676754047296637641179551715⟩
def polyval2Tail61 : Box := ⟨2251465674241097014519064477292314422722626999975487133453,3228781706619284071900755945244477751726959959466983842749⟩
def polyval2Tail65 : Box := ⟨5166207570726005252046425694678165441472111149928087772078,4182852517585950486010420030380080456890523844802328078699⟩
def polyval2Tail69 : Box := ⟨11854367254053876323651387523135475177070133094679190838556,4094716630703416266935039465700525627844128851042175233527⟩
def polyval2Tail73 : Box := ⟨27281250000000000000000000000000000000000000000000000000000,2⟩
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
def resval3 : Box := ⟨114289994063198569250678519658409387848192040732111738130,1736033968933952513235925027343439644640795596024104833⟩
def polyval3 : Box := ⟨3802038163523618556360434691058775642509309630999835080237,240855918350116623661752308258434767514265123664752617496⟩
theorem cell3_lo : Holds Q cell3 (7/8:ℝ) := by norm_num [Holds,Q,cell3]
theorem cell3_hi : Holds Q cell3 (15/16:ℝ) := by norm_num [Holds,Q,cell3]
def resval3Tail4 : Box := ⟨-188647737401457748824292536864819273325025895209292508,1988209593237111852728036933141377613462398204458584498⟩
def resval3Tail8 : Box := ⟨-279762330798132410976362463291988043900970770044451157,2538334932483608051186795457799330933616654492217422094⟩
def resval3Tail12 : Box := ⟨-414760290033840481136509346120372230395686519880397400,3233374478759164440460217902161987626441143489832698416⟩
def resval3Tail16 : Box := ⟨-614900846889134338971723395885310349638409332157359996,4107749231293317028463048321774750632752881672825251128⟩
def resval3Tail20 : Box := ⟨-911618254170045871108406087068664461450077949309116937,5202033015435218855909065035087346851488523821677878055⟩
def resval3Tail24 : Box := ⟨-1351515200443119946762455324196987193914519210728891118,6562840347307016284855717042617844820901378820915474204⟩
def resval3Tail28 : Box := ⟨-2003682274541299642183261905627163467895877794991336046,8241753877110116233228725135854337605018240569647924362⟩
def resval3Tail32 : Box := ⟨-2970549392263354755159091231322963385405542899754412171,10292559815334219385325437962546341401256397020987350592⟩
def resval3Tail36 : Box := ⟨-4403973526140161372807774036937907189876349786529205870,12765628943570744679091368779047347832632771424918232943⟩
def resval3Tail40 : Box := ⟨-6529089490804851044568926898317900507828564270055944015,15697618014478584787776683286180281490772568976585391203⟩
def resval3Tail44 : Box := ⟨-9679669808619470180196251926385151086790816941471169483,19093653708738658228106160039749307102329881951574787662⟩
def resval3Tail48 : Box := ⟨-14350547306152674196749028479137962666359724959590678889,22897621188337840429194001602522458928044969166319645893⟩
def resval3Tail52 : Box := ⟨-21275333979134666920032149565076115646113864016442932549,26943845684172599353157400400980573433563433611422068386⟩
def resval3Tail56 : Box := ⟨-31541642716975432468584683356775668495531112206532155244,30879930782570327737830308642135566461134384178511854905⟩
def resval3Tail60 : Box := ⟨-46761908708973987606209653074142576548326986116338758315,34045207159983594757436916007357256819024616406023553686⟩
def resval3Tail64 : Box := ⟨-69326639880351817792487277937119041799482030856030574636,35281264222512670373491709377479278075018825881499067891⟩
def resval3Tail68 : Box := ⟨-102779740850419674707312985026547506995255944032327387049,32639062481985925507238434691204381704709724216820559344⟩
def resval3Tail72 : Box := ⟨803177543199729449339674010730885471824842410116840973808,809609612708916966105976670845370515264319837671749477⟩
def resval3Tail76 : Box := ⟨-2344881280441949571450960529783221310100221524332357,25390987394673044779750708169352255788715607503033634⟩
def resval3Tail80 : Box := ⟨-3437273506729108309235291655791512565128945069008719,32433563335469938217772306730780461497421929395921245⟩
def resval3Tail84 : Box := ⟨-5095911044656458761822135491445368802294074570807346,41340258281454832204434427426752437958197999465895502⟩
def resval3Tail88 : Box := ⟨-7554918085983242166551471508655501093391066536228861,52558480292406223927572759458082319720091272820098034⟩
def resval3Tail92 : Box := ⟨-11200506993579449723623886811562058735628065413384004,66618587843477303127314159374196612248263455808627579⟩
def resval3Tail96 : Box := ⟨-16605257063740642316543424941280693904505177972324016,84134539464483556709286521825381348089852808700290029⟩
def resval3Tail100 : Box := ⟨-24618042943142693221544108329303975738279845755993179,105793479136337821764061100590839557686236692238238374⟩
def resval3Tail104 : Box := ⟨-36497359602688030143520703694086474717962693590131469,132325346787451921015879548169935563090162915548325144⟩
def resval3Tail108 : Box := ⟨-54108982628896017127122418700296644541005994061820486,164438471909063722897599443966576122788196061362931320⟩
def resval3Tail112 : Box := ⟨-80219008525716469202712314364118138683995186494407815,202699035535512755926532730561798289986950271951159005⟩
def resval3Tail116 : Box := ⟨-118928300186010471673080688925146041514377965265542579,247319935578862980145381782448129568595436678202442632⟩
def resval3Tail120 : Box := ⟨-176316571908260106521900708054220005259498333253075082,297805786197157109115970018599641466461866374655110424⟩
def resval3Tail124 : Box := ⟨-261397274499492776851879788228248725720455493433891153,352372263491551622568513153376648327902257193877418851⟩
def resval3Tail128 : Box := ⟨-387533255531507580549404643119892545010270768784869554,407014901343180626415506467728603979028647131802070286⟩
def resval3Tail132 : Box := ⟨-574535539555313168432840439820025380995512151028150154,454037458152154617234574020707804736047461695418709647⟩
def resval3Tail136 : Box := ⟨-851774864501560449602096614162610959230281235140906684,479752246189327766471790783794500793217332651601439245⟩
def resval3Tail140 : Box := ⟨-1262794855719804674663415308710301505240182698023971770,460918116714210261956120087751160733794912895095171840⟩
def resval3Tail144 : Box := ⟨-1966886459194427422140402060252178549503859798540680871,353918837413541828647721321828578502460923364191423665⟩
def resval3Tail148 : Box := ⟨597426854761984230141147540823090055913778136,5242948932356242742802433780480552432008148435⟩
def resval3Tail152 : Box := ⟨795576910088726188337184508118385143843912892,6685775959122335179930935992957951832861383113⟩
def resval3Tail156 : Box := ⟨1179477121474164938981036160166095699086582472,8505419123998087542149252306292212469391185781⟩
def resval3Tail160 : Box := ⟨1748628058423755826405028838497631954471359814,10788840787440616646115762029080791949946262596⟩
def resval3Tail164 : Box := ⟨2592420007025750547130723508061143993276491524,13637813242999557062391108039089374498940080735⟩
def resval3Tail168 : Box := ⟨3843379648664434338091214810464236611187644299,17167278450568322715866042886002450940100108895⟩
def resval3Tail172 : Box := ⟨5697983769503150557902509650180740258840979984,21501117251559920289752636880140517059855226265⟩
def resval3Tail176 : Box := ⟨8447518071446194080909931478421751108290661181,26762759153568905392220309493688702091105354969⟩
def resval3Tail180 : Box := ⟨12523826752429040797288828289699080334895290045,33057224669172728270180485747273499531101953921⟩
def resval3Tail184 : Box := ⟨18567138323742662227559997039047531555463957337,40439277201513506416365370313775878342627461437⟩
def resval3Tail188 : Box := ⟨27526620444995391913508055954392862769973159707,48859442722672524496364727538227627826769752269⟩
def resval3Tail192 : Box := ⟨40809457004686239375586001274800019505955986340,58075225183092221263956467049993694624466759348⟩
def resval3Tail196 : Box := ⟨60501861619562632320942748751243773573478442151,67508143948007722190419747225175859407527383643⟩
def resval3Tail200 : Box := ⟨89696740121103927808695267955666262660427320690,76017111234477124614215222841445354479565594614⟩
def resval3Tail204 : Box := ⟨132979464978172351934159564709608411641342072552,81543457736679259613255720899868130325449935603⟩
def resval3Tail208 : Box := ⟨197148057800185348351908197003553233092293222756,80560075790765092496836687186115211149307751131⟩
def resval3Tail212 : Box := ⟨292280892477702550958506804162763253168003516259,67222914865327021952456814160250467932216706324⟩
def resval3Tail216 : Box := ⟨433323423873869284209356408927198297520914451688,32071552623902380843867787464126511327614383593⟩
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
def polyval3Tail5 : Box := ⟨33698168648528814492555007842442826149228689411885263437,304233549000868011051510435901465741627092141855974533038⟩
def polyval3Tail9 : Box := ⟨49956069913982825338231344897940742528618748725678691824,387506856320379596661591998007547671997292815151165491843⟩
def polyval3Tail13 : Box := ⟨74062127737203717110279783980729402196253966842311220067,492250372434978093261451384175066473513665815722014670371⟩
def polyval3Tail17 : Box := ⟨109800446575004319198077961130757690299896318611995276571,623312758585974917878271234100918860996692833847526612376⟩
def polyval3Tail21 : Box := ⟨162784117016901658980578596425039219233970925745957108269,786258984482948275967971594352941042051988803590831838553⟩
def polyval3Tail25 : Box := ⟨241334799443382005480316912506837762915060448555606861185,987237816850823722251403861430226738749017687142410885370⟩
def polyval3Tail29 : Box := ⟨357789730900651550929970495123581391819455563759063950295,1232644540338006553969082847340343970866603711887265971443⟩
def polyval3Tail33 : Box := ⟨530439422052736607731752304497666858311205785965810864655,1528438610537815442869145446366912161640648111951081742934⟩
def polyval3Tail37 : Box := ⟨786400380355714830719998808524553794004535136283366321991,1878896029399434190277647550538271439397320808365976808841⟩
def polyval3Tail41 : Box := ⟨1165874051801015486541777693236941158146564454423255996186,2284454155798262463879312511476180416358989161896516434751⟩
def polyval3Tail45 : Box := ⟨1728460894243308691762880962231253069720329180780677532836,2738121020092025229401362478654891572608465640250242920284⟩
def polyval3Tail49 : Box := ⟨2562521276044558887919149835691565742694503515731299290024,3219639955320980743870398867720968812711139601234953699544⟩
def polyval3Tail53 : Box := ⟨3799053430743508423405494871201805174620073420571396882461,3686175575849518842877055438975031419665931181770901186913⟩
def polyval3Tail57 : Box := ⟨5632268151124242183957268192096647533454932183514524108180,4057647269637844490977242815747173551180621397980982664376⟩
def polyval3Tail61 : Box := ⟨8350091701647949644150745391497944421262186970909947699731,4193874659143453123356301140981491576461685817823758624260⟩
def polyval3Tail65 : Box := ⟨12379387762653253816918138057498590125260335149704637350973,3859256769129068336075918787671737605743054981137644544863⟩
def polyval3Tail69 : Box := ⟨18353001123307681416120475847002752120751632799585695392131,2668545813764253119643504494636912973121428268399682160839⟩
def polyval3Tail73 : Box := ⟨27281250000000000000000000000000000000000000000000000000000,2⟩
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
def resval4 : Box := ⟨111069034367217411255684056013572907304416125396343094668,8816447368213258760702865729775516897564718001771523097⟩
def polyval4 : Box := ⟨4635218463539853349086020104651892980508513356012729571344,1910984529051387451023472333197284619640269384768752272570⟩
theorem cell4_lo : Holds Q cell4 (15/16:ℝ) := by norm_num [Holds,Q,cell4]
theorem cell4_hi : Holds Q cell4 (31/32:ℝ) := by norm_num [Holds,Q,cell4]
def resval4Tail4 : Box := ⟨-4023437355727131906715544800564844556371058246841237930,9560968836926993224384388520501099256015131335596643877⟩
def resval4Tail8 : Box := ⟨-4875328246036858672750193133082267209110802888295900984,10548620531688818834535537752305607859743971549212597596⟩
def resval4Tail12 : Box := ⟨-5907509349894343629436270725336207125458261654156065827,11605013397615768224555794766514846802119314551418483322⟩
def resval4Tail16 : Box := ⟨-7158218874916534165062139940170589269023758349339550933,12725693946231027378740780118175219713170519793070838040⟩
def resval4Tail20 : Box := ⟨-8673722617481454787388457283525942061925906441817540247,13902692829863703131821940265889384510364576814394508722⟩
def resval4Tail24 : Box := ⟨-10510081538389163046569509163945163332937677587769598748,15123431293604258421217573347296051822541856053943080748⟩
def resval4Tail28 : Box := ⟨-12735225555975059995328279513025073717201276683729847951,16369349598591359088402444850517667982455275138820220129⟩
def resval4Tail32 : Box := ⟨-15431466384838138193938559636599385612052105297623759298,17614191480304763221309757612319953826456631165620038769⟩
def resval4Tail36 : Box := ⟨-18698542380716965442537898091838303386515460697550699209,18821864563575674350685762409213139099112055937960384148⟩
def resval4Tail40 : Box := ⟨-22657308025308304789385741100600594806490780983061092768,19943778719896838421989839490128077362518481539387825891⟩
def resval4Tail44 : Box := ⟨-27454204531102942467489676261920479885072695072977425234,20915542485954848581439042894506659249441352628808800101⟩
def resval4Tail48 : Box := ⟨-33266676941219589616282479012725730804487345343579450374,21652871015089352247723254588152163183755931930484904560⟩
def resval4Tail52 : Box := ⟨-40309738111614914230155566212775806717721425516695987892,22046526573037199603156705158329118895428592058784908316⟩
def resval4Tail56 : Box := ⟨-48843922388101618718228779409672635401615867944684477223,21956073061892219045725540547854963662032488208728694797⟩
def resval4Tail60 : Box := ⟨-59184923197684615446348477013306184837248163276742234249,21202177939125746260605545063767612376141660563994345584⟩
def resval4Tail64 : Box := ⟨-71715271057456414657674373805042758949874211516014987676,19557136343015136025172946971882448516538733523039881265⟩
def resval4Tail68 : Box := ⟨-86898358810372182856681168953315894158053729034449154987,16733218202271580796181101708108712577846323992082012733⟩
def resval4Tail72 : Box := ⟨803496645282051843198825209676964239159984566897981815617,782449331052507586608339706193377392100933950899333316⟩
def resval4Tail76 : Box := ⟨-51993929089589399963557272371623140703633136156396035,126475508190430646832553266510643061464292721487213783⟩
def resval4Tail80 : Box := ⟨-62969948107781437008075938672430601719594514182872584,139636196844299490882110472037257435417391562903450824⟩
def resval4Tail84 : Box := ⟨-76301641620547923868004056731300316653084461133748410,153739623922773205894366017000217686981193688089338781⟩
def resval4Tail88 : Box := ⟨-92455858955046159343448855236108486554740541026565393,168735548774238412270665355047119230643398589975964819⟩
def resval4Tail92 : Box := ⟨-112030169648366649470962677588013703613431122512920781,184529455472383362103132174050927638386439296616627376⟩
def resval4Tail96 : Box := ⟨-135748659449959812006044445438531061977041692722184109,200968432495556904864835362813966394021300022518505700⟩
def resval4Tail100 : Box := ⟨-164488714069619674870925407726021644709130064588417477,217823611696510317126670349364440373832470877376882279⟩
def resval4Tail104 : Box := ⟨-199313475108391633455789285975672006815924594993395991,234768185517133419518310245962684286351599515562696662⟩
def resval4Tail108 : Box := ⟨-241511167404284784650887487331636690400520893979985173,251349970969472344792784296855625650149277222960811592⟩
def resval4Tail112 : Box := ⟨-292642752574859494457491358440114729627139345781308716,266957257637578290674122997806145700493948497699948189⟩
def resval4Tail116 : Box := ⟨-354599671539126724643966081814175341008825334631875071,280776394959109009018030420806078056227276400159250469⟩
def resval4Tail120 : Box := ⟨-429673812009034446649585723137276114261756097934924727,291739230362989614223610597074013671557733326285930519⟩
def resval4Tail124 : Box := ⟨-520642289162425372849600326042622591543531629570511906,298458091141095070151644240021416287955343721302720106⟩
def resval4Tail128 : Box := ⟨-630870175673147697347871668253863910438318189134217400,299145493030806339979409899324212706358245614370354402⟩
def resval4Tail132 : Box := ⟨-764434981250083218204855514460289035481200961391443175,291515137726025547127531163359889637814067765023668105⟩
def resval4Tail136 : Box := ⟨-926277486406613273771202359536836524992898051842359126,272660006051814885396499607145111084615375878744520345⟩
def resval4Tail140 : Box := ⟨-1122384682723334369722359062586767356492315928698727754,238902424577628737924430937780492976957786735952417433⟩
def resval4Tail144 : Box := ⟨-1450180511233507934803011909323694299235182627579624857,182009336491287558888255538596298107434347117007041687⟩
def resval4Tail148 : Box := ⟨18388116666673651290979166057184754670253316021,39069281445214913990181581147319059120557523889⟩
def resval4Tail152 : Box := ⟨22207623877246288694371386877941880104136477154,42960728975983023353382441291524471196553499529⟩
def resval4Tail156 : Box := ⟨26909314152779777101680271006857949887700026783,47083556239308224982330926484851934881482810010⟩
def resval4Tail160 : Box := ⟨32606424986946781563434221711446117675657409741,51405901818738702447292446223133961959311803201⟩
def resval4Tail164 : Box := ⟨39509700782624496120738230409046142202886645176,55878828111247851930881652448449915601702545670⟩
def resval4Tail168 : Box := ⟨47874504995793333262201860498759261167036425576,60430690092808969799543916745409268858000051357⟩
def resval4Tail172 : Box := ⟨58010265408038691358195805283228982048458005484,64960655930215932480629640480125393108317264227⟩
def resval4Tail176 : Box := ⟨70291920365689109185747212594739384410667100081,69330629433591773915550831351648796234113212433⟩
def resval4Tail180 : Box := ⟨85173788362148978429729481743060081895649541980,73355205324329998527332212487897747967389234409⟩
def resval4Tail184 : Box := ⟨103206374021632895776711683268880629296898241516,76789206028840650294934131651952828459404192614⟩
def resval4Tail188 : Box := ⟨125056732165111802537160270550267751855836770297,79312248450386219755428810421818925305953655307⟩
def resval4Tail192 : Box := ⟨151533143258558896879557665629317362242455908938,80509667048815222630698122030487678403569136902⟩
def resval4Tail196 : Box := ⟨183615013028662286522377723379040333253695553267,79848970855694565949553563503571309998031486262⟩
def resval4Tail200 : Box := ⟨222489102281665763744914536904822768147049342301,76650831044726783256017510059907661268269594724⟩
def resval4Tail204 : Box := ⟨269593427125560682513751910056030475185884892197,70053375413477893332074314145432692670281942047⟩
def resval4Tail208 : Box := ⟨326670453536638339389090209642398290582706979494,58968298174691368540514269275453573050592758209⟩
def resval4Tail212 : Box := ⟨395831554100764159882096101479561183980540687928,42026967557614136505907628348346921913702716768⟩
def resval4Tail216 : Box := ⟨479638743034206284200101823073764843972957329783,17514115900575640327118939981779114671252470720⟩
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
def polyval4Tail5 : Box := ⟨1039829200633014702030411023894425991815882162228454470597,2102204928207443909353174807602380522558595955596552139942⟩
def polyval4Tail9 : Box := ⟨1259974415680595667813991482964414140319685887877856862474,2307523740514794024357773105138560006356258222267572698139⟩
def polyval4Tail13 : Box := ⟨1526730151183833794890208025195932091383850665642798391869,2523846875685981998794488003071479554363295416715328669897⟩
def polyval4Tail17 : Box := ⟨1849962130875361653351836394337546980013347905749793789013,2749108011034667760049866579954739206393263547567969315783⟩
def polyval4Tail21 : Box := ⟨2241627233875948996425115019270361752885432358274334867758,2980208082401050106970260785239099205672738822170597209853⟩
def polyval4Tail25 : Box := ⟨2716213792590808563213443409664854798649066043207113459640,3212716019076138486156723043413350159893851852786827859214⟩
def polyval4Tail29 : Box := ⟨3291277539621839863451058073234487263102366815316583485092,3440495215083771236946198972509711261252879704777481551616⟩
def polyval4Tail33 : Box := ⟨3988091023014359742127977600064052206534082064188284048019,3655238525570015561947150996918968319008182062569431699436⟩
def polyval4Tail37 : Box := ⟨4832430512583012075276003578045459204697378730969959111765,3845890743497152770832861609398426559522533073555672831948⟩
def polyval4Tail41 : Box := ⟨5855529506268049121574850585785015260401051722443393879181,3997932829093588495407485289447286048513359695989093160507⟩
def polyval4Tail45 : Box := ⟨7095234108280776444806195676852068662711438780294201214284,4092496459583045304637334543205337758324227742824536510306⟩
def polyval4Tail49 : Box := ⟨8597403018364429799740333219526474319595066519105626725523,4105270519030361173914025210397445239186847786857771258589⟩
def polyval4Tail53 : Box := ⟨10417603920061772013818210243485617181057366333958907187998,4005152689855360721477682912529495015828946926118424471737⟩
def polyval4Tail57 : Box := ⟨12623169020164472733638989727134865791789210766709411234740,3752589013492008741783868851477274506255393120857829331883⟩
def polyval4Tail61 : Box := ⟨15295685777108657010269432789710238336837649006536925629859,3297531763044074050354075497754267511394763949791979661446⟩
def polyval4Tail65 : Box := ⟨18534014954444908222560973730837584638262508566719679062447,2576930736443342785137176294135829358680481717571871956550⟩
def polyval4Tail69 : Box := ⟨22457947756599827973943062391314165267784412719031819831472,1511654546831677305445705041816272208144344530133350104195⟩
def polyval4Tail73 : Box := ⟨27281250000000000000000000000000000000000000000000000000000,2⟩
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
def resval5 : Box := ⟨99224562830201751282443909178786924267003440528653935434,14091927587771727397094710549581090930089986373556616600⟩
def polyval5 : Box := ⟨8709961981739049431607016655413055330074423557540854009475,3825925132425738821519161971428560569507911614344856198076⟩
theorem cell5_lo : Holds Q cell5 (31/32:ℝ) := by norm_num [Holds,Q,cell5]
theorem cell5_hi : Holds Q cell5 (63/64:ℝ) := by norm_num [Holds,Q,cell5]
def resval5Tail4 : Box := ⟨-16658775105977981306519853285402145391423877800602365957,14306624714581876523910223591729220853931419212196183337⟩
def resval5Tail8 : Box := ⟨-18316578569252330153482746484750182949745736189476534926,14662245720561827843542551836567775491741135162542494602⟩
def resval5Tail12 : Box := ⟨-20139291125151930344883500431405247545088402564390877788,14983811042373509988162881469894617284952583482262762226⟩
def resval5Tail16 : Box := ⟨-22143384767276828253818913984937438180306366568960265899,15263415875138008218924544604730418562224979177673835535⟩
def resval5Tail20 : Box := ⟨-24346909029938852317854440835958912032014885142152597447,15492075796261937801231282886957157415741856374709901188⟩
def resval5Tail24 : Box := ⟨-26769709578822260934952549243060806507220539083846178404,15659599657066351980289602390611592207476185825189802770⟩
def resval5Tail28 : Box := ⟨-29433606954101643508478718792109471838894830751060321674,15754449169524778912754199526921864852286250482711675546⟩
def resval5Tail32 : Box := ⟨-32362593093423291374694824370661793734946865259271540040,15763583198526088318442948154028871404041512506872781816⟩
def resval5Tail36 : Box := ⟨-35583047411202178339717125322597866704351655134545407814,15672285151616570730943819747157361371602256446276078728⟩
def resval5Tail40 : Box := ⟨-39123974380321489923276575455542989441458880259395892681,15463971692689401299416087518835000287509804386487703066⟩
def resval5Tail44 : Box := ⟨-43017264755973802287113645278309803840475462207268708928,15119980823651227723647506722366840664304850525096441837⟩
def resval5Tail48 : Box := ⟨-47297982794311910765483837693700582450104593702002861722,14619337177115322969548697158333217644078744938385670396⟩
def resval5Tail52 : Box := ⟨-52004682052695129802469525126139400996616327133793153089,13938492141778437751087736897762857228523823795830515353⟩
def resval5Tail56 : Box := ⟨-57179752615732139540257212547668708536976336639208650406,13051036198276146379621112870401178727444200177609684860⟩
def resval5Tail60 : Box := ⟨-62869802874348110659174235939362919066300448918803044970,11927380574714269805330298881076312626262114965816896849⟩
def resval5Tail64 : Box := ⟨-69126079289435899484625456991132779280012930952571314494,10534405034951677622383569123261490846156438685381900675⟩
def resval5Tail68 : Box := ⟨-76004805565059999805806151915014708500093549960982553785,8835064587191436492640236249940898094917043122654269027⟩
def resval5Tail72 : Box := ⟨803519621347481904668132698768672087043779543613128787839,793078928829130064444810247260642480835132003211478662⟩
def resval5Tail76 : Box := ⟨-220037256323601807921177588402525477666978759786175062,192089728443119984078431476174200237736467965382163234⟩
def resval5Tail80 : Box := ⟨-241904627474900482410352431115921807630509656302782688,196990638689158498221699142121508188360855504572672007⟩
def resval5Tail84 : Box := ⟨-265976949218456957063044401344450714480993186109975447,201455215350294499118492213350077365512926534825801843⟩
def resval5Tail88 : Box := ⟨-292444748385262455852718881148514236612910405390420491,205379780622634712935252995831323151447154875079917793⟩
def resval5Tail92 : Box := ⟨-321546401331620509549582316338227450835945197296273689,208646598782054791850568543849209662964527300928031385⟩
def resval5Tail96 : Box := ⟨-353544007133645020170300437170845622620507904597663567,211122056890455259331269814577134671006251186450309419⟩
def resval5Tail100 : Box := ⟨-388725746773963791547475374834435281832138949459178535,212654814252128990997648835693151028197386227141348780⟩
def resval5Tail104 : Box := ⟨-427408478593882109141830053852389446258600239847585649,213073750146222068615741664779150671861967330441352819⟩
def resval5Tail108 : Box := ⟨-469940592024022969452420239729480131011043216936618838,212185688599291952271972764146124644938224973817059800⟩
def resval5Tail112 : Box := ⟨-516705145294350617638902318585060742193160492361782548,209772876792669662407583598963761972433733242651777362⟩
def resval5Tail116 : Box := ⟨-568123315382826034265157928342584417202239141030441217,205590191291043724874887095243368367254386189908219484⟩
def resval5Tail120 : Box := ⟨-624658191274068873610234139422899500296731167270616809,199362043625576628337906972113447806704020304456049780⟩
def resval5Tail124 : Box := ⟨-686818944691363428274014667377675386904523419075088577,190778953842257707026246395970589591743396185464533175⟩
def resval5Tail128 : Box := ⟨-755165415864995618055061552376435655950052296700330263,179493757406914753363302073114875445885848358856193109⟩
def resval5Tail132 : Box := ⟨-830313155637881796562175052317901455569222335494983303,165117407312446352514917031375910878678913550550979944⟩
def resval5Tail136 : Box := ⟨-912938969338828650457718439586069379350576277735372986,147214329327297751448265306665323656136086752867715024⟩
def resval5Tail140 : Box := ⟨-1003787181191285304222365473322865048829471710594476027,125297275696414962938563642703113521251115490994428064⟩
def resval5Tail144 : Box := ⟨-1191723739941735071669539069293702631295170267053570810,95997045401233909521700142042399091137768809047335752⟩
def resval5Tail148 : Box := ⟨100465754501095937717995649930931981143242234694,75547438781175573045297130227260964672616359054⟩
def resval5Tail152 : Box := ⟨110396598175902772712290581037413743976939416287,76995871506295434301184055243780323556850698818⟩
def resval5Tail156 : Box := ⟨121382342219903880796118468566342952400059542576,78194354693968198773917564773267795360427732533⟩
def resval5Tail160 : Box := ⟨133461296677120583740190857889005503845029115297,79091845090013103562830914660442671908114969716⟩
def resval5Tail164 : Box := ⟨146742247554555926255223950959418182517314442026,79631065431225881056943160423686097342086742330⟩
def resval5Tail168 : Box := ⟨161344807472218538127949294456668282854855220772,79747262050334475946091370533010580610617345467⟩
def resval5Tail172 : Box := ⟨177400491896984332683424461819789914927063043883,79367345353859415829060875164764699171130501196⟩
def resval5Tail176 : Box := ⟨195053903613916341730711273418887340059746929896,78408937271060885787540987466653198679684897622⟩
def resval5Tail180 : Box := ⟨214464035066600165942222414197266139854886460768,76779315913631049074917879853043498284775020510⟩
def resval5Tail184 : Box := ⟨235805700295486693025233878327161759309277491854,74374246697281893419156456570149838995632371792⟩
def resval5Tail188 : Box := ⟨259271109370750178034447950769591000627924144245,71076688072932251750865199424057692800347692419⟩
def resval5Tail192 : Box := ⟨285071599499522855333958734547390803596195800599,66755358799739610936745116759080368007793909014⟩
def resval5Tail196 : Box := ⟨313439538398428321619001905529191778892189773486,61263152353470260337963764313668499975627477335⟩
def resval5Tail200 : Box := ⟨344630417073813980506972667625575904351457478974,54435382589233806343670494969224236091592458780⟩
def resval5Tail204 : Box := ⟨378925150857951055429414272359701301201408650244,46087843153757653596464537219408083836229616074⟩
def resval5Tail208 : Box := ⟨416632609425119835279322057585767919028451835407,36014661354103694629193200154750586566191308071⟩
def resval5Tail212 : Box := ⟨458092398648481114869879386306557315415501911992,23985925216070752998368217423715491201069818547⟩
def resval5Tail216 : Box := ⟨503681467844457230207607199367208086228906125312,9744890193496639597386110166547836145106574867⟩
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
def polyval5Tail5 : Box := ⟨5424997773154757161128930313695250687003484851943150684428,3902165618420895342099509460826771854852896535226291468353⟩
def polyval5Tail9 : Box := ⟨5964845928681102230431209401077830278995799834292557958411,3968765987221473733731940043641516409552311071690016763283⟩
def polyval5Tail13 : Box := ⟨6558417456271384538154244418819654419255222093637790622506,4021076314461306230516231730068338460586730585608173106074⟩
def polyval5Tail17 : Box := ⟨7211056252979327558399581862233230088095478352793941703438,4056314507491317351432887902366724264553469281547297900525⟩
def polyval5Tail21 : Box := ⟨7928640198697603171892675564698223177918580312222228900396,4071333203160007161285406266791550620366739201987423866360⟩
def polyval5Tail25 : Box := ⟨8717632090920229732853846745694406508495704909894604048600,4062577658676682854584116174924020965546368704382331499786⟩
def polyval5Tail29 : Box := ⟨9585137850639996223152429791437976345537566834219837646955,4026039089002863008807002420715392137883976329227263008030⟩
def polyval5Tail33 : Box := ⟨10538970520614532210674600434279444581301850355229984608562,3957202962618696906818648018912951664443780891433682902358⟩
def polyval5Tail37 : Box := ⟨11587720632204162474797591600248161570060361441538449586802,3850991728073772783318910488194206965205700033254350284573⟩
def polyval5Tail41 : Box := ⟨12740833574528338489427773972270719116361093421204474051811,3701701389549382509147251580601666013346806840305173586389⟩
def polyval5Tail45 : Box := ⟨14008694662752766063956000184389665857216625920278395195940,3502931289973465276354059995723947822759259688333400517161⟩
def polyval5Tail49 : Box := ⟨15402722671660257172073154119500048092007978170405210295068,3247506394487610017020059339647064540532164829617940200298⟩
def polyval5Tail53 : Box := ⟨16935472676899468948748339222570127405919454427212339940336,2927391294657437450310967138079618864955444412632453694163⟩
def polyval5Tail57 : Box := ⟨18620749130133707280508110704330182354105781620179513610993,2533595074071970360332138046329632614563161037659012206884⟩
def polyval5Tail61 : Box := ⟨20473730186481862014797577494191795851908475792849900979130,2056066088155455889580459980537191968600585903602205824753⟩
def polyval5Tail65 : Box := ⟨22511104403998501259883925400958484941257412988459958106868,1483575614302891337612187790760733427824446798711839700532⟩
def polyval5Tail69 : Box := ⟨24751221158297287255118683740993813650388194955362987028289,803589216747314095536443748899120262617682185617248523282⟩
def polyval5Tail73 : Box := ⟨27281250000000000000000000000000000000000000000000000000000,2⟩
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
def resval6 : Box := ⟨83030628095814217167966161116560312688059712300481667028,12665200367004539096534126469511152337137914455433199815⟩
def polyval6 : Box := ⟨15422261523665269721692884199750592923033902883858583915533,3829015934960537359194841445199682305649210939290324566198⟩
theorem cell6_lo : Holds Q cell6 (63/64:ℝ) := by norm_num [Holds,Q,cell6]
theorem cell6_hi : Holds Q cell6 (127/128:ℝ) := by norm_num [Holds,Q,cell6]
def resval6Tail4 : Box := ⟨-32851121885871192126444102162969097013390163637979153235,12383488576565788892348485056716114040490455392641952443⟩
def resval6Tail8 : Box := ⟨-34437270548188857119951179082280167059182640627081217557,12239025129704490123848825276378479180228539495305184000⟩
def resval6Tail12 : Box := ⟨-36099941586718940736512797883736485993088672009233749029,12063928590444810900342373501791792896310034302127535608⟩
def resval6Tail16 : Box := ⟨-37842888288552320786220974594641220570590202690801206129,11855965410814270950894075276651671163100877935493250704⟩
def resval6Tail20 : Box := ⟨-39669986461875180315752064156601643911826671760480643316,11612770715762638406524932168464735749452636244464734709⟩
def resval6Tail24 : Box := ⟨-41585299036527673251494443743843228941666514871298522775,11331840655450378841759926171385003903076483363466498206⟩
def resval6Tail28 : Box := ⟨-43593085105269897853314286501906343724484788338952823570,11010524905023675551706105316404607198216655382727283771⟩
def resval6Tail32 : Box := ⟨-45697809394759180904520586910484089050193124300316176109,10646018777197357962000741282286361170089002276825470924⟩
def resval6Tail36 : Box := ⟨-47904152193791176916079967485214603013437387216404930613,10235354928036483269442505102329524852469231907548093918⟩
def resval6Tail40 : Box := ⟨-50217019760887845624401442118832380867526206443422298834,9775394635467355539555491221927849760550783042241311653⟩
def resval6Tail44 : Box := ⟨-52641555234375747566525503519790258857025399802806986587,9262818629034235813509725730748811434970332627250677021⟩
def resval6Tail48 : Box := ⟨-55183150069215468485850799411810523781037818855978794666,8694117448353500391783576810521225481157198485487479577⟩
def resval6Tail52 : Box := ⟨-57847456026014322781842817228421260959030565539261463361,8065581306600244186641905768784467246913994069785102928⟩
def resval6Tail56 : Box := ⟨-60640397738882365409554250483689900963120247171554877873,7373289434190750358295689873962832502365498926407473702⟩
def resval6Tail60 : Box := ⟨-63568185890074538816328818380168072293393956237585672790,6613098876594905602737483551211138254022471192845429008⟩
def resval6Tail64 : Box := ⟨-66637331013919106014614326300586969654983332460159953218,5780632718603054403667750445590418445429046073169319172⟩
def resval6Tail68 : Box := ⟨-69854536969809208716544034295750500209882638939744614357,4871263580350019205000299513415481086372239514150231978⟩
def resval6Tail72 : Box := ⟨803392358966554221191317801187748006222895807723622892390,744699730040747441411836379867604755696483363771675970⟩
def resval6Tail76 : Box := ⟨-437629561510795768677003997376082094102308369549104224,167156822377857690812758537936369571050099249818365593⟩
def resval6Tail80 : Box := ⟨-458731290588597276617364994163216077765514030625881567,165302386786546070728605496910296312454650616420818797⟩
def resval6Tail84 : Box := ⟨-480879363498200567006206529768345572027214742968811467,163042278441131757086494571574574819119461831188449856⟩
def resval6Tail88 : Box := ⟨-504096772272798672112213102074777007728346147474016376,160346665491695515797449410819050130726100942511515958⟩
def resval6Tail92 : Box := ⟨-528435144248388828899294161086172020450982813811324943,157184119392406586360936746762220875365530484072116049⟩
def resval6Tail96 : Box := ⟨-553948600816868833726833739343942399794866714278377131,153521362701622913153704801960642622744523154146584284⟩
def resval6Tail100 : Box := ⟨-580693876413959387958143051811068826521261942773712097,149323169231773119604973492313231216182468623006201382⟩
def resval6Tail104 : Box := ⟨-608730444679195526548805727688825929401199021122039470,144552259059779515844772180225696138869643961187122922⟩
def resval6Tail108 : Box := ⟨-638120650707835416104323483577803692195648879308755521,139169188121036213336590642050673364740468898501429866⟩
def resval6Tail112 : Box := ⟨-668929849688045388208400860668607688270742379391556431,133132232114341853027439691661057106167664932259786596⟩
def resval6Tail116 : Box := ⟨-701226552231647743063794007745129636521870291787843308,126397264431687332100358867705480332417000167444513649⟩
def resval6Tail120 : Box := ⟨-735082576721604216424132046532966346096554284459348203,118917627812621608354426493943757913712173010351201205⟩
def resval6Tail124 : Box := ⟨-770573209015011179218511432223348645177258509311869889,110643999408045197596710146627225064235926565503320631⟩
def resval6Tail128 : Box := ⟨-807777369856739227718770028847983450249912906793336437,101524248922677423362977173428389360969619182096554156⟩
def resval6Tail132 : Box := ⟨-846777790376015663921212787096410918780478936409844015,91503289489072741809656313901458049510880365943236359⟩
def resval6Tail136 : Box := ⟨-887661196075476481495023091541350959041860510959167201,80522920907766900674195340135831554659200585671251000⟩
def resval6Tail140 : Box := ⟨-930518666704326672068593664865594570231354307123802742,68521657236513077390095886253055130679203059094823466⟩
def resval6Tail144 : Box := ⟨-1062469328129120297992080635799158476148158338117497525,52976489783610588046184784083185457116628819387615331⟩
def resval6Tail148 : Box := ⟨231512487986695576644864950992452036418750701838,74576695062555620592329316077671329094689965234⟩
def resval6Tail152 : Box := ⟨242626644968356806985116122103929637828696991053,73154577388063865454037993566234045971707400472⟩
def resval6Tail156 : Box := ⟨254340937368728176276228154521475932257182702294,71504237883121299320544625644599968314467369742⟩
def resval6Tail160 : Box := ⟨266620810366572612311458873182069749112394778853,69609057247895112947718261628146371647566665613⟩
def resval6Tail164 : Box := ⟨279493569757349911709526817568671940218636854857,67451950576890334823712873304659295235530034382⟩
def resval6Tail168 : Box := ⟨292987840777715205336455144558509924314061394373,65014840346433156611800799027716141788159790449⟩
def resval6Tail172 : Box := ⟨307133630724004851076909872773151706305178425593,62278603129328141981879494893250876348261548302⟩
def resval6Tail176 : Box := ⟨321962395679337156024581265078454355812300013370,59223013580729358705656981183244907792249419845⟩
def resval6Tail180 : Box := ⟨337507110462704054085052260732803160655743195778,55826685543774424446542695367500821525733715490⟩
def resval6Tail184 : Box := ⟨353802341955285925843997192563383387518472738618,52067010130310291910854154382442288677858466293⟩
def resval6Tail188 : Box := ⟨370884325967045240815797633333793082623735321827,47920090624882831017586118594781043346470861346⟩
def resval6Tail192 : Box := ⟨388791047814527752469013039726504549666711205044,43360674052647585123333500648983815738343619133⟩
def resval6Tail196 : Box := ⟨407562326789052615252885902143572797155681631328,38362079243975692187717811841907938806983272128⟩
def resval6Tail200 : Box := ⟨427239904703123875968978482830099359673789726896,32896121220258896683221369639731058259752809327⟩
def resval6Tail204 : Box := ⟨447867538711964617470591220138543802664170159984,26933031716741966550439075187281435705111532946⟩
def resval6Tail208 : Box := ⟨469491098616608661079565008150468831612277408928,20441375649108011472318133719571378171464691087⟩
def resval6Tail212 : Box := ⟨492158668938868683385659122088117111941266905902,13387963316880742629040939575399105722424555976⟩
def resval6Tail216 : Box := ⟨515924164276943589207087502063675507900579317008,5737602918752049789642364624892116765942570966⟩
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
def polyval6Tail5 : Box := ⟨12209188249622251783273095096579085677508615321266376856862,3757450874376199833705772564003530145817533859947253147881⟩
def polyval6Tail9 : Box := ⟨12798659802098166891760837860731943216512486457857296601937,3676834358584829407700498900247976101464880114707954049486⟩
def polyval6Tail13 : Box := ⟨13416593818119159857152282576679505464636874656878025140069,3583974676380421990892093369661990149418346421363829878045⟩
def polyval6Tail17 : Box := ⟨14064362399374883425514220098336899596078776746754300370325,3478014558835030545210186150149966695052818543426915876459⟩
def polyval6Tail21 : Box := ⟨14743405992794831070271400322985135800910612630143169706736,3358046875884370627483025948579622298954945438899456020282⟩
def polyval6Tail25 : Box := ⟨15455234591938548805326756866341423878135713495503494390108,3223111947848175549933192628183036360828943975905801483718⟩
def polyval6Tail29 : Box := ⟨16201431094591573292360589856775555909001345928832017497889,3072194729334861136870780480417204981345565278642783747816⟩
def polyval6Tail33 : Box := ⟨16983654822665170618991515514133441187567080710418881952910,2904221848294459629401670891244228033714200319474232825962⟩
def polyval6Tail37 : Box := ⟨17803645212041028790608157689770144930599147894316957673796,2718058492940579126958756167526584515961870660995132912038⟩
def polyval6Tail41 : Box := ⟨18663225680565896491030952270859105880285366201536128903052,2512505138903982163764229325470022725712882444030561310373⟩
def polyval6Tail45 : Box := ⟨19564307682797451960611787075507252417199763433883622884502,2286294108602319964597732960805760802684692948665120622985⟩
def polyval6Tail49 : Box := ⟨20508894960517966177772608462564732142975863711648385575409,2038085954413949160240354645629521620713837658396811378775⟩
def polyval6Tail53 : Box := ⟨21499087998467654625043322543606703647804028829913668348751,1766465656827692792659110309497060133112515114942234987419⟩
def polyval6Tail57 : Box := ⟨22537088695205960305262343978883962207604114176100358590401,1469938628303938227065092608174300469935649558217460601334⟩
def polyval6Tail61 : Box := ⟨23625205259487404945669730978711369974735199444971852461539,1146926513124594963680439269866222648582580436798271127674⟩
def polyval6Tail65 : Box := ⟨24765857343053097718187450240525825990293268537236928107446,795762773028393230527848323694271525716337526359281778274⟩
def polyval6Tail69 : Box := ⟨25961581531966090873261200089572021498998107237663082738048,414688043172655517916770081971422592390547505307630823112⟩
def polyval6Tail73 : Box := ⟨27281250000000000000000000000000000000000000000000000000000,2⟩
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
def resval7 : Box := ⟨64135684237185103744882997541004577798328015697527586576,20499182980493094791194819781628079596024325278244210341⟩
def polyval7 : Box := ⟨24307088982767791909787368413677194006437583087155828925224,6687696647925589430735837524303433763051168348740727161385⟩
theorem cell7_lo : Holds Q cell7 (127/128:ℝ) := by norm_num [Holds,Q,cell7]
theorem cell7_hi : Holds Q cell7 (1/1:ℝ) := by norm_num [Holds,Q,cell7]
def resval7Tail4 : Box := ⟨-51020960232199500939061899142410720387012226912277230250,19540825898681820119459659146614810470633212151514555332⟩
def resval7Tail8 : Box := ⟨-51826066015478208734287319512806444058508932941515697595,18735775573760792533551709860486610483193789985427515567⟩
def resval7Tail12 : Box := ⟨-52643818540159585089391629388353300749345024685680260787,17918023055490358310110048645429550023855007244130904426⟩
def resval7Tail16 : Box := ⟨-53474474202098253087890625085419590661764363002297346489,17087367393557237597848826153242710110353119013011420873⟩
def resval7Tail20 : Box := ⟨-54318236603774589312074360381522287360480616609590207040,16243604991880922242358012487297826539459653534998953405⟩
def resval7Tail24 : Box := ⟨-55175312553664430058082734523525829922704687289883390476,15386529041991081756553476562164119202975667473315082479⟩
def resval7Tail28 : Box := ⟨-56045912123425032805361311930796743862575217067778325154,14515929472230479018194855484610708874752828803676086227⟩
def resval7Tail32 : Box := ⟨-56930248699389817132770898486122556603609830387225467998,13631592896265694691472279539409110325781571008294464136⟩
def resval7Tail36 : Box := ⟨-57828539034869958717534820295705538924950326125792409095,12733302560785553106763297813091576409113869672899514822⟩
def resval7Tail40 : Box := ⟨-58741003303281218412723836048938069174707634943309795730,11820838292374293411441939112133246323075417851135191861⟩
def resval7Tail44 : Box := ⟨-59667865152109048070204799270862725814297026952425535434,10893976443546463753177275921898531880568523629375876799⟩
def resval7Tail48 : Box := ⟨-60609351757725200326016153470526122501064019717154778485,9952489837930311489088537245035777598422281115882281110⟩
def resval7Tail52 : Box := ⟨-61565693881069277895640096354033400474038724000403183428,8996147714586233702512751461159176640546352419575916094⟩
def resval7Tail56 : Box := ⟨-62537125924208855733273009456972827496918790006729275514,8024715671446639099019604959418193699559718161266481843⟩
def resval7Tail60 : Box := ⟨-63523885987787672824762398810940524545553497589123047932,7037955607863081622265478437615785951682613316133964043⟩
def resval7Tail64 : Box := ⟨-64526215922626712852816740127210302192688365234976556591,6035625665928896663603405814225809726907491615236755394⟩
def resval7Tail68 : Box := ⟨-65544241277548747952743891066382533072039530150978969021,5017476076408047714581356759849038631438212101133007523⟩
def resval7Tail72 : Box := ⟨803198474696990708319738654616930701325039138404670398723,848204532158043090964405035930129743990881800806494931⟩
def resval7Tail76 : Box := ⟨-682008397963866662485802464294376884415389562273058479,263427974398411806871425920684040868929100867837676931⟩
def resval7Tail80 : Box := ⟨-692743000055819469175826610414704935883700364651327253,252666965097500124432594423705288376601285873001534892⟩
def resval7Tail84 : Box := ⟨-703673643734072566227153726031138092286368504817939302,241736320037929444772774776413994227773880214167479082⟩
def resval7Tail88 : Box := ⟨-714776761108339909504889339926341365040630426670816804,230633202662906046501063806888439982777960112534721364⟩
def resval7Tail92 : Box := ⟨-726055072220586788161082051688792886025489731362997521,219354891550657153592625165752394135221716553979124129⟩
def resval7Tail96 : Box := ⟨-737511341414947056150566358140272697417953774268142594,207898622356296866489806328169592254581355346317143834⟩
def resval7Tail100 : Box := ⟨-749148376654302030545503582969864921502682198344889399,196261587116941891560453376025255687914428280525601404⟩
def resval7Tail104 : Box := ⟨-760969030207786492966878657711923116249069037993685383,184440933563457429101056480720961017326908867231990820⟩
def resval7Tail108 : Box := ⟨-772976199349885763175300855960575454794982172097436280,172433764421358158886990750848407551744333611662989262⟩
def resval7Tail112 : Box := ⟨-785172827070565575609982234665476119093108353036163027,160237136700678346451851225545170945522030015317125165⟩
def resval7Tail116 : Box := ⟨-797561902796606961183601972180535601413740890997880978,147848060974636960884380961454886415803520142102927801⟩
def resval7Tail120 : Box := ⟨-810146463124322919810225157137726983958420828828525473,135263500646921002325087911868156485986361946147527790⟩
def resval7Tail124 : Box := ⟨-822929592563836475492871006371639608826174192817277871,122480371207407448130032425595362481490775169184711759⟩
def resval7Tail128 : Box := ⟨-835914424295102629190132649611232643775077603737905844,109495539476141384194672888512003669814481583771108110⟩
def resval7Tail132 : Box := ⟨-849104140935879110654089885817024513905762058717820793,96305822835383549819970604597419150425352229628336112⟩
def resval7Tail136 : Box := ⟨-862501975340976403567612810992916729679683997220160544,82907988448426163228418935860786101909205925333647665⟩
def resval7Tail140 : Box := ⟨-876111377201012061839167586753941516652603736956067844,69298744899166056576412355256976854051805449720722670⟩
def resval7Tail144 : Box := ⟨-976290025925163303868215441264848229225345674125012355,53038840798389958688630833504993936101149020172680631⟩
def resval7Tail148 : Box := ⟨401742436658730283647299911404413504177776088783,128278257368586759715552692175439305127979382045⟩
def resval7Tail152 : Box := ⟨408019901540724189362410650011921009332208383178,121939727986597893518629850983563952156122921162⟩
def resval7Tail156 : Box := ⟨414457960089451463109291181695465928615371838516,115501668388085900754864768605281491573240348791⟩
def resval7Tail160 : Box := ⟨420997604452481208540912992478733255306283996048,108962024024732812235528791126837159201097885252⟩
def resval7Tail164 : Box := ⟨427640436479034043789928108525367925345794463756,102319191998179429935729089100659701456167654836⟩
def resval7Tail168 : Box := ⟨434388084345075120360013773780942443392323439459,95571544132138349864705520877138409262690106657⟩
def resval7Tail172 : Box := ⟨441242201917533500118035462831165726814756607000,88717426559679970038012730157216355212822474955⟩
def resval7Tail176 : Box := ⟨448204469159354732426140718400027727743767546402,81755159317858737726346347128074642711229717168⟩
def resval7Tail180 : Box := ⟨455276592541263844366277489419051963506718423557,74683035935949625785789814528683502080030213226⟩
def resval7Tail184 : Box := ⟨462460305460025975177440007123103627484056872190,67499323017187494974552122065050476917007289976⟩
def resval7Tail188 : Box := ⟨469757368663306659760309137862822232917967640204,60202259813906810391761109589846854141574917130⟩
def resval7Tail192 : Box := ⟨477169570681235892655738182666405076588251772375,52790057795977577497183691694632280453918014271⟩
def resval7Tail196 : Box := ⟨484698728264781749989732116679140463669135449552,45260900212431720176320443573688017172643143953⟩
def resval7Tail200 : Box := ⟨492346686831041016434136890476604908228336982134,37612941646172454223843892780476995788737959218⟩
def resval7Tail204 : Box := ⟨500115320915556018062623684171110624604379655346,29844307561657509009069032121770637605068032682⟩
def resval7Tail208 : Box := ⟨508006534631795416405176274156190202053845014047,21953093845443455496621667358831255872635883247⟩
def resval7Tail212 : Box := ⟨516022262211334937425853550399978363114603678864,13937366335400143137788288835746544140966721741⟩
def resval7Tail216 : Box := ⟨524167950602178262849244014712051067719896915275,5795006492501711676420395791010215036441084352⟩
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
def polyval7Tail5 : Box := ⟨20856034635921664523688696355601183753254023393644445072431,6361343161612831321766059607304639699062624826175528007806⟩
def polyval7Tail9 : Box := ⟨21185115555805577779453621946976419847260501400644949452455,6032260229994728075537153705437198962937282937097784178974⟩
def polyval7Tail13 : Box := ⟨21519391006620804625854952529058185254967601747056879257507,5697984778990535392960434414745258681869796740209827468593⟩
def polyval7Tail17 : Box := ⟨21858940919159036163346118050155620511105443726690568645899,5358434866452159987366846743373821127822520978081292854435⟩
def polyval7Tail21 : Box := ⟨22203848517845187598814956443106656905855455068615826879888,5013527267766008066233398184148862023743594299659443247946⟩
def polyval7Tail25 : Box := ⟨22554198340473999954809222612435610920771685408654613662446,4663177445137195704713103745326157435497736432984668741648⟩
def polyval7Tail29 : Box := ⟨22910076258744312949399949772766520995045322257964020389360,4307299526866882709944118433868387314251101523305033789797⟩
def polyval7Tail33 : Box := ⟨23271569499306313741420677800450446323517723193067646742846,3945806286304881917909229608126606036696060339824134753490⟩
def polyval7Tail37 : Box := ⟨23638766665141026782372903228750480019929713573252134369866,3578609120470168876954765905129454315973899330594134056811⟩
def polyval7Tail41 : Box := ⟨24011757757277146564166502720863707724155539600944239965905,3205618028334049095161119148803301706058429313378682045017⟩
def polyval7Tail45 : Box := ⟨24390634196850535675451769758517799771636047579886541983867,2826741588760659983879376356826121334805805259253550766887⟩
def polyval7Tail49 : Box := ⟨24775488847511795005373554687478210905127677967756689188952,2441886938099400653996740991253534686340372901525177024507⟩
def polyval7Tail53 : Box := ⟨25166416038187398252125088729453713501191616636983904216759,2050959747423797408148341175506865621083210991079308028550⟩
def polyval7Tail57 : Box := ⟨25563511586199969610126108665196287778033889938108030423235,1653864199411226107110013904447432768204848602554748845182⟩
def polyval7Tail61 : Box := ⟨25966872820753384376425269765033270048517758164588486428478,1250502964857823628935405826755294644257963741514290739411⟩
def polyval7Tail65 : Box := ⟨26376598606801347276163544631832113699617791457723580926682,840777178822107881901879487683177617354377608111301179964⟩
def polyval7Tail69 : Box := ⟨26792789479215055411447410651479768935926167780212919011504,424586411682340597072719390994639744534514318623246634814⟩
def polyval7Tail73 : Box := ⟨27281250000000000000000000000000000000000000000000000000000,2⟩
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
def pend : Box := ⟨1030990641062799001308125461425415114023073675947920175244216,4144567894380032397744512565513746415075487976380842465⟩
def zend : Box := ⟨1003770726070036841609062500000000000000000000000000000000000,2461507171039602578125000000000000000000000000000000002⟩
def betaquot : Box := ⟨428753154835205099149730562138990320339040930056736480386961,394777140345999139168026100365935843017952209710505121⟩
def crit : Box := ⟨131703184166821754632759309092029173485793613381081030462,10375414002922393924469129504573703555437285367466430263⟩
def subsonic : Box := ⟨480934123929353487326757178073743770991232223498641817140,5311333071330556018475324159665568270714667660876666369⟩
def pendTail4 : Box := ⟨27215764405557214057371661199554535117482481200554762566922,1576402408548443068162681259703405230242011046443914526⟩
def pendTail8 : Box := ⟨27215799514836592573179963501690174720825231524684394149199,1576269290838428025927684829364538920908493593119947519⟩
def pendTail12 : Box := ⟨27215799516335697706204167200289010725185203268963504939200,1576269274780043367631164309532004074220186091937980003⟩
def pendTail16 : Box := ⟨27215799516336427014083072281905318003544497238914316403635,1576269274766942980039653743820421128205251843611339464⟩
def pendTail20 : Box := ⟨27215799516336428749544420124014619983213209547627049014205,1576269274766895379076861590730549967063118714407649088⟩
def pendTail24 : Box := ⟨27215799516336428764193437749500626616803973570848174728110,1576269274766894771241968938561263254164078478954703563⟩
def pendTail28 : Box := ⟨27215799516336428764554400569736283430802836571935658457938,1576269274766894747795011178569945161663780761114144531⟩
def pendTail32 : Box := ⟨27215799516336428764576629168322035010060239244565760565365,1576269274766894745302478822242286051768452502040826831⟩
def pendTail36 : Box := ⟨27215799516336428764579343074815109641262741714196376487992,1576269274766894744609654639897713263248007959083496361⟩
def pendTail40 : Box := ⟨27215799516336428764579320369787299909976298097114175942903,1576269274766894744118209905145400868759828931939390244⟩
def pendTail44 : Box := ⟨27215799516336428764576436072932246248524512377074690968825,1576269274766894743229595758415117518894044526136205135⟩
def pendTail48 : Box := ⟨27215799516336428764551901695818527537834626601364218422153,1576269274766894739044762377629624939083230139407561140⟩
def pendTail52 : Box := ⟨27215799516336428764119917319480128073834818291206033731399,1576269274766894685189251522669833946400852074537866470⟩
def pendTail56 : Box := ⟨27215799516336428743915868505812063708223431785224151893616,1576269274766892636581612024715902377824457663295306319⟩
def pendTail60 : Box := ⟨27215799516336425692278532112405171325209479553627623186096,1576269274766661431230716934222314981177028864178599958⟩
def pendTail64 : Box := ⟨27215799516334473342165143317605374173104430992693242206273,1576269274655539587151774039982201882804242761985775096⟩
def pendTail68 : Box := ⟨27215799507550728910834044813212802496718510835333162072568,1576268900414952419571370383906400080616494089447935538⟩
def pendTail72 : Box := ⟨27214680435278095367140373656809319054962659452701249862701,1543674765190492127174000360249065995996210111523649442⟩
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
end SepticProfile.ExteriorCertificates.C20

end
end

end OAI
