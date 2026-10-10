import OAI.MathematicalPhysics.Transonic.Certificates.BarrierData50

namespace OAI

section
noncomputable section
namespace SepticProfile.ExteriorCertificates.C50
open SepticProfile.ExteriorJet SepticProfile.FixedInterval
def cell0 : Box := ⟨250000000000000000000000000000000000000000000000000000000000,250000000000000000000000000000000000000000000000000000000002⟩
def resval0 : Box := ⟨128570646576994755685940598900135560575034431882534024384,307875416672964409638191770007286947063348387841012505⟩
def polyval0 : Box := ⟨3900792264488015902603390245457051762714810430932389075963,14853294610151442295491430393361135865597742611461634046⟩
theorem cell0_lo : Holds Q cell0 (0/1:ℝ) := by norm_num [Holds,Q,cell0]
theorem cell0_hi : Holds Q cell0 (1/2:ℝ) := by norm_num [Holds,Q,cell0]
def resval0Tail4 : Box := ⟨72828289853966907222710859437667240847195296062772,2067583670622249870216382988198536026518807361994⟩
def resval0Tail8 : Box := ⟨9706567675767828599193628827979232459372206553,506340693893116094565625071709079111202493258⟩
def resval0Tail12 : Box := ⟨9718916520937807157321976936819592784716819,772805999038229005822835601469098078035726⟩
def resval0Tail16 : Box := ⟨42790553501782093635160811413118723755081,31987587400484851921954435749070982219467⟩
def resval0Tail20 : Box := ⟨640004654798863759672124656157671043488,434261493661638009964805607383033651568804⟩
def resval0Tail24 : Box := ⟨27902176630109823045257985196507042185,6946574245750338826380556723547629766136413⟩
def resval0Tail28 : Box := ⟨3225764015787906536104414171132462028,111145091441104125936683684889140572630700442⟩
def resval0Tail32 : Box := ⟨931911505864447698727917304773444256,1778321447634242969964523425561173696553509156⟩
def resval0Tail36 : Box := ⟨46049376048966380856160496746264323,28453143156038124946057451182570390165233175822⟩
def resval0Tail40 : Box := ⟨-155618907370969317653841523476137143237,455250290347372518087499925440817888982259259607⟩
def resval0Tail44 : Box := ⟨-40120712487908696924702451929710461231063,7284004607936182072449357326924189811729013728493⟩
def resval0Tail48 : Box := ⟨-10272051114407321531204166485697569241221786,116544064096868756109984865002169888066983570588661⟩
def resval0Tail52 : Box := ⟨-2629656404004298031578407372210290534349278582,1864702560245672701859697848891709387125838679538171⟩
def resval0Tail56 : Box := ⟨-673192281527195406822792897433980649978905520690,29834609846070191666816911551468317299575310801341773⟩
def resval0Tail60 : Box := ⟨-172337214186010169258785676447903832320706105840406,477192191371330689082027661944413913061533263525635197⟩
def resval0Tail64 : Box := ⟨-44118262409002328008953974992394721043410754136017940,7593714148299368645475153824956793703018402864587135410⟩
def resval0Tail68 : Box := ⟨-11292803964507979077512622284009674047550902295293963520,110911669269272574898506156151516353256629155166504553753⟩
def resval0Tail72 : Box := ⟨933189469646046706711836981051491741821728414113486234350,2760236895234700484729849919752066122433149407091431089⟩
def resval0Tail76 : Box := ⟨-35203128440881910438236312429404106667666094408841,739304719014725858599612993161552151103988242682⟩
def resval0Tail80 : Box := ⟨-2097065132633173300999249490338954449506083923,94021397584215438944875573889112440445633089⟩
def resval0Tail84 : Box := ⟨-1306281154063873150620893813129633161157894,92544625671099636666416974824708429597969⟩
def resval0Tail88 : Box := ⟨-3976252002755401646383137104218480961654,605483450442149163581305561238822860185⟩
def resval0Tail92 : Box := ⟨-43516215956201308514682206032798613820,3152406123931933376854519486398541236822⟩
def resval0Tail96 : Box := ⟨-1437123716930148719597039144618609785,50338497820429524845401367169528132621962⟩
def resval0Tail100 : Box := ⟨-128622823824626256294783108318768391,805411414259835234441513865312233663551037⟩
def resval0Tail104 : Box := ⟨-29230360447597647017654501204586914,12886582066060823094415740099297009122818212⟩
def resval0Tail108 : Box := ⟨-18441592967679580483085137073882359,206185312877229782980477646093906456177622381⟩
def resval0Tail112 : Box := ⟨-580714340538037095175807455308786610,3298965005474875596138723432977137092203914204⟩
def resval0Tail116 : Box := ⟨-143132414730552404984894021503393688589,52783439953498443060796615653407388803278133490⟩
def resval0Tail120 : Box := ⟨-36624077631989818043879462985345179059339,844535004921409750773016039785380313367995227617⟩
def resval0Tail124 : Box := ⟨-9375624366183374943234944574950050986518388,13512551289103736897231833597519322044210287516334⟩
def resval0Tail128 : Box := ⟨-2400157316528680514210910371010944549715461114,216198570478708480353338776866349733228246255678421⟩
def resval0Tail132 : Box := ⟨-614440252982919322343297554150667101272983924112,3458601090037286846341787771828025187594405603279578⟩
def resval0Tail136 : Box := ⟨-157296880842188242386378058981205519657085445945981,55190151734710301551416014803451118901300623957514743⟩
def resval0Tail140 : Box := ⟨-40270250178760065127418518757178713026094002081920028,845290190788453524088104169968330040782001535783899433⟩
def resval0Tail144 : Box := ⟨-11203320002482121474303681395140244494206819700098095685,3428359279712071071508960797551676912298449701382726723⟩
def resval0Tail148 : Box := ⟨94522556410449833537963020983781014375812874,1598821272398898135349448078683479161625913⟩
def resval0Tail152 : Box := ⟨1858455584034173524271893211276914581592,73916433745779898365748970103514175443⟩
def resval0Tail156 : Box := ⟨650714789891690421410032782371598118,41851583250343561387566987880797055⟩
def resval0Tail160 : Box := ⟨1254907779584640506331191779718122,120303121213577751004065680115375⟩
def resval0Tail164 : Box := ⟨9214098854816837831696901903729,44066330189492546604147912791318⟩
def resval0Tail168 : Box := ⟨210760330371742224312912446971,685778022499512918614106991204883⟩
def resval0Tail172 : Box := ⟨13287738770889534972498422968,10971843755229598757033658208286240⟩
def resval0Tail176 : Box := ⟨2140736665540183251978116540,175549447969698519964006196662397587⟩
def resval0Tail180 : Box := ⟨853027189731035229931289845,2808791155906221932081264450473174661⟩
def resval0Tail184 : Box := ⟨3297593916335663053016621147,44940658487237435394909293535942640115⟩
def resval0Tail188 : Box := ⟨642152232667921706909998850346,719050535196335235153246029907679955610⟩
def resval0Tail192 : Box := ⟨163939024397417260806264615731532,11504808409458073639187053318690943748437⟩
def resval0Tail196 : Box := ⟨41965962895389112180216441708320115,184076895208343190911585852705168295206959⟩
def resval0Tail200 : Box := ⟨10743255418869996724124827966272936346,2945220251535141912595569254078290250517057⟩
def resval0Tail204 : Box := ⟨2750272648946782577768017028949767604351,47120945644378461242247166721537919881658018⟩
def resval0Tail208 : Box := ⟨704069989055063130915802324037514123805213,753275064899671422267128737983068481619555354⟩
def resval0Tail212 : Box := ⟨180243053328076462778001313670187642528711905,11883423794524292608499643232660799950833404561⟩
def resval0Tail216 : Box := ⟨46206924382078835934377864309841033532307197787,146846080478242671347224693640650393648926088175⟩
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
def polyval0Tail5 : Box := ⟨2370653166293292641677376674535549435331393213952802,57619462633768254829741325116104145549767023763735⟩
def polyval0Tail9 : Box := ⟨253246325905972628153293323643532562953759621477,12184429684508160916413059287661996323245047780⟩
def polyval0Tail13 : Box := ⟨219400909945623497438791978432826524205927963,16388443646542488167445489509211061461030909⟩
def polyval0Tail17 : Box := ⟨846475924543147765341204940989472977940662,491210017440186124747447429694473309972725⟩
def polyval0Tail21 : Box := ⟨11124681782483621787818281622096803667116,6406785877860771762907862100652443499879786⟩
def polyval0Tail25 : Box := ⟨425689602357014152334270355346225034922,102482018618393891297403070116136960351431384⟩
def polyval0Tail29 : Box := ⟨43041503157020430762862388138051770723,1639710902108323028989816896130271984712974848⟩
def polyval0Tail33 : Box := ⟨10864426707569232828391256245741090417,26235374239336539249763586089164559656659907414⟩
def polyval0Tail37 : Box := ⟨12635599516276627441859071864529175225,419765987758911512411789620736033353360774961398⟩
def polyval0Tail41 : Box := ⟨1557314724317986077898931677003620047810,6716255802700686099209257320409770243291278704164⟩
def polyval0Tail45 : Box := ⟨396254577936999001230637933546267318829911,107460092471762219783340904807849219128705664025427⟩
def polyval0Tail49 : Box := ⟨101432851926339064833055824184442550422967572,1719361384455145934406423005099656976493332849400315⟩
def polyval0Tail53 : Box := ⟨25966741272025996807764580163597768930528060204,27509757807467084818745975339604079764740966263978811⟩
def polyval0Tail57 : Box := ⟨6647484471116716583370167651093288645380132130519,440149892903071005072553348282230034412840632931627826⟩
def polyval0Tail61 : Box := ⟨1701756016745533032914518968238546837681017067065577,7040802890247681559560126754059623951036585229429483178⟩
def polyval0Tail65 : Box := ⟨435649637933256243072820668386312322849042893880335236,112244424775205480310659031086151995093839865778176583599⟩
def polyval0Tail69 : Box := ⟨111527453151058144113250961208875062940792863455567595116,1691354386242850044283611624915944080732987371065419502897⟩
def polyval0Tail73 : Box := ⟨29156250000000000000000000000000000000000000000000000000000,2⟩
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
def resval1 : Box := ⟨128309058437739863017446364245095353830432409653512386925,218316366222988937927116970021686487651996015322825468⟩
def polyval1 : Box := ⟨3881698939393565397294580836039454437782566056670240354790,8339523159670109436085463957345790034474831744929049933⟩
theorem cell1_lo : Holds Q cell1 (1/2:ℝ) := by norm_num [Holds,Q,cell1]
theorem cell1_hi : Holds Q cell1 (3/4:ℝ) := by norm_num [Holds,Q,cell1]
def resval1Tail4 : Box := ⟨70666468714362430696169806143158565689482121062614,3463173182204172124239723442545196760248647193455⟩
def resval1Tail8 : Box := ⟨9152536736001218254781871442347774271256294440,6942528658461778765776774427397429459616483059813⟩
def resval1Tail12 : Box := ⟨-348322735170602193165826233070693604088921950,21940746723392509942194460358660011365132086700538⟩
def resval1Tail16 : Box := ⟨-2341719857964800104461951075017456584260287745,69342380990374863003123168735955146720065532057971⟩
def resval1Tail20 : Box := ⟨-15346947800719791167589260505375493768383184045,219148221238962201409637638991762130311243343680823⟩
def resval1Tail24 : Box := ⟨-100577760764400569794970348470675709500116245132,692564526633596227820057630982857333927343270102491⟩
def resval1Tail28 : Box := ⟨-659146413098643466970281431840472460559083876630,2188504640314823023928061342653746931694498063925351⟩
def resval1Tail32 : Box := ⟨-4319781932899951223230732613393338348269062058729,6914518852663995017707219618497244638615750545083104⟩
def resval1Tail36 : Box := ⟨-28310122875457487184696397787605388043853119307555,21838636672887570110886384310522143789728113152438607⟩
def resval1Tail40 : Box := ⟨-185533221276600667262622927854534738123335379148607,68924817145579388292790751410658723832248707453954230⟩
def resval1Tail44 : Box := ⟨-1215910518958332243814705722378229592108292282814283,217206925208388989697943960745946436334903581048071257⟩
def resval1Tail48 : Box := ⟨-7968591177045314527288849166027571677497963609845940,682355432850126443632145721252037401007527328848659241⟩
def resval1Tail52 : Box := ⟨-52222959137883479731938204723645383547595502799202136,2129541857540584485718883291825394228859913512949401313⟩
def resval1Tail56 : Box := ⟨-342248385005962875140972031599413056440042113486780810,6553205850422212336344291256474976459662524076071190557⟩
def resval1Tail60 : Box := ⟨-2242959015952064439032098778789209699739875663170809088,19550081530565165864640290990890289032764622439701340128⟩
def resval1Tail64 : Box := ⟨-14699456169340756297851598785111501537820167709723551488,54177313919589393052650814311115723802156085756962194318⟩
def resval1Tail68 : Box := ⟨-96333680450372686337136583448814299874309038593843525296,121350341869167106465018758969818692451136020160735236523⟩
def resval1Tail72 : Box := ⟨936647372069353295461030825881300106920564935487183983185,1606571120045929742376681693585279319676043017850795093⟩
def resval1Tail76 : Box := ⟨-34399506658773935779477100326419780918695389297512,470731586958448718539656678621875207987981051443⟩
def resval1Tail80 : Box := ⟨-2002124184548203443485394265934167939740982237,75517892336047370936340602105048031856548403254⟩
def resval1Tail84 : Box := ⟨-4437484859396976557443402511932190374583424,238494191637819430963715217898002038417123964706⟩
def resval1Tail88 : Box := ⟨-21103477955672616341008814095117343093347054,753748523803550744613611580323241762905088989568⟩
def resval1Tail92 : Box := ⟨-138280102914512475278449755072622629046097975,2382145962735115778710589098584947232752261694427⟩
def resval1Tail96 : Box := ⟨-906232231436457874913556582463424585814118107,7528288411680467255049932623617149618030885874266⟩
def resval1Tail100 : Box := ⟨-5939083543960650950171064399867619172478529349,23790034112025687601146410159396968441431879725578⟩
def resval1Tail104 : Box := ⟨-38922377913022891664572400131323158457738386110,75168104017961104331852705310277015991653835102584⟩
def resval1Tail108 : Box := ⟨-255081695890645557569607572434891702446492090721,237436260987365791452944529308525802240703823322722⟩
def resval1Tail112 : Box := ⟨-1671703402188868554513179755020265592653881257045,749550317917732683304170063589802798297723528977628⟩
def resval1Tail116 : Box := ⟨-10955675416584913539838928556145380178946080522709,2363276885792056029492028736751725382412925920876165⟩
def resval1Tail120 : Box := ⟨-71799114410130957296408157441868534274348759661158,7431948239533228231087599726637642319490572341041340⟩
def resval1Tail124 : Box := ⟨-470542676198240062309594305735618969411626366967956,23245004516511641418722636602554639888266214637203996⟩
def resval1Tail128 : Box := ⟨-3083748482733255769546060716369313950388285590987632,71869092027560106533659523682825147871806453051265519⟩
def resval1Tail132 : Box := ⟨-20209654056551140018524575246161051460104041272111469,216678335704468593882169560366238267704742452296207791⟩
def resval1Tail136 : Box := ⟨-132445988941111058887563392802397361886746145220520572,616237040523555755076857923022024960302112856839551268⟩
def resval1Tail140 : Box := ⟨-867999103212884196798272315139571741013601391025574153,1498209875075447242264602404853008649666982686566023815⟩
def resval1Tail144 : Box := ⟨-6066692261782203340008221037528481973690400733874905179,1725322422211433366533436595395692141697296606726115257⟩
def resval1Tail148 : Box := ⟨93087487254692313620081279345183837590998491,1091267591217036313545565230230029278923648⟩
def resval1Tail152 : Box := ⟨1785772057239568015131328820163033239359,4493888829794054034747512024789086937219⟩
def resval1Tail156 : Box := ⟨782890878108558579908730628611479712,14056719471376552486087555823685040694145⟩
def resval1Tail160 : Box := ⟨1126312573536791041555995042833708315,44425600863645403719180574268167963308131⟩
def resval1Tail164 : Box := ⟨7373870899683306677786954475307006322,140403019523910354408542357623159295923346⟩
def resval1Tail168 : Box := ⟨48325346586856229772320144659488229369,443717856221215345174686024556387169727441⟩
def resval1Tail172 : Box := ⟨316704990203809210954261850204987467048,1402203572556852613363767634409817747703737⟩
def resval1Tail176 : Box := ⟨2075557823728115179207400884104451314887,4430581121831132456800665173569536746796894⟩
def resval1Tail180 : Box := ⟨13602375753573813183601713714120425188598,13995781698217338569685724417655894248197695⟩
def resval1Tail184 : Box := ⟨89144529738617602731258915460262604952451,44187427358366980398805276745712706669684411⟩
def resval1Tail188 : Box := ⟨584217590095001686270968686176206633286125,139351614550090591106788222524520130305605619⟩
def resval1Tail192 : Box := ⟨3828728398446601422221689043150909568243985,438437605279177001777371669560585266905124572⟩
def resval1Tail196 : Box := ⟨25091954432059695777377347250044064913066437,1372688063116972979144039153405202808758713146⟩
def resval1Tail200 : Box := ⟨164442632565949354841620324367668582701901183,4253232484626057717787001424403428028454355899⟩
def resval1Tail204 : Box := ⟨1077691236784606999673093827400399025868704175,12884343701501579436429800231633361165538797468⟩
def resval1Tail208 : Box := ⟨7062757289591004350333197757375942790243914782,37064167947627088008088037130484631989829432472⟩
def resval1Tail212 : Box := ⟨46286486771184715917876515224026682821138155196,93176388546319563596128355048848936596378529680⟩
def resval1Tail216 : Box := ⟨303371815119588345848337975935293903840931872022,137423359298529681333057272957846146268485184205⟩
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
def polyval1Tail5 : Box := ⟨2305265450342504858601817018740243247918367871885673,125848864835003752588839502058653013742847057681058⟩
def polyval1Tail9 : Box := ⟨243161028730692883593497344368993088691804757243,292096949518221733203110198990472002473439087929854⟩
def polyval1Tail13 : Box := ⟨16562449795513228083407920675526558791597276606,923143008652088183556089709770050102567846299005817⟩
def polyval1Tail17 : Box := ⟨107209679288027459278333552099473083034062376354,2917532279236320306474810936928454035181969718365958⟩
def polyval1Tail21 : Box := ⟨702604342798128764233723522103106671624463834060,9220478987868413368735553644020357726150339265914346⟩
def polyval1Tail25 : Box := ⟨4604587757110417589656284115988788270706363421856,29138882913522101241612517351938975317053553959357825⟩
def polyval1Tail29 : Box := ⟨30176626322648551616559559159979853451588844661384,92077635723398196028323360768789262865500082873609429⟩
def polyval1Tail33 : Box := ⟨197765538267884550082113890330645711239005725268152,290908406826281840616342187978265109109440074462575275⟩
def polyval1Tail37 : Box := ⟨1296076231592356413589384291873216903508065162518264,918743184574885764140665628558317148436453814466408419⟩
def polyval1Tail41 : Box := ⟨8493965191363640795268949932818841295080775865046960,2899284439332814112565012083681867366546595828420213783⟩
def polyval1Tail45 : Box := ⟨55666050278120733689413038245550906604781663881237974,9134349647971132409286215980982156177454315968237053387⟩
def polyval1Tail49 : Box := ⟨364813027102692083228791236607961026891746482039533165,28680174858722108057182165368782995319676947580023096644⟩
def polyval1Tail53 : Box := ⟨2390838654420205928197960637671338403285179497297463409,89405666268680399903306301759110058811273177763745365313⟩
def polyval1Tail57 : Box := ⟨15668600205608516989721928671988334844759061844065946080,274453686958759049465633401360443349402092865005432859388⟩
def polyval1Tail61 : Box := ⟨102685738307537503922711968834694233385669436858982407977,814243959397181997549134511540666306500418265578600211593⟩
def polyval1Tail65 : Box := ⟨672961254636798068605165354671476763892667291061118517728,2224989394952850064854145990978061489530780392217870203250⟩
def polyval1Tail69 : Box := ⟨4410319426972336806894427142486885062191441689486088325858,4748636167661319786542921417849786169365376950652885272248⟩
def polyval1Tail73 : Box := ⟨29156250000000000000000000000000000000000000000000000000000,2⟩
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
def resval2 : Box := ⟨128180335463594624398957801572487120827928653559603568015,195204326014776263827012696029020969680478145691846607⟩
def polyval2 : Box := ⟨3872267382211615132969613564752568954809517659298085470830,7016557840963774016755770208024032041704091183394773049⟩
theorem cell2_lo : Holds Q cell2 (3/4:ℝ) := by norm_num [Holds,Q,cell2]
theorem cell2_hi : Holds Q cell2 (7/8:ℝ) := by norm_num [Holds,Q,cell2]
def resval2Tail4 : Box := ⟨-131466308609295715549263720632258409942996351405653,36539569698142014586533040515618382943261293025293815⟩
def resval2Tail8 : Box := ⟨-461451370799884683675576037545440855567032384977067,62215134491320938155788561935505529477346654496907541⟩
def resval2Tail12 : Box := ⟨-1058865766569304542841013824321020711091092468852949,105864637642477678788184225675835439104043253455325604⟩
def resval2Tail16 : Box := ⟨-2429670790444782868412252407776167669239822768877880,179977105551863212799252076751514323103855456746147609⟩
def resval2Tail20 : Box := ⟨-5575116589929920679684458930714237774574624974523310,305602790906212144405779336061514016647643060957627415⟩
def resval2Tail24 : Box := ⟨-12792648746111178105426617967655656360766606112222879,518063123475546422112965440297955801496463007960933341⟩
def resval2Tail28 : Box := ⟨-29353980190649611322986296811020039603144360332855681,876262530854710492293084195155137625903985910433443366⟩
def resval2Tail32 : Box := ⟨-67355570385295090111248129680537715661989194369157922,1477586216054436268422590127868613308830955856375913958⟩
def resval2Tail36 : Box := ⟨-154553925309712512057167274814531753432096888947708529,2481048555846947065563092090572514298473308123339791777⟩
def resval2Tail40 : Box := ⟨-354639054973471489058992527092498392218266668579196791,4141582420585744516641345569492551902691221125124396138⟩
def resval2Tail44 : Box := ⟨-813753898909051765453329642157587204465885425449675901,6856601437988302984501090091611688513045229363054230524⟩
def resval2Tail48 : Box := ⟨-1867237684916621122383701829900300052568892743710562894,11218049886899940724444992967582550550488441506342596316⟩
def resval2Tail52 : Box := ⟨-4284558976180654101501148381953970947622953181786836027,18038363928509323211196493867047544230181411487445799357⟩
def resval2Tail56 : Box := ⟨-9831338435733118239522707611929511698817217239253502598,28250582521205656191410012365956360795973808607801451788⟩
def resval2Tail60 : Box := ⟨-22558964872506637965076689356421950443692834792164805397,42407111029024466784444824970892316149998162305311147204⟩
def resval2Tail64 : Box := ⟨-51763745002705243687628360596192303849272131047166845834,59065512316130600584202093992610146673173092371308317504⟩
def resval2Tail68 : Box := ⟨-118776430393449425731873047920668085471104137062368267395,70292883401197064481669160074986685851500438120821870229⟩
def resval2Tail72 : Box := ⟨938374227253578373711621053736057343758997099475891063482,1030244917805422027978129999485114377747215294365009782⟩
def resval2Tail76 : Box := ⟨-36373197207945613106947740714010792838469393442845,463421819872672686857763061603211375914609245001625⟩
def resval2Tail80 : Box := ⟨-5413895519241812943523127808286614525828374873433,789135292011040940977979862055089363762529608402053⟩
def resval2Tail84 : Box := ⟨-12418220930277848803124676118738206595566405434488,1343044267090352491098433217547558377222816734160988⟩
def resval2Tail88 : Box := ⟨-28494816349610794473505847895279399072598468719052,2283864344870698396542004439606641286022355455646476⟩
def resval2Tail92 : Box := ⟨-65384135151516808522759267845799271563296170002428,3879398507224238533559297537809843086983286939149558⟩
def resval2Tail96 : Box := ⟨-150030274895397659845268607394035746662976449907187,6579594757662263884683832128457378486608079454993060⟩
def resval2Tail100 : Box := ⟨-344259097914803692679130206991659685695405631239722,11136184106315174265950507069984701078891596947105087⟩
def resval2Tail104 : Box := ⟨-789936075100471585140665383756944033727006537567863,18795193189591735556457716358066250298856191839461310⟩
def resval2Tail108 : Box := ⟨-1812585365280785151953960420529221214035391902331345,31598780510678931792719487547230695829475451703504460⟩
def resval2Tail112 : Box := ⟨-4159153898639457140461509783132379604145472235559092,52839161231694154099103134810160011998728162340998258⟩
def resval2Tail116 : Box := ⟨-9543584254796241850296544456608073682809409898064092,87693024980458431896514384609980406920945359218677598⟩
def resval2Tail120 : Box := ⟨-21898684840248118513509975874904228245406888152317327,143982677686866893642312651225161272336713799718610083⟩
def resval2Tail124 : Box := ⟨-50248668103025134862617795523004593802669389750956082,232737612992794566606235080581789618015567640082208871⟩
def resval2Tail128 : Box := ⟨-115300469619406437707898417797402378856054614407329327,367461632574878609199218992272056486650008211111320205⟩
def resval2Tail132 : Box := ⟨-264568172577292696802650699249842081246162013613549927,559002660653857243912423058876386016519834856191043946⟩
def resval2Tail136 : Box := ⟨-607077474902970031842514977427221767332784194288887351,797898007445603252305454959886958582698337919286465660⟩
def resval2Tail140 : Box := ⟨-1392999318195715481010018946816637382826484052923979913,1003827597211120333251405159027051098982772527506913570⟩
def resval2Tail144 : Box := ⟨-3489898872010501864292611550171659379271503250858638749,869098744547972320946082687314369893348081490673557061⟩
def resval2Tail148 : Box := ⟨92774590831332722963118028149630288617248855,69040636488322895427085406576638163705770391⟩
def resval2Tail152 : Box := ⟨877241352099392544115336241863718182451508,116229385628486738453338052064582041008928822⟩
def resval2Tail156 : Box := ⟨2008896896488616623354179570342111584658577,197766837491224828427514528722283635190354868⟩
def resval2Tail160 : Box := ⟨4609608492540754007622522747879850865926386,336198973601639727638602333393043305199474185⟩
def resval2Tail164 : Box := ⟨10577196249955209215257746855811408580301704,570827198690991172466747499374464033754722214⟩
def resval2Tail168 : Box := ⟨24270408369334317153232997934543132090010107,967579821400796585650814992837913550053384911⟩
def resval2Tail172 : Box := ⟨55690819050197221795399306045661235119721934,1636361884464361496200698277351263217101287030⟩
def resval2Tail176 : Box := ⟨127788015730321924770471816630615549038499595,2758779195263277603955017275086203117995035171⟩
def resval2Tail180 : Box := ⟨293222065015313804637048646692588775544813113,4631134159986678558577359264706006780292013332⟩
def resval2Tail184 : Box := ⟨672826625567858460024924191085700099047763613,7727907692469692859522177648509002204164611277⟩
def resval2Tail188 : Box := ⟨1543866311866362243402605484694846627579325817,12787415556805778616595990308368998861812045632⟩
def resval2Tail192 : Box := ⟨3542551822921953575844567503859106972010771601,20905982343709070568158379229916649378542817723⟩
def resval2Tail196 : Box := ⟨8128730656034913043847832335373527156309521708,33579389271712140280817420059665505242989314478⟩
def resval2Tail200 : Box := ⟨18652165269910162147182878063125884723509735619,52500045985421756354263065578050070319680985626⟩
def resval2Tail204 : Box := ⟨42799212322007009684284905016827181566885445172,78583318832445415954298201047747604134899755569⟩
def resval2Tail208 : Box := ⟨98206966798771515132896472320435917964328970658,108866272521923971513820543363077694260462163866⟩
def resval2Tail212 : Box := ⟨225345463735353329745936340567004165510512006183,127912341051984284425220154497689368825197270137⟩
def resval2Tail216 : Box := ⟨517099585560477711983786812833157280555748159477,85563062645411542794885168617202655078481513624⟩
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
def polyval2Tail5 : Box := ⟨23643660350016136875619474353326994219966454705486135,3279185830001661323707972069876860294183328699665410825⟩
def polyval2Tail9 : Box := ⟨49034632355768585347475047631384557964414831849953188,5581568336334153611605270982459273790514063255483676117⟩
def polyval2Tail13 : Box := ⟨112514207448879239844037238482012808062708343170754155,9493045474562237092527812095502991401206831023079830146⟩
def polyval2Tail17 : Box := ⟨258174821837528443449933052784026501027587626101331768,16128485926480121310432751663981034601197413268339364025⟩
def polyval2Tail21 : Box := ⟨592407308003801455930560788337041400445702651682849604,27362512485876288755355299834601800356167856198204063083⟩
def polyval2Tail25 : Box := ⟨1359336344572547726428342681112658049840014341044782469,46330522662396553444451538898050025460456645418258581572⟩
def polyval2Tail29 : Box := ⟨3119129816109606332995741471380181413065422107147107638,78237664224933890980076202418727803554421860715630171272⟩
def polyval2Tail33 : Box := ⟨7157147565861109859990112487315794811163888899468075866,131633951306323048770795928567534139492850029815839008463⟩
def polyval2Tail37 : Box := ⟨16422773112855771695572880371298905061839213434522209111,220348714175968182376707584202152991667004367576105430549⟩
def polyval2Tail41 : Box := ⟨37683654589269138115659737261764836413372126299638069735,366238049673547569869910249554128459787304386312882808034⟩
def polyval2Tail45 : Box := ⟨86468820670226610963540557421290174814336198935963132750,602603774357052537693027396596726938713091315640064258450⟩
def polyval2Tail49 : Box := ⟨198411142167430103274650349587357210879463449582617185797,977116283585062771844225630023147641107403674112078727684⟩
def polyval2Tail53 : Box := ⟨455273716364437496699908712655991024675480967113713668061,1550124174465304620555134174655384504722362476439806447054⟩
def polyval2Tail57 : Box := ⟨1044669944177717247341352750692610561318895101713721575998,2376450322727165801933697131812117691936382338739132330182⟩
def polyval2Tail61 : Box := ⟨2397097071588261779138166239196646855480491431175030739873,3439183067204954452214014079182711864458597946952930413950⟩
def polyval2Tail65 : Box := ⟨5500373015128919580668206651995719893083326305667471563628,4456063240019226139882191144619661042364487086717812124636⟩
def polyval2Tail69 : Box := ⟨12621142757608334528582763605319678402055237029499726322580,4364098330201498558994261385763629883401093565793784351423⟩
def polyval2Tail73 : Box := ⟨29156250000000000000000000000000000000000000000000000000000,2⟩
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
def resval3 : Box := ⟨127993076115775556164431291523556799954302756241897816471,1712915245748322707503648913612318122588234108085409360⟩
def polyval3 : Box := ⟨3891771526084801734183623679232878645111763441586023009859,255660490279425394183019234336589277932794635250981725114⟩
theorem cell3_lo : Holds Q cell3 (7/8:ℝ) := by norm_num [Holds,Q,cell3]
theorem cell3_hi : Holds Q cell3 (15/16:ℝ) := by norm_num [Holds,Q,cell3]
def resval3Tail4 : Box := ⟨-183103630983277163099353755198977308286636751785912826,1999620137987406361105994505025328618952124193392218011⟩
def resval3Tail8 : Box := ⟨-271561891934233379780370781180418169886760967560067152,2554146229568419064121736500591205959702428660302833889⟩
def resval3Tail12 : Box := ⟨-402602772716018617050304830818153959963615193292377574,3255384546232464241171503199738342800919144339101692727⟩
def resval3Tail16 : Box := ⟨-596876778836691308119801493106074223721705966128749298,4138527802598400308450192726625736608405878780523929324⟩
def resval3Tail20 : Box := ⟨-884896759909427542897702222324482495015910566878739618,5245265702291706640177113727793021073112525676817061301⟩
def resval3Tail24 : Box := ⟨-1311899379339736851447264493089144278311067225298505994,6623830539135592746599812290000369080926937821613152117⟩
def resval3Tail28 : Box := ⟨-1944950032010677410423347583750135661499688348662580109,8328156060575973487931985710989195274411648079544611713⟩
def resval3Tail32 : Box := ⟨-2883476192299281443049707197570674558823222826683799605,10415452812812002574364807923831817254432827284653259974⟩
def resval3Tail36 : Box := ⟨-4274883577837396082745637779578076023434175084143123357,12941088990636146818586589952696033507416383066180520118⟩
def resval3Tail40 : Box := ⟨-6337707816998371842062249920534256994522226792041056819,15949027555791398183991027750500500944110901126213937516⟩
def resval3Tail44 : Box := ⟨-9395937840712368565658464846985621686690926086593923775,19455094048495539944374021018203785865883280113077008949⟩
def resval3Tail48 : Box := ⟨-13929901859745719968668428542725220761389760921417952922,23418863096128442813168721412532037441924589970273069518⟩
def resval3Tail52 : Box := ⟨-20651708122351268570138101088109679620933678861870083052,27697697510205158010471041521344219661514098507902493692⟩
def resval3Tail56 : Box := ⟨-30617089241903236880411239717430475857683238168091443087,31973066758792367499838454699206322993180155960876108730⟩
def resval3Tail60 : Box := ⟨-45391216459802497991844242930856013474025907463402486310,35634135908803715959970716418403964670959843112825778372⟩
def resval3Tail64 : Box := ⟨-67294526745553553149461194268960362563635909523197114945,37595892838389258921847075237704092512620114685498325820⟩
def resval3Tail68 : Box := ⟨-99766693087287837705408882830436216958650111898684071453,36017494826598326568883694002409890506186748046873739653⟩
def resval3Tail72 : Box := ⟨939235528215590898356177375332194582321866606166093803550,762853164960417303016602555713990986678894108164952230⟩
def resval3Tail76 : Box := ⟨-2430642101900087566310240711054346117454752771163049,27239655067294042287808504200760880854467278954736449⟩
def resval3Tail80 : Box := ⟨-3553389671647492164464982114297138563170706511930683,34812033991857285961499496366149563544397558896685876⟩
def resval3Tail84 : Box := ⟨-5268057672940580960910695108117506043076672634527680,44397449043427450395640459502827901796510766641220883⟩
def resval3Tail88 : Box := ⟨-7810133230283050529792717215207559566886634216222697,56483765991193269623138170329396635215088954693307119⟩
def resval3Tail92 : Box := ⟨-11578874962106651889716014800326546173126474309907042,71652038210800969562018002143643149038148137747176318⟩
def resval3Tail96 : Box := ⟨-17166204651709728142406453188365735153189863053642537,90579397831246746992499493541819406254679820623685048⟩
def resval3Tail100 : Box := ⟨-25449673056212705830764813731864056245194354089169071,114031132955106513589279826251031891586831259180866723⟩
def resval3Tail104 : Box := ⟨-37730288774322078698531877113058187708879193893869803,142832952761634787638564976246274729972420606119438613⟩
def resval3Tail108 : Box := ⟨-55936855764291063918765220625219762473472525941502801,177809170849051537391345944281564139112372482452034461⟩
def resval3Tail112 : Box := ⟨-82928912935448946936271931474790355271034665710753945,219664264351109487025337548235851479488779339788427387⟩
def resval3Tail116 : Box := ⟨-122945855763411310353317823478735120723043174175793092,268772592960576709972693545590766407055817464717219621⟩
def resval3Tail120 : Box := ⟨-182272779352159577805599251841951751243411747171891255,324821744214759511806026950258671435533125392300168502⟩
def resval3Tail124 : Box := ⟨-270227620821102342386071303885728839043928808514389492,386225647257546738813954376030695426090622047693958575⟩
def resval3Tail128 : Box := ⟨-400624642440710960045015896617005105740335648143948452,449179236607236979286673930379636107661714496212645319⟩
def resval3Tail132 : Box := ⟨-593944111423848573516797791376734270262847535008144654,506159533362132888259947292498190126218648285418544236⟩
def resval3Tail136 : Box := ⟨-880548948212721976688914294451609185913599814226567267,543577322775041242301547613357911577275774980210849411⟩
def resval3Tail140 : Box := ⟨-1305454316765902379494677588954371302821072849285378220,538132367263075286424196470663044144184195161509465718⟩
def resval3Tail144 : Box := ⟨-2199380510755703639204344511637262585825478802104506260,439809343461479725581912382834666082500831279333529742⟩
def resval3Tail148 : Box := ⟨891178043327298986162766956832993784915442804,7808069286507654654697586443625504636440774976⟩
def resval3Tail152 : Box := ⟨1184743150520622261020249545217506963120811213,9956991447392579394151331813602175895748569287⟩
def resval3Tail156 : Box := ⟨1756432612565278280335437462744416553372411852,12666966973069941893898766116471998417060839735⟩
def resval3Tail160 : Box := ⟨2603990609871893493556573199250426369024294597,16067652159618602422100601944486187082815751512⟩
def resval3Tail164 : Box := ⟨3860533589529338392285846272358212223426939210,20310622569310311798675792472683626641208332453⟩
def resval3Tail168 : Box := ⟨5723415260941984387568542058018686526734804725,25567071455615345214715296784631293626095571446⟩
def resval3Tail172 : Box := ⟨8485221405152269117297725784091615026166435891,32021511186577136156479550565095420887785175690⟩
def resval3Tail176 : Box := ⟨12579723646088253088272830598814591363218225020,39857791951572552904907339097858963578518675187⟩
def resval3Tail180 : Box := ⟨18650007991053960263440475741970968536430191197,49232362817998851222739704457882931855163712528⟩
def resval3Tail184 : Box := ⟨27649478466447419677551154461581988766708073055,60226848513149322120778049600932470420583702772⟩
def resval3Tail188 : Box := ⟨40991599565708070110804164377245718176183538784,72767668877449501652290419536708991904511526501⟩
def resval3Tail192 : Box := ⟨60771896185832653962636369482505242809475251762,86493830563614746002549540366109937285759048957⟩
def resval3Tail196 : Box := ⟨90097078551460679713591044295948847650319644367,100544040821414081907325347291563037540127869477⟩
def resval3Tail200 : Box := ⟨133572984767265677381720060212958424948569995040,113219240402526332460854295685827756886381956241⟩
def resval3Tail204 : Box := ⟨198027977671280014772476783285320770787721157637,121454002945559569679903790633337812883468623943⟩
def resval3Tail208 : Box := ⟨293585413314857596838976117794603461038318236832,119996237681927342939487093289676676631165993080⟩
def resval3Tail212 : Box := ⟨435253624313769302056515929453274660886260717026,100143651741460848147592679772172939174972861648⟩
def resval3Tail216 : Box := ⟨645303376410272395895847924731564782983919307679,47808024977930795850025422309037840420312736537⟩
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
def polyval3Tail5 : Box := ⟨35891789533014328055719544129782247075014227515858588604,324077330094419186151839739593624162965888794780844605863⟩
def polyval3Tail9 : Box := ⟨53207848860905044946346790210958269648332265255484959058,412783023044686633158295977627108853113485931047546080903⟩
def polyval3Tail13 : Box := ⟨78883036705274091993904147922285465972237676187285110015,524359980893015053972570542470297137565083579654444917676⟩
def polyval3Tail17 : Box := ⟨116947661673461099309511554156555297694586536443476983280,663973511685723383350712707495181849970464230418425694989⟩
def polyval3Tail21 : Box := ⟨173380185933045566850562432882831277189697479758000539908,837552160087052548009478252452666118950875431693665923374⟩
def polyval3Tail25 : Box := ⟨257043949780821454415094934773731764851989529533412934348,1051646662145561744943978777133306250884040002316037587081⟩
def polyval3Tail29 : Box := ⟨381079255183406081970902427999287659924282239326571831440,1313070827645383040644434710960447440440501908038567899235⟩
def polyval3Tail33 : Box := ⟨564967192789280661831583807120984147666860697461452024007,1628174927275263020892248248759597012917702587887980172585⟩
def polyval3Tail37 : Box := ⟨837589358608831227271569207363329424060139036310650763001,2001517050883513163655023584216718798551979836637267650947⟩
def polyval3Tail41 : Box := ⟨1241764022068476055439293773924330979008954021305323272495,2433567882178245564387362405158896919208751107314065457067⟩
def polyval3Tail45 : Box := ⟨1840971199854759774850301066818326273490341948261066584148,2916886611043277718036813003565276475175872102635034573188⟩
def polyval3Tail49 : Box := ⟨2729322881370918469131695563630132395446966567806005877136,3429906145691082224984588616030624105157679233513217505235⟩
def polyval3Tail53 : Box := ⟨4046344337903028933287449400621196981569630743853665124805,3927013361208779020006952747815446957883153491270229081452⟩
def polyval3Tail57 : Box := ⟨5998888080495597390113376836084988429719158627137473298951,4322928614200530134410077327574940540859095435081613417721⟩
def polyval3Tail61 : Box := ⟨8893622291414282261093005052281471573685149240686984890199,4468364452360683477331583084006309916667949157540472566414⟩
def polyval3Tail65 : Box := ⟨13185196389943512129970928533373809208548349514810671205235,4112406834595707892962693082538353153922017460161684827668⟩
def polyval3Tail69 : Box := ⟨19547649049321626659264005701461408551123019056994571653875,2844760703671124175263065686366992595758091835603626414797⟩
def polyval3Tail73 : Box := ⟨29156250000000000000000000000000000000000000000000000000000,2⟩
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
def resval4 : Box := ⟨125099818560671543321588611538302680768643795402771045894,8287008229707524171731853986655625721282854659062962892⟩
def polyval4 : Box := ⟨4779376875466293536355889479679357692890086485243033928716,2034998791167858522649735614627026572864630308674729510254⟩
theorem cell4_lo : Holds Q cell4 (15/16:ℝ) := by norm_num [Holds,Q,cell4]
theorem cell4_hi : Holds Q cell4 (31/32:ℝ) := by norm_num [Holds,Q,cell4]
def resval4Tail4 : Box := ⟨-3616952357997300844358656031135481321189196952063132031,9022633223796766034662879199419331140698364765626521522⟩
def resval4Tail8 : Box := ⟨-4382799622376078492753917954438537562356044601571782022,9968403800305620415532187625245348277183085766409446295⟩
def resval4Tail12 : Box := ⟨-5310704932772030782358533490308760266500973066830863762,10983810827279224447544472605670913216741283186027531646⟩
def resval4Tail16 : Box := ⟨-6435061891113965442893791214321128362496083018710343154,12065912269322179237062993649124194073094823944735704907⟩
def resval4Tail20 : Box := ⟨-7797462308038064953669137190202246934096817690258679344,13208749225054876691518071942474138082586621171301198816⟩
def resval4Tail24 : Box := ⟨-9448303602057336941788221884557177132681200055005087536,14402382267050636637974109288659681555246910076726402908⟩
def resval4Tail28 : Box := ⟨-11448653091227465820129968396993169082338156158480733103,15631680529649333432869176497749185087540783628400182997⟩
def resval4Tail32 : Box := ⟨-13872506973075228816141084223530486168595175803604935150,16874804573543105423278632359895339614647550771534621141⟩
def resval4Tail36 : Box := ⟨-16809527564904818573506616761290510635278251953640888088,18101311443961104825759051694622928261740256654550075577⟩
def resval4Tail40 : Box := ⟨-20368360059483722270558416507949304933516369822910475100,19269794270044891040916026675593441055587132294200016026⟩
def resval4Tail44 : Box := ⟨-24680651488322829721385876403316684327007526933489807912,20324949157726145049840767992468603161209112380087210061⟩
def resval4Tail48 : Box := ⟨-29905920560572202992597490327483241548866616916934352520,21193938243971981434752040017785490451573876825154591665⟩
def resval4Tail52 : Box := ⟨-36237458520833868026435591011802460580360901121304878208,21781888679537019131250633701174926930879860441710385927⟩
def resval4Tail56 : Box := ⟨-43909479308268059580263505485814089016551538426321588947,21966331864381019281871684691271734909567361571239279463⟩
def resval4Tail60 : Box := ⟨-53205783513049982251280793612423948725202303834024821093,21590344107389341693253727858750419495223290871025758609⟩
def resval4Tail64 : Box := ⟨-64470256597896453930394827569349820889774752661687524579,20454097359474922472775855334556706352824055855898629060⟩
def resval4Tail68 : Box := ⟨-78119132377323472689006574516929270390836782319478912360,18304462120170447321633349745081357208434475538780700335⟩
def resval4Tail72 : Box := ⟨939627410618983264551509073348604474213913922292061152858,711146026103575648144362566562772364893853470553231374⟩
def resval4Tail76 : Box := ⟨-49794293314588235691197034902800228336896261725351366,127317674478839765743613454847670643687320668484479644⟩
def resval4Tail80 : Box := ⟨-60295629292903682065932939233616517614468659305961155,140760822156192181711615981619531559183346430153039597⟩
def resval4Tail84 : Box := ⟨-73061128190875217656040831140410410059509910745542671,155220597507663505654210666854064518883264648356439967⟩
def resval4Tail88 : Box := ⟨-88529279575198646895091941624131457742404199185135347,170664327072458484127812854317992406576205287123644681⟩
def resval4Tail92 : Box := ⟨-107272273728799876723853858698770426798436017182746966,187019025856342388891379086897643604717404711510815890⟩
def resval4Tail96 : Box := ⟨-129983444642994266708143959265079438122896282667124096,204158165297429502221704864593745823637017559032691937⟩
def resval4Tail100 : Box := ⟨-157502915655290110739274603044917988535408206369281009,221885179239021759601135856027102882346317384616230007⟩
def resval4Tail104 : Box := ⟨-190848676983838231946184297915867443852130934002012322,239912779433393172285548520955385541272905358984939350⟩
def resval4Tail108 : Box := ⟨-231254242849681902762589978579520891790763180474295842,257837098791877776887176437309180169942870126697497135⟩
def resval4Tail112 : Box := ⟨-280214281184188725982505258105760420062973898051770295,275105459951248456980687919491448029550972246529199779⟩
def resval4Tail116 : Box := ⟨-339539903839129023720139958633141472225716048594959029,290976297612524138017425135907412377775668619274350424⟩
def resval4Tail120 : Box := ⟨-411425662574653059101113885951247319382376964913653023,304469435049947427444181915502243039596408042791460861⟩
def resval4Tail124 : Box := ⟨-498530729116279074802531946413089844883693474234151914,314304515438867028876689239045101915911778931830947461⟩
def resval4Tail128 : Box := ⟨-604077262263903538497262418583328109405044570526505628,318824901730913262622833357279350675414207216027610220⟩
def resval4Tail132 : Box := ⟨-731969600813073759646407133491016071549413097903803734,315903765913941777848012138655735896681198822754478081⟩
def resval4Tail136 : Box := ⟨-886938691510926565911374177330186307060669964550293345,302828366803072389105919843246753100392218255982796368⟩
def resval4Tail140 : Box := ⟨-1074717823927019836773123572737047655244191637786047765,276157608778141342527345185319997504495297275637046048⟩
def resval4Tail144 : Box := ⟨-1553590668693450701500951018526258716736864808782796778,224870137466677306556008137579047827795618624783786332⟩
def resval4Tail148 : Box := ⟨27402475224227422322909978871535955585711069129,58204052733205011449936445426039610505150039427⟩
def resval4Tail152 : Box := ⟨33092662889250917254281403582681735121258286598,64001015745165833204395940492054314155974872212⟩
def resval4Tail156 : Box := ⟨40098880547528950492181828762185787381510712852,70142358514704627715886111546433776628188650159⟩
def resval4Tail160 : Box := ⟨48588423071907641987328846890274529064702560930,76580704094993628233499708502711706092948903562⟩
def resval4Tail164 : Box := ⟨58875330792601196577418309793815834354245805060,83243086317740121497347791238327390140321183904⟩
def resval4Tail168 : Box := ⟨71340133241377057036878789668878324816196935930,90022695909116813657135100633138695685476468978⟩
def resval4Tail172 : Box := ⟨86443923836722017877699692383529430276412627886,96769224472096363930693043509213208450521289681⟩
def resval4Tail176 : Box := ⟨104745416482554871585320274980806649114653903602,103276826867696550432680683199474050362320083240⟩
def resval4Tail180 : Box := ⟨126921613308847278574246154714149064902324082110,109269152080605949985492907175582264923020109843⟩
def resval4Tail184 : Box := ⟨153792848087090231907891722232742383692129213160,114380770064539572492900174223994491288366111960⟩
def resval4Tail188 : Box := ⟨186353131717481056745851371099443529448152597226,118134172661047827578001525597040945785260284603⟩
def resval4Tail192 : Box := ⟨225806922317007010624433575597662863517956366090,119911344702389736620094153600100599837442286512⟩
def resval4Tail196 : Box := ⟨273613680094090860329101690006298208167387361794,118918679817736768595620419260983269081464098656⟩
def resval4Tail200 : Box := ⟨331541855167444341083222791398973027569464224915,114143745730536939248294857745766768844935707434⟩
def resval4Tail204 : Box := ⟨401734305426801746975260045591480833631875022527,104302075605358737707688935854122931652162737839⟩
def resval4Tail208 : Box := ⟨486787564349280749392347284926541839601655599860,87771762701542945827601163162066851787325551976⟩
def resval4Tail212 : Box := ⟨589847891430530079905688020335729594921561336965,62513149938468028635443774004252994572476151322⟩
def resval4Tail216 : Box := ⟨714746945037671781569177591315411435050775260010,25969576893321719609526926165740574926908970401⟩
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
def polyval4Tail5 : Box := ⟨1107696928494662122330746054268907919789691729889547526820,2239585836494254026677723744027688145339065519895326615910⟩
def polyval4Tail9 : Box := ⟨1342210477605718381268553876377642827652588826497219479104,2458328984358586510143461460544015784720694633405736076478⟩
def polyval4Tail13 : Box := ⟨1626376837375641382517386497351400416784241784806766079848,2688797876166306550502696209387424204713645068251733098118⟩
def polyval4Tail17 : Box := ⟨1970705535188855729645017914975987390937913141599037408130,2928791758783624105051403211586671948239241144999417884037⟩
def polyval4Tail21 : Box := ⟨2387933852213023507527147363301365979628528375464777775491,3175009789051751485292226421494961380673098199370090516343⟩
def polyval4Tail25 : Box := ⟨2893495745927601888129581244475773863129898445970434243849,3422732246270575190219748149259439943504138895360951488366⟩
def polyval4Tail29 : Box := ⟨3506092777210752112071811456101986566041817199821756709590,3665422632993450854380323423674023195622413882992160455883⟩
def polyval4Tail33 : Box := ⟨4248385911647018458919657796069696503444043938532304330429,3894232331760854594018372193793270451363398416993751120941⟩
def polyval4Tail37 : Box := ⟨5147833785687625940613994429419406758376536172265263631831,4097385399582285511700305031258229803206316371552697434727⟩
def polyval4Tail41 : Box := ⟨6237708446498772370193551995017856594091065971550633897414,4259416093618434137316139861307694982580613176093826441038⟩
def polyval4Tail45 : Box := ⟨7558326139375307559124408889370008321550754828703420484291,4360225644263548439631974355825824789129282362266035967965⟩
def polyval4Tail49 : Box := ⟨9158538671558169705089537101938164080262911072258187641721,4373917390708846494713918873021386035072379650497273600799⟩
def polyval4Tail53 : Box := ⟨11097540520441081892428590409233521667646069942803546766301,4267360383758929565196633145823719055073258902672475858120⟩
def polyval4Tail57 : Box := ⟨13447058534053110175134415048822991517299463466392799990208,3998420594761969710632774951451762051459482882789892401099⟩
def polyval4Tail61 : Box := ⟨16294005224417427174761396968580692626273404796759481723753,3513785527472828522373563850697430526474882729541228755886⟩
def polyval4Tail65 : Box := ⟨19743693803490149537375703984626593840796281767963043431578,2746291801053986948521756362497405701695657435175330035026⟩
def polyval4Tail69 : Box := ⟨23923734265371882052549361530923217794700414488331304893394,1611645523987385985161891328178372939260033399306220699324⟩
def polyval4Tail73 : Box := ⟨29156250000000000000000000000000000000000000000000000000000,2⟩
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
def resval5 : Box := ⟨115371822668876415626932973385514975024765235294233030385,12540643124933220742684090817532097906577914458164973122⟩
def polyval5 : Box := ⟨9120493293795328274263304045505778444359009568209678674078,4075310895888149217786582520407693674466311486069407457981⟩
theorem cell5_lo : Holds Q cell5 (31/32:ℝ) := by norm_num [Holds,Q,cell5]
theorem cell5_hi : Holds Q cell5 (63/64:ℝ) := by norm_num [Holds,Q,cell5]
def resval5Tail4 : Box := ⟨-13960635169017899751771665621080709675645415426623309319,12774736959651567278167847581988990292684881785996381380⟩
def resval5Tail8 : Box := ⟨-15349956306072181350926229526504396892689656287474680582,13123818114713868939340617545701192031568848960927430970⟩
def resval5Tail12 : Box := ⟨-16877455454033098717981809848039073771056973090708993659,13447679226236449051379009256774865024931601107021034540⟩
def resval5Tail16 : Box := ⟨-18556958518990088142257051695712709718285178009971392335,13739911558966112864531063097166314103333666522340674198⟩
def resval5Tail20 : Box := ⟨-20403591667786540456891152495075906966883994380587624718,13993215727458619582948183258697136502824088204094257883⟩
def resval5Tail24 : Box := ⟨-22433986287124810254438522024567096431437056251003375585,14199296013290040688164171752375560295705727474533678713⟩
def resval5Tail28 : Box := ⟨-24666428780061062654410788378794247380453066246800851819,14348743665489767069891360030218335179229135240408247290⟩
def resval5Tail32 : Box := ⟨-27121025259385712893716238328473509523019064889504661349,14430907446868972132721691660207139765326233129324925641⟩
def resval5Tail36 : Box := ⟨-29819882629901197805881316265604638711616608006979369883,14433750082723393958354303684445949187121613091238292507⟩
def resval5Tail40 : Box := ⟨-32787307690491933769392650016004168001717465008411772901,14343689130002238909333034246152251009731237752958104342⟩
def resval5Tail44 : Box := ⟨-36050026049165349295145876823772406993502273182242752054,14145420632429556052362381500720219717832559485726950644⟩
def resval5Tail48 : Box := ⟨-39637422822684995387243547645207265339099434426403829881,13821723758938672132873573384115096410581507891897902153⟩
def resval5Tail52 : Box := ⟨-43581807288615951248809737676573023052222617737740729932,13353244437568217536862716654091572526796154779852409448⟩
def resval5Tail56 : Box := ⟨-47918703873326011239283537175334043176419140445296828227,12718255792946491775696780662582324633320067564701700029⟩
def resval5Tail60 : Box := ⟨-52687172096660344588296594076301017588359207767776419118,11892392970762438004800010831944734585907281610387918817⟩
def resval5Tail64 : Box := ⟨-57930158329178482365896091095957686656455884102274320497,10848359684510095955634462038329781214669087759683481232⟩
def resval5Tail68 : Box := ⟨-63694435482400393590711790788035078283205575826022627030,9555597479198610832069742045789091077665565509827231707⟩
def resval5Tail72 : Box := ⟨939705510037452373298074112671842542699655234032290398384,700315982050316052480973407477518320868117539598982927⟩
def resval5Tail76 : Box := ⟨-196407951279357484698768856863805316198472269727781174,183002759598485235135949259535593169625440280500216434⟩
def resval5Tail80 : Box := ⟨-215915789371464492682117807460860852673467644033341873,188128117477735697752962229922101461747542656696998329⟩
def resval5Tail84 : Box := ⟨-237401918923904856925175298875596863920437238899879906,192912855941423827783489588204545798518764772180137503⟩
def resval5Tail88 : Box := ⟨-261026170311911986084154696598789624487702071568689318,197267602261226648586713499084722500384740528855959402⟩
def resval5Tail92 : Box := ⟨-287001309411782123341572313315139997440535089621786857,201090650818067111398191748018291033987509345923313668⟩
def resval5Tail96 : Box := ⟨-315561276885191954374511566605210340110253014385464865,204266344388014376364835083146570892569224665714349364⟩
def resval5Tail100 : Box := ⟨-346963293211110447717335221485840517464172861934163710,206663436701239211855456314113172942060522789222071511⟩
def resval5Tail104 : Box := ⟨-381490175297069618296321293134121353903096690693245549,208133275882245261288450689784244840672442535896152679⟩
def resval5Tail108 : Box := ⟨-419452883621432600364347022088397164076915884384244068,208507789873589730142041876394294995011431011013682198⟩
def resval5Tail112 : Box := ⟨-461193322845938448189350075690206672167904984343406360,207597253016686017377678373967071529139907196175683952⟩
def resval5Tail116 : Box := ⟨-507087421121760072064702577891415325842620387061360020,205187810817913808041200753236625905685264183396788388⟩
def resval5Tail120 : Box := ⟨-557548515822320420994364360880736842477819786209839594,201038737564646490162168182489224931202309726215235915⟩
def resval5Tail124 : Box := ⟨-613031076195892423261653708884300976668585015742019503,194879398851933540298032929343567052168319243389089174⟩
def resval5Tail128 : Box := ⟨-674034796465419139207115121169614265937028407898488232,186405888212210166747446381254375711652772074809002261⟩
def resval5Tail132 : Box := ⟨-741109096239438008072890995875490942461786066025978587,175277303880874304006830190739608192863843661359666876⟩
def resval5Tail136 : Box := ⟨-814858068846001184132268956546395303042827435871260178,161111628247347591376562282669789824997818946047468038⟩
def resval5Tail140 : Box := ⟨-895946635200772848277600161525297774393077391545071817,143481146123041419363806382086921958450895698489948540⟩
def resval5Tail144 : Box := ⟨-1230562957249794367053489267581312006926655641259040698,117326911536577044767759755949405519395049756518472612⟩
def resval5Tail148 : Box := ⟨149756433147042315362914809969825636486077878339,112537441975186935080735240288467216041438078179⟩
def resval5Tail152 : Box := ⟨164558009005345723617421600424673632142729240504,114691812295570811936541078969788045726871511261⟩
def resval5Tail156 : Box := ⟨180933442451000259006377653539503325755446620950,116473155630924109010552779944368607052227784999⟩
def resval5Tail160 : Box := ⟨198938423827779422681781377233005220773042492646,117805503605024173718830137636097564651749077442⟩
def resval5Tail164 : Box := ⟨218735110210072371067888199282565421036756745979,118603456630057126682872768460942480979178973548⟩
def resval5Tail168 : Box := ⟨240501797078839421957110377589317102819750673082,118770469322841501686378740147776427565735764914⟩
def resval5Tail172 : Box := ⟨264434522389207974471527885992121234450999590005,118197569204908434268024831114706938483959106345⟩
def resval5Tail176 : Box := ⟨290748832152327176617351199266117576005475281389,116761936725109599771273140339904964263840198205⟩
def resval5Tail180 : Box := ⟨319681721713776259547983366606912156988447085525,114325332057437566462033335955337548818022861918⟩
def resval5Tail184 : Box := ⟨351493770211748379499350308871197470493621991422,110732352651329167709278080833429314610303072632⟩
def resval5Tail188 : Box := ⟨386471487438642760942759838642030123086604427444,105808503866889604323348934948023633354422701454⟩
def resval5Tail192 : Box := ⟨424929894242674039012560620053468603340061563839,99358063215675441260803645515845503847035085121⟩
def resval5Tail196 : Box := ⟨467215359709446063462895261318041039780389016924,91161716732090244215688959920318228202897974559⟩
def resval5Tail200 : Box := ⟨513708720676082410176783820133054143203572956378,80973943802561702659997953468075943720452096620⟩
def resval5Tail204 : Box := ⟨564828711673286179408769532080545401122531403074,68520124359110785203125013336394701876443651496⟩
def resval5Tail208 : Box := ⟨621035736186656332717992671013378834112186006358,53493339678269130656321048259089669319185582231⟩
def resval5Tail212 : Box := ⟨682836013606620061485315217874710185621965022032,35550835075076233790216829308283471198783099932⟩
def resval5Tail216 : Box := ⟨750804984751392553273444069425029729714280784122,14309532173845220378619872414943966276811287667⟩
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
def polyval5Tail5 : Box := ⟨5779518708504597976900128144007649253503959085356935244085,4157421682668843401937113576679539711693122118943142168132⟩
def polyval5Tail9 : Box := ⟨6354645551746185135205175271322800144436916934285092921799,4228390708758898994649988745872270274561871754558680319100⟩
def polyval5Tail13 : Box := ⟨6987006674287211823114194925314471718600656226232628833419,4284136907826290753964337906712087371759927000510505871521⟩
def polyval5Tail17 : Box := ⟨7682295081727099264424835517044641226553488014832843218710,4321696450031833533500101534047085327032721169713105409041⟩
def polyval5Tail21 : Box := ⟨8446772770365321100237403905462613447140289836067884569114,4337716367295240843933888545284857631757897535334938826674⟩
def polyval5Tail25 : Box := ⟨9287324878198367247723821954882243595809182421016873367804,4328409694634320033790478546340970510685213590321512152026⟩
def polyval5Tail29 : Box := ⟨10211521694512427706448149404728123377480928064531072597717,4289505758490326910747171700603960036738405325049331481599⟩
def polyval5Tail33 : Box := ⟨11227686840403297194151827905504491715707898717786948303906,4216195093980788617223057489287827648114002317855067450361⟩
def polyval5Tail37 : Box := ⟨12344972234051003622255509974961899557399317934751078471307,4103068429012888595842352375973457368721696189443340118580⟩
def polyval5Tail41 : Box := ⟨13573440515910942247313725741485723051824139351599274699351,3944049115467320007239621090644203681121837260816075259517⟩
def polyval5Tail45 : Box := ⟨14924155676169949337806254015153228776886968282056252290658,3732318324076320779249700937497208426836980727468425933156⟩
def polyval5Tail49 : Box := ⟨16409282700688050929758535594608894665086495187948598425837,3460232249581661980088684287529119936013641341783830397575⟩
def polyval5Tail53 : Box := ⟨18042197132870076276084423927984834074272696278195341265703,3119230495618576224935990919807205375532633624269618009283⟩
def polyval5Tail57 : Box := ⟨19837605538217457924024551402904294145149404505506612149263,2699734723814669213665054428575608721973945427260872252934⟩
def polyval5Tail61 : Box := ⟨21811677956503714334215341561224108407328801477947179510310,2191036558031696728084423799879408979279006114845145944501⟩
def polyval5Tail65 : Box := ⟨23982193534525868704544986501455969674017764758955438166691,1581173631645046780019638286164735503921237880800090228543⟩
def polyval5Tail69 : Box := ⟨26368701017006434820079696225324934808657429974424162155451,856792541591783503110024434833123954527946968136664295036⟩
def polyval5Tail73 : Box := ⟨29156250000000000000000000000000000000000000000000000000000,2⟩
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
def resval6 : Box := ⟨103128868130950390351762050729975454225270822269803390863,10845572436058319423686577053296199528953723829118746722⟩
def polyval6 : Box := ⟨16271906216344054389601679779174089681493831862888944594738,4078723999385549309379936786202293814835550909305680795091⟩
theorem cell6_lo : Holds Q cell6 (63/64:ℝ) := by norm_num [Holds,Q,cell6]
theorem cell6_hi : Holds Q cell6 (127/128:ℝ) := by norm_num [Holds,Q,cell6]
def resval6Tail4 : Box := ⟨-26135910445483465965500582909707812912647745110463089622,10645860882568157612211691494787409835901687918248036277⟩
def resval6Tail8 : Box := ⟨-27397854282547988838408153256182221727673612581397719573,10556223221239744681267606817936978654561231643300519151⟩
def resval6Tail12 : Box := ⟨-28720654209410195321915285799103966704404772946257506258,10443020525330220681058071666124739765589299980082256434⟩
def resval6Tail16 : Box := ⟨-30107320429040594019738176918563178474361841189567173468,10304501416091801718577143150888741853330113717482840459⟩
def resval6Tail20 : Box := ⟨-31560936488684416399780809611991848838983706987395317348,10138810940626976210254555786278850122623639951155294225⟩
def resval6Tail24 : Box := ⟨-33084734803631675242182098064337113224607213936627795839,9943984424422811435525072603608535508284140896525599939⟩
def resval6Tail28 : Box := ⟨-34682103853891829033838129410268133101458462057532036182,9717941531162918754820043870706788457467476080751211335⟩
def resval6Tail32 : Box := ⟨-36356595719186575156370072299064034869406753605684667636,9458480015384742835936230771877026394577613354053785489⟩
def resval6Tail36 : Box := ⟨-38111933977732163176649139580491446322224591514477139982,9163269152376470157913905206626580594848538124741510103⟩
def resval6Tail40 : Box := ⟨-39952021986383969204224367518967249563516554478576942622,8829842829056677595846080446900718085099831710447834765⟩
def resval6Tail44 : Box := ⟨-41880951560555973666140071060543275901487306674335004579,8455592278773647058753910027499173472093039617467381118⟩
def resval6Tail48 : Box := ⟨-43903012073216735051864556420457094144925252400309829648,8037758442115300817814772552208907895254724235669884714⟩
def resval6Tail52 : Box := ⟨-46022699993195354353462755173819718371983370078530966258,7573423934933189564373721407070274116317289018031481257⟩
def resval6Tail56 : Box := ⟨-48244728884007771518412282764989179998027154749703439208,7059504603852861126384133757546613726743495431190608677⟩
def resval6Tail60 : Box := ⟨-50574039885421863883872506460315968365895872807377356087,6492740648565529845026651777713999605994353283524072848⟩
def resval6Tail64 : Box := ⟨-53015812675699532534438877251035965974850807512968341973,5869687288496362324205978580027040836549777276608919249⟩
def resval6Tail68 : Box := ⟨-55575034872138199539703747468607238536862947077136762897,5186697265022621507114402932415276463806111568391235734⟩
def resval6Tail72 : Box := ⟨939638259996350881009813796392576256219921973699644968314,641073476537307355566632004879096303850037775883543677⟩
def resval6Tail76 : Box := ⟨-370769656904986027860697720044798805406127104336738695,153443629922493815412502179455171165607810837215894042⟩
def resval6Tail80 : Box := ⟨-388635555577247334320690235910010060623143235511552371,152249528951150720423974906001591585927722966823750130⟩
def resval6Tail84 : Box := ⟨-407399325198345893181423820730514068673272718683847299,150723775977479557242860452214864336781553563777338829⟩
def resval6Tail88 : Box := ⟨-427069033206938428086362331609361924036713109972940418,148841462554362965302710875891967003505533763280064273⟩
def resval6Tail92 : Box := ⟨-447688417343404054091178604823011102369562017420273223,146576357631799460302264563399597438414762063898520145⟩
def resval6Tail96 : Box := ⟨-469303329062321782350974635309680703024001845603909427,143900676378659547478677442450827562941460580929447814⟩
def resval6Tail100 : Box := ⟨-491961833580421199096512805593792160285765538051156636,140784995986505394164906678927291513489422827460844984⟩
def resval6Tail104 : Box := ⟨-515714316758383379059613972231777261712214818272082690,137198167136882495585430998017796219026951883819370803⟩
def resval6Tail108 : Box := ⟨-540613597144196744023306490826130585712517566305780325,133107220893021063966375117838814983504681864180691914⟩
def resval6Tail112 : Box := ⟨-566715043426098298101895449024767815462288227276504615,128477270785416008122200349466463341331613392353056080⟩
def resval6Tail116 : Box := ⟨-594076697556277990486499335167214365434008185408376983,123271409849336885305802607998099208981214815463419608⟩
def resval6Tail120 : Box := ⟨-622759403819137142180016558736649181933141623657857828,117450602360322100280366404322022270769276719441925726⟩
def resval6Tail124 : Box := ⟨-652826944131110848302699741290831457752847407977686442,110973570001125152629139434798188723747455959014113248⟩
def resval6Tail128 : Box := ⟨-684346179872921772020159257968693796547385467641673535,103796672180376168932886034506034906807765964850848495⟩
def resval6Tail132 : Box := ⟨-717387200569735888283404095413045765744297850746021431,95873780209365503229324432446264734544135745971875113⟩
def resval6Tail136 : Box := ⟨-752023479828727068288007375427840627191159847529616188,87156145025942237991771298197718208453695698389370951⟩
def resval6Tail140 : Box := ⟨-788332744088071095766111576267091891303548237986232600,77592238373521872590025121741901289536786239831441438⟩
def resval6Tail144 : Box := ⟨-1069015789828280267421647246420927291416930242359526954,63536856004326630255467545594059685645007501884571693⟩
def resval6Tail148 : Box := ⟨345146959677791954893158287576239840620217981083,111028863822379544692801771661752887607221194803⟩
def resval6Tail152 : Box := ⟨361714868290009624446225922015473302004281085972,108904018761908094054081047651081502548700912262⟩
def resval6Tail156 : Box := ⟨379178876370498750433388986614813020450326231373,106438642389597934569715890938988473468544352986⟩
def resval6Tail160 : Box := ⟨397486068651217117321220601045779597492123081521,103608090308596949508789253112254517649408992708⟩
def resval6Tail164 : Box := ⟨416677153232717358946128580873315773569037896387,100386886765376946767702593265648931980968042766⟩
def resval6Tail168 : Box := ⟨436794805451328742732160161146928592565544634910,96748076018563547134520984741478623236723956514⟩
def resval6Tail172 : Box := ⟨457883761058304603636634822095992159650807711417,92663142896270755300001281383176390902415783062⟩
def resval6Tail176 : Box := ⟨479990915698424771699348065219975285089224357450,88101929283281538983805848539250809102646004945⟩
def resval6Tail180 : Box := ⟨503165429192138253254373412815847339522446933252,83032546314117303883971501532691764351402274621⟩
def resval6Tail184 : Box := ⟨527458834852568778258571661049565035027598195813,77421282056310929676356484378835792878702669018⟩
def resval6Tail188 : Box := ⟨552925154080471118400101315127526902550287920486,71232504457528266521892578548746697122928205435⟩
def resval6Tail192 : Box := ⟨579621016491963703072116081042961657102944948216,64428559318979710596699934015664516678775693963⟩
def resval6Tail196 : Box := ⟨607605785846166336577330448882506010924314840828,56969663045810511999789320831186872336943599716⟩
def resval6Tail200 : Box := ⟨636941692052769108056956171702419332117645216362,48813789912829025066272286529470431794547102541⟩
def resval6Tail204 : Box := ⟨667693969553078849717714706116602905551058705828,39916553570998052877531922977885556639893743558⟩
def resval6Tail208 : Box := ⟨699931002382399297074088303353529576763048977272,30231082506540121277102599512685739632339509872⟩
def resval6Tail212 : Box := ⟨733724476636141495740712917972767658750572408012,19707889136035548628463886723386955003381543487⟩
def resval6Tail216 : Box := ⟨769168173095682654834762328079141899630663552338,8294231099257132308171812878278135305624001974⟩
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
def polyval6Tail5 : Box := ⟨13007532395826273822337969866956345761353243609856631516284,4003362441295219522928439675382926071341005238152316866728⟩
def polyval6Tail9 : Box := ⟨13635548667010650337970863703654898407079345298065675220953,3917481408001041351089590672835529829650247365580593289569⟩
def polyval6Tail13 : Box := ⟨14293888639971452534376428343246532873667037135429634870558,3818556860319556991139308407272507545978799685938997593933⟩
def polyval6Tail17 : Box := ⟨14984014024287445394887211601538871779188691476943438089577,3705675482503945771355794727761537508011601010482516416254⟩
def polyval6Tail21 : Box := ⟨15707459455938102555937155184540292231043088245925490137439,3577870835582152108857209066729887527378786246862549004953⟩
def polyval6Tail25 : Box := ⟨16465833665133140426765611597491221149266287137636928590756,3434120495040593430091896802911914277856924886847911659636⟩
def polyval6Tail29 : Box := ⟨17260823053427353022262935060794004042005928582399185546039,3273343050595267559053887271537434441648126689808548591779⟩
def polyval6Tail33 : Box := ⟨18094195443782293406736833267003618294033124454873485791351,3094394951639519607100255012540512455067801241097191374690⟩
def polyval6Tail37 : Box := ⟨18967804011685441931194183951814520827271399970350297071880,2896067190613415682847403282041558329335395014076253386119⟩
def polyval6Tail41 : Box := ⟨19883591406068330157694098182696709986966683317761273322045,2677081816157923935714000266538821644437863026076871278555⟩
def polyval6Tail45 : Box := ⟨20843594069187331679299297251004857264185816890209614066940,2436088267514325967911452587005080063895756359795828359283⟩
def polyval6Tail49 : Box := ⟨21849946765073266232177879046661051288654176155047553615108,2171659521206738307739254124383565503389587368558885187218⟩
def polyval6Tail53 : Box := ⟨22904887326619759302945800263251290978547084512718747642630,1882288040602352964550352427014263308149760753236082898353⟩
def polyval6Tail57 : Box := ⟨24010761631866488008549476332106492466801927526175268292831,1566381518478996943842018136432776547025931519305810719252⟩
def polyval6Tail61 : Box := ⟨25170028820543148987487178206381056648243815382905069706392,1222258402241800748939470707427160214456162689712249850105⟩
def polyval6Tail65 : Box := ⟨26385266762518065338044437665696408212794358981600632204502,848143190917520145721038316686906762047274684279340694141⟩
def polyval6Tail69 : Box := ⟨27659178152256299969403886265166498144916447368330108821907,442161483245315632186342200195976997626899721769138723782⟩
def polyval6Tail73 : Box := ⟨29156250000000000000000000000000000000000000000000000000000,2⟩
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
def resval7 : Box := ⟨89855264200600436064252365825293624756359147032727583191,17093192162181187942279612098870455599110955137687128300⟩
def polyval7 : Box := ⟨25738236280983560663298486477700027751838038584411107618203,7124655526245374885649248045538072992666901633254976277402⟩
theorem cell7_lo : Holds Q cell7 (127/128:ℝ) := by norm_num [Holds,Q,cell7]
theorem cell7_hi : Holds Q cell7 (1/1:ℝ) := by norm_num [Holds,Q,cell7]
def resval7Tail4 : Box := ⟨-38803240679608039604253496744064343011881301757637382146,16358414948388167306444647823784216920672618008686478468⟩
def resval7Tail8 : Box := ⟨-39415578539896502832079199329024289497103253152161806668,15746145248539935782441567152222654729146802879180638206⟩
def resval7Tail12 : Box := ⟨-40037508613715435815389736527728874995887065012195129777,15124215183358952434674822255245148089826180610524783887⟩
def resval7Tail16 : Box := ⟨-40669251981547805416928266161148096571686934419941271136,14492471815534772905504941137303791682501897174469263452⟩
def resval7Tail20 : Box := ⟨-41310963494159282249587805997110839490195966053505331056,13850760302923329806262042572566319654560252956713651342⟩
def resval7Tail24 : Box := ⟨-41962800436803342598357207649606328590479528430825454270,13198923360279269917395447570984756298121130894516548378⟩
def resval7Tail28 : Box := ⟨-42624922576495775087348927080342235397098583397435570253,12536801220586837445598552431682195230097170992934028692⟩
def resval7Tail32 : Box := ⟨-43297492201182235333899896304510522299156067016215657577,11864231595900377200481748028565952237576614303391059961⟩
def resval7Tail36 : Box := ⟨-43980674159515497806188657837501297138011903653056043281,11181049637567114728308331325822923002088253253646168086⟩
def resval7Tail40 : Box := ⟨-44674635901260311474971660389532909148777427967949833727,10487087895822301059176769573236776535984921168575808783⟩
def resval7Tail44 : Box := ⟨-45379547518335794714125951143988521827767546294399480582,9782176278746817817832085138492518891420296345920583265⟩
def resval7Tail48 : Box := ⟨-46095581786505429428942308744666921731563777184037031290,9066142010577183078189912842059242058522355269995248306⟩
def resval7Tail52 : Box := ⟨-46822914207724872224772221137280519407786163498129170260,8338809589357739591127392608052557688531634185966929623⟩
def resval7Tail56 : Box := ⟨-47561723053157912134792000064701541448621406034263659175,7600000743924643221120414000351972802626206836618200393⟩
def resval7Tail60 : Box := ⟨-48312189406855238468394806680984752097093301103773209837,6849534390210511385310860539289907647156143685274082265⟩
def resval7Tail64 : Box := ⟨-49074497184912973856623521264755206466198911730794206310,6087226586189327436128401786472683233739010768723871738⟩
def resval7Tail68 : Box := ⟨-49848394322724746698614359243861504728934910403474126695,5312882853949530126633719117034388875579412950976339620⟩
def resval7Tail72 : Box := ⟨939520199164464022817668374107451208157058819563011265427,729441781454162353321315378477053539701876803604429096⟩
def resval7Tail76 : Box := ⟨-552202609078884737563201273758652802338878856574381184,235518476790641765600534125547286694742159735631767986⟩
def resval7Tail80 : Box := ⟨-560881520043959078093017110076238623770232818392070778,226805768365699084889823734586630301107528693438372506⟩
def resval7Tail84 : Box := ⟨-569731548799668738356426533759541973387330137171453648,217955737675350892978233284059441612980685769854076253⟩
def resval7Tail88 : Box := ⟨-578721222228664285993227508629515037550690314319493490,208966064245198068803891912827995337708657203878908510⟩
def resval7Tail92 : Box := ⟨-587852741811691267415115704056388895494762966654929742,199834544662167724148939706365920062636963670649721754⟩
def resval7Tail96 : Box := ⟨-597128345708018582758481255199259880297155662490639028,190558940765840374099696254971639050327847970117994445⟩
def resval7Tail100 : Box := ⟨-606550307393503140235376318799010026266063277482975918,181136979080355815573643614869388630509281792312633623⟩
def resval7Tail104 : Box := ⟨-616120936216699072769132602344808912896039533745271849,171566350257159882960287854486689630249317234576304010⟩
def resval7Tail108 : Box := ⟨-625842577964882222793007944381880474669719080396201193,161844708508976732924442621427766113522185062668818692⟩
def resval7Tail112 : Box := ⟨-635717615439008983389756220694451019353783665335880010,151969671034849972328054175450904558191687929941861322⟩
def resval7Tail116 : Box := ⟨-645748469037747322847316779607240498460054069416682584,141938817436111632891851260325515370024718647024730637⟩
def resval7Tail120 : Box := ⟨-655937597350723111939054614103702944945156290955377059,131749689123135844032275368420681997491993851774501062⟩
def resval7Tail124 : Box := ⟨-666287497761127164209797288024168196751660274164099481,121399788712731797151553586828358757630309035001295377⟩
def resval7Tail128 : Box := ⟨-676800707057831027884500597019016233027759674054680176,110886579416028279640736442326742930559462282887839694⟩
def resval7Tail132 : Box := ⟨-687479802057238339382618670700237111633622981441679146,100207484416696096322974968754628326389448486046443252⟩
def resval7Tail136 : Box := ⟨-698327400313371077459394565087989816214093749391269506,89359886236499153876881601182983501004088713273749619⟩
def resval7Tail140 : Box := ⟨-709346860993496862872683957394548825462115489006530177,78341106503870736647003751560652636013048540200874284⟩
def resval7Tail144 : Box := ⟨-961305258599400701305768007079270660388878567299024525,63593428329630039114721129901070018469208906542332359⟩
def resval7Tail148 : Box := ⟨598988915049436288730544317114696715853675690977,190994949569359924593005833712922637314887465914⟩
def resval7Tail152 : Box := ⟨608347061436934940499834082361165675109085696887,181544504293347302601828717347376761034019580049⟩
def resval7Tail156 : Box := ⟨617946039115224755356855725548120840953872724941,171945524877276690989207426444842245952147536415⟩
def resval7Tail160 : Box := ⟨627696478774872507975081749095179450709716535527,162195085217043476178932630765044367801486034223⟩
def resval7Tail164 : Box := ⟨637600768557192853598950801379400347180756532329,152290795434722048836019556097323985978886782287⟩
def resval7Tail168 : Box := ⟨647661336030100718183159835372739838315171756778,142230227961814176710578759210667892471027472316⟩
def resval7Tail172 : Box := ⟨657880647066172681173058286782300282213142449457,132010916925742213560252656655109012458027053934⟩
def resval7Tail176 : Box := ⟨668261206446467447395353025172495657759518468571,121630357545447447329020064138124355947231048977⟩
def resval7Tail180 : Box := ⟨678805558474453500799191734645910098856066562303,111086005517461393924080449947069712909686068586⟩
def resval7Tail184 : Box := ⟨689516287599624830045389625677376142019872996754,100375276392290064677714047196309749359354519254⟩
def resval7Tail188 : Box := ⟨700396019050956561241390947985521411290676389741,89495544940958333482088504412668449137074153803⟩
def resval7Tail192 : Box := ⟨711447419480355753052460233068942182244589769986,78444144511559141674629869067210483120066915046⟩
def resval7Tail196 : Box := ⟨722673197616265065668783940513571458858507324788,67218366375649829115964679148153764035248591331⟩
def resval7Tail200 : Box := ⟨734076104927579505840005926252070896761477057892,55815459064335391250418972213157990818491938836⟩
def resval7Tail204 : Box := ⟨745658936298039258598584576491622482427332634752,44232627693875917930618401546160726765973572917⟩
def resval7Tail208 : Box := ⟨757424530711400330955745566934125671340917988761,32467033280646776053843860875488043748536609827⟩
def resval7Tail212 : Box := ⟨769375772344544060363977646176113420009105642751,20515792031172517832712068056184524526726970854⟩
def resval7Tail216 : Box := ⟨781534085065027606771726107286451874618577407345,8375478092521768341997424900780543319736623007⟩
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
def polyval7Tail5 : Box := ⟨22220321532840575449601690202900552153306356383085832019926,6777830402246168302794059227474076823467114592182888588711⟩
def polyval7Tail9 : Box := ⟨22570928999834620699541306874169281183353103705980427681206,6427220681774234380233106120551635851931087446745821376412⟩
def polyval7Tail13 : Box := ⟨22927070907402237680027449463788985821798785372536046502928,6071078773975101417906799348411787245933659349128187330412⟩
def polyval7Tail17 : Box := ⟨23288832302925477791264305838152272716375357305625992347035,5709317378451668768624115888832407286510061412768808640781⟩
def polyval7Tail21 : Box := ⟨23656301854881955883333546251260899042848985444866118123691,5341847826495189968019392484933839779784658672087161015672⟩
def polyval7Tail25 : Box := ⟨24029569631062760955211223628483386400115148540217297117416,4968580050314384887382503084462481339145993684599173248072⟩
def polyval7Tail29 : Box := ⟨24408727120419770297995891697214509934413149192325238166786,4589422560957375544292784755322305205252387563188812446618⟩
def polyval7Tail33 : Box := ⟨24793867255489654713082222909865379386525654169642581461564,4204282425887491129180688103792000674525295575756063446775⟩
def polyval7Tail37 : Box := ⟨25185084435171896523756034583597537807375883684075635966399,3813065246205249318502801954874076541922827366322703291838⟩
def polyval7Tail41 : Box := ⟨25582474547866217771287929479041047546049545896614904920987,3415675133510928070971451791832994839237652261552242159352⟩
def polyval7Tail45 : Box := ⟨25986134994975088996989032105546959868927940110935555829069,3012014686402056845280791075292850909593763965570162414190⟩
def polyval7Tail49 : Box := ⟨26396164714777079132416289207700049014846554681657845924680,2601984966600066709969784796926355815044311223536501310713⟩
def polyval7Tail53 : Box := ⟨26812664206676897923278591518295435171009114408249079328302,2185485474700247921922952376920456166942060974512444922631⟩
def polyval7Tail57 : Box := ⟨27235735555838074822210674015805780819351776569098945213925,1762414125539071210785802989435052839747200378768468925657⟩
def polyval7Tail61 : Box := ⟨27665482458204354631023115361082313143346331213802917082057,1332667223172833272476666206811753381944170768532047106130⟩
def polyval7Tail65 : Box := ⟨28102010245959498308125586222538317789238521153213783502191,896139435459979374121105892438623104428607222218346795743⟩
def polyval7Tail69 : Box := ⟨28545426272749245713757451529646628775544389034088168995794,452723759053888077916128783636275391739337847686722524505⟩
def polyval7Tail73 : Box := ⟨29156250000000000000000000000000000000000000000000000000000,2⟩
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
def pend : Box := ⟨1032859338592956123507340841320459499132000152144696353413039,3553214272812041606893202778601612504788072969730482636⟩
def zend : Box := ⟨1003859839318500606041582031250000000000000000000000000000000,1776122985890535136718750000000000000000000000000000002⟩
def betaquot : Box := ⟨428776842897707342663574615790426635281618804781895393759349,394824944536067602409993474222440360481366178245075062⟩
def crit : Box := ⟨247334477968382043603081466952729533387186510306493346742,8566042184025322889728485336946036395962945354501471945⟩
def subsonic : Box := ⟨278898880490726875788214777050881201514952286633572120313,3946895564023279241257690475041409572861404215053276382⟩
def pendTail4 : Box := ⟨28996414223348014106416703489945222677637263746371849987581,1697081817550666449731296791281473104517689940028757513⟩
def pendTail8 : Box := ⟨28996452710245532863354397171386498723282042391113699006621,1696969346739750935210200671102595664649034066373186599⟩
def pendTail12 : Box := ⟨28996452712045189942475034384169355499513627691338199359029,1696969331009333201475462692327969299887953004779720343⟩
def pendTail16 : Box := ⟨28996452712046148005462866931424154613571797282295685569758,1696969330995377647327929714852605748404696958747397714⟩
def pendTail20 : Box := ⟨28996452712046150496846505540207353051531005057622508208396,1696969330995322613431101711962522696421230277119813624⟩
def pendTail24 : Box := ⟨28996452712046150519779067006863328672504912617281985656166,1696969330995321848818072055505680938230288715886587854⟩
def pendTail28 : Box := ⟨28996452712046150520392859208478534812547320327657217529916,1696969330995321816675331435346650834895778749059259506⟩
def pendTail32 : Box := ⟨28996452712046150520433540608980507879689503358070400478606,1696969330995321812949387334922578735201534208871214395⟩
def pendTail36 : Box := ⟨28996452712046150520438699122284296323131751994302629710556,1696969330995321811820488388162631469411086078262606608⟩
def pendTail40 : Box := ⟨28996452712046150520438283651258360628705352215867340604554,1696969330995321810948859718829730967870708932257816037⟩
def pendTail44 : Box := ⟨28996452712046150520430493566033366067080933489322942659998,1696969330995321809237749199913643753231683274591285095⟩
def pendTail48 : Box := ⟨28996452712046150520361818241375772790269207861645779608533,1696969330995321800523080709883105139660255276174740101⟩
def pendTail52 : Box := ⟨28996452712046150519082513782599861517823056382340272194576,1696969330995321682149017862246239249807242951589600059⟩
def pendTail56 : Box := ⟨28996452712046150455775945889298403479281257228640274824276,1696969330995317582627025508133154317687586848314960036⟩
def pendTail60 : Box := ⟨28996452712046140444351026961403686975822704019963433391660,1696969330994849720777594397792902365941130776427689031⟩
def pendTail64 : Box := ⟨28996452712039560475444027844633603224552637415940364776062,1696969330769997014892067780530825534675001494534849239⟩
def pendTail68 : Box := ⟨28996452682844047835964189304032341913065534222701393886131,1696968620397368100970338511852677348634718642887708176⟩
def pendTail72 : Box := ⟨28993277564127573073548645034053286351130696282534280990413,1651107766145254595777090265742211379543488973850411824⟩
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
end SepticProfile.ExteriorCertificates.C50

end
end

end OAI
