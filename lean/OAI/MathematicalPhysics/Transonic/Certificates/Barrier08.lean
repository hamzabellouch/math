import OAI.MathematicalPhysics.Transonic.Certificates.BarrierData08

namespace OAI

section
noncomputable section
namespace SepticProfile.ExteriorCertificates.C08
open SepticProfile.ExteriorJet SepticProfile.FixedInterval
def cell0 : Box := ⟨250000000000000000000000000000000000000000000000000000000000,250000000000000000000000000000000000000000000000000000000002⟩
def resval0 : Box := ⟨108253169041590098701102289662505419409676685402860247538,384590531649210274838384928730720392529234247718908432⟩
def polyval0 : Box := ⟨3752659355615911415799539709582779347903979111091302096097,15966455662029474963414571459699670982707312776631263870⟩
theorem cell0_lo : Holds Q cell0 (0/1:ℝ) := by norm_num [Holds,Q,cell0]
theorem cell0_hi : Holds Q cell0 (1/2:ℝ) := by norm_num [Holds,Q,cell0]
def resval0Tail4 : Box := ⟨52578695219573039736277723604554010834827859364949,1721611433226172151423287211503303310597688747595⟩
def resval0Tail8 : Box := ⟨6014426119745690703795262407313921267204785139,349471859141003867443939366215892113741764804⟩
def resval0Tail12 : Box := ⟨5174910482281175586178888379878455314781973,453259505738381426528092365139304074438409⟩
def resval0Tail16 : Box := ⟨19607596795432529395622701890468506099987,25192383265824965453809193601696025507387⟩
def resval0Tail20 : Box := ⟨252801749837762458384297720851175467138,364356370550092836843890976386110355165814⟩
def resval0Tail24 : Box := ⟨9519144243373555655755595323401733912,5829015478216256818497412778858072325484372⟩
def resval0Tail28 : Box := ⟨952661129753442291684956429102171372,93264212448552027069318114235639310817837616⟩
def resval0Tail32 : Box := ⟨237421542288131923129657614399842772,1492227394355021407473151727502415289663366288⟩
def resval0Tail36 : Box := ⟨-386246041152314867562765659958518834,23875638307769111667232184875240808591971147926⟩
def resval0Tail40 : Box := ⟨-136280663344129295917977725173134571705,382010212795698201199886801059908114845958853372⟩
def resval0Tail44 : Box := ⟨-34943050430915660079076274212794158772213,6112163371970198439796958279192693225313847744499⟩
def resval0Tail48 : Box := ⟨-8945618885272938453472889859686399749114656,97794605564993974320767342788671520782107616217144⟩
def resval0Tail52 : Box := ⟨-2290080174667582948909534003087673580983045323,1564711542089524522503398965809997192292495947939027⟩
def resval0Tail56 : Box := ⟨-586260559187188662517511887123514125129214412828,25034835054144477378539399020692795349311123484322871⟩
def resval0Tail60 : Box := ⟨-150082702374825814982854182871439946602118130697068,400416658329353424447993554476074150589777615882489260⟩
def resval0Tail64 : Box := ⟨-38421165066143153189620396589800508486335857749368612,6370646686113256776638167622446511593021894594160025868⟩
def resval0Tail68 : Box := ⟨-9835661283315140091114539523229570693551753988431014567,92709329355749241775601126469571524176106072523376716855⟩
def resval0Tail72 : Box := ⟨743220595808281076089375024775042162671250906563906354123,2566210775987049491059195746876299154307026881530968513⟩
def resval0Tail76 : Box := ⟨-24022914257157736304152692862551176616892599712258,587100547593264474753553960800007767621297068940⟩
def resval0Tail80 : Box := ⟨-1227548236998055218106969747766323298643532597,61104373216350626114145892237197575685648860⟩
def resval0Tail84 : Box := ⟨-656650681499720307941289914984548599440217,51104072428955384849210377759318031129366⟩
def resval0Tail88 : Box := ⟨-1718825614414071273639744810221070549891,343260578855923541093166220899341866928⟩
def resval0Tail92 : Box := ⟨-16201175719711355393498036531842856600,2415402605183375248803430384799462662880⟩
def resval0Tail96 : Box := ⟨-461642372885253292115771039919725788,38606238945944675870468958155794339543407⟩
def resval0Tail100 : Box := ⟨-35723207800683173122759214894874243,617698258559499938114706808329533649408947⟩
def resval0Tail104 : Box := ⟨-7041222487334701992803094385572864,9883171971454284431676758098236580881401111⟩
def resval0Tail108 : Box := ⟨-5161169875586550806401446974721631,158130751497496837293817353329022626179135283⟩
def resval0Tail112 : Box := ⟨-454303306071896979746080841604750074,2530092023539628773461901933332068655772407542⟩
def resval0Tail116 : Box := ⟨-115290494344142083922574799875941986918,40481472268559263531793770349043144648591632017⟩
def resval0Tail120 : Box := ⟨-29511505104458291051945955682361068746987,647703528629965825936152883104120273722402952149⟩
def resval0Tail124 : Box := ⟨-7554925439452683083837864246875735276825388,10363249375337747876807685101362312077806498430428⟩
def resval0Tail128 : Box := ⟨-1934060585701435859969513386849368942171394853,165810176823653804283310210716636939037088294291975⟩
def resval0Tail132 : Box := ⟨-495119505537782571548543642092097944525132042463,2652498654651956337503176473644777166040318682713127⟩
def resval0Tail136 : Box := ⟨-126750609393383525893069478590111492197358743533904,42321149788169348548669607323528530815663309405667907⟩
def resval0Tail140 : Box := ⟨-32448351457820554079267173435376476603621175725614770,646718157985401274345439783326981843654451032158343748⟩
def resval0Tail144 : Box := ⟨-8448532377901358852321995503523412389365374863493486900,2487328798110579987358513918204246466333440972656624803⟩
def resval0Tail148 : Box := ⟨51131652945909540291004763672160422270572990,1046679966086501595363539071189645492749318⟩
def resval0Tail152 : Box := ⟨861610352166083082131230085890444413432,38234122622976372948881198826684402293⟩
def resval0Tail156 : Box := ⟨258829973742117273569555533277973302,18351559819987172652073535780816907⟩
def resval0Tail160 : Box := ⟨428775340220732481762195839747208,45465210560058937033385776785904⟩
def resval0Tail164 : Box := ⟨2708149000147097035796863772028,24933017993972387379661203040496⟩
def resval0Tail168 : Box := ⟨53370888760661983254030529385,392783323411346783513872546682325⟩
def resval0Tail172 : Box := ⟨2904434670614027780162074604,6284368588277941159842321298892201⟩
def resval0Tail176 : Box := ⟨404775633849648633712324568,100549885278498694990291568023152371⟩
def resval0Tail180 : Box := ⟨144040667938628103666452409,1608798162139835659792473826279308697⟩
def resval0Tail184 : Box := ⟨1592232632990850433669999993,25740770592147285984802470173055792825⟩
def resval0Tail188 : Box := ⟨378765822036161937167441440185,411852329119485377628010608878716935990⟩
def resval0Tail192 : Box := ⟨96907630434360689939130899912638,6589637175061612200986226831889977981379⟩
def resval0Tail196 : Box := ⟨24808086558681550716428519775296429,105434171543412311571569738880588856739506⟩
def resval0Tail200 : Box := ⟨6350867103823648421688613001585743176,1686940790756933679187826858837849151254417⟩
def resval0Tail204 : Box := ⟨1625821908848764347793854674094435848160,26989528444098354904118493993832725172614228⟩
def resval0Tail208 : Box := ⟨416210420384139918432937486560924426667290,431442257848779399629507056430737475327858179⟩
def resval0Tail212 : Box := ⟨106549936774459770450105647255284414063829105,6803185594719714739196369257876067587871320802⟩
def resval0Tail216 : Box := ⟨27280736743368192592575001754029528281411898164,83277004557630372855025888193373228149639843011⟩
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
def polyval0Tail5 : Box := ⟨1955133753991871503325712516216045983089246967190737,51845652917431521009092624962484299739858422791208⟩
def polyval0Tail9 : Box := ⟨179259193291343481697509547259510300824664567678,9362066023904446200873740617930646539829351756⟩
def polyval0Tail13 : Box := ⟨133453542786785757642885541146429338955107523,10797598843339207904274135213238483285550143⟩
def polyval0Tail17 : Box := ⟨443091471694888485159207305815723095996054,418680898803533747257551481621797523687958⟩
def polyval0Tail21 : Box := ⟨5019762513954794004565232674022036746982,5879542473697465538554313440834697758463681⟩
def polyval0Tail25 : Box := ⟨165901156366090800004185517123486766212,94059844427016283038124018746854621215619617⟩
def polyval0Tail29 : Box := ⟨14520932832392564606669855111912305908,1504956932276298294775780259557942049226234921⟩
def polyval0Tail33 : Box := ⟨3196455665434768236766319414622562083,24079310847229986056408661205924924777232993487⟩
def polyval0Tail37 : Box := ⟨7274454518422797485764084078840626568,385268973532939124339401663129893590408768178807⟩
def polyval0Tail41 : Box := ⟨1434191824314723812191012975283389577779,6164303575185415559997222538164222685967003117926⟩
def polyval0Tail45 : Box := ⟨366613061548377119139645000249763206759147,98628856859272633610366214186620477815843149671981⟩
def polyval0Tail49 : Box := ⟨93851306879727245393477983726186159846760993,1578061621762794726567792511263515344026881103114047⟩
def polyval0Tail53 : Box := ⟨24025922504416101083513262629929798449901272669,25248963423902946705495596997301311722046180709624588⟩
def polyval0Tail57 : Box := ⟨6150635953732362388499677990281569794353339674582,403977648561273792930670174007851906221704881750959171⟩
def polyval0Tail61 : Box := ⟨1574562801790425514260394721685677719713436988307170,6462166224360750001087884326720445752266286618026563387⟩
def polyval0Tail65 : Box := ⟨403088089060107033723897311361975766812647483178087280,103016764513643387805261315515079126200316887316888109823⟩
def polyval0Tail69 : Box := ⟨103190695309420125685872892020122770242070004748072968109,1551527022844603063118569941674488278405319394248348131426⟩
def polyval0Tail73 : Box := ⟨26531250000000000000000000000000000000000000000000000000000,2⟩
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
def resval1 : Box := ⟨108041089666631552465733633686192904985323462142599630730,313031908445377407529277851065637537841038810871114604⟩
def polyval1 : Box := ⟨3734980737081571183840371713578072535617667345478067034599,9955117818663853480835485253438173010303174591752187251⟩
theorem cell1_lo : Holds Q cell1 (1/2:ℝ) := by norm_num [Holds,Q,cell1]
theorem cell1_hi : Holds Q cell1 (3/4:ℝ) := by norm_num [Holds,Q,cell1]
def resval1Tail4 : Box := ⟨51073340460410343018411656176626755489850643756141,3082292734353061801413802101176525598813885637770⟩
def resval1Tail8 : Box := ⟨5666602285837470777061644919822216900566338528,6034874483378686186669605472753992804290592693861⟩
def resval1Tail12 : Box := ⟨-315129400968903955729811349742433740016709978,19072355301904804649889567316522493698757801292214⟩
def resval1Tail16 : Box := ⟨-2096705131704540204909369776413829719906229470,60276974838302384221518827560138277899776829613526⟩
def resval1Tail20 : Box := ⟨-13741082887666807195152035892374590853894364364,190497892489046908623836992601199710242944469125111⟩
def resval1Tail24 : Box := ⟨-90053562264426916868592270078606969305519606965,602020788344727558328363863928957543990623872622287⟩
def resval1Tail28 : Box := ⟨-590175025708734866103538276543599826608581786159,1902377424087769273534987917868303132963284261409878⟩
def resval1Tail32 : Box := ⟨-3867771048489746398414653893978615837548972406060,6010449579236084636931204061276894013180821541395498⟩
def resval1Tail36 : Box := ⟨-25347824343383544667502386240143404989378069270455,18982865035815271663738135962418739779399206448234104⟩
def resval1Tail40 : Box := ⟨-166119501616798978402860070098699442812193715318808,59909219908267345974325241993941913265188517436743525⟩
def resval1Tail44 : Box := ⟨-1088680765795854277554433480865230717333638498898711,188779058603714529518940776021836965088023675451740522⟩
def resval1Tail48 : Box := ⟨-7134778266719709241870002362640794015555656501224204,592941039987535326663265347093092313003096103159846526⟩
def resval1Tail52 : Box := ⟨-46758482848774195643837635812033848606455606528840672,1849777436572081106324530885839053567789256621088802940⟩
def resval1Tail56 : Box := ⟨-306436393197718016984481106487935857191099774743634212,5687553673120037565331404950918613553596745964443389332⟩
def resval1Tail60 : Box := ⟨-2008261546457978972837955733711895383134679473274878204,16935707058198015209259714878825211696090589173639616207⟩
def resval1Tail64 : Box := ⟨-13161342866884367661722773269488053235952435865167892196,46710952966285269959019396492891686132242967060730408344⟩
def resval1Tail68 : Box := ⟨-86254104694202440706896939722971841211781488819231902687,102971851370080528960449656371962409746157366178224271810⟩
def resval1Tail72 : Box := ⟨745869945714445579423610986764573835966959556041078012250,1684463027387996035594368457242517490649498391667932452⟩
def resval1Tail76 : Box := ⟨-23494246594669225488291675916127540323787137570845,416126057157571732258000537108407376538552558589⟩
def resval1Tail80 : Box := ⟨-1174011572814887152319087992284817162754131930,59917677856668034143491116663456248575564055403⟩
def resval1Tail84 : Box := ⟨-3255301480031631411382106851937162192954782,189241297902746579875621067144528112548921973441⟩
def resval1Tail88 : Box := ⟨-17313692023476103152701221511331527472507436,598086982563716849751529672365397422606444298623⟩
def resval1Tail92 : Box := ⟨-113456754579093429478078461412273701382573456,1890191474583442007461510542794598059135372487699⟩
def resval1Tail96 : Box := ⟨-743550092932183394956815999494807320268849832,5973553516806216339605777754251173277726619413240⟩
def resval1Tail100 : Box := ⟨-4872929886460328642062284214989885346501334151,18876856071670080448617118170872317999378242704735⟩
def resval1Tail104 : Box := ⟨-31935233303716368671458161751328914591812134181,59643652722232911783517711575858638430581905960695⟩
def resval1Tail108 : Box := ⟨-209290744979200996815610358437431947938321715180,188395036620667409301910767021485812699088638859289⟩
def resval1Tail112 : Box := ⟨-1371607826295677285038575862027017394792791217637,594711204588587429908318993487964853871472570635096⟩
def resval1Tail116 : Box := ⟨-8988969050411339314156346743505276696517164263255,1874927080063293291275393748730990670575846451604954⟩
def resval1Tail120 : Box := ⟨-58910107568775756559431141648671351038290554430919,5895194936543673458074821497445843627153155553720527⟩
def resval1Tail124 : Box := ⟨-386073280962729488678071758958876432974853857204209,18431838957219826620452477475177840032154123368236065⟩
def resval1Tail128 : Box := ⟨-2530169854117396157074163189046615626848671939378777,56943725614706524559041971728153812533557017120357354⟩
def resval1Tail132 : Box := ⟨-16581721155954997185814115763128991166573493033282459,171385158350459935341515516309762434095875918773651652⟩
def resval1Tail136 : Box := ⟨-108669967778519663051329327389264404154861414883367934,485398194620478831182837469713171886468422460692125472⟩
def resval1Tail140 : Box := ⟨-712179594128030443715850974472412413782510454577447108,1165369238875037302066501918517781488177479398508389445⟩
def resval1Tail144 : Box := ⟨-4726232448201920432394712226883570411193368500307505465,1254454104975972748985568493339806229472880265272715386⟩
def resval1Tail148 : Box := ⟨50383772947816848839301482136212826230559511,785206687280550684075021585894795680153700⟩
def resval1Tail152 : Box := ⟨829095919504507785303294916244338913494,2545298351271494480230024035826667310595⟩
def resval1Tail156 : Box := ⟨341247330132088202851651252295771225,7961922315100309030672907435321725977177⟩
def resval1Tail160 : Box := ⟨640073103089986422481380588433446101,25163270499154602162499738866601337816122⟩
def resval1Tail164 : Box := ⟨4192202016577283767234471012618546734,79526190574101392431821799977229424250205⟩
def resval1Tail168 : Box := ⟨27473999276169007013431109844469977454,251327809828618266920255758864901599246869⟩
def resval1Tail172 : Box := ⟨180053601353831422660444977665860310115,794226769360732125418896393617298036840208⟩
def resval1Tail176 : Box := ⟨1179999281816697144350188265722067098591,2509537860944027439004407903591381036978124⟩
def resval1Tail180 : Box := ⟨7733243293311843527694099530835200145192,7927375055692071072714638305576976397994315⟩
def resval1Tail184 : Box := ⟨50680583247047868018559000159673644719288,25028180213546260793454023864997170300864203⟩
def resval1Tail188 : Box := ⟨332140270367852505866608844582475764554061,78929444470114703080094811535136718045517970⟩
def resval1Tail192 : Box := ⟨2176714475882757871524147667696005535418836,248329034827370751097935725241337319661848515⟩
def resval1Tail196 : Box := ⟨14265315989145246116419945004764451292544358,777456558352001650178136322610298163275066391⟩
def resval1Tail200 : Box := ⟨93489174866462530512928008140396419136194974,2408742921816668588727290913805155156071952540⟩
def resval1Tail204 : Box := ⟨612690656404879510548394605394336760674813101,7295598439285039279722542435614427270476827540⟩
def resval1Tail208 : Box := ⟨4015329485828808271566984599037765335456851011,20978769384510264511397436981462877172881533909⟩
def resval1Tail212 : Box := ⟨26314863355276722004524581558126511710915525697,52678831868376411530223983049762112299547314908⟩
def resval1Tail216 : Box := ⟨172458833318718282417138007153163078721235544583,77201613021146009968304569162846999099499052612⟩
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
def polyval1Tail5 : Box := ⟨1903125674049850127435313049200413751491921851758867,117418569217665713209739993817319979811692135036250⟩
def polyval1Tail9 : Box := ⟨172943815604765230745409703657227974329690345169,267341893859311787084019779572254105512223901784712⟩
def polyval1Tail13 : Box := ⟨15113517858434770630221704030554362134554479756,844908798323898268570921189675738328404162451073477⟩
def polyval1Tail17 : Box := ⟨98234435349517050101330315407307510990599583710,2670278180625519199711569925370490852974013783160694⟩
def polyval1Tail21 : Box := ⟨643786563125881163289692757023449411728885845613,8439064388157996848069706229993944952426921820975610⟩
def polyval1Tail25 : Box := ⟨4219119591155154773626278603062345550621100753159,26669426469636856868573261084635939781867304511756558⟩
def polyval1Tail29 : Box := ⟨27650422151672406888876829877089504272881885549575,84274241810469743201766966625283668369493653894883181⟩
def polyval1Tail33 : Box := ⟨181209806613123598139992979986137373660482749520312,266254400212536004283529133180385658866535207257842033⟩
def polyval1Tail37 : Box := ⟨1187576588619751372077723291790224297638000524765148,840880524212641682320805215461681494118812674418164021⟩
def polyval1Tail41 : Box := ⟨7782901931178395642482476073029611119192340944952417,2653568132699968848323695134396663906229300951878036194⟩
def polyval1Tail45 : Box := ⟨51006026096170727958673011061237723890016865957086222,8360177490762763769359151313857477128342233875108578449⟩
def polyval1Tail49 : Box := ⟨334273092623864486685329518749522529105588901935798918,26249220491522891463874810978093698439593040253175575342⟩
def polyval1Tail53 : Box := ⟨2190692139819758756597059034831330608814262289751819047,81826275237236655485811567004081489478647912847576124382⟩
def polyval1Tail57 : Box := ⟨14356920007522806445325901686014698510811748575021385009,251178186764408603873936176375868121706982178209215862701⟩
def polyval1Tail61 : Box := ⟨94089510961309392962477196004031581964784152999738324000,745132554885788468342177066534415655886676621517800564011⟩
def polyval1Tail65 : Box := ⟨616625019043959448519600352653366725164205605641456231221,2035731139688786704723260138683503562255848471118371242435⟩
def polyval1Tail69 : Box := ⟨4041113793770663975610059192756323927517950481022922653686,4341641527367039394096181066807524570662776985202093757839⟩
def polyval1Tail73 : Box := ⟨26531250000000000000000000000000000000000000000000000000000,2⟩
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
def resval2 : Box := ⟨107936652777406011314773226455960749543595826522911948873,297275967947410625577475768304171734280713583267227283⟩
def polyval2 : Box := ⟨3726244335718172038673494130914793630144912938447883767373,8717868836088874483514856599327579698509392066461748211⟩
theorem cell2_lo : Holds Q cell2 (3/4:ℝ) := by norm_num [Holds,Q,cell2]
theorem cell2_hi : Holds Q cell2 (7/8:ℝ) := by norm_num [Holds,Q,cell2]
def resval2Tail4 : Box := ⟨-143117701433833817588291309517166882884185590208822,33813781687662306396511730857140848342541618762806639⟩
def resval2Tail8 : Box := ⟨-443943189846684204342975852450374477971932803758752,57569464357431426257754615809943145542115423919999709⟩
def resval2Tail12 : Box := ⟨-1018683740200298159716010592186945806375887747481504,97949637577792083530194022593664490312782310529624109⟩
def resval2Tail16 : Box := ⟨-2337469202808288102813234981388977933538489970125046,166498117692926222988243895000432562627763490732038503⟩
def resval2Tail20 : Box := ⟨-5363551054807235570614599342056075744185195981925141,282662506390004689459318694813668783064622607866385294⟩
def resval2Tail24 : Box := ⟨-12307190992187267970455373037010669416541887661145905,479052547156063635385767476140447500871608490911691505⟩
def resval2Tail28 : Box := ⟨-28240050028499886944432298591587951677047231237390134,809997970569265929834700534351145061216748747041180427⟩
def resval2Tail32 : Box := ⟨-64799548988752796943032515787007375854860454468038942,1365197507391275852631136870119859634892499333051046997⟩
def resval2Tail36 : Box := ⟨-148688884931441591995494027661317981291095612552582102,2290822961354521485458253885464545818982812723494897342⟩
def resval2Tail40 : Box := ⟨-341181147819297509736745635575283160159469885642778745,3820518361713107640276923285907206140670701825555880715⟩
def resval2Tail44 : Box := ⟨-782873418419715051762434533656328764992762514849363767,6316802213002497148795292212073882366633612053066746283⟩
def resval2Tail48 : Box := ⟨-1796379410719318145042929009377834140227486038803029163,10315353778079257932911017718199437320568843020203917615⟩
def resval2Tail52 : Box := ⟨-4121967755362250314962537517502022586182218725220711096,16540114352642317510603571869087379574984842365604733949⟩
def resval2Tail56 : Box := ⟨-9458257022352866541443705763579835167244926337728097646,25790342858691152550689003281293371869966867352093949460⟩
def resval2Tail60 : Box := ⟨-21702893183601983762594728948747608156131095919405622633,38429662048697403945576353076911665444773149534989041935⟩
def resval2Tail64 : Box := ⟨-49799405048463147900742829943766024716118837634649094513,52784079426175504486850486649976720194982499812579426971⟩
def resval2Tail68 : Box := ⟨-114269535217425579402409401869533822773106543787780312981,60733303886933625797367827781601966366104131048160655231⟩
def resval2Tail72 : Box := ⟨747193072391598298961765911175807167533650686027080032213,1243997245990104251224050915915948379668880592070118717⟩
def resval2Tail76 : Box := ⟨-25316782520340743192585092983654219296518058594601,391451123894404487031610536646144499470922339073216⟩
def resval2Tail80 : Box := ⟨-4764984555628901565520061233080568167707699262442,666362656828747057862876278502830630926950248451915⟩
def resval2Tail84 : Box := ⟨-10931086891133908327753042910039517684403752199075,1133981061041428289135338100421612071384214992335605⟩
def resval2Tail88 : Box := ⟨-25082443597455088956008909393061310716106507000700,1928087133853695502360783022409244456284262505284750⟩
def resval2Tail92 : Box := ⟨-57554113073939638947972339792818035699106928895334,3274466956994214317313642487776196470077048645731528⟩
def resval2Tail96 : Box := ⟨-132063525591289721115729393325236090872009598996617,5552217316973933727696010821110119270134743822155219⟩
def resval2Tail100 : Box := ⟨-303032639373647264360754737245672306646379787366491,9394099526868399254897031685165983945992411412083441⟩
def resval2Tail104 : Box := ⟨-695337945239709584934054813302475866766954680781782,15847541418745056109042488014701380434085906369098422⟩
def resval2Tail108 : Box := ⟨-1595520730339610205745970578780532418782527336545653,26625901125087961749096983700400163050915243125290832⟩
def resval2Tail112 : Box := ⟨-3661077923865995391027917785732559577581225372140539,44483421834497742518541097935210631511753029625022574⟩
def resval2Tail116 : Box := ⟨-8400700354276176393613853357359254630294591900705622,73731690737043219890542989292106488033598198277684948⟩
def resval2Tail120 : Box := ⟨-19276226267212054797290342279589088438069928549044434,120838006931473595863593761748612999375018692410701635⟩
def resval2Tail124 : Box := ⟨-44231181143797809802467221717965238116309359501854786,194797514891944142125586993944166072082660522676189876⟩
def resval2Tail128 : Box := ⟨-101492758917402563427743979860701159576308644000802130,306279643815791574854880001488729470555689330266626600⟩
def resval2Tail132 : Box := ⟨-232885033731702785563472589284585686615570459782095833,462756682884366218319704032403242072124912523936002425⟩
def resval2Tail136 : Box := ⟨-534377422740503701769838948586481333983089674774654764,652356634434503295685607650511451864598130504237994636⟩
def resval2Tail140 : Box := ⟨-1226181186977389335105900293116485630704487088215121807,798334785772562513088739309535046666617602027900726076⟩
def resval2Tail144 : Box := ⟨-2859171444027362064404431981032407267602978259705946191,634739674746282307355858756959982035626181810362202444⟩
def resval2Tail148 : Box := ⟨50236999716138272112986721362591045305244461,39160400540473921596954076998074221260995764⟩
def resval2Tail152 : Box := ⟨495430622303290386563871512887348316161631,65620370244776037370952042585304075636564262⟩
def resval2Tail156 : Box := ⟨1134946702627860661991355670843174248394094,111654287115091242028375297921520457228797367⟩
def resval2Tail160 : Box := ⟨2604245355518307168924823143183801581065185,189809207677331036672320414660829522545510841⟩
def resval2Tail164 : Box := ⟨5975694954464913067103254838531498670417041,322273161197540288348885994814626564597800562⟩
def resval2Tail168 : Box := ⟨13711814871176167467049585623656108635212432,546266242104502133478532675707993767387846743⟩
def resval2Tail172 : Box := ⟨31463096509134782024058304938786501258062244,923834746628048948439285438267935400004741556⟩
def resval2Tail176 : Box := ⟨72195143476161791737016710102588230985783969,1557500802167280336767655487038055531159913438⟩
def resval2Tail180 : Box := ⟨165658797761063659051593617581243205679325061,2614530537247490675464148976681631526842792427⟩
def resval2Tail184 : Box := ⟨380120267850182695119992559468791993442732754,4362759997120678843347510927616815902773596977⟩
def resval2Tail188 : Box := ⟨872223026988886002116351128139436800692809065,7218921315085520020982001989572484519307680387⟩
def resval2Tail192 : Box := ⟨2001400801678639860092973515543771498335070677,11801734235862704192852407947452270981056303148⟩
def resval2Tail196 : Box := ⟨4592409332264673577616082500623011729490790240,18955129657226932108399794734582580558170150138⟩
def resval2Tail200 : Box := ⟨10537731101827584972707010597325246796785205795,29633330831099369354260726424244546700026440428⟩
def resval2Tail204 : Box := ⟨24179851738012442263482830371249751663917142140,44350206436610154946215255691724796662490936937⟩
def resval2Tail208 : Box := ⟨55483028027824883204756627986989023493286936473,61426225734472751228402475871962114743974571333⟩
def resval2Tail212 : Box := ⟨127311218993519330318880935195609138975127120065,72130806608511281582240830328749595023878385268⟩
def resval2Tail216 : Box := ⟨292129371936462384566262995324526460610626576955,48111095983456250965586300677071771513180148948⟩
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
def polyval2Tail5 : Box := ⟨21428314398093116862101562680122956645206184114492858,2998847945673186314011367922107650484979786932542538607⟩
def polyval2Tail9 : Box := ⟨44859481923961903029525771700097204507283961325609282,5104384248658593851802750612932481486948672246242069644⟩
def polyval2Tail13 : Box := ⟨102934073976406181039272654200732822506617885271114105,8681448113521955234440046006879207202623408942715803401⟩
def polyval2Tail17 : Box := ⟨236192271428188385720498922695826962345391551466878766,14749575924946304890153197734739285531175971983602104652⟩
def polyval2Tail21 : Box := ⟨541966202174036493447062212262853297941319212406515400,25023092745076409498801694436333652330131735925034888255⟩
def polyval2Tail25 : Box := ⟨1243594307821063140172233699503086388511107058982019313,42369267603023505481901753663822795223945350094676267295⟩
def polyval2Tail29 : Box := ⟨2853548424682650661466856494467699078934463334691140173,71548068562747317070469001283271304242984636925885891257⟩
def polyval2Tail33 : Box := ⟨6547745161584054938017287255158204545231217703721731898,120378128716180687996350792385690529579213854763267352347⟩
def polyval2Tail37 : Box := ⟨15024439862384812306947415161998778189009249203498699186,201505497415134715827531961672874455877053885427453163960⟩
def polyval2Tail41 : Box := ⟨34475042569281574850724819577973817425351479999670840301,334915471003696345697390766567227560549259741382601972213⟩
def polyval2Tail45 : Box := ⟨79106347460538401647065348360644245216137283007227274753,551057560742259416997671228516753379960469137965836400495⟩
def polyval2Tail49 : Box := ⟨181517229339793588842346541840002055997981708579617118569,893514577406836925612060462035243685870499382408710820980⟩
def polyval2Tail53 : Box := ⟨416508985750243781834564858657469155083290950669531069621,1417447815763374955426735381925345559698414068949149814527⟩
def polyval2Tail57 : Box := ⟨955720489133012758646777800587500120443976339312174656997,2172928848226330185771228022462455806732799142823106015758⟩
def polyval2Tail61 : Box := ⟨2192993871916995683207798055329752162011258958813401508619,3144343773157507347864655613477738735498385882207923475287⟩
def polyval2Tail65 : Box := ⟨5032038317640667965992205391522893596189208353762912458163,4073224070630123394832774650057439451497084749670671279176⟩
def polyval2Tail69 : Box := ⟨11546502739420800259680390090418400574811993840765553451390,3986672960453729598032239310553430968501466122581961499247⟩
def polyval2Tail73 : Box := ⟨26531250000000000000000000000000000000000000000000000000000,2⟩
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
def resval3 : Box := ⟨107753507151379078966699785371399752736992105660993523434,1838801297729600475238520301625367875457456412953369136⟩
def polyval3 : Box := ⟨3744021223234765905497321693909435448721155450370702431956,236012783047193282939880828205657881067280861026062325495⟩
theorem cell3_lo : Holds Q cell3 (7/8:ℝ) := by norm_num [Holds,Q,cell3]
theorem cell3_hi : Holds Q cell3 (15/16:ℝ) := by norm_num [Holds,Q,cell3]
def resval3Tail4 : Box := ⟨-194850260731804928597945520545720966218857510931292057,2020758355395291284456609036302574143523879310648502424⟩
def resval3Tail8 : Box := ⟨-288948439601259566700727383504724928181025272915657208,2579305476773514134995105021956676033423105005506213677⟩
def resval3Tail12 : Box := ⟨-428379109264213227274049333587601076978867765971415361,3284685365111555831749106717269687314217676354677278426⟩
def resval3Tail16 : Box := ⟨-635091360973367412013046743007276340454959168318665228,4171612706048405996346683647480647939479061206404605728⟩
def resval3Tail20 : Box := ⟨-941551602438107284646502536370166560356580514970601420,5280910772600706751560618177732397928181359590772511204⟩
def resval3Tail24 : Box := ⟨-1395892740054011055784332598441520719148760056343626446,6659322948055494696391425262676490331088210986258916441⟩
def resval3Tail28 : Box := ⟨-2069473979641577681356286581117343419701107056238767583,8358311014648685417293212142748283878432713538025644859⟩
def resval3Tail32 : Box := ⟨-3068088564059612741501661956505723517093175668722703132,10431078199116815554069348127577526379434089514633180445⟩
def resval3Tail36 : Box := ⟨-4548579749982499869414621276360550987552387011700788384,12926608259726742694179441202139418956350937160123646782⟩
def resval3Tail40 : Box := ⟨-6743474743302378804289997968197441657736266502037274343,15878824938757965307210904115056512885880894621969058475⟩
def resval3Tail44 : Box := ⟨-9997505620019532769720952816120754325889436248684948968,19287927110123809683034958189691563190508645775873261138⟩
def resval3Tail48 : Box := ⟨-14821753239543550005102929321420403066024334084240133511,23089360230138901170606003391319380055685376191525869577⟩
def resval3Tail52 : Box := ⟨-21973918039516991726934599062335552528469318830773530004,27103469266144422887970859546179452777588815162209851356⟩
def resval3Tail56 : Box := ⟨-32577325111525071569154006367367753915871022004789237983,30955231026031986585255633633802178918026977614035925441⟩
def resval3Tail60 : Box := ⟨-48297354596180473047181848576767804116868191072782123690,33947970816774204443421943583351079730718156962494450135⟩
def resval3Tail64 : Box := ⟨-71603007702716324202262538330904674697280552450342106193,34866713701866383209537618447503466077217887769910112420⟩
def resval3Tail68 : Box := ⟨-106154639111697080135619027369835477125688502813351886719,31674437056056350227722122062813891675868769167455950836⟩
def resval3Tail72 : Box := ⟨747852685876510000539606735188352388739205430961336862365,1042957171451006830052218555546485884330343271745471020⟩
def resval3Tail76 : Box := ⟨-2355308338410755106840598162808777297188297837507027,25119800920016752764040116539439964573675012390950846⟩
def resval3Tail80 : Box := ⟨-3457580890679742245139912892300717808314241662030969,32079857848393857671390553980736618282176311811518495⟩
def resval3Tail84 : Box := ⟨-5126018016542995234030070875271861962380589260763775,40878555014336719029760076178092419796014582528898122⟩
def resval3Tail88 : Box := ⟨-7599553030693588720355462948335890087459619238935805,51955127425851231453870024616411295523495158978595858⟩
def resval3Tail92 : Box := ⟨-11266680313356399255663956880133685659123093352218898,65829132790841572114219933613784063281035653825215750⟩
def resval3Tail96 : Box := ⟨-16703361996516216379851073113588380784570069867750587,83100118647369558536860880876882673915158828470623833⟩
def resval3Tail100 : Box := ⟨-24763487933167988036778301989608769306400412392317780,104435937399724814348817864413070650996129222636318424⟩
def resval3Tail104 : Box := ⟨-36712988363902828153528930612258249020033238908341111,130540612398891496694646716658957966141759544160442555⟩
def resval3Tail108 : Box := ⟨-54428661998085304045079148132335324049113627461688887,162087525253084846532211234240390868254888900224134386⟩
def resval3Tail112 : Box := ⟨-80692947616724181440990697683649541146757373151746979,199595543201896796102938108892579416678951905516714189⟩
def resval3Tail116 : Box := ⟨-119630936275899077284449033052283980249217598532519802,243213242179195132777680529047865434670425144815661799⟩
def resval3Tail120 : Box := ⟨-177358261619408906627025859746197101010463222635143871,292357414019762533411842820320087755616536085070264097⟩
def resval3Tail124 : Box := ⟨-262941626504647112280750669009166585211936312773191365,345123292383031693161366713621378576389805345300262202⟩
def resval3Tail128 : Box := ⟨-389822827071187946206590542358126073653659631527837343,397340482049264795549658454037510837713803899227775637⟩
def resval3Tail132 : Box := ⟨-577929932684469265691486314653775660115633632464126450,441083096975152718764960888683387818874201792625760809⟩
def resval3Tail136 : Box := ⟨-856807205481571184527715856576342480648250784022086329,462344160683907713837423604784165360307713621540628840⟩
def resval3Tail140 : Box := ⟨-1270255413978698109095364122326152062929369352838662361,437436575192912043402970983680944527029645959003909734⟩
def resval3Tail144 : Box := ⟨-1924161984158067141565121626826851337180295322186514059,324062350426534352720775600400934448963481075572088575⟩
def resval3Tail148 : Box := ⟨500330813884429135703519647100637977036096863,4402815502858618756473623909265085120995500311⟩
def resval3Tail152 : Box := ⟨667869247902784414643250853245320271085042544,5614316476339303556328356346451471180711086536⟩
def resval3Tail156 : Box := ⟨990145103629709570915125865734530450722012706,7142383686870704898450156040202383918001972475⟩
def resval3Tail160 : Box := ⟨1467934798105841180231589278801624267693001647,9059934965817263019869831058489170239380740846⟩
def resval3Tail164 : Box := ⟨2176279581747908015752735214830043319986673090,11452450746122501556441911610178029943628238362⟩
def resval3Tail168 : Box := ⟨3226432689003227943155599925617181312448142924,14416480313807932728906131640773876239003942857⟩
def resval3Tail172 : Box := ⟨4783332060813522066531572986798219627225273204,18056094043921929250641664220986779958307859712⟩
def resval3Tail176 : Box := ⟨7091505637786961211074479529538576444713244688,22475005556285977798838069613994927468329448708⟩
def resval3Tail180 : Box := ⟨10513477126698017674197632833839913342383875359,27761503171865224418365170755535949831854284848⟩
def resval3Tail184 : Box := ⟨15586704282462699522102439252962090975127356138,33961722558952424108000360026060613596797232003⟩
def resval3Tail188 : Box := ⟨23107992480623129440925873311723752246413764965,41034342363406135590621927012053482184282923860⟩
def resval3Tail192 : Box := ⟨34258641647890836282812469787442129359320665456,48776065637804016322056314496796308841967999585⟩
def resval3Tail196 : Box := ⟨50789982234188083025805459882755264190198058048,56701624218657306812387179227496131903241185314⟩
def resval3Tail200 : Box := ⟨75298440663888897775429261012205269050118000806,63853557765615803019209176827691224471745424102⟩
def resval3Tail204 : Box := ⟨111633336280174332705594348478141449470073327990,68504251257129787861217034579683763612166904805⟩
def resval3Tail208 : Box := ⟨165501458717719561955120557522256037040710314971,67693542503914266556534573871106768867597152357⟩
def resval3Tail212 : Box := ⟨245363381167225721917711354129326282308205988223,56516472684730234067413796828697008049478202384⟩
def resval3Tail216 : Box := ⟨363763514352456944194298411639463505284711589389,27032612959566085124339075335846509658029402766⟩
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
def polyval3Tail5 : Box := ⟨32817699418372112197397689891419022192722685496874428507,296270257277477340196006099794659368124983043880886361543⟩
def polyval3Tail9 : Box := ⟨48650953734939425400897388088176049720269961084435281954,377363572147857980652013246578917190164006716425926352777⟩
def polyval3Tail13 : Box := ⟨72127234141552175629878851014732626726224797517200954989,479364873657444878729376671173123772399883123198755624438⟩
def polyval3Tail17 : Box := ⟨106931879503462757527453560699366738975272938974139546207,606995760530259428199177865280504097957181796015960667651⟩
def polyval3Tail21 : Box := ⟨158531336883392276100933198762473574214206009681970972036,765675316296854477017318117806331100673597055061521322361⟩
def polyval3Tail25 : Box := ⟨235029860980062994920807992094865219059703147020985747947,961391022433678258167267162124540145803984201150449618204⟩
def polyval3Tail29 : Box := ⟨348442375105552863479146986298327901732999338332616067607,1200370247420925097090048691738727803041645302581893269055⟩
def polyval3Tail33 : Box := ⟨516581545267977224562530983838731345262518043675918012392,1488415670137361237130017418003919852795351768183618204729⟩
def polyval3Tail37 : Box := ⟨765855452657309451577704723078666575739886387819979305465,1829690177146231514849239382800078877944305275644825669659⟩
def polyval3Tail41 : Box := ⟨1135415269356296741319669053668499396320810444901551546476,2224617884121330138200834367828645007982089186601839815440⟩
def polyval3Tail45 : Box := ⟨1683304374754232351536862236500046438261304421187366037268,2666387136283985034661815691173129989291517809939518657845⟩
def polyval3Tail49 : Box := ⟨2495574698121812889446806935607501157320494953515814537401,3135267432592273325323650894492093166376740558548295912178⟩
def polyval3Tail53 : Box := ⟨3699802107871946330689652807771311656068244046033062876832,3589538531702934739757837897961833246451142868371252700605⟩
def polyval3Tail57 : Box := ⟨5485123586048450356848230357646448587869037031484037576271,3951206846646451511652805457447541600997406432702060220451⟩
def polyval3Tail61 : Box := ⟨8131943243723985523586147273972539846262087286135379056444,4083747644909957230562942232248762949254747875146031348206⟩
def polyval3Tail65 : Box := ⟨12055972829377930326805704269584572820884456274559399108278,3757706540059567905625793925912128765779535843474720438345⟩
def polyval3Tail69 : Box := ⟨17873523819243655628396468062111621144508485064246625738372,2597889383615876961218483602273378519887012284556972077254⟩
def polyval3Tail73 : Box := ⟨26531250000000000000000000000000000000000000000000000000000,2⟩
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
def resval4 : Box := ⟨104305964229158936620326369482390685113617870292032249766,9328398117587997791910302382531024859360645209314015166⟩
def polyval4 : Box := ⟨4555386298973142543656459932788049209233774976250143571281,1862348155548240128860758595146372324262218819206707461246⟩
theorem cell4_lo : Holds Q cell4 (15/16:ℝ) := by norm_num [Holds,Q,cell4]
theorem cell4_hi : Holds Q cell4 (31/32:ℝ) := by norm_num [Holds,Q,cell4]
def resval4Tail4 : Box := ⟨-4305445511521474384750292885579694756491080623715010628,10036214685542981866384548845589097218718930518898204794⟩
def resval4Tail8 : Box := ⟨-5217034152452757206093374918515703935035597868743704808,11066701909874046158755127739322691120566429008765349004⟩
def resval4Tail12 : Box := ⟨-6321559589405979143737182558155960255845519777261232214,12167175188573517856381042158594212229045105592655295116⟩
def resval4Tail16 : Box := ⟨-7659929843800106508277633005118292429315537519302039748,13332384958526196427378890949477231011522729251668367826⟩
def resval4Tail20 : Box := ⟨-9281653424611832553013294411102091263986569658453271657,14553253942046989029516041537330210374731843954442924487⟩
def resval4Tail24 : Box := ⟨-11246720538091722574753147444310864960659764436659036305,15815697995868675390472004781500316614052939019265964719⟩
def resval4Tail28 : Box := ⟨-13627822229014550835925262998610619085806607699645683724,17099148328954416045094024882890198566307843525866564742⟩
def resval4Tail32 : Box := ⟨-16513039341256236188655342639264805900405363410415617418,18374704283190709161461828518474566347718401097954119486⟩
def resval4Tail36 : Box := ⟨-20009100772192428461768509403067391371872078480114467053,19602830801370143658936260975407112958352289672736872458⟩
def resval4Tail40 : Box := ⟨-24245331549079551460066510380248374500412207857079959444,20730495488616340267329020896897006847567981593037583674⟩
def resval4Tail44 : Box := ⟨-29378436773217476354424879689512410606081952928416096530,21687616745737704267958778976565522323224178257327420547⟩
def resval4Tail48 : Box := ⟨-35598298397808599400082570028843911190959562883827446645,22382665905863918574547342660333609409560449337795685016⟩
def resval4Tail52 : Box := ⟨-43134999271802182154091835746944920402220167745666695527,22697231533656182205672323134022730949711987382746280912⟩
def resval4Tail56 : Box := ⟨-52267334280587782658045152677853943301361849965486810463,22479311706958036843877177038552620360933950726918214320⟩
def resval4Tail60 : Box := ⟨-63333123424543128454320800144953205149725058020778287839,21535048564003872784869626404400544596106286924898669708⟩
def resval4Tail64 : Box := ⟨-76741708330294676080885057459734354956158211029774709311,19618556686193994454237904922210641829735685601936401963⟩
def resval4Tail68 : Box := ⟨-92989045793000434674172064300767795590472665936603981189,16419417943759577594985061696569487035505785895884941457⟩
def resval4Tail72 : Box := ⟨748140063620024562422192575674172395034688333144271246282,1028660024700441309123570245836445033545984679570291203⟩
def resval4Tail76 : Box := ⟨-54180339105078689675881955523960800983254662744839626,129229670829343579672757093260219685555355744754844779⟩
def resval4Tail80 : Box := ⟨-65623205580712052964305944926807470059887052975319918,142596165953928392987906158582620327770827769235048993⟩
def resval4Tail84 : Box := ⟨-79516634322233706396887648954000959827711643762936082,156897951293184471282155820724528081281999433676314333⟩
def resval4Tail88 : Box := ⟨-96351514480587024788566114723329906056524161302277260,172076231640670014626097022308396673256331520142834952⟩
def resval4Tail92 : Box := ⟨-116750594663618632722056411477713451457588219492921511,188025249433961874586079303137842197936279696321361282⟩
def resval4Tail96 : Box := ⟨-141468470192599852024387369593345954326945507619683552,204577408028322643321731849462533341631042793697090374⟩
def resval4Tail100 : Box := ⟨-171419495689052713617943523407405005831886007137502025,221484837619428659408749042216065137437444588718718888⟩
def resval4Tail104 : Box := ⟨-207711608546299658603845501538410079121176215800256007,238396335077369065958220026156379380217284967161409802⟩
def resval4Tail108 : Box := ⟨-251687313344759294366588688850380061863058486242978328,254828600308673661161488457017091072627955774356520108⟩
def resval4Tail112 : Box := ⟨-304973343290935462106812804460836277604712921428461956,270130450423622317061062266774519893264395379393376778⟩
def resval4Tail116 : Box := ⟨-369540835737906790196118849648606525893967288137466703,283438398733248860677596291274936212897300021083966240⟩
def resval4Tail120 : Box := ⟨-447778247778187082134915388152613496519320950399127564,293621627010611989890253451772810300876548968853776385⟩
def resval4Tail124 : Box := ⟨-542579709175929781070896466149892624926298360402268640,299213942626833530552375912870694596650529715505191200⟩
def resval4Tail128 : Box := ⟨-657452080957867169822796355761280134963417147203555847,298329780237205141024782056892429242391561971924467143⟩
def resval4Tail132 : Box := ⟨-796644679935277309141599998449814502449433202901675736,288560660153893134938851398542623548751252068577534870⟩
def resval4Tail136 : Box := ⟨-965306467886722034939281421962410618938271314858112025,266847727519376223170678654283555103249001476026097285⟩
def resval4Tail140 : Box := ⟨-1169676583691443423488787425183899228699935967336287791,229325031925334036971215643880247584480693143675409681⟩
def resval4Tail144 : Box := ⟨-1456287352909847777035619316691576992077285156674484775,168518579492232929584246453428739664022773022226763591⟩
def resval4Tail148 : Box := ⟨15431007344426299974425180510832623752767104735,32807261154881929006942001041450762892455998632⟩
def resval4Tail152 : Box := ⟨18637698638689745664136696402905269560079764575,36075513673379048570442960419092029035305389360⟩
def resval4Tail156 : Box := ⟨22583581765719827127762695856095432129078038995,39538406210898443364884567399885463739060934217⟩
def resval4Tail160 : Box := ⟨27364869301421154030534741049595323895555544651,43169125772130545949874104567705638610841073113⟩
def resval4Tail164 : Box := ⟨33158428085495540302838812910504566546581336474,46926653269713652194572980571517379465931745298⟩
def resval4Tail168 : Box := ⟨40178571327723979346452070341034263893798155997,50750919465793257196678096123916083819788424325⟩
def resval4Tail172 : Box := ⟨48684985602292557685910286541083539764421416296,54557368105206383626799489720515413225199240623⟩
def resval4Tail176 : Box := ⟨58992337078444879979234994671784594216600468227,58230177927921418008180186935294531443090118960⟩
def resval4Tail180 : Box := ⟨71481911536459121226523893218326126929307806398,61613833871945828177096384475850083924854418429⟩
def resval4Tail184 : Box := ⟨86615718751939051733081017292684750513705932354,64502668742621037561899663667986875962485155018⟩
def resval4Tail188 : Box := ⟨104953582992649698184581776168968626686590431469,66627912485521171987921894156024413867944047484⟩
def resval4Tail192 : Box := ⟨127173851833313007045483071902224373062512985957,67641683712190017100452533435673737743676526241⟩
def resval4Tail196 : Box := ⟨154098489341274994772712286864031604682885150983,67097233333316464491745400753098591240364032573⟩
def resval4Tail200 : Box := ⟨186723481871001429653845479062643000482654560999,64424598247623283977200488982241448742962130763⟩
def resval4Tail204 : Box := ⟨226255681227444071390242662909777676476106789899,58900638183232075852112969390940426667002538270⟩
def resval4Tail208 : Box := ⟨274157448087126810669983892956904118650842149343,49612203910366643800765640507212978592933042875⟩
def resval4Tail212 : Box := ⟨332200747135627171517169503183703772977099483964,35410911542518043799433719906173160943679293758⟩
def resval4Tail216 : Box := ⟨402533866402810506677217106711909141311853931414,14857562922899256624987353783685764240371310184⟩
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
def polyval4Tail5 : Box := ⟨1012594520538281847185621554246508610273870009426597692984,2047080690000430734823223935220142876078761832237019670347⟩
def polyval4Tail9 : Box := ⟨1226973918293511650137985717234194694090314318907260144970,2247013170668658902129520040974914402435551272327536803152⟩
def polyval4Tail13 : Box := ⟨1486742946913044931940805108313332742602418070724056311721,2457660575715408008530550096236085588698021863342065518389⟩
def polyval4Tail17 : Box := ⟨1801509027644816071834085559189142047384582338636732667605,2677010538389445387080400240999798137706257799317498434491⟩
def polyval4Tail21 : Box := ⟨2182915872192021006264574892179575297853352869576521496437,2902044981404097914584370128757908044335877578173310708985⟩
def polyval4Tail25 : Box := ⟨2645072343210782922663903577594680278621517698866627757595,3128448683404100755343290163798458203267698177293522580332⟩
def polyval4Tail29 : Box := ⟨3205074364039962514422827900073934235325367795173245650989,3350245530151645762395137850057026374452219068317401000478⟩
def polyval4Tail33 : Box := ⟨3883637324851634778720049115483314146972306169462167980514,3559345686224301600054381142337346117694039429157255271759⟩
def polyval4Tail37 : Box := ⟨4705862378796495253388862792507819375749957820582822570994,3744983193553198001348166952695062444187387728569699229552⟩
def polyval4Tail41 : Box := ⟨5702164974691145226142593509334518582619873500877330353636,3893018943023938626069504965571496413289807316414294626440⟩
def polyval4Tail45 : Box := ⟨6909399974189207917842855249471121998902036772571574587686,3985078409845385519034407320006586351280576104902795573837⟩
def polyval4Tail49 : Box := ⟨8372224973359636739066381607110321720519014311515929998894,3997486777664387454950583099544222924069566823953279022768⟩
def polyval4Tail53 : Box := ⟨10144752260165985674659073855132077047115824934221768211737,3899955839640913349437248530060688723628350103444766408349⟩
def polyval4Tail57 : Box := ⟨12292550516454214512370774161783033471271781652614082080480,3653967040226271338724859587123986752197461363559230139754⟩
def polyval4Tail61 : Box := ⟨14895070310677696817380711380914366752689047372390041707786,3210782824783003937268037743392269207517902394778199551448⟩
def polyval4Tail65 : Box := ⟨18048583104305781147641201729950058553137540009897900495194,2509003628831249540692889384428919916168328093988483122930⟩
def polyval4Tail69 : Box := ⟨21869742537585394759523556658178613019479778532290658028821,1471569794171707724979557446789119294888674702341912539992⟩
def polyval4Tail73 : Box := ⟨26531250000000000000000000000000000000000000000000000000000,2⟩
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
def resval5 : Box := ⟨91154060045461952128694171352032475234484784152064627444,15273094883938084688215260187617675890241097731845114455⟩
def polyval5 : Box := ⟨8523259196793576370695827623751510558546079927476080101253,3726986366120933883245631716304453809431293006219566582280⟩
theorem cell5_lo : Holds Q cell5 (31/32:ℝ) := by norm_num [Holds,Q,cell5]
theorem cell5_hi : Holds Q cell5 (63/64:ℝ) := by norm_num [Holds,Q,cell5]
def resval5Tail4 : Box := ⟨-18353286311457928016138606715428661060598998939796907794,15428251184557205415404899496060578606682550113111125640⟩
def resval5Tail8 : Box := ⟨-20179706403601123337009714509603338523127298201833243840,15798353522492222070768736703205591050606419251137457823⟩
def resval5Tail12 : Box := ⟨-22187821841867558592028800522837291274247861325722953897,16129525781254659177400872712027459523902939224268992926⟩
def resval5Tail16 : Box := ⟨-24395768110160624026573022626761857933186439021329179748,16412967315533680421963160772585217273314764638460892954⟩
def resval5Tail20 : Box := ⟨-26823430705648556755117786702743182714167748949004044250,16638682158321940771393116849784602280497850718111010539⟩
def resval5Tail24 : Box := ⟨-29492673957704385169034948769413011008941926264976794409,16795338520407612800015582676360283507838448406031582956⟩
def resval5Tail28 : Box := ⟨-32427537950702392720634360403627097521585816549922944879,16870113681646615330308975250053833597978534274002133404⟩
def resval5Tail32 : Box := ⟨-35654455036944803063389845638091850461602591245223416329,16848522005191713078777742664098365449675998762945744677⟩
def resval5Tail36 : Box := ⟨-39202487895137382634175993688763275502289149783696734746,16714224301316695605792591653358190978879514957912397777⟩
def resval5Tail40 : Box := ⟨-43103591278451439575223633021153520223394183082376571076,16448816585044477459782566809617187166180661561122619562⟩
def resval5Tail44 : Box := ⟨-47392899809561539199623766165962634656257806464632263403,16031596070671358933485376840085043296523291662794885658⟩
def resval5Tail48 : Box := ⟨-52109044414635888370843317871127396848456907815747022585,15439302024727318471347057066746139290611114746067996195⟩
def resval5Tail52 : Box := ⟨-57294500246188186612933792811347080661905209499445161432,14645828854863191729621353666795476244949605705235758583⟩
def resval5Tail56 : Box := ⟨-62995969228298799124347486228611523342778152934973346540,13621908543342016977939800252867420651267064936595419948⟩
def resval5Tail60 : Box := ⟨-69264800669531764800635123604203634526929254338090338114,12334759237737996928011875275893050926675977528086887550⟩
def resval5Tail64 : Box := ⟨-76157453729009073965787275273501608377884420046020238795,10747696485140044654122743001828989609058876256562050858⟩
def resval5Tail68 : Box := ⟨-83735958330516967599235090150036095987835703855218412661,8819700260881244424871058166341651705142754261153487159⟩
def resval5Tail72 : Box := ⟨748135285947692856875383035454212203969548143494135963168,1051074604799460809089373592034535381932043500191193631⟩
def resval5Tail76 : Box := ⟨-236086910641076788062871444655481487343036422455249481,201622402971733884459752360298655738306277195625415058⟩
def resval5Tail80 : Box := ⟨-259554989034829754172865945303548918508849463188778434,206589380923328078821680878829453573486473249403535299⟩
def resval5Tail84 : Box := ⟨-285383727251844143259759233253828896250431493557656920,211069273726046532978664320978413148992489361067695524⟩
def resval5Tail88 : Box := ⟨-313782726490822517862733492487774840964628053943124406,214949569059476562049546917469043239860522885765644620⟩
def resval5Tail92 : Box := ⟨-345007756371914082974170276047746321958324224080412539,218102628312157783664450170790901878718755302146460593⟩
def resval5Tail96 : Box := ⟨-379340039803828875446808940050262470313995415803460322,220383691860825486353705489969364936435738749313840453⟩
def resval5Tail100 : Box := ⟨-417088784645320518197438649176626181727057047672953151,221628887953751223757511136878313925012188013037949302⟩
def resval5Tail104 : Box := ⟨-458593968532489877760841694728180390233793107021704189,221653024792251294000796837836676123861363163618815948⟩
def resval5Tail108 : Box := ⟨-504229400829413667435958825137957295647194006081041686,220247143000012481887576670258249038382935055593676664⟩
def resval5Tail112 : Box := ⟨-554406089278465785982174344119017155464857552494357674,217175803342213568409458997577996479375554159751568761⟩
def resval5Tail116 : Box := ⟨-609575941671492297693012056786540439760735842481552948,212174081970789530809129145027892510056715289162512815⟩
def resval5Tail120 : Box := ⟨-670235835880310526528264563851963479578048573108154355,204944242623766832013466031185552624717156237544156885⟩
def resval5Tail124 : Box := ⟨-736932094902568213680961113062659484721477245947360723,195152052068903545475305479479263560202203140570589786⟩
def resval5Tail128 : Box := ⟨-810265407226700531007722507636303348351866546208025423,182422701625732234182001255195591157005015625511577334⟩
def resval5Tail132 : Box := ⟨-890896236830421199917461587531342988646471711744844915,166336293793433484862170318215317845131118478402396394⟩
def resval5Tail136 : Box := ⟨-979550771544436969039864162034351727892974413253585761,146422848818678599808225968936177353340334157742308040⟩
def resval5Tail140 : Box := ⟨-1077027525546881452021060066101490973151603122859920505,122156776232087406545237722563108917746031853934776448⟩
def resval5Tail144 : Box := ⟨-1222257488563762851975497557346340199394049151432618912,90695416698691257465458927675366509570246806052869038⟩
def resval5Tail148 : Box := ⟨84303737631364981335134556805182097852073894070,63457899933561410333818620285126750637931031474⟩
def resval5Tail152 : Box := ⟨92638283389129879340253804166756387584228654521,64677306719742404696910601160685948385498874619⟩
def resval5Tail156 : Box := ⟨101856868883084841943581512893359837169648571265,65687354819423801058076699595562369631340050965⟩
def resval5Tail160 : Box := ⟨111992811705553546502057672529221300622832435600,66445110574920138503683264396097311276981664731⟩
def resval5Tail164 : Box := ⟨123137398697583845695788542162406327199422791785,66902528697063626367954585652727542316959370478⟩
def resval5Tail168 : Box := ⟨135391001682082714146735968880588004331514142000,67005291340182613880829686068374408075892324683⟩
def resval5Tail172 : Box := ⟨148863980645689919041783407356144199785221898979,66692086917343990386899651027313917359821936742⟩
def resval5Tail176 : Box := ⟨163677677676957482402104768695977064217156268864,65893810858792305448785694054925322335426729906⟩
def resval5Tail180 : Box := ⟨179965509813186979762860566698665080478737918223,64532680121124284813006836327785565357759626243⟩
def resval5Tail184 : Box := ⟨197874170638234917789282004901513049770094028700,62521252427750321241117753370609237290603634120⟩
def resval5Tail188 : Box := ⟨217564951453271659282027929868015950679839680641,59761340295271145338948573340143009887434441523⟩
def resval5Tail192 : Box := ⟨239215193919393138898359642660045184508225039209,56142808880481774673556540228591294751465637994⟩
def resval5Tail196 : Box := ⟨263019887255063447490484730925979613215582736425,51542245559339266897922463142061680793929168600⟩
def resval5Tail200 : Box := ⟨289193424373274807866285399294711151480568731312,45821487911972534085574028046723803081302310628⟩
def resval5Tail204 : Box := ⟨317971532774774959845673758691037863914117534097,38825995425202719336293913990237754526807888592⟩
def resval5Tail208 : Box := ⟨349613397587632294404364527647022001640820606375,30383048723461316371053228008821994386429808285⟩
def resval5Tail212 : Box := ⟨384403995898934744472535383034158486882544916070,20299758484119256090677246669458213648869119462⟩
def resval5Tail216 : Box := ⟨422657807959273315527218295521584147155169119095,8360772973577852981409955023847900099698472032⟩
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
def polyval5Tail5 : Box := ⟨5282742729382480949354541322703798033957488653494313960075,3799750984511518822831553381086092455249722542700592013174⟩
def polyval5Tail9 : Box := ⟨5808435015565747556894195928782337429048528587319149159102,3864598992371892049725402759378788416452808416766529792193⟩
def polyval5Tail13 : Box := ⟨6386441838616295629794885970274713344307995736863207886841,3915531290354995380415127039882319872465703398625101166976⟩
def polyval5Tail17 : Box := ⟨7021967061673625587833158513976286994835928455616235876835,3949838709377620239581885196899919307230338127473672213546⟩
def polyval5Tail21 : Box := ⟨7720734434170223449351472983973470576472048936841181483001,3964456390016625734936428354188184966185070508729925038582⟩
def polyval5Tail25 : Box := ⟨8489037285340716696385438033551706840676529181986270631022,3955922773825353292295800427507616903692864547850453531850⟩
def polyval5Tail29 : Box := ⟨9333795203856127597485086914111026642040385946293593488183,3920334164203752451039281750008771962789925266584577039445⟩
def polyval5Tail33 : Box := ⟨10262616357919672606813439581203522851538981680127873987351,3853294377838773599459640760291081466013111939101562866910⟩
def polyval5Tail37 : Box := ⟨11283866016936863856969142050496921306028070962533465068970,3749858972957948669196354182020167026430814693723600330174⟩
def polyval5Tail41 : Box := ⟨12406741891888540764796741584724614938828541076376345358629,3604473487878036898347309611519511492188384102147097228081⟩
def polyval5Tail45 : Box := ⟨13641356972947059267065282538990580743498103625914988512750,3410905065209824574351235121504970491036959533548499392829⟩
def polyval5Tail49 : Box := ⟨14998830610398509130625873883489147378845793596526660639241,3162166773062180075335212841751772609492319157806629756566⟩
def polyval5Tail53 : Box := ⟨16491388659175760446740707409329948186626916279551894902224,2850433864079061952903213333022710824833168561581099562120⟩
def polyval5Tail57 : Box := ⟨18132473588937006475810110015057346841263207855282482225873,2466951135488527163398368023721272025576650957995743378098⟩
def polyval5Tail61 : Box := ⟨19936865551377462463386536806636220319740054100552190776069,2001930467823482227024932544260663342627160877224388331461⟩
def polyval5Tail65 : Box := ⟨21920815495151770413774895068455139501724036289829874510973,1444437525797871773497909556367066833281821624035954202893⟩
def polyval5Tail69 : Box := ⟨24102191573257965958072081033939683858072522289188680326400,782266497429788331723294385500808733615770612743262314407⟩
def polyval5Tail73 : Box := ⟨26531250000000000000000000000000000000000000000000000000000,2⟩
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
def resval6 : Box := ⟨72624212488149322936344525338773372338660634370335144117,14008655649841570215391634720189442200079925112789422269⟩
def polyval6 : Box := ⟨15059377460373253215732446168293198406380156105498203972632,3729951313983062992720061881063891170512565220437608398081⟩
theorem cell6_lo : Holds Q cell6 (63/64:ℝ) := by norm_num [Holds,Q,cell6]
theorem cell6_hi : Holds Q cell6 (127/128:ℝ) := by norm_num [Holds,Q,cell6]
def resval6Tail4 : Box := ⟨-36915886601641814571344760825836361178933746847280405664,13625344383520233300047121968157251763833639616713885606⟩
def resval6Tail8 : Box := ⟨-38698280170012611073833121912462435492150305482203878452,13453751492652871441086467036046270542018280487114938929⟩
def resval6Tail12 : Box := ⟨-40566677652955027753888582986387783195243396311944432696,13247440325066799696453827267821409552278393379579341670⟩
def resval6Tail16 : Box := ⟨-42525283509688477442776174435232400600835587791599815318,13003891502874049629601090960701467176997578010331973055⟩
def resval6Tail20 : Box := ⟨-44578453109961621379594940983914574122354181803621317676,12720437839712147932795672670686480955306705294290269424⟩
def resval6Tail24 : Box := ⟨-46730752100084091672290036422443704635737085815868596612,12394255669612580128693903677095944839740579052317415992⟩
def resval6Tail28 : Box := ⟨-48986966561016091462556361936244429487898743388969049525,12022356408900744449193836793979859768914036782432012147⟩
def resval6Tail32 : Box := ⟨-51352113651211499015790919964290805431764989692295411276,11601577682683401898805351261472376851812197420331504354⟩
def resval6Tail36 : Box := ⟨-53831452763305062937513398187920491777642611925827710954,11128573993876246759703096103445897903638917262008192018⟩
def resval6Tail40 : Box := ⟨-56430497219457271639341703656527299391194091021712342594,10599806911759354665213842322310435939700841783259611189⟩
def resval6Tail44 : Box := ⟨-59155026531363924872358246368963557722035187833241072017,10011534755907869885607798713289277287980759845581439620⟩
def resval6Tail48 : Box := ⟨-62011099252193068785222767447919843096631529502049778818,9359801750148744670468632248457799368244480628610641949⟩
def resval6Tail52 : Box := ⟨-65005066449028228384169947145884716941077614918150207311,8640426619939053306931861205483840197700814147187894875⟩
def resval6Tail56 : Box := ⟨-68143585825776688996074335720907077721677600985302053834,7848990605244504898607521214412952259360672540445459812⟩
def resval6Tail60 : Box := ⟨-71433636527946229350752920414487034846826269940950806663,6980824859615062377731701274253795020227124457494177022⟩
def resval6Tail64 : Box := ⟨-74882534659523099240163045770104493803713577559919048372,6030997204470947602629318155526087437700065744551931410⟩
def resval6Tail68 : Box := ⟨-78497902506756017365233790118007609248602555013353941548,4994295077326260737022563351031637912258504519127455516⟩
def resval6Tail72 : Box := ⟨747975701333267431328930356492572074945982979705033177986,1007794999993412125966849468359675488793970293661408172⟩
def resval6Tail76 : Box := ⟨-478973128495086357013356802266146582870228633692728686,178953814406993443380685277184331673775346700255499840⟩
def resval6Tail80 : Box := ⟨-502074383215971976832865751848199101478629121990977637,176796751881420889837648586932752674946184047976804915⟩
def resval6Tail84 : Box := ⟨-526315110741835060710848047845004487991091872177743230,174191660057327486100627604753992967992251786933792791⟩
def resval6Tail88 : Box := ⟨-551726209653560031466350552085561935135197184654089211,171105726178636142703756954626622550485490028878130371⟩
def resval6Tail92 : Box := ⟨-578364185649098357519212652761580195603903504288441928,167504418680436605753892396135942174126285110924446744⟩
def resval6Tail96 : Box := ⟨-606288273764605205800055282523693629775593814467437912,163351178155845035279195347059250301158244903036455476⟩
def resval6Tail100 : Box := ⟨-635560568972512631477540103991481499461757424255173849,158607307935073314500008565699625170069403244534383792⟩
def resval6Tail104 : Box := ⟨-666246164261944582440253123453126522514763328626040733,153231859036024116676700042147214568352344036408311370⟩
def resval6Tail108 : Box := ⟨-698413295386409640802785812833347648490926444677619097,147181509182210520087534472295499589529634297391153637⟩
def resval6Tail112 : Box := ⟨-732133492600080297118834119404672228459393604909706313,140410435589501114166900379809894371843719588607047894⟩
def resval6Tail116 : Box := ⟨-767481739720074326212307508236661436670627125767720027,132870181208412302071507591290438985628483287986639073⟩
def resval6Tail120 : Box := ⟨-804536640868446060965720571697546496683864042869510106,124509514093147983404782256173205082113148817361978885⟩
def resval6Tail124 : Box := ⟨-843380595264672791442409093706706334568461892756678392,115274279552303199795524321412060015202084872764889620⟩
def resval6Tail128 : Box := ⟨-884099980457323491563953845850429152806313941635723370,105107244719065500518939213564624147425858013116465352⟩
def resval6Tail132 : Box := ⟨-926785344402371170555634251936292109638766972343462755,93947935160825739392084126538920401255086090743523561⟩
def resval6Tail136 : Box := ⟨-971531606822657851187103776183715400905242641361224065,81732463128567283245578431296175640977211372655418049⟩
def resval6Tail140 : Box := ⟨-1018438331805846594453430610503535742928303997692928855,68393342111883075512490270471063445880560360875147626⟩
def resval6Tail144 : Box := ⟨-1105219354638035475232596206869880692765160831301127893,51770995011974621824329244140141992878192983318088484⟩
def resval6Tail148 : Box := ⟨194258436878453204443184799043431999952686872953,62691368201631763550165719292744411157671002240⟩
def resval6Tail152 : Box := ⟨203585371000262179737748663729090718477360179663,61501623888723426445261042499374751079891153573⟩
def resval6Tail156 : Box := ⟨213414706036809282833226933368949433823939384862,60120615931414609899185552885670180398854989835⟩
def resval6Tail160 : Box := ⟨223718613512838384113824897182472544009392039465,58534284729964476171055692812401803760977675144⟩
def resval6Tail164 : Box := ⟨234520005493567856013029004995623956986138407117,56728298357243673575752377250539689464579094812⟩
def resval6Tail168 : Box := ⟨245842901102848827988664464541944823427878961681,54687492115665130555621310341303195920311710287⟩
def resval6Tail172 : Box := ⟨257712479135698953439474452464362105787234451683,52395823827463382442313817417546219864203073828⟩
def resval6Tail176 : Box := ⟨270155134048320270568919279461196483958264912870,49836326837866628948562971446737945810560875733⟩
def resval6Tail180 : Box := ⟨283198534651619061007596374487151734642777586687,46991060601622171331048548743860265890915348109⟩
def resval6Tail184 : Box := ⟨296871685638516726681826078465679179143389637646,43841058731486442750413046983553227913412015219⟩
def resval6Tail188 : Box := ⟨311204992081870006388870374814312114421598362230,40366274381286670776709413535469384575851283242⟩
def resval6Tail192 : Box := ⟨326230327046424965733499437865336526129144961573,36545522829855860033994788985579366921376207419⟩
def resval6Tail196 : Box := ⟨341981102465153892726316767782176874841959832113,32356421125528058128217343332449419631892412941⟩
def resval6Tail200 : Box := ⟨358492343437583260593876487468075430259845268587,27775324643941689502515977448773972116295289606⟩
def resval6Tail204 : Box := ⟨375800766115330444286988013807634413723244579921,22777260404619279665280773336806998486196315937⟩
def resval6Tail208 : Box := ⟨393944859348053268740452554482024611156220137809,17335856984154434622095597294469389145845574665⟩
def resval6Tail212 : Box := ⟨412964970296104807433765514610822079717741720844,11423270853497957916849836397648603599627383518⟩
def resval6Tail216 : Box := ⟨432904525785413346472018924562873185710165099318,5010022666194209686243432302568287320235715992⟩
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
def polyval6Tail5 : Box := ⟨11888856387563801457973179362973570472335300360338606668596,3658790826284193060466969262066533460115227102555295061240⟩
def polyval6Tail9 : Box := ⟨12462862103238770088413104397335882359178946714254900879038,3580287014689057677655908801894920128771591918149971389751⟩
def polyval6Tail13 : Box := ⟨13064583420150587067138712541526425888363669998572034043240,3489861186311519120071474978614963900598724857269711813562⟩
def polyval6Tail17 : Box := ⟨13695356534511343722387121154339724424487064161246847562222,3386678558275226587258017169244979330621347666346744716858⟩
def polyval6Tail21 : Box := ⟨14356584100346485297347866654923071643492521510553721649377,3269855798294998574278462054549989294056697904761671878641⟩
def polyval6Tail25 : Box := ⟨15049736493601672728342650078562020348081557234536943339995,3138458403130489832297925525574121521327912336082732454395⟩
def polyval6Tail29 : Box := ⟨15776355081664565045133885057622918472401945907916468765601,2991497956373496891331605879403146180400580385021670882901⟩
def polyval6Tail33 : Box := ⟨16538055650913172952068133466155965496184391099066551629746,2827929245184427233625183494004957185104069786285343235916⟩
def polyval6Tail37 : Box := ⟨17336531999750309089080542204532579102655774189209402301983,2646647228889161236782671444534028639641830618137378185678⟩
def polyval6Tail41 : Box := ⟨18173559705113874610770910906905162334050036117640236403153,2446483851999279515365756676354761658709452241713885607788⟩
def polyval6Tail45 : Box := ⟨19051000070838594631390094427259038998233806451690495747234,2226204693850490666539017186318707448181754060962931431629⟩
def polyval6Tail49 : Box := ⟨19970804266649199648421397187243943224430867795810605280016,1984505446667890401405919021096765554245604757065808813682⟩
def polyval6Tail53 : Box := ⟨20935017666988958420484655730890472914430148860936480981630,1720008213461534273775071780470349767963802090999323227043⟩
def polyval6Tail57 : Box := ⟨21945784399331842943381810740291289416889446570568416228448,1431257616730788529746448863777723175711612304082466634775⟩
def polyval6Tail61 : Box := ⟨23005352112092441779856329272897091010987644979651730410767,1116716708510067201999122552423587539550577975048250877074⟩
def polyval6Tail65 : Box := ⟨24116076972741440529070336493011803220144435259605607197130,774762671820325270464031393663944764922721520755735328569⟩
def polyval6Tail69 : Box := ⟨25280428952710130917709200762538321378092710305706709527730,403682299611333741208194830038569440960765039234847181078⟩
def polyval6Tail73 : Box := ⟨26531250000000000000000000000000000000000000000000000000000,2⟩
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
def resval7 : Box := ⟨50480171834120673484474685572315108839730759079289072346,22893905909825618199945285247125727776637589460438065574⟩
def polyval7 : Box := ⟨23710896635231914105254795316363522403691447289737902935406,6513510637308524564551464810522725422067044222855902813690⟩
theorem cell7_lo : Holds Q cell7 (127/128:ℝ) := by norm_num [Holds,Q,cell7]
theorem cell7_hi : Holds Q cell7 (1/1:ℝ) := by norm_num [Holds,Q,cell7]
def resval7Tail4 : Box := ⟨-58260390738532377272953124217512458436888788363333800225,21744791127403353288545929149111429170809588411048467324⟩
def resval7Tail8 : Box := ⟨-59179719561726628131624920783045553055450080853573174329,20825511329749023311209565899328152309867629697429069416⟩
def resval7Tail12 : Box := ⟨-60113503827000637877582966521698202855396262439788958762,19891727069796881699440758733961791064830887031042369136⟩
def resval7Tail16 : Box := ⟨-61062022070878970188247729185179558481752690301976147951,18943208825922870686068755710055417334837574497273039209⟩
def resval7Tail20 : Box := ⟨-62025506783211423254947122560370587442556634917064746647,17979724113590432862036605919359109868990700070043686102⟩
def resval7Tail24 : Box := ⟨-63004194116738107396483362369398989891674567073479699909,17001036780063748898425569583373320600615182398325025114⟩
def resval7Tail28 : Box := ⟨-63998323950398701234182191059570023170902034229813503604,16006906946403155066416460485808490021853869504052779789⟩
def resval7Tail32 : Box := ⟨-65008139948131846598831321277522744761742164696094040529,14997090948670009702171139164407125116269676612631947834⟩
def resval7Tail36 : Box := ⟨-66033889618597861009804059940592242684544208351904275466,13971341278203995291223721910553949337096589496710472761⟩
def resval7Tail40 : Box := ⟨-67075824375843786793625854054475242671162390892378470685,12929406520958069507323954069899156611068548299758698812⟩
def resval7Tail44 : Box := ⟨-68134199600925660995347863932002614681364511640821233953,11871031295876195305185198531574399839799064719892365424⟩
def resval7Tail48 : Box := ⟨-69209274704503110027434927771766567777628647916503355462,10795956192298746268987021426657777884370573252128886925⟩
def resval7Tail52 : Box := ⟨-70301313190421611095898194209358350713919673083731577277,9703917706380245098949755067759070649281547888447065201⟩
def resval7Tail56 : Box := ⟨-71410582720297998481987743538599458208197691643490508561,8594648176503850223121676164921215769714803629372260386⟩
def resval7Tail60 : Box := ⟨-72537355179123258020505356601363456868446892429790283393,7467875717676557047961420007844873023724831330651051995⟩
def resval7Tail64 : Box := ⟨-73681906739228631713397901932860238695731484943104714998,6323324154656581321255081109977587094814073831495239712⟩
def resval7Tail68 : Box := ⟨-74844471230103106065912736589067929111837152610193798742,5160709849957184568351864345209799121096904276444972180⟩
def resval7Tail72 : Box := ⟨747740883374753136393662698244706142629717064793433056782,1121990522618582579645991041148608791013793266406443437⟩
def resval7Tail76 : Box := ⟨-758584595494787973484252160942831189632254955231409867,285232379079617791089878810464428288228176136560480334⟩
def resval7Tail80 : Box := ⟨-770530780479679567151728616117895784837635021074317668,273262991095283184514482641621093023362747080080802849⟩
def resval7Tail84 : Box := ⟨-782688821311655757517044820146981127217729024766666789,261104949118785804032116092602620009384445140032476963⟩
def resval7Tail88 : Box := ⟨-795038702436395548830656566168845217927849939885058475,248755067993454528873296422374838014973300999125889308⟩
def resval7Tail92 : Box := ⟨-807583449720080928373052624809025248783044259480292235,236210320709767658902467592731797953610136934544718038⟩
def resval7Tail96 : Box := ⟨-820326137913976631328130989612782047768370505219399905,223467632515871942531442615750371248203051881408405356⟩
def resval7Tail100 : Box := ⟨-833269890285776352593526796918723033756103082292966203,210523880144072220908160296321157773293939711353965593⟩
def resval7Tail104 : Box := ⟨-846417879384554582373903188625096801893811458405676052,197375891045293991103159007085501547522851468098894646⟩
def resval7Tail108 : Box := ⟨-859773327818365671928802875896883291939244501308459394,184020442611482901544555239382468200753516570961971039⟩
def resval7Tail112 : Box := ⟨-873339509044113861889168000785299004933338374561271974,170454261385734711583560068192151449706937883921659525⟩
def resval7Tail116 : Box := ⟨-887119748169886513794596113665958944230364814972123360,156674022259962059680461778261851176979979931306773475⟩
def resval7Tail120 : Box := ⟨-901117422769947188013485595887922363302380257236500415,142676347659901385489529762472336170068964032294735467⟩
def resval7Tail124 : Box := ⟨-915335963712588325415546437651113774743802025923599214,128457806717260248696670999251137209550310285513300595⟩
def resval7Tail128 : Box := ⟨-929778856001046479474050568485673067468772112748557134,114014914428802130131516277555477833092279865098899190⟩
def resval7Tail132 : Box := ⟨-944449639627694028804305648085823675181989542001476113,99344130802161604457682980647833160278539397530111698⟩
def resval7Tail136 : Box := ⟨-959351910449049660814023051633150773332808510121198474,84441859987444019270302213020440858079465361663552705⟩
def resval7Tail140 : Box := ⟨-974489382144322420862854811304410631901218986125973540,69304444522234021776988386393538753100326756542457789⟩
def resval7Tail144 : Box := ⟨-1027185292610566548326476477481725190351913247561581568,51857597327883676790494125464492830234210989018855973⟩
def resval7Tail148 : Box := ⟨337082963392131235546784359386467361953488191778,107831640977978523775631795757232233836905992101⟩
def resval7Tail152 : Box := ⟨342351267302235951691892821736536081420417772774,102513145902985221372123229766739328297683035839⟩
def resval7Tail156 : Box := ⟨347753154621580808250389668562137622163260378444,97111257770434339627825497291173830920351876536⟩
def resval7Tail160 : Box := ⟨353240277988377963376448919866994347085593481773,91624134403400825997944244448839462104108000521⟩
def resval7Tail164 : Box := ⟨358813981512751614847613507490068710364023480893,86050430879026796638378315213267221543359214566⟩
def resval7Tail168 : Box := ⟨364475631324436162876327480674215460450212435382,80388781067342246318954404128537255321726554903⟩
def resval7Tail172 : Box := ⟨370226615109270275345858833915388882950925810749,74637797282508133806677824345551684555536015053⟩
def resval7Tail176 : Box := ⟨376068342449093896610586677745692195157783694249,68796069942684512539821491550065695716422585615⟩
def resval7Tail180 : Box := ⟨382002245167240253355333976678565324590548486478,62862167224538155794826876159677086010609921417⟩
def resval7Tail184 : Box := ⟨388029777679479663941590456057869719143122216773,56834634712298745208519833598969727000034182367⟩
def resval7Tail188 : Box := ⟨394152417350500817800138605918982804378203205547,50711995041277591349990799086017911169768786063⟩
def resval7Tail192 : Box := ⟨400371664856016897455024687014035787541298034276,44492747535761511695420673064918205404763173310⟩
def resval7Tail196 : Box := ⟨406689044550585296352685750942544213601184938868,38175367841193112802678073525448217684885988052⟩
def resval7Tail200 : Box := ⟨413106104841231086296747907778609494466606426691,31758307550547323037792669986479366306164595485⟩
def resval7Tail204 : Box := ⟨419624418566965832295350224672171016092728436067,25239993824812596626097782701367956062793508010⟩
def resval7Tail208 : Box := ⟨426245583384304227546566716254985544803065725535,18618829007482654535639059951337247117408505088⟩
def resval7Tail212 : Box := ⟨432971222183434458521326059831688481843711012971,11893190230655990780504900482222307999522795464⟩
def resval7Tail216 : Box := ⟨439804106634622035050917951416932820297711490338,5061343456384241832788418526261384009978008089⟩
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
def polyval7Tail5 : Box := ⟨20308633872060085405972100548136144981867893037760458239199,6194251786520771948879062856115935647208715439158065362878⟩
def polyval7Tail9 : Box := ⟨20629077620314797681473585470525923336930093673568207516351,5873806169955797813704616740415568491017716849393021532581⟩
def polyval7Tail13 : Box := ⟨20954579466347981151246061779916180909380553945983342493464,5548304323757053898815758819350448061375538111929838486951⟩
def polyval7Tail17 : Box := ⟨21285217337228493572419052068837981703275650138443953528556,5217666452876422433451047602324967871188394200774954070366⟩
def polyval7Tail21 : Box := ⟨21621072273039297807594711496796322190904490556406515492021,4881811517065617818051502886644579608135276705147684610581⟩
def polyval7Tail25 : Box := ⟨21962226592742753178173224469560989020456390354032976777378,4540657197362162443366791600013210952697888486132330004238⟩
def polyval7Tail29 : Box := ⟨22308763914194806236387666718996336839905357454103343559037,4194119875910109385025849723913128930909120531813614656840⟩
def polyval7Tail33 : Box := ⟨22660769174639841260191695339195678182045201364173835785063,3842114615465074361212079463049132194461120940857985811724⟩
def polyval7Tail37 : Box := ⟨23018328651529030588424512260430605931998600481221486437909,3484555138575885032977686250645851690156715729694863830354⟩
def polyval7Tail41 : Box := ⟨23381529983667173648645224630987222346991971411476589087774,3121353806437741972756752437889793937306203090446962803241⟩
def polyval7Tail45 : Box := ⟨23750462192693207482159179835470491908298731600483568702042,2752421597411708139244259786153049790087251730280474724298⟩
def polyval7Tail49 : Box := ⟨24125215704899653694797649179868338180690900581512997710550,2377668085205261926623175566589655010852788745888031401371⟩
def polyval7Tail53 : Box := ⟨24505882373396349839811915966758350544617259925382715449509,1997001416708565782003587443440613210847938434487160773394⟩
def polyval7Tail57 : Box := ⟨24892555500623897649584613920115850038268374265883348133780,1610328289481017996281888048054939919553846484361042313434⟩
def polyval7Tail61 : Box := ⟨25285329861222351740190473374307690538343344731171495892791,1217553928882568869956627994287872170170145757842051757228⟩
def polyval7Tail65 : Box := ⟨25684301725266104395186437385180384631319990691607046560648,818582064843672042767165450920916047510489298568026238724⟩
def polyval7Tail69 : Box := ⟨26089568927009306494351072212183488184783728059316604846471,413314904809782205198098305264925149580122774213072850019⟩
def polyval7Tail73 : Box := ⟨26531250000000000000000000000000000000000000000000000000000,2⟩
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
def pend : Box := ⟨1030218898330326963957727429555165187289311451356401732558160,5508942213474712078830571721060536447040156192073191008⟩
def zend : Box := ⟨1003712773761197055106757812500000000000000000000000000000000,3810881859274040351562500000000000000000000000000000002⟩
def betaquot : Box := ⟨428743680413269974802306194338818194926177523948278339600588,394758021148777186841301460907222555173510051073154347⟩
def crit : Box := ⟨104620036996276911464253591791304076821097563393925400485,14329076209827876027450914592821108073401595582106469817⟩
def subsonic : Box := ⟨606162991933457369232345702208164765652005708812805198882,7998079080960950749196648234876199130863860006354360510⟩
def pendTail4 : Box := ⟨26501313068037154822459010078629630319261585246587121036442,1537870667807399617686964846606097244607912726817855493⟩
def pendTail8 : Box := ⟨26501346099480023855034582008428218930500749550035511692644,1537689316219296321438847142686165626128158061727610867⟩
def pendTail12 : Box := ⟨26501346100807496743146031549542914207091672492331485475097,1537689296824552843301045783099691075955487335887768249⟩
def pendTail16 : Box := ⟨26501346100808104778353784839136553594776501231516227470008,1537689296809521438109877896030471009937057003754321630⟩
def pendTail20 : Box := ⟨26501346100808106141465944326395861603596786792146029728230,1537689296809469468182998656726582413775667291895527963⟩
def pendTail24 : Box := ⟨26501346100808106152317720611177521106419604917054983162059,1537689296809468838919679259053427405331461522017926725⟩
def pendTail28 : Box := ⟨26501346100808106152570468213752471875384763099592457535544,1537689296809468815960509374421214096888866829776511036⟩
def pendTail32 : Box := ⟨26501346100808106152585260783968268937638282686293024709688,1537689296809468813655622589499241755350695931154942831⟩
def pendTail36 : Box := ⟨26501346100808106152587013922628870304565904270731414114264,1537689296809468813051108058203161019029978276266533161⟩
def pendTail40 : Box := ⟨26501346100808106152587064902696534769064058649666461963011,1537689296809468812646570787978145537450057196843688024⟩
def pendTail44 : Box := ⟨26501346100808106152585609963914231084785936936101796037664,1537689296809468811956153577471469170444565078088493096⟩
def pendTail48 : Box := ⟨26501346100808106152573525592840744866424287671450874700533,1537689296809468808883553482741239166679667930901300610⟩
def pendTail52 : Box := ⟨26501346100808106152369784260922630469576966091527443921604,1537689296809468771444040570042011037198686106807025678⟩
def pendTail56 : Box := ⟨26501346100808106143255962932029370170024569132889289492308,1537689296809467410709467955448240050129506758480271575⟩
def pendTail60 : Box := ⟨26501346100808104823477520522723625273269865538377563682682,1537689296809296967877168813917754653955965643870818815⟩
def pendTail64 : Box := ⟨26501346100807289415927823735824606820840853358252560963278,1537689296726633254334265352658364930411987311947420256⟩
def pendTail68 : Box := ⟨26501346097203521995147939206245810610693622753430375526089,1537689014491733980257214246470446403076852035840324636⟩
def pendTail72 : Box := ⟨26500866214854197908404687695442214963171466019073485939257,1509777987919774357447094084560439939962080395118945771⟩
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
end SepticProfile.ExteriorCertificates.C08

end
end

end OAI
