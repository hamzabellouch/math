import OAI.MathematicalPhysics.Transonic.Certificates.BarrierData18

namespace OAI

section
noncomputable section
namespace SepticProfile.ExteriorCertificates.C18
open SepticProfile.ExteriorJet SepticProfile.FixedInterval
def cell0 : Box := ⟨250000000000000000000000000000000000000000000000000000000000,250000000000000000000000000000000000000000000000000000000002⟩
def resval0 : Box := ⟨113810029494539010314809080249297940302666190034561612027,323180694889150991290617003298196574766634700920392088⟩
def polyval0 : Box := ⟨3803091373988383207720845973132362045284724488530222399440,15027260817384008254550008601538774889482492489214897693⟩
theorem cell0_lo : Holds Q cell0 (0/1:ℝ) := by norm_num [Holds,Q,cell0]
theorem cell0_hi : Holds Q cell0 (1/2:ℝ) := by norm_num [Holds,Q,cell0]
def resval0Tail4 : Box := ⟨58293363037156650187614084259702151815295077469222,1741752734129168699889368287831468843559395271116⟩
def resval0Tail8 : Box := ⟨7030418947823167485594492568786107670802968286,380053205265239549693112635620742576946350931⟩
def resval0Tail12 : Box := ⟨6375838057266555542092760340079292079308285,522729752495145028088935130280697460945301⟩
def resval0Tail16 : Box := ⟨25453740395293888400007581804739714733534,26735077680226169419037614430091232349057⟩
def resval0Tail20 : Box := ⟨345638923385062561446846698838916302054,380456817290283727344452130364740892265638⟩
def resval0Tail24 : Box := ⟨13700949861999481914387144337291846676,6086421608722457663768389162128998148838181⟩
def resval0Tail28 : Box := ⟨1442655009594613206788739614050220418,97382697597723431935739055890684006787150467⟩
def resval0Tail32 : Box := ⟨379194909562077497099372216923970778,1558123154590616812523604643214392071542653650⟩
def resval0Tail36 : Box := ⟨-305364889725454889778065185337799772,24929970470730975593393627816111152453105524760⟩
def resval0Tail40 : Box := ⟨-140721642367720682826723076740542539987,398879527398470454106911177061615499040319928142⟩
def resval0Tail44 : Box := ⟨-36121592546480653662421150155146452231663,6382072404508501170986817680621703326809986788904⟩
def resval0Tail48 : Box := ⟨-9247491436943910303241971542300210111164907,102113149802592899926757160114367047905454772299287⟩
def resval0Tail52 : Box := ⟨-2367361143208610417897660492259893446964808592,1633808177440017882395013923679034040295666547118194⟩
def resval0Tail56 : Box := ⟨-606044520706046007090184193434304477519022265631,26140362672275517290048012658478324378508155331898546⟩
def resval0Tail60 : Box := ⟨-155147395296675585193151526687687329103043754070459,418100352066269582677173602631185871317980578819333881⟩
def resval0Tail64 : Box := ⟨-39717718023126739345917628891545087120330981171665175,6652370261969950492365580897060664296640927358023229014⟩
def resval0Tail68 : Box := ⟨-10167378991745791837351886455998313391933858784022797011,96905819617536424327636128830688250224344903222910319554⟩
def resval0Tail72 : Box := ⟨789170476435646400723205424893674551527293945268425498073,2469581772965982087649116967752130558027594353627016185⟩
def resval0Tail76 : Box := ⟨-26904488867221901699398122712806653613346718433893,596970864248733247057498234709160042867415640464⟩
def resval0Tail80 : Box := ⟨-1449676085250957705522671784838242671688201350,67262846219381020193498459072541628823159144⟩
def resval0Tail84 : Box := ⟨-817490903394958593942187070325672896379031,59636427706910466783042267663638041440993⟩
def resval0Tail88 : Box := ⟨-2255033636930819145347428405544175285187,398731476109990423709300788089379369575⟩
def resval0Tail92 : Box := ⟨-22391098699715621755715182332683178007,2579224688042807978872676580466184108024⟩
def resval0Tail96 : Box := ⟨-671819302355931423871229683103516402,41215055320485895230325235572746724735879⟩
def resval0Tail100 : Box := ⟨-54713508507632731818870890230180552,659438722489466853337664270184739989198167⟩
def resval0Tail104 : Box := ⟨-11339230559738624966375991741907505,10551019317937101256078817475492642558836804⟩
def resval0Tail108 : Box := ⟨-7614181669101704838526951220818852,168816309016537756773515656765586491885646625⟩
def resval0Tail112 : Box := ⟨-481631981078646971169346833103059369,2701060943825731389635083118732470657686964816⟩
def resval0Tail116 : Box := ⟨-121500829397189111129906835883354454373,43216974987328269343335797334374687190247878349⟩
def resval0Tail120 : Box := ⟨-31098882270479874401913549098105750290917,691471570642177783008414171504997921905486244248⟩
def resval0Tail124 : Box := ⟨-7961275186027101685559039164556760159402340,11063537666581481826805816180876537054219394118097⟩
def resval0Tail128 : Box := ⟨-2038085788278136918454641147731188157464038500,177014691959993658461865213569651273973884437189837⟩
def resval0Tail132 : Box := ⟨-521749954225947757756064245193121963345842284420,2831745930802184188555529019091167677803170429853144⟩
def resval0Tail136 : Box := ⟨-133568025453167500444246497286971836935892738193320,45182714893662180139439164323509960828506252427980039⟩
def resval0Tail140 : Box := ⟨-34193879953771077243988651293122312181441218645629755,690866901872705831100602653231797964525173330990045926⟩
def resval0Tail144 : Box := ⟨-9047245137894328543622668059101973871764452086641024484,2701491132224210066968246777168540943991708899611166222⟩
def resval0Tail148 : Box := ⟨60496880180630681972961637094397262122280749,1112853561929572159988496102970729181764757⟩
def resval0Tail152 : Box := ⟨1075167957444576535886580932883695453182,44523736614314158757370294028976848375⟩
def resval0Tail156 : Box := ⟨340560227800996678671745812445037854,22646493476121266704720404024732234⟩
def resval0Tail160 : Box := ⟨594695186790625368935138222924635,59123987316748981215231627082396⟩
def resval0Tail164 : Box := ⟨3957986485156988471764319161407,28842035670538155667211452754458⟩
def resval0Tail168 : Box := ⟨82162576937251925747544454704,452987215759472427197566346005621⟩
def resval0Tail172 : Box := ⟨4707649752934440530124998445,7247555100108849281417856513544235⟩
def resval0Tail176 : Box := ⟨690390809510784499362647564,115960862864658811846660482301178004⟩
def resval0Tail180 : Box := ⟨254626827592013054091079021,1855373802054004626504751595436380301⟩
def resval0Tail184 : Box := ⟨1906586860207237346801957398,29685980829985075276592998025705452891⟩
def resval0Tail188 : Box := ⟨433731040724373886158540738229,474975692873704940731511730761593281456⟩
def resval0Tail192 : Box := ⟨110923582043971846694269704848698,7599610981990373543951861834864289286756⟩
def resval0Tail196 : Box := ⟨28395884446868620023497395220582358,121593749090724257012824106256491987317710⟩
def resval0Tail200 : Box := ⟨7269339824321693677262687773346347020,1945493170446142075098622745841521161211892⟩
def resval0Tail204 : Box := ⟨1860950841883890470809542671658584522426,31126146085795282042530170302556352799164055⟩
def resval0Tail208 : Box := ⟨476403445922088016996540225801613643116212,497571709175277530871471587886401458979887646⟩
def resval0Tail212 : Box := ⟨121959461302800803286178595589916566764707231,7846810446825154487479401284748462655647710454⟩
def resval0Tail216 : Box := ⟨31232138793843416497398794422143333475307893543,96273613282765571075225542015089211162367088743⟩
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
def polyval0Tail5 : Box := ⟨2089634768977850263237876934004157635140759278018206,52171489851456379008123685338850571534218697391978⟩
def polyval0Tail9 : Box := ⟨201999440385129819796987930738425845030969695770,9959946652459189141180145929787364290259677730⟩
def polyval0Tail13 : Box := ⟨158506687229997052519452573295691785194599261,12119232452627458642480050876602810949476274⟩
def polyval0Tail17 : Box := ⟨554505083022163783665441653862904829846638,436055876488860227392547252393286324800278⟩
def polyval0Tail21 : Box := ⟨6616258840613169078647562216797876532186,6005639947700364206447245117435627899558168⟩
def polyval0Tail25 : Box := ⟨230192185794835725193363916475458820187,96074168258014208539380033287948198069749135⟩
def polyval0Tail29 : Box := ⟨21198553336339910762147291149936516573,1537185926889360449545023698423890944049902952⟩
def polyval0Tail33 : Box := ⟨4895177457530048118694135885585525998,24594974733562050568375621813397183943904504202⟩
def polyval0Tail37 : Box := ⟨8412510882703646372756503361661384007,393519595704233628710986116901910838396234004390⟩
def polyval0Tail41 : Box := ⟨1463450670513158482692674345254461425668,6296313529902010858614082657875756158297374649854⟩
def polyval0Tail45 : Box := ⟨373729826812204741318793062931622908963279,100741016128073112351571881767112692839851245275374⟩
def polyval0Tail49 : Box := ⟨95671935519444420603549069168256820615960882,1611856168356803686645517057324194970381088946779378⟩
def polyval0Tail53 : Box := ⟨24491993190872836377002232867837263857364897471,25789675732466540258794287168609206114026476042433549⟩
def polyval0Tail57 : Box := ⟨6269949859768171740473588263095177955256771541678,412628933641545876888605195957252070375348889965966146⟩
def polyval0Tail61 : Box := ⟨1605107160422079818487495105937620140257717454758835,6600558150318125731882385254525485241931990421345893986⟩
def polyval0Tail65 : Box := ⟨410907458662720497146802405875882651942333342355751894,105223704679509255650772965862759384860042426437774912396⟩
def polyval0Tail69 : Box := ⟨105192622989281235967610475215770619521366395094937042384,1584961343913593636405528680549315250754048095555855167115⟩
def polyval0Tail73 : Box := ⟨27156250000000000000000000000000000000000000000000000000000,2⟩
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
def resval1 : Box := ⟨113584135045478292163609431260663401668206350197189556014,246314173448198620544188049809076667290944407326957505⟩
def polyval1 : Box := ⟨3784937098766484540278370549073967743582334354710337332430,8843449559630445958011692890555153958328464349893624343⟩
theorem cell1_lo : Holds Q cell1 (1/2:ℝ) := by norm_num [Holds,Q,cell1]
theorem cell1_hi : Holds Q cell1 (3/4:ℝ) := by norm_num [Holds,Q,cell1]
def resval1Tail4 : Box := ⟨56603394699236661157969881702119069552201004366136,3090614916994117122694385163471366571851296247158⟩
def resval1Tail8 : Box := ⟨6626747581295287653484687509598746606891065920,6227308776620630282959277848902874105427223307977⟩
def resval1Tail12 : Box := ⟨-321397524328362294075236790670839331486151776,19680517153308941171950106137318691003995657396531⟩
def resval1Tail16 : Box := ⟨-2145052325934864191442840102962102061790273742,62199041533132151969020336362619622206441564054532⟩
def resval1Tail20 : Box := ⟨-14057965499976430330452198060362702898473684176,196572408347983962702798280408450866493877355865228⟩
def resval1Tail24 : Box := ⟨-92130284682280575156931849518147947359182721412,621218183003252584410154084187930554053873752843388⟩
def resval1Tail28 : Box := ⟨-603785033769300385051417672740765200650652316870,1963043624863933477078854159736903115837646960209098⟩
def resval1Tail32 : Box := ⟨-3956965597318002019403178196692435763407768780784,6202138552104066599827034929557574293630482338279777⟩
def resval1Tail36 : Box := ⟨-25932369738585064639075903454329729531553680990925,19588394204725050835746241576984010941774863744738069⟩
def resval1Tail40 : Box := ⟨-169950378318792034485117968280594689951913552115137,61821007684183563591348266699270202143549636937686454⟩
def resval1Tail44 : Box := ⟨-1113786799350036292444290212662123648919991850780314,194808253496953704556391989826307338791193015828568981⟩
def resval1Tail48 : Box := ⟨-7299313168220394931259301931760743155326065628793040,611911085792937099469500989970027898248791034177491465⟩
def resval1Tail52 : Box := ⟨-47836778779248995014868569781133818371525835986142458,1909173864851075697378509992012859741861536745288790469⟩
def resval1Tail56 : Box := ⟨-313503113407668273604103364398560339133409893672930350,5871616945473339349894538862607202823353119262323239575⟩
def resval1Tail60 : Box := ⟨-2054574004022881893372705321561202650750167356767558779,17493459762311740936715696370793506048155264791703337083⟩
def resval1Tail64 : Box := ⟨-13464856183857985030163804935358370936711718604060462816,48316583859653625176633324748137342084701005684728701147⟩
def resval1Tail68 : Box := ⟨-88243118039886925258519178535068882099926209591281671187,107016597665120054180429283052365168465846307015948143520⟩
def resval1Tail72 : Box := ⟨792021429039858755590729319601021890181137434369307286748,1519361291639787324381673226661824854110174164615165352⟩
def resval1Tail76 : Box := ⟨-26304859853875612984580155487030512167849207367219,400066173827541760848604928561759329453729074815⟩
def resval1Tail80 : Box := ⟨-1385619180855190107804603928014103918125134221,63233566473396985316090931621166164465429155519⟩
def resval1Tail84 : Box := ⟨-3524827212671172418271369109399211296285784,199715282230923055681635682213331058496382624067⟩
def resval1Tail88 : Box := ⟨-18099525623832077567358805955187270784964314,631189552978732974166963144976752703835806644352⟩
def resval1Tail92 : Box := ⟨-118603609136457605495642203683297222657718948,1994809279328989049507193530206556197395332474580⟩
def resval1Tail96 : Box := ⟨-777280483292370677515519989527827498298116199,6304179979110790331123363572369585387697458225772⟩
def resval1Tail100 : Box := ⟨-5093985371558352874344563692939424554801296293,19921684514084486043709149741630728692683315307471⟩
def resval1Tail104 : Box := ⟨-33383942530754725793845853953726361802229073229,62945076500194382948396768959544737893413061575382⟩
def resval1Tail108 : Box := ⟨-218785005769498765423424125089015882690137142354,198824250467534614111264788381944637254421347256292⟩
def resval1Tail112 : Box := ⟨-1433829413810963086911762215182961438588695591508,627640455538853876981230165023349024937493659189606⟩
def resval1Tail116 : Box := ⟨-9396744446351508280281389753975987149711463298069,1978788649971947239749716852861547294805553415658232⟩
def resval1Tail120 : Box := ⟨-61582504403609255726574553379812453650599700997883,6222065161906075710652548486576532216959871165157400⟩
def resval1Tail124 : Box := ⟨-403587100859495059467983550779706958866320684607160,19455842560563708111170550504285526105007629610139212⟩
def resval1Tail128 : Box := ⟨-2644948424192898375172778017231435475063505439377726,60120656431663241788403176333687271287652382548681038⟩
def resval1Tail132 : Box := ⟨-17333933992815468882118256596453177758447174658771298,181036372712132603426242806879040550400099122613194273⟩
def resval1Tail136 : Box := ⟨-113599669840239359719965276256375433544003033785671945,513348460012798216132160149381790953583021741471737605⟩
def resval1Tail140 : Box := ⟨-744487018019381722423078489086797979100886909794255842,1236978855661187294360015662415610901521566003981575720⟩
def resval1Tail144 : Box := ⟨-5001572518952273637292112997051584401388527314153779768,1360635173971535984692936208016650112238576534508991936⟩
def resval1Tail148 : Box := ⟨59600563170650525334757573901431512614363356,797630965870394967963209587744785831096999⟩
def resval1Tail152 : Box := ⟨1034089718422791658430975914658026005231,2942288388127462616855862082611132161369⟩
def resval1Tail156 : Box := ⟨433133002820156976022683789158972013,9207317126889541908370413135538301915747⟩
def resval1Tail160 : Box := ⟨739768677347973497633821231697526155,29099286125483661765275491535895741422982⟩
def resval1Tail164 : Box := ⟨4844571884332338207772808065348028469,91965605913380359625440427467318494439280⟩
def resval1Tail168 : Box := ⟨31749363154467314749191972823078309054,290640291665538856728526088439877780807856⟩
def resval1Tail172 : Box := ⟨208072625904365832818136319223065256575,918459118773198685331704351070210029632156⟩
def resval1Tail176 : Box := ⟨1363624761101359018448295486836096605397,2902078362870619477468761214078792549425267⟩
def resval1Tail180 : Box := ⟨8936651234350364318429991014172750757449,9167373828194296536741794785641213436562819⟩
def resval1Tail184 : Box := ⟨58567237529437428260923757686721297306396,28943105388812952263129024243209569617884960⟩
def resval1Tail188 : Box := ⟨383826247872920389159650013281687696412851,91275781065011668960605327550527196381699243⟩
def resval1Tail192 : Box := ⟨2515443698059970521707324622744615257162498,287174179414266632967524596484496831043069459⟩
def resval1Tail196 : Box := ⟨16485211819605832256987202056476150671352377,899077053819352331725483227208591280087844358⟩
def resval1Tail200 : Box := ⟨108037484180969345154505573685151092709545638,2785591404752034700071617792315400872564762531⟩
def resval1Tail204 : Box := ⟨708034456328473451017023146746154436824285980,8437261785237622173696550553090321230050252895⟩
def resval1Tail208 : Box := ⟨4640174613028306660752081973826981751910186684,24263477706022660267881791511487584486907045520⟩
def resval1Tail212 : Box := ⟨30409848439107223122146260566874272256284316991,60939966374168034096126446612909807503127766911⟩
def resval1Tail216 : Box := ⟨199298625590925617100107196361535483458591408558,89415638165376099424247122355736866082392404004⟩
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
def polyval1Tail5 : Box := ⟨2033347472943479928411898286403896584929023522579668,117925201918005360688096821785778029515959459928548⟩
def polyval1Tail9 : Box := ⟨194525499015471891269574682936647775801396705116,273253828979493622251535507305514815116466120845825⟩
def polyval1Tail13 : Box := ⟨15463963859795142913898203295423798170533716063,863593100123987420238311502265762022290686181357622⟩
def polyval1Tail17 : Box := ⟨100379254295979722775098733149762448773571969586,2729328693543152544733813592188489896919849767154197⟩
def polyval1Tail21 : Box := ⟨657842190620364638253798750018088754653460157650,8625685892480948433682669416441393574287684524591423⟩
def polyval1Tail25 : Box := ⟨4311234542358263314282915737515982183293634764576,27259194889833488749318349696325595519663184278912260⟩
def polyval1Tail29 : Box := ⟨28254106695522697721906418520868620522787082857976,86137888706146050064313571187196872069086037301832269⟩
def polyval1Tail33 : Box := ⟨185166113639665991916089296638536490748141503746898,272142396356575622081927804711650026130691777617779277⟩
def polyval1Tail37 : Box := ⟨1213504642348891492134930409449528938358769502444625,859476075510430279626151137440655559971593629242072577⟩
def polyval1Tail41 : Box := ⟨7952824024097684226625308761299923447064363685808047,2712251281150117962958517400349103186047640111319419710⟩
def polyval1Tail45 : Box := ⟨52119627524326574063551294908630161264121596761390099,8545068655495416703479564819746117173009216550530197200⟩
def polyval1Tail49 : Box := ⟨341571190943426645608752744705153182562061754350200809,26829789308476996574405466812318630636043426184551746239⟩
def polyval1Tail53 : Box := ⟨2238520956966841766983183124647921964038356833566642912,83636396177003879343137499086194709007095211482416257324⟩
def polyval1Tail57 : Box := ⟨14670370943577965944786906383987832485971461876409430376,256736774566255482598053171314925912107044838329014544663⟩
def polyval1Tail61 : Box := ⟨96143743015849138524233241101166882615371258457699430783,761636865015242785452901813760303449520908161411364627799⟩
def polyval1Tail65 : Box := ⟨630087634245689760038944362001368930513307615063849941806,2080922682508319633027707615186233599043156165551218783716⟩
def polyval1Tail69 : Box := ⟨4129342469422566732108260762921941112962838282775859466713,4438789023447018248902738192861412784468886425544819927653⟩
def polyval1Tail73 : Box := ⟨27156250000000000000000000000000000000000000000000000000000,2⟩
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
def resval2 : Box := ⟨113472923407136349584154322207171230570763972266996480438,228144219333393036964382221384595384061152375340337891⟩
def polyval2 : Box := ⟨3775966847294450393655340784540244009866428243552245362025,7559560090696596652305990651043044161715024444875501417⟩
theorem cell2_lo : Holds Q cell2 (3/4:ℝ) := by norm_num [Holds,Q,cell2]
theorem cell2_hi : Holds Q cell2 (7/8:ℝ) := by norm_num [Holds,Q,cell2]
def resval2Tail4 : Box := ⟨-137765834912682558727254396509277252968526178210080,34203439788199112305754817469260628505450885116491041⟩
def resval2Tail8 : Box := ⟨-444150971882806115128192637297093393679297264040249,58234311336705591429012673465073245541099896365158172⟩
def resval2Tail12 : Box := ⟨-1019162663584884297307693914231147373733675745938397,99083714323792532641488213057873038706501788536655828⟩
def resval2Tail16 : Box := ⟨-2338568141672074820722922266360118201948867352260203,168432520639180549881178948524566034288820555856388769⟩
def resval2Tail20 : Box := ⟨-5366072677219055736655162592905175058360468100431136,285961865534549968843128027070423651524349593645101235⟩
def resval2Tail24 : Box := ⟨-12312977100740399095099375021703003555301084899554670,484679623863610704190737913742428848576055252615767420⟩
def resval2Tail28 : Box := ⟨-28253326818883214137695348630996086248432031516648018,819594109061992319910499100654180658157904118017924777⟩
def resval2Tail32 : Box := ⟨-64830013879147452324504055095470369656090294293917554,1381560280734790986143527943756809830739781807734640389⟩
def resval2Tail36 : Box := ⟨-148758789593634937461646117128975254357141594315840663,2318719197386245047753394315608144378834352030330268599⟩
def resval2Tail40 : Box := ⟨-341341550884368868927685853624918112239822889956907591,3868066960015084866750035848431664412436596406823776382⟩
def resval2Tail44 : Box := ⟨-783241478896327095850738926147517688090788231764170113,6397823602588122091901999903858190276904511117923772936⟩
def resval2Tail48 : Box := ⟨-1797223961379142620172153881645031785035583799377105942,10453356036022066815211505745841619881826149449001351754⟩
def resval2Tail52 : Box := ⟨-4123905659218636787877854126581894324007757794694326095,16775042974415412915465812719366779798858234890106614176⟩
def resval2Tail56 : Box := ⟨-9462703731751413820327345392874527671249802950129556552,26189979984768797599023778107348514666802074855300474486⟩
def resval2Tail60 : Box := ⟨-21713096591993555190741416751572505785337486056442139828,39108807824022872679815920193780865398343816630799206225⟩
def resval2Tail64 : Box := ⟨-49822817760183209047287996562536309205632541280662823060,53936665984498487830708542968951039813311066707189103002⟩
def resval2Tail68 : Box := ⟨-114323186054150150559499903206445440723504501820800943589,62685787580562430273725495990880122862815112377807583895⟩
def resval2Tail72 : Box := ⟨793445218117651197261417820446536758390430601759301469277,1044679810076263846803737751294038771175811036344300786⟩
def resval2Tail76 : Box := ⟨-28140555911057002630332298604430071927207150186726,404929904169821487174052999409459959322639059001513⟩
def resval2Tail80 : Box := ⟨-4873143692559768196775747522609098508877356929757,689421988657523851989511581739242345155448036174630⟩
def resval2Tail84 : Box := ⟨-11178794379050916029264420172539274446057772167704,1173255724461458924498060557453608746444621707282947⟩
def resval2Tail88 : Box := ⟨-25650832255325832945774751979981810777932608209900,1994942164878705427606356044205180135013387059970428⟩
def resval2Tail92 : Box := ⟨-58858336282225782705136397927700700669375558595777,3388184111136706889141724840184394352835333397665190⟩
def resval2Tail96 : Box := ⟨-135056192941099133063056943828205618273931951408781,5745446041389542542201773372788692454502534611290716⟩
def resval2Tail100 : Box := ⟨-309899606476938430319909290898995102384029134160506,9721977591281623043484977297679549297621576789957677⟩
def resval2Tail104 : Box := ⟨-711094870980450069750742096266587948285265967198828,16402844738356937532318066987798194637454189126418079⟩
def resval2Tail108 : Box := ⟨-1631676533194733214519307464102616208811042255430958,27563948889481626464667552746071983196693028104245252⟩
def resval2Tail112 : Box := ⟨-3744040939723750422500000122812662761629562700057330,46062407094962784037031658223773280276021093494751242⟩
def resval2Tail116 : Box := ⟨-8591067085386915996035962630499928867424228498471972,76376534393195360201962470617184207281913787533044483⟩
def resval2Tail120 : Box := ⟨-19713041297850808045109091191148403592717420929331773,125237935651867227538483390779735932092902751173543050⟩
def resval2Tail124 : Box := ⟨-45233495833337439246609538546314540835655368345335661,202046471507789206735986494541364172589646783777275708⟩
def resval2Tail128 : Box := ⟨-103792667726396319956677607443600700676886605978440580,318056039574417901920971110509238290875523695683120568⟩
def resval2Tail132 : Box := ⟨-238162398799681535400905529767171223640823143062157214,481492871964241177712118451308451798352747887930385941⟩
def resval2Tail136 : Box := ⟨-546486851591725442464160200699398982836506339638112078,681213268812969916033452024869267897266893221453972090⟩
def resval2Tail140 : Box := ⟨-1253967553910559269035786712379566531535748042539548973,840434806734724173327888222724021457006121261676625963⟩
def resval2Tail144 : Box := ⟨-2972225207824891537567263390211590264189978437295727184,686595530225208401971359118482934147702442698752441387⟩
def resval2Tail148 : Box := ⟨59415976705618140026278244255031916312926411,45204313258834560041723597600163237956111685⟩
def resval2Tail152 : Box := ⟨573480131570021624587614285069087895699279,75944817182317223387484945096576651918634493⟩
def resval2Tail156 : Box := ⟨1313577794732123190194321983993299599664037,129221515691458337951823451410935826668652105⟩
def resval2Tail160 : Box := ⟨3014131647279741470427196562774799304114284,219672974405208353295184846215817800935411738⟩
def resval2Tail164 : Box := ⟨6916219026008066650957826477469801341628217,372978152647800421321843761391744704421626290⟩
def resval2Tail168 : Box := ⟨15869939080853117115710585361675426217275890,632213087314776037144927530209227767950713905⟩
def resval2Tail172 : Box := ⟨36415122985987380847582534005728246726257349,1069185908299517300163833757315297078670935362⟩
def resval2Tail176 : Box := ⟨83558051189022399918782282500830976785651026,1802548497809489536207233908660018351387101081⟩
def resval2Tail180 : Box := ⟨191732097710996532762430516757049838991452902,3025882406536360771888708116790723444895967820⟩
def resval2Tail184 : Box := ⟨439947997464650003979468481393775773136388551,5049160294662453502621325360728612031559560856⟩
def resval2Tail188 : Box := ⟨1009503587473943582487295269407272479191160902,8354672824251427497452636618324626044739623216⟩
def resval2Tail192 : Box := ⟨2316404436423527419988219963775096719969468646,13658467109776855730702149333559395883170112417⟩
def resval2Tail196 : Box := ⟨5315215893892100885440676217564927606583979832,21937209700958698536612998352862842855548656347⟩
def resval2Tail200 : Box := ⟨12196281251430718082126778900003815686214992703,34295153665899092630698688789966133451068882221⟩
def resval2Tail204 : Box := ⟨27985556811517990488985999879035861568375039375,51326778640953076877718123222289447219747907016⟩
def resval2Tail208 : Box := ⟨64215589482176375206333266878696724069401983445,71087753297240456697403174543323214384166152288⟩
def resval2Tail212 : Box := ⟨147348932967073742769548866775185223767153357405,83472596472933351812277280270783537657264577472⟩
def resval2Tail216 : Box := ⟨338110125721283900063033063069607272321317362780,55664446379660084188572303754243673484964546375⟩
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
def polyval2Tail5 : Box := ⟨21990969856714598566436473870893642061368758519145928,3065769264812950269335107370276236709607275259408769131⟩
def polyval2Tail9 : Box := ⟨45856406004212279224955484231090560115533032079949423,5218299552819838919006806518196675924086762514507686770⟩
def polyval2Tail13 : Box := ⟨105221565392129122675555720558106416333304191903621703,8875195775538067545218784673926009201011464072437313703⟩
def polyval2Tail17 : Box := ⟨241441143525035900879624747184992822042691545088867052,15078754369953972587480984113104360920192187458416613067⟩
def polyval2Tail21 : Box := ⟨554010251112545148713692928939263720348508068243224934,25581566934730035215275393203886281700500739745376661236⟩
def polyval2Tail25 : Box := ⟨1271230552743650510943118752981811309444210982297800119,43314910285744973592692537066764786038859304456164906048⟩
def polyval2Tail29 : Box := ⟨2916962483967923681308737985412275142909892059542091127,73145025385440407673476438815763360678228443507727011357⟩
def polyval2Tail33 : Box := ⟨6693254905266686930239278909467021766357796041722259684,123065138394648567200034141043503663838242651907728215801⟩
def polyval2Tail37 : Box := ⟨15358326160553117694769656699007775909487995655789973996,206003764200318552819947764421588495619193610862985811781⟩
def polyval2Tail41 : Box := ⟨35241177243724278603299942180771621883575587968249431898,342392776158245884838866580333954624366806784107279458184⟩
def polyval2Tail45 : Box := ⟨80864318190704608472992101553402863575325243461726364455,563362534426733871103337988835603270615888601074974187465⟩
def polyval2Tail49 : Box := ⟨185551064631701173698038176061348279205049566504946422183,913471504431617448718384179779171164009921826592662440859⟩
def polyval2Tail53 : Box := ⟨425765014239808415247292779571864290819497581773922442149,1449118968635390701546792585282227560410216937698668849849⟩
def polyval2Tail57 : Box := ⟨976959349225170202120642448833889757226445779853443521244,2221509952672712227658229499668095608151334530868207755496⟩
def polyval2Tail61 : Box := ⟨2241728507784081450580037692781108431222768709180415155158,3214718914362422243806174899615697366375962617056466194037⟩
def polyval2Tail65 : Box := ⟨5143864692641376933954155343784614560674724097458687381771,4164593716830201681658824282921349074534086992398679331284⟩
def polyval2Tail69 : Box := ⟨11803099326786534845768855877754741802464622333587986340768,4076719873081882995797645191018259450303184516004134897771⟩
def polyval2Tail73 : Box := ⟨27156250000000000000000000000000000000000000000000000000000,2⟩
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
def resval3 : Box := ⟨113290148392887718217293973920702112238383713742447815625,1743981233842642793673370836390851448153634993733143622⟩
def polyval3 : Box := ⟨3794122345042041208388095851961403445109129537810193399575,239936981860156408277755785969760578229006475573444835202⟩
theorem cell3_lo : Holds Q cell3 (7/8:ℝ) := by norm_num [Holds,Q,cell3]
theorem cell3_hi : Holds Q cell3 (15/16:ℝ) := by norm_num [Holds,Q,cell3]
def resval3Tail4 : Box := ⟨-189321137864108275593267576444998060199619456960192309,1990306099717059821207364675038547845185340852067784269⟩
def resval3Tail8 : Box := ⟨-280759270838585490847188304546995659311951233907126594,2540922505734749108455161684726831296448945714757721695⟩
def resval3Tail12 : Box := ⟨-416238298389779406355874368534314237167514941790531512,3236536759832157471771463596815451820428217784602921350⟩
def resval3Tail16 : Box := ⟨-617092060974679341671068275094810328789166434362510079,4111565049464604712615388386943507255821987798592275052⟩
def resval3Tail20 : Box := ⟨-914866827934876956362714495601474472488419531064324016,5206560774825621924167755557347952800712739602610946292⟩
def resval3Tail24 : Box := ⟨-1356331357648009524847923581266831192356436147037801946,6568090950984327686774390616790808823431869727121714640⟩
def resval3Tail28 : Box := ⟨-2010822444936481039150513523917561908627359807903130719,8247645513948039495816127348832083868030687438012067769⟩
def resval3Tail32 : Box := ⟨-2981135017088986616393802661999312649334823593180326166,10298844363720019562909720651244589400255721145323525071⟩
def resval3Tail36 : Box := ⟨-4419667192642105797321685552648016651683636939523037051,12771774361939603416958508984183886264126493295279632198⟩
def resval3Tail40 : Box := ⟨-6552356059602744494103548890668946077106993627717525420,15702622976862774420714340504401814438057988146671483610⟩
def resval3Tail44 : Box := ⟨-9714163546813794531870159023125404229545133066895505877,19095758549656412827467411994918269829391911076504431573⟩
def resval3Tail48 : Box := ⟨-14401685829626161893832984913831996624970211517883847637,22893860926211300014569964600662034418554151280650148874⟩
def resval3Tail52 : Box := ⟨-21351149147914452960263477869986715077249582700737745068,26929363487948537524947326366774724745785719614836578784⟩
def resval3Tail56 : Box := ⟨-31654042126005837897501579035672964186028810225775595648,30846929253824604460466422666759007402980801832560407500⟩
def resval3Tail60 : Box := ⟨-46928545905115051735035354726114582286009555547184978974,33981353558555901801077724145775198679797705924056491090⟩
def resval3Tail64 : Box := ⟨-69573687044325917390991733544856745100186569956609243311,35167274356435082334734973721528599780714804020327121751⟩
def resval3Tail68 : Box := ⟨-103146014704026982488439597362605084164824228430449833284,32445051450771112177761160014990216821863414559656774124⟩
def resval3Tail72 : Box := ⟨794155139491105360895154361701405668234857590479422777444,826662060666588337447949470008576586082895862455197381⟩
def resval3Tail76 : Box := ⟨-2342526786829495978204504565895360293139148186847912,25304943021840700004436659421762186186552258359559067⟩
def resval3Tail80 : Box := ⟨-3434539808723993079826700198847087589450936599558450,32322516747890032908226985306813704236661105221146963⟩
def resval3Tail84 : Box := ⟨-5091858269907240649430316785108306209258470573458026,41197018170500211957769217146796214393460042164304083⟩
def resval3Tail88 : Box := ⟨-7548909664567139566523408774107025071501995529359977,52373812436177814342468887510612493519539692045567679⟩
def resval3Tail92 : Box := ⟨-11191599237687914396705474221170630891066603501939683,66380657860470959600913482298530950386915567897741067⟩
def resval3Tail96 : Box := ⟨-16592050913650760721983082992178747635667828747903291,83828204714693708414914246881326507212518728331303679⟩
def resval3Tail100 : Box := ⟨-24598464229679942701015919047535124410241087239263427,105399399925563180166418469122489353298014300441657269⟩
def resval3Tail104 : Box := ⟨-36468333276450060952684024489022698184576348982937323,131818877099411930113992602501589060072423228800877747⟩
def resval3Tail108 : Box := ⟨-54065949790375959636777594215751999689681008083952724,163788284662809056583313567690625535353748811939791098⟩
def resval3Tail112 : Box := ⟨-80155210400665735755969882875380242813009638088041475,201865433730177389634872773212504147215523349194723140⟩
def resval3Tail116 : Box := ⟨-118833716586602035881473231604238605739328773608920366,246252800623451002455796364814643335032745084672839267⟩
def resval3Tail120 : Box := ⟨-176176347453858956237537692422359687496270336675426700,296442121521509654595114579157261021507914346292790951⟩
def resval3Tail124 : Box := ⟨-261189385417928107798114291340702541424739655570797716,350633310538017716352067413515099970645004094951852622⟩
def resval3Tail128 : Box := ⟨-387225050586668453270928863554493392339211927687630598,404802844764815392606714236775477691527281733935729351⟩
def resval3Tail132 : Box := ⟨-574078611816208882169169506057354104687401864280763472,451231810895015137023644337052988661314669881126603188⟩
def resval3Tail136 : Box := ⟨-851097448506018701914827875315537141121566344026300691,476206133985872422083861310564435358969736741691631503⟩
def resval3Tail140 : Box := ⟨-1261790533363893501666471592511878539326223317073182259,456454898774363493110705397546390537926004423068168227⟩
def resval3Tail144 : Box := ⟨-1955922464535500035008169109821065769061012207354828661,348671856130272563220115083208569797608958754484913930⟩
def resval3Tail148 : Box := ⟨580622662679951216662462440071069037308097895,5096902139391230233543833626963938816812465905⟩
def resval3Tail152 : Box := ⟨773400091498695664283984637463870881105687533,6499523418883774770611881508704360660080562373⟩
def resval3Tail156 : Box := ⟨1146599046520257097403205853624891781183830016,8268477468918381501747737434082280912908797718⟩
def resval3Tail160 : Box := ⟨1699884828636280223313700393793664550174152885,10488292050284731803533396551609210478629119207⟩
def resval3Tail164 : Box := ⟨2520155969228041584615884038528509561822443794,13257905461624957016490281703754447577986409912⟩
def resval3Tail168 : Box := ⟨3736244951567000290650167235489474842542317762,16689059422405975447655737189257679807603527157⟩
def resval3Tail172 : Box := ⟨5539151746384137041541600793236775358431989328,20902186474903624611195085759842622747337579491⟩
def resval3Tail176 : Box := ⟨8212042429552741949925775069458421536319998657,26017281850354709851494206205252122558077123012⟩
def resval3Tail180 : Box := ⟨12174723487002614155454478625483694893814940052,32136446804513726807108893578678321446883604152⟩
def resval3Tail184 : Box := ⟨18049576978749963791746022428649970880870583205,39312928823221688974991930792983733720321292374⟩
def resval3Tail188 : Box := ⟨26759312395030719096001926459433607339252165657,47498646720781907782459419262437648824114521854⟩
def resval3Tail192 : Box := ⟨39671888194270355498641254372775294833226824598,56457881852423892701681229222707185863299153523⟩
def resval3Tail196 : Box := ⟨58815364523004622345478080473268585467565584028,65628301843023115938739412712808034547733563813⟩
def resval3Tail200 : Box := ⟨87196432068829920845177449152130155094948210669,73900656700829217497033081432226885887262681961⟩
def resval3Tail204 : Box := ⟨129272645459167493666198790879473221894389473001,79273701397294410036627799772611244830040856906⟩
def resval3Tail208 : Box := ⟨191652530585453412737845531731630819278485505900,78318696823657751011173755382480842850304079315⟩
def resval3Tail212 : Box := ⟨284133525373846251212498873949620764582803597458,65354560802530766688461707223810466764740244593⟩
def resval3Tail216 : Box := ⟨421244044535392459948440519806586038347510737612,31184687263186578428416978804454041736137608508⟩
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
def polyval3Tail5 : Box := ⟨33551538015826773374748035638030756723219178043180073876,302907284608381544078358113134073230331382954876127375249⟩
def polyval3Tail9 : Box := ⟨49738713991185166464881882133372635124786869840754697583,385817519583661521570138349037859492071826232875349037915⟩
def polyval3Tail13 : Box := ⟨73739887778154128372765753153555439220095601271396251288,490104325778518430044206797160678022954462130176765738594⟩
def polyval3Tail17 : Box := ⟨109322711293982447335883520578812800426742032591210809150,620595202377934668373338966311058491864916773492110827185⟩
def polyval3Tail21 : Box := ⟨162075852904006256639223541654793741574838174395714407225,782830821474319251329188549131864247095781713928817925541⟩
def polyval3Tail25 : Box := ⟨240284765934149594081887519701916014062585952993783046586,982933087143538112283435823179256035508860550410411461653⟩
def polyval3Tail29 : Box := ⟨356233008838307327056473910539695788194096927141593163897,1227269316481185838628713323458898640050724090451239813251⟩
def polyval3Tail33 : Box := ⟨528131511345048069666183445421853704493359991811489280774,1521772851956449295378799451130778555773769206720719182209⟩
def polyval3Tail37 : Box := ⟨782978798582381153595214760040800828860270163743718372995,1870700852841360699548938651435514517956142003282237235157⟩
def polyval3Tail41 : Box := ⟨1160801402416180981126266553237251603402089987053919935200,2274488466931104867518114522231641630960183300322642609654⟩
def polyval3Tail45 : Box := ⟨1720940462616625341933293780073786306673332771474186029684,2726173747310164295140991642713083770508550957820907897117⟩
def polyval3Tail49 : Box := ⟨2551371896783160490063291510913593305993009908014347036284,3205587646165226387112688335543550802121141171810901085740⟩
def polyval3Tail53 : Box := ⟨3782523972849969523727331047011504736531395401773219231380,3670080483577990622928384728863076128117790389014712564368⟩
def polyval3Tail57 : Box := ⟨5607762483871515968896312145219450180495477413021061918376,4039919208107996107041728369143404992115286361096401725068⟩
def polyval3Tail61 : Box := ⟨8313760944077485125663953260646277829252215700995586390162,4175532238452290360424335237557745435824366303404073554385⟩
def polyval3Tail65 : Box := ⟨12325525775053850828393996902026455491284204432603434254215,3842342235037060454813901575910240820116889021613681359872⟩
def polyval3Tail69 : Box := ⟨18273148282988711717411254516637012926437106553408702626499,2656775725554638480249917839411553746815923143241318035004⟩
def polyval3Tail73 : Box := ⟨27156250000000000000000000000000000000000000000000000000000,2⟩
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
def resval4 : Box := ⟨110040213766091297564597452291414936156156272182252017247,8873534813852317221950575946084611908743642279182033789⟩
def polyval4 : Box := ⟨4623667393342434050918835506091797069883199848361226999066,1902769584767532061301497454681846634972310030770748052557⟩
theorem cell4_lo : Holds Q cell4 (15/16:ℝ) := by norm_num [Holds,Q,cell4]
theorem cell4_hi : Holds Q cell4 (31/32:ℝ) := by norm_num [Holds,Q,cell4]
def resval4Tail4 : Box := ⟨-4059457248935701228159271772643987758869095824837762042,9616289455398681898800961635758049326690524390049186535⟩
def resval4Tail8 : Box := ⟨-4918972953048335762507861914923539946952243524205233448,10608683773661658918849128395213008129585670297774610575⟩
def resval4Tail12 : Box := ⟨-5960394304593483089412136449162471472762901901679796377,11669879599785948762583999704762729323532137154740413506⟩
def resval4Tail16 : Box := ⟨-7222300378389998107399018695344558310993883259461783066,12795308414008036428808380828274693192915305761079257758⟩
def resval4Tail20 : Box := ⟨-8751371149295379269325682712418137080193023572512313823,13976844188631514257469823403062498314939738824877123711⟩
def resval4Tail24 : Box := ⟨-10604169444665501379204984184257025982126528082940907123,15201698668980025436172255185221062717055959328212090472⟩
def resval4Tail28 : Box := ⟨-12849233302170172584473466769804171131832024055092927335,16451035953357283678054319050517550140388824641039006985⟩
def resval4Tail32 : Box := ⟨-15569611303849455892264651651753901993623763356948703064,17698239816898158919585964700377492772555727357269077766⟩
def resval4Tail36 : Box := ⟨-18865934678920836443894453403727920088854115109786157907,18906752955457863064862831514994028955781153906122618503⟩
def resval4Tail40 : Box := ⟨-22860139817447385097036722726453033511010169544383454225,20027389225104196530231377364844447547059465212639548264⟩
def resval4Tail44 : Box := ⟨-27699978896732625226636547421473247805089068809255320069,20994997885952952313821566218192210127323453248782032793⟩
def resval4Tail48 : Box := ⟨-33564485475885859702113103677821347329845258116981622273,21724331968310116510712372904019286825718908719488461384⟩
def resval4Tail52 : Box := ⟨-40670597239835403070675384247031798270197531137842023258,22104940122460895301553349543389324089950370983658526417⟩
def resval4Tail56 : Box := ⟨-49281180878916792793295607638528050975751945730818240250,21994861425705613335010569803163084077513401781105554695⟩
def resval4Tail60 : Box := ⟨-59714755957446002681315493456874953660876876945418623325,21212854065074043779145333281352762495222011098835164377⟩
def resval4Tail64 : Box := ⟨-72357277466866189534668837304016220596614407108086439698,19528829726140359482607227513768310551107332946851500948⟩
def resval4Tail68 : Box := ⟨-87676302314640188238408690365046986888706395981255372587,16652090858853058513438193159002793565804552240455534504⟩
def resval4Tail72 : Box := ⟨794469258565329424290737346177159718799286737662215927054,801336700578887119310495913965224650619211951138053596⟩
def resval4Tail76 : Box := ⟨-52230450746280726478170972551282890263063516893948722,126642922557778577496609053901586654020460264497301605⟩
def resval4Tail80 : Box := ⟨-63257161823199162889575750967607030495324923050723980,139808190288983281546327707012845046163429404438764560⟩
def resval4Tail84 : Box := ⟨-76649662890672783355633703258760667828609465697520900,153912991604580548036937555546370157184914323399939658⟩
def resval4Tail88 : Box := ⟨-92877561618100041888657468650657484144137205074869129,168905836917770233424519215439884379844638824575524325⟩
def resval4Tail92 : Box := ⟨-112541153175176731476844086715456243824416350575366440,184690624882005153604949430946644550284171210839452648⟩
def resval4Tail96 : Box := ⟨-136367825956474985230008349051406214977489845473548567,201112435897979361851575794302686398197677834346015003⟩
def resval4Tail100 : Box := ⟨-165238967537052275675214584489996408050436640219626404,217939869819430490723294815460828962100640511757464765⟩
def resval4Tail104 : Box := ⟨-200222568638922982846111154038699453454871967342048407,234842938869743602126412124209915121346071609386937574⟩
def resval4Tail108 : Box := ⟨-242612729853682191677206846079197834364222674462098028,251365479197771508886317098930750578338692083501494267⟩
def resval4Tail112 : Box := ⟨-293977532538823356784108973184302623702201697532866804,266890812127228758458662017999359588347096808277068345⟩
def resval4Tail116 : Box := ⟨-356217044710456218781405863608150592721159092881664268,280599102812502395908789483558694858500413825714587387⟩
def resval4Tail120 : Box := ⟨-431633607665217406586993358765140176321713317526169626,291414518695779097457896841090724452503502660287611544⟩
def resval4Tail124 : Box := ⟨-523017003348414021126704294778636599782365412692138599,297939869475385623340551685351534862051378526207389289⟩
def resval4Tail128 : Box := ⟨-633747652948568927977130766584516188773389312724795357,298375897981067334338332832655210122755050764379434761⟩
def resval4Tail132 : Box := ⟨-767921664203094152036783764388026557052019521314811318,290421767662136610099053336916630469442766952260063429⟩
def resval4Tail136 : Box := ⟨-930502353136827892464602891034804594747866577883102886,271152533353666773834796966173830729366291002707911220⟩
def resval4Tail140 : Box := ⟨-1127503996412722416949942146740495758311887635546110867,236868449486805921531550307205110591809013743198422152⟩
def resval4Tail144 : Box := ⟨-1447363639752080130690744977396586178872793193043690270,179483966008596176739521553650117458892121069291645393⟩
def resval4Tail148 : Box := ⟨17874589262735289533654912095159519647891365411,37980323193917828497722164500521975537891503613⟩
def resval4Tail152 : Box := ⟨21587606944478856505656508010682770748776820913,41763357231219247517818484484027311638559415618⟩
def resval4Tail156 : Box := ⟨26158030259228216592346162351459500797570949145,45771356889891641666875220601986367019846843930⟩
def resval4Tail160 : Box := ⟨31696082873442187843408109257892685288989484170,49973342141203313052018407019798391449473930845⟩
def resval4Tail164 : Box := ⟨38406625406259665619962060420920783052992076905,54321746773860086959044510403154366616265453223⟩
def resval4Tail168 : Box := ⟨46537891795226169981255829005041756656027206891,58746931816950755284656024804519155415722580489⟩
def resval4Tail172 : Box := ⟨56390670876051315452626953657163142059995280396,63150887143703548291124570286188284648602701814⟩
def resval4Tail176 : Box := ⟨68329433053031747683713593821821156732131595949,67399379548005452338180470043044500738630580306⟩
def resval4Tail180 : Box := ⟨82795812655096435510221360891380696174779034871,71312188572753481329491862460004256927660503102⟩
def resval4Tail184 : Box := ⟨100324944711562583983460359014234483613890670393,74650991401957254114460639518047429699746849751⟩
def resval4Tail188 : Box := ⟨121565260471642218700187010771962846050749809783,77104360669804676122355307175036203204580230240⟩
def resval4Tail192 : Box := ⟨147302473936325238594398902265597391590684033035,78269220327274418788709739109101559750238804085⟩
def resval4Tail196 : Box := ⟨178488646703663488143457849038542080512492700392,77627960156546809565846044655456634850774008013⟩
def resval4Tail200 : Box := ⟨216277406283594498798547475535769144026184052119,74520233569805557652057797465080613539838225103⟩
def resval4Tail204 : Box := ⟨262066620665340800654439725585186623436098995181,68108249215169619497392651690397095499160179560⟩
def resval4Tail208 : Box := ⟨317550107739416157563464702578903736552679114121,57334106436381478120766714226040150848667111968⟩
def resval4Tail212 : Box := ⟨384780292456063134308838410873351663716550029650,40867407834714973015388977814162579888028970359⟩
def resval4Tail216 : Box := ⟨466247246700425984834449329889354757150197443026,17040815378188428726538398235287369444726777282⟩
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
def polyval4Tail5 : Box := ⟨1035293339796524490060161984086291254028445628953106932450,2093023883458383218110978009258371112977717317868540437636⟩
def polyval4Tail9 : Box := ⟨1254478269077920908243957946746384609015110799173330022185,2297445583200268125825451817604654794662834419007038420736⟩
def polyval4Tail13 : Box := ⟨1520070386806712496270488198853219042801173078361745401674,2512823402431564388185102396947040316059471081579705081684⟩
def polyval4Tail17 : Box := ⟨1841892393149498207483485390861060485888174409188836879469,2737100004364112871309900856607138094602506268943923979906⟩
def polyval4Tail21 : Box := ⟨2231849010011457157645663512243728020691800051835142655439,2967189812294946004065060573441077500975701596617883243593⟩
def polyval4Tail25 : Box := ⟨2704365370102717424098990870979046794003288191171259225701,3198681049132750958394440312289369008373003402165448750734⟩
def polyval4Tail29 : Box := ⟨3276920625993988549221097705857922974738867769670582554953,3425463837484644307486984068498809612553228107805743350387⟩
def polyval4Tail33 : Box := ⟨3970694532542758550498839124768170795538889472530755595877,3639267223796914208800559970659931705377792428565146214690⟩
def polyval4Tail37 : Box := ⟨4811350920647499089259663251115803089289450842436042028218,3829084173536205128893127769002661760740194359949223780470⟩
def polyval4Tail41 : Box := ⟨5829987044304636466669927450687143837624099938225857600663,3980458922077039569125106847917499168369133940146803428559⟩
def polyval4Tail45 : Box := ⟨7064283918867799782104471770827027185242508588552548733959,4074605385917508111178379315282228256544486504589580798893⟩
def polyval4Tail49 : Box := ⟨8559900203401985649676446611551675389911179241104563855575,4087318421463674156152728814499916633991502662612788931212⟩
def polyval4Tail53 : Box := ⟨10372161189119465411065815043386392356044328382940491029540,3987631297231287952760281878562234161521232163762855874868⟩
def polyval4Tail57 : Box := ⟨12568105372340627182882454117245391162921376142164020453225,3736162496140682508056815979174513198191375589655134200555⟩
def polyval4Tail61 : Box := ⟨15228964318059068984515057214409029878497897060981072691537,3283082494585871551084235419818416111317868785134628840210⟩
def polyval4Tail65 : Box := ⟨18453167548329927437647240362019849512446791950010066806592,2565615997064592703903928019090064795098237129845313384590⟩
def polyval4Tail69 : Box := ⟨22359983713231672158971182523784733923044537982881691035695,1504976654558274783840965180788752572077611083691955704754⟩
def polyval4Tail73 : Box := ⟨27156250000000000000000000000000000000000000000000000000000,2⟩
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
def resval5 : Box := ⟨98020646943108086422508830095166488884176498561744338051,14235926000622838160713375938728156735742757927003485822⟩
def polyval5 : Box := ⟨8680610542945107615843717914688868677088785267143688009187,3809332217918071651544882661092855200404571079126696430647⟩
theorem cell5_lo : Holds Q cell5 (31/32:ℝ) := by norm_num [Holds,Q,cell5]
theorem cell5_hi : Holds Q cell5 (63/64:ℝ) := by norm_num [Holds,Q,cell5]
def resval5Tail4 : Box := ⟨-16884141924198886608031568016839682128408557588158242155,14446079724500373453890778992015088656052208265232882788⟩
def resval5Tail8 : Box := ⟨-18564370969359894176699839338475315109286401409758361108,14802994791395221637572232301334169029225389920425102050⟩
def resval5Tail12 : Box := ⟨-20411741750166275765357135243670307146830640315610071015,15125164792308293408404842553517606886287687394152157701⟩
def resval5Tail16 : Box := ⟨-22442947397474734432371351938423552233184490267258891768,15404563114041117230048767544027328215916250301757327325⟩
def resval5Tail20 : Box := ⟨-24676281625088611105746815923667132405787197205474477519,15632067955283756219116640802150136267707172320428952557⟩
def resval5Tail24 : Box := ⟨-27131858577060177647715082972081558527470157314362858194,15797333434106267265187538696731028079535948217856556012⟩
def resval5Tail28 : Box := ⟨-29831793988651663068452967330337774108340950199025555191,15888647208201033919682257971383299614755215636397034736⟩
def resval5Tail32 : Box := ⟨-32800404367940681732718151098235826437203963675575838825,15892772589387925731213922292177557989089195663715313743⟩
def resval5Tail36 : Box := ⟨-36064425998305479401078678767003790763081123527672085402,15794773522300508920903171558427956327162739922378909779⟩
def resval5Tail40 : Box := ⟨-39653255734203951473923726977887886644862301532275364799,15577820629427185362481739822669047422558563922520827369⟩
def resval5Tail44 : Box := ⟨-43599215758932592684101380894483915901021555983104268753,15222976339755020839394874153585303849913805255302098390⟩
def resval5Tail48 : Box := ⟨-47937844688861006187828230816239590441351540675215401010,14708956914543928826558869038832925079113141353578909846⟩
def resval5Tail52 : Box := ⟨-52708217645922640992072818741982982162574530653122009001,14011868959349277543795277246917500082210048086030457727⟩
def resval5Tail56 : Box := ⟨-57953298181040075854247132378130379849166677098405128997,13104917764225926914543474763059932209855529562038085687⟩
def resval5Tail60 : Box := ⟨-63720325218019253888438844307153323679183321957020485296,11958084541790628784350753616755079276207718835541409513⟩
def resval5Tail64 : Box := ⟨-70061238496782800316181652118778383957220776921903717866,10537769332682430468571360365217901562220465420601284137⟩
def resval5Tail68 : Box := ⟨-77033038237955974828777045120674000621511918775440215884,8806392449586585634588958886879879132537560088322414487⟩
def resval5Tail72 : Box := ⟨794488212377318532006814856416236687008831635079923820544,813597498752996916101589673912764356995468726338772960⟩
def resval5Tail76 : Box := ⟨-222043559526026130451845774217138129012401868963791178,193099829948013618229692835389104803978989505965057125⟩
def resval5Tail80 : Box := ⟨-244111140056108885427559519697473673722568432395395175,197997194572166698033993749756263522399731196627638298⟩
def resval5Tail84 : Box := ⟨-268403035499436339350593527276897032241366708849836690,202451110769924827914930432938145207318827276525925508⟩
def resval5Tail88 : Box := ⟨-295112258461215929463018974916657440458593787134633991,206356748949161662180014848364765082872712714595073970⟩
def resval5Tail92 : Box := ⟨-324479359677341087559878515304578703470807328209156901,209595082240560759871349577035387378003334090200361567⟩
def resval5Tail96 : Box := ⟨-356768828938547458085041357138623281063848809808123129,212031047613936437139029961979266571511143571205174212⟩
def resval5Tail100 : Box := ⟨-392271475845959609388034992011643610143443072838264671,213511677536719217668935914936729848285113814556538463⟩
def resval5Tail104 : Box := ⟨-431307048937484916715213636140282854933504914419779198,213864028008768764707107775534725038090719503167389303⟩
def resval5Tail108 : Box := ⟨-474227115448516932036181908994735386569438470467719691,212892881539980557669071045460137623147514334085528630⟩
def resval5Tail112 : Box := ⟨-521418227642315928268405904520777516577566937159833282,210378201447768907225748221989871257818152560488203613⟩
def resval5Tail116 : Box := ⟨-573305404227079704996192180169424370373943893556352033,206072311420983966556826617488347951593111656749473376⟩
def resval5Tail120 : Box := ⟨-630355958214494077651486801336107738007593093818885826,199696771619226973288587319188158812822473336950171601⟩
def resval5Tail124 : Box := ⟨-693083705694718623405609345640265359920215780684993799,190938919626957864989406740847543147092093536987880154⟩
def resval5Tail128 : Box := ⟨-762053593433422284399700360896527381514615174434882113,179448041332818626683208161107605362332292054833702455⟩
def resval5Tail132 : Box := ⟨-837886786968550348232063472994849947434349513952116642,164831133226046377776312798857060986391101888815178508⟩
def resval5Tail136 : Box := ⟨-921266265049022206187667719885934957752512010076168834,146648213659403562251147364056328353735456035450998791⟩
def resval5Tail140 : Box := ⟨-1012943118584741285464188424202297199405329328432477657,124407128567357241609947073355995953334597813029582459⟩
def resval5Tail144 : Box := ⟨-1192982279841351698892162646485093347672346917622205446,94833508044652775040417898026864064140476546247436639⟩
def resval5Tail148 : Box := ⟨97658640896118210466907564115054784061620127504,73443503015561701686826509431966037217907457882⟩
def resval5Tail152 : Box := ⟨107312167533571138119640041589204138330319456316,74851897564398769198423737613747897417838002956⟩
def resval5Tail156 : Box := ⟨117990974907311049614965116380678306646093886012,76017367436545437847379295717845915106166181243⟩
def resval5Tail160 : Box := ⟨129732448882881446472734946550014607418425745754,76890284792370919470015096125158582642513828640⟩
def resval5Tail164 : Box := ⟨142642336046583136917676647002991746134656665163,77414974663458872222584674063207792926384207069⟩
def resval5Tail168 : Box := ⟨156836907096349821949449286907422805892358329174,77528494694557176484872866130196122765121816515⟩
def resval5Tail172 : Box := ⟨172444003016860878332842395265447704850382036790,77159799644291748627990629910611953635440578439⟩
def resval5Tail176 : Box := ⟨189604186457278159106138601250149165448756578421,76228815456935456444183311812677733996074485031⟩
def resval5Tail180 : Box := ⟨208472007684786123400836231664690345420646125148,74645413417391130654577259181373180135354000431⟩
def resval5Tail184 : Box := ⟨229217396515229971650823039239118358041473926858,72308273940894807784182334328782752645025900145⟩
def resval5Tail188 : Box := ⟨252027192757037336104890413269574422259743854945,69103628476331041277263225715334451722853410304⟩
def resval5Tail192 : Box := ⟨277106828952105838700836536714941481541553129314,64903866820556054826448431335060592905339287335⟩
def resval5Tail196 : Box := ⟨304682180568975495066622662734850936437549351722,59565995839779372215648129713628980748647733050⟩
def resval5Tail200 : Box := ⟨335001600311735404919722451745878038274580439793,52929934160785964634920938831789042459716351606⟩
def resval5Tail204 : Box := ⟨368338154866321198999731848584702542242123218356,44816625816303347596162417934339952314669573023⟩
def resval5Tail208 : Box := ⟨404992084229101209330650447131581767292596583836,35025954090511739383256152779348782384859290235⟩
def resval5Tail212 : Box := ⟨445293505831633985044607874772665872103223129671,23334434892462081289121557630366392525104963110⟩
def resval5Tail216 : Box := ⟨489608433543780919806069874217876902735298602554,9492512413891814384371198529384682000463382342⟩
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
def polyval5Tail5 : Box := ⟨5401305177547283387539102966873834558831150893263079805917,3885107953374495897912494121788535254413209001622000202240⟩
def polyval5Tail9 : Box := ⟨5938795666886500534095206479594122575131522147581612123338,3951416434512514295765535300995619427958926327913047256983⟩
def polyval5Tail13 : Box := ⟨6529774890525377345520074802313954661488253940204897383326,4003497216722636181442511043095863250066520797908239833001⟩
def polyval5Tail17 : Box := ⟨7179563418892258175278015192473010050572211297459636007455,4038580352940397928096011868802509391579735115253306092146⟩
def polyval5Tail21 : Box := ⟨7894013461427250033269192116803134831293840390800054812902,4053532220879154419234780680245046458960031993840750993510⟩
def polyval5Tail25 : Box := ⟨8679559590659531866663027659855166280463556493953434418735,4044813597461858492490322483224510662206727100951242399328⟩
def polyval5Tail29 : Box := ⟨9543276693904854127948260571243551043500485175438752897056,4008433199982472849688195617734534335016206367328220385763⟩
def polyval5Tail33 : Box := ⟨10492943692032089859874785569028727149971454530637317852992,3939896207659451582156619571505503271877645461266181375456⟩
def polyval5Tail37 : Box := ⟨11537113598988114363056123234273826845730613303486829256525,3834147238294687527069482548260840377147689955591540178886⟩
def polyval5Tail41 : Box := ⟨12685190553060047329800943893090512345007214034183683263431,3685507200805681176467964209089804211057697006617509341365⟩
def polyval5Tail45 : Box := ⟨13947514513643790337465192897620360281089728904720338365170,3487603384973502128825973962095457847975396773347513269046⟩
def polyval5Tail49 : Box := ⟨15335454386325868875022930889856769604962677045757199940400,3233292084294379409899040815555921546330746405934599356398⟩
def polyval5Tail53 : Box := ⟨16861510414993755243689339759453677493111148234567689510532,2914572975730919277031868331660939452803112393920579119829⟩
def polyval5Tail57 : Box := ⟨18539426763151761162307754662751100139136166843425171675262,2522494400761503256522824317702807015769571956120557216400⟩
def polyval5Tail61 : Box := ⟨20384315298386943773293955054775602748029763598452251746276,2047048604687812564071069703560481775354596130494278008891⟩
def polyval5Tail65 : Box := ⟨22412791694840408934009341454530844125192845807769178035933,1477055894870616331300617597453232864846081167060747726284⟩
def polyval5Tail69 : Box := ⟨24643125179219092332556472046374630497480524936378713688644,800036567605766808836198683332094145973087364541556650924⟩
def polyval5Tail73 : Box := ⟨27156250000000000000000000000000000000000000000000000000000,2⟩
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
def resval6 : Box := ⟨81507981524772934076888624234026953180606660969152135340,12830448809998846117900309612131323201819538277076937010⟩
def polyval6 : Box := ⟨15363566163776017070977667768942540551715379826144048890287,3812401901491384095807792713980430756584429384693259676107⟩
theorem cell6_lo : Holds Q cell6 (63/64:ℝ) := by norm_num [Holds,Q,cell6]
theorem cell6_hi : Holds Q cell6 (127/128:ℝ) := by norm_num [Holds,Q,cell6]
def resval6Tail4 : Box := ⟨-33400184992309405827400414839415145005975170259525593719,12538757241425708098079709793277177734118676631325286121⟩
def resval6Tail8 : Box := ⟨-35012842065177082505015290079799139301043852996513185903,12390231470072536750079355600768558553208227045687627850⟩
def resval6Tail12 : Box := ⟨-36703302358397757170149105058043658436830038047170759782,12210508101051042120605020254509386996783847821254497922⟩
def resval6Tail16 : Box := ⟨-38475380012270945284007786818512644055047441237393379075,11997314581430677362374515394607611471569306396339383071⟩
def resval6Tail20 : Box := ⟨-40333015613504603553146567158843042004147206115131082421,11748244783510590717120138112253879659589161814988810871⟩
def resval6Tail24 : Box := ⟨-42280339998211467253478162343088107698231427465174361140,11460751226987035988059217523986782645607729183998967332⟩
def resval6Tail28 : Box := ⟨-44321683444017354352575710174945880196392885015184162787,11132137451619542163128834696053450753338577702272138915⟩
def resval6Tail32 : Box := ⟨-46461585299332505740127056494395536749739337817500399748,10759549996176498140499459343216721695078797417927790017⟩
def resval6Tail36 : Box := ⟨-48704804077529550405781194505808539697441539206681755487,10339969963722578285260463705735690325930288402385723108⟩
def resval6Tail40 : Box := ⟨-51056328038479972514877338618739065302875956272674968292,9870204152434842355822235862749384156687757159358108251⟩
def resval6Tail44 : Box := ⟨-53521386280979329724821315732206693309510310533148558858,9346875730102795110438690054919799684971019626261238284⟩
def resval6Tail48 : Box := ⟨-56105460370727519497561744258484720208239940930182364481,8766414429385342453116998192969821582973463137252515796⟩
def resval6Tail52 : Box := ⟨-58814296529721306981421716579850710122497046382508912440,8125046239762093209303620996227695124079746560763186779⟩
def resval6Tail56 : Box := ⟨-61653918414164731318503975430622314052053748930554529683,7418782570925234380203470268199819093187329883010621150⟩
def resval6Tail60 : Box := ⟨-64630640509307809757699611644231861846952432195538489266,6643408861108271834308403459470463601300639349204588475⟩
def resval6Tail64 : Box := ⟨-67751082164989226669041654877423924585111218288572626313,5794472602233208162693653672452486496232848445979021909⟩
def resval6Tail68 : Box := ⟨-71022075399216672856745893709261739015342889712083895817,4867266810401919128980816385820104568822491148701394688⟩
def resval6Tail72 : Box := ⟨794356442092745610484461016806055204770719684187449664166,765978825529053649116303796021726266434594345465089590⟩
def resval6Tail76 : Box := ⟨-443013908928028652379423408788828004376840543466274372,168492341132792294900100155086416242804168764005864173⟩
def resval6Tail80 : Box := ⟨-464376132938474450769199606662812592858846182343266192,166592093492810292624967807340386686185012430716073819⟩
def resval6Tail84 : Box := ⟨-486796745368542081404355299730678908802504365625861493,164280449884831405088588088401459751608042364838464556⟩
def resval6Tail88 : Box := ⟨-510299852146018642278891529090280821460921487595544697,161527186562205844491439271127281660600577594503992743⟩
def resval6Tail92 : Box := ⟨-534937715952647702278355174544244069508412856395612586,158300464144136886580618684987696231765196035887548328⟩
def resval6Tail96 : Box := ⟨-560765124162243488629227804189624978661992715907534572,154566570834658217110949610698746116877597825730487301⟩
def resval6Tail100 : Box := ⟨-587839509346788921311573797374983260954814844203509750,150289821319477726216470255179752210460988311342805900⟩
def resval6Tail104 : Box := ⟨-616221076988902902164605381923918981192053018912077653,145432450459214206413897543397218792457071007421417870⟩
def resval6Tail108 : Box := ⟨-645972939361153316119354847385447143743307674113992817,139954501498732905335493831290506531027232310861061299⟩
def resval6Tail112 : Box := ⟨-677161255869219130793641542678545420488603939030694627,133813708516599564445933969699429933708349753295909877⟩
def resval6Tail116 : Box := ⟨-709855380170981800528140964277811036487788224670514244,126965372825006309760648409219157363161485966448432803⟩
def resval6Tail120 : Box := ⟨-744128014398695619660039626892914227067881245204808227,119362233016170153306341618321773272259439194950523286⟩
def resval6Tail124 : Box := ⟨-780055370827181847472032761994651074893157492944708125,110954328336147507023281427740496185833333170818985344⟩
def resval6Tail128 : Box := ⟨-817717341347549277831127153196386180695243436889791846,101688855051211650245365854796380232709423707192004723⟩
def resval6Tail132 : Box := ⟨-857197675123318472834725762113674003472385099078470169,91510015455367091366835122732243816488331986619521322⟩
def resval6Tail136 : Box := ⟨-898584164840951490237049744049682681655276434314782960,80358859149142183486073026918178640048180102013470078⟩
def resval6Tail140 : Box := ⟨-941968988129046216939130061681558483434636077898891906,68173109091922570242117761243572003120819956027859858⟩
def resval6Tail144 : Box := ⟨-1065766038294569840405609006255826159197852881946436516,52494126605144919091902819770199061296872024452232398⟩
def resval6Tail148 : Box := ⟨225041704960360320074083287115492695617625676692,72505223597074330281057033839498063758341552934⟩
def resval6Tail152 : Box := ⟨235845373301287254802739629918895476930619465513,71123251544148958889554567207309968790107383309⟩
def resval6Tail156 : Box := ⟨247232258147410696801240257619357307877111141882,69519461972667205995550201654943919916213352465⟩
def resval6Tail160 : Box := ⟨259168915936088461079050434324920247425459584974,67677687946612897874074422746597612088895911345⟩
def resval6Tail164 : Box := ⟨271681889292620330218463482508400871695706923118,65581322503867034335319012827662519347981681983⟩
def resval6Tail168 : Box := ⟨284799003395182215319027762071336549277639264678,63212793821177371411538155684475452604135060932⟩
def resval6Tail172 : Box := ⟨298549426853872398029979365633238174407281964593,60553513418316473647477885465713584789472267326⟩
def resval6Tail176 : Box := ⟨312963736572834851644102756037314992235726983108,57583821709965922583537310454108565217290131800⟩
def resval6Tail180 : Box := ⟨328073985744315066790179351378385913951302586494,54282930757878813831962639854617425866036125384⟩
def resval6Tail184 : Box := ⟨343913775125547610782895273098271446653616636511,50628864082693236066586105373728670363689434489⟩
def resval6Tail188 : Box := ⟨360518327756973803776153692369202135369307475977,46598393387812763946695921287193923112157149553⟩
def resval6Tail192 : Box := ⟨377924567287940884992300124341446033536278844630,42166972040465362398169313430521755534757530672⟩
def resval6Tail196 : Box := ⟨396171200084056024641103493881366827646549265320,37308665147389065071531348293876295001646903190⟩
def resval6Tail200 : Box := ⟨415298801298777827543461159254398490488515039423,31996076054553884210278073437371678419764557904⟩
def resval6Tail204 : Box := ⟨435349905100643325867607231493474075416680996911,26200269091896292704673103838974404875074027075⟩
def resval6Tail208 : Box := ⟨456369099256792778031194342523355872286628830046,19890688375194339989867464654881130796236943251⟩
def resval6Tail212 : Box := ⟨478403124346791022805445398021699611600314297635,13035072464178356857465171284664153253389846480⟩
def resval6Tail216 : Box := ⟨501503989039585850585632914811243416103333671813,5599223058780723554758411333884577054403610196⟩
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
def polyval6Tail5 : Box := ⟨12155836504268434103693896610885992257091505413611383457653,3741018249045055772902872572426756966492347675176586237998⟩
def polyval6Tail9 : Box := ⟨12742732194609421894266860638991664898844378977555489101837,3660753586958642930828139764024037705296101359568750827020⟩
def polyval6Tail13 : Box := ⟨13357965961416713893087389568845954267163310350439684860334,3568299245464394298479989591641651912825724463737605048018⟩
def polyval6Tail17 : Box := ⟨14002903922317301168976931494746708120914724063263813473473,3462801700986416753065088197508002828859739730708246679981⟩
def polyval6Tail21 : Box := ⟨14678980229775593505472527060742629506439630512962423521268,3343357786994460276226042551425745671672877832365188156433⟩
def polyval6Tail25 : Box := ⟨15387698278978465750328291711305110359612153959966265901533,3209012016959573705986236909118127469480183354847620070663⟩
def polyval6Tail29 : Box := ⟨16130634050761757575391302545748091268613119589531533129328,3058753780564056932376856628745122256227116245885238718806⟩
def polyval6Tail33 : Box := ⟨16909439616128750841390663236534763174471332757394738040781,2891514395692680844225038544869793563151338952070318352881⟩
def polyval6Tail37 : Box := ⟨17725846809970971880332869445339416193820141786125449036157,2706164008957700208286148899548868570743433273859935242102⟩
def polyval6Tail41 : Box := ⟨18581671082160460066009132966159958815092301256062141814479,2501508337153626529312593226950735089849011826610344296885⟩
def polyval6Tail45 : Box := ⟨19478815534577200627920888700444376838266275809968182433385,2276285241661322934205773411835702963093656109358381175841⟩
def polyval6Tail49 : Box := ⟨20419275153048885295777103131399774310892576358157490880605,2029161127426106449970119928491116983033683889863636146969⟩
def polyval6Tail53 : Box := ⟨21405141243613592150285727969416891645749599786657491821925,1758727157720296200224457420008133157529860614935301700297⟩
def polyval6Tail57 : Box := ⟨22438606082970330282940545547220204737423707578933338893261,1463495275466084099757070650689610472455376953222726736304⟩
def polyval6Tail61 : Box := ⟨23521967793458697335643349001876085386669583096800553291093,1141894021438735828661309717590096711492899514636406028007⟩
def polyval6Tail65 : Box := ⟨24657635453419743623017960240088850959230340175792489429568,792264139191224982038885523597705066148393964343048308023⟩
def polyval6Tail69 : Box := ⟨25848134552957955399979039882054878705916207961426090987428,412853951520924991235226202189158815988646414361961475084⟩
def polyval6Tail73 : Box := ⟨27156250000000000000000000000000000000000000000000000000000,2⟩
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
def resval7 : Box := ⟨62165376424829604891761342340675574996641457193352161788,20799995363728868932491530431634626816964849188398779736⟩
def polyval7 : Box := ⟨24209534980348742156386530873546145818460929139388739820641,6658570394019507335331576906679636902173697671667608154331⟩
theorem cell7_lo : Holds Q cell7 (127/128:ℝ) := by norm_num [Holds,Q,cell7]
theorem cell7_hi : Holds Q cell7 (1/1:ℝ) := by norm_num [Holds,Q,cell7]
def resval7Tail4 : Box := ⟨-52007774333758757013569379038872817467471870542711660469,19819862906736681645932247519704084848319902469797847572⟩
def resval7Tail8 : Box := ⟨-52828449891210045911866700161122926301023091827522332229,18999241856752591086855450617642111227785111046156882265⟩
def resval7Tail12 : Box := ⟨-53662018818581070396916590628753106045136443775539772131,18165672935630070166869226033748641152855815242640018945⟩
def resval7Tail16 : Box := ⟨-54508740447041473548245905650413240251073087919812136129,17318951307175028562184267465315096274043999810777520577⟩
def resval7Tail20 : Box := ⟨-55368822316722447859782578097218358166500771024104340068,16458869437494074251750305612621490350167203414291000549⟩
def resval7Tail24 : Box := ⟨-56242475236045845459422343092582593758682343238661448089,15585216518170676899400867212588973448351432168394109088⟩
def resval7Tail28 : Box := ⟨-57129913339729426905615077572599529946282350397017168453,14697778414487095461613410681638330737096546626944690004⟩
def resval7Tail32 : Box := ⟨-58031354141277286762476679230517374627016727223876890687,13796337612939235605393455043033809186135318315035476858⟩
def resval7Tail36 : Box := ⟨-58947018586293027583456545799001351770279852017934951816,12880673167923494784464206477586784492238364413827016106⟩
def resval7Tail40 : Box := ⟨-59877131106634131306604477649864690504897311007666799942,11950560647582391061194108403852307033267490416409792428⟩
def resval7Tail44 : Box := ⟨-60821919675420820778995770720066013270667417962865822364,11005772078795701588086070843313933239812653324345422375⟩
def resval7Tail48 : Box := ⟨-61781615862912894444552495912027840138083672740272475833,10046075891303627915017734993784302912612297618688600209⟩
def resval7Tail52 : Box := ⟨-62756454893268229622959818244266199739296971202224412898,9071236860948292541119621285545307047370548648587375876⟩
def resval7Tail56 : Box := ⟨-63746675702196853248384975859675210261939831418461657557,8081016052019653880934764735902053402956627026137336474⟩
def resval7Tail60 : Box := ⟨-64752520995520835258073254474849168198071982962611476770,7075170758691446264069307191121116399469954029975662307⟩
def resval7Tail64 : Box := ⟨-65774237302685527104470861480157446336719345070948738779,6053454445231464194270828237749851743702581104390966427⟩
def resval7Tail68 : Box := ⟨-66811968910387721206631479148517704902304684770774485097,5015612773300627149221574094123346522470163368023368439⟩
def resval7Tail72 : Box := ⟨794156866846554780723631035153638323956686286864221535545,870792526340129758015782116598853663490551142468152658⟩
def resval7Tail76 : Box := ⟨-692196515424380100073061860165834860624421066777097645,265989766712620720393973168307078137823806064258509274⟩
def resval7Tail80 : Box := ⟨-703092389346766730044533071389239731099231576897132780,255067989862249025863127243597615380583952959831721493⟩
def resval7Tail84 : Box := ⟨-714186333884359313293490654642984793228857881671882347,243974043980548360376294820907524418690183705214874391⟩
def resval7Tail88 : Box := ⟨-725455328769776734259220043166165956272925585903267251,232705049094401032774065310876232438950279778685854920⟩
def resval7Tail92 : Box := ⟨-736902134739260151683255212936717041397668107717433397,221258243124915685675265648349411298556424751564121319⟩
def resval7Tail96 : Box := ⟨-748529557435519273200387431474632457010383953625410825,209630820428656545981909806862002241923900848456018437⟩
def resval7Tail100 : Box := ⟨-760340446771626482087142950577091993040098104368944217,197819931092549336590357356119786925139310358557059309⟩
def resval7Tail104 : Box := ⟨-772337697628830722671632227396895897728555201275641708,185822680235345095970141366073504515253521572720885264⟩
def resval7Tail108 : Box := ⟨-784524250566099000003633634061014224171407792177591950,173636127298076818632836305691632295961646592508715295⟩
def resval7Tail112 : Box := ⟨-796903092540855401946769150650948127036902959118429194,161257285323320416689213365589324697355713654694471617⟩
def resval7Tail116 : Box := ⟨-809477257641092525176054857991239414236821689256810060,148683120223083293465387017063493720846791835717445269⟩
def resval7Tail120 : Box := ⟨-822249827829034732690877632304702792719972909730772936,135910550035141086010634777503866278598874464311175745⟩
def resval7Tail124 : Box := ⟨-835223933696535517586119342169656778557279229432705190,122936444167640302438102850586851654121209723470683727⟩
def resval7Tail128 : Box := ⟨-848402755232394203543728653057886497569506422405766117,109757622631781695786284241183806050881416659290729745⟩
def resval7Tail132 : Box := ⟨-861789522601797370747047743451339856413919645226742828,96370855262394925998782513756717449697757022495185641⟩
def resval7Tail136 : Box := ⟨-875387516954907215727390442911664613648545756273890735,82772860925174179419254119726656478024410042790530220⟩
def resval7Tail140 : Box := ⟨-889200216361931081404259351894151801346184292044482980,68960299663666061084843756538658488322676855915857862⟩
def resval7Tail144 : Box := ⟨-980945689867557589356786761617456827195519448181260468,52558295858536699273960827263277932609438665945069180⟩
def resval7Tail148 : Box := ⟨390511235531961008208498513319362329384728013300,124714510197872936136156330267419890888062064925⟩
def resval7Tail152 : Box := ⟨396613353496967160519190094935711476846902067976,118553167307427087682751888507606174006036204845⟩
def resval7Tail156 : Box := ⟨402871430580512139579102473980210243184136809932,112295089213930973185022406882292044124234604885⟩
def resval7Tail160 : Box := ⟨409228253548649545812923191756078736640637899328,105938266245484960042231431405987022820663188537⟩
def resval7Tail164 : Box := ⟨415685379480229742862579589749929764863428167210,99481140313904244931679475697458369696922646660⟩
def resval7Tail168 : Box := ⟨422244391034161133868813433364092098807230840735,92922128759972850634951215868066565227241318880⟩
def resval7Tail172 : Box := ⟨428906895842097271256910381249178376580623980835,86259623952036713182765737392474416239257531275⟩
def resval7Tail176 : Box := ⟨435674526902171547621180626541787185499194753128,79491992891962436815192030692887256333301781726⟩
def resval7Tail180 : Box := ⟨442548942979249009964565888353805349840447736377,72617576814884974471418575398799350793518710138⟩
def resval7Tail184 : Box := ⟨449531829011494157690344467551263396107896867503,65634690782639826745569396163163327727916202951⟩
def resval7Tail188 : Box := ⟨456624896523353890682771192163623289043513779117,58541623270780093753209547634498905273418156977⟩
def resval7Tail192 : Box := ⟨463829884045056827898153104130309299878070532092,51336635749077156538575523133481584209764355307⟩
def resval7Tail196 : Box := ⟨471148557538731816858979735763668432242887567335,44017962255402167589262514931818195099388114402⟩
def resval7Tail200 : Box := ⟨478582710831250077279766980771476685315283381697,36583808962883907597838062912855777621041222433⟩
def resval7Tail204 : Box := ⟨486134166053897120974186375883211855548618443214,29032353740236912797794956568373858126832454007⟩
def resval7Tail208 : Box := ⟨493804774089005515953083618592554935097753492750,21361745705150385470703817232877926539544510714⟩
def resval7Tail212 : Box := ⟨501596415086881325624556531392205423194022057936,13570104766908293215482875946830852027875108127⟩
def resval7Tail216 : Box := ⟨509513987686344232144960553984453281918534647351,5655380788313405083483040995332075659456097058⟩
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
def polyval7Tail5 : Box := ⟨20764863747922140959410992061175936244150780555437353549335,6333512605980398253648886541899840382188510820501088349102⟩
def polyval7Tail9 : Box := ⟨21092506122491653960341966985135462716070608720253144451228,6005868239901529052213454460486781180138650123402336955043⟩
def polyval7Tail13 : Box := ⟨21425320308678266425868533184409325801031325519601666167858,5673054053529336795655463485842339806921654880421885776241⟩
def polyval7Tail17 : Box := ⟨21763385899599361844975564026793947158412948159883169276396,5334988462608101191553977394179022358795712578091804973930⟩
def polyval7Tail21 : Box := ⟨22106785755871979956006415004412303527405540754186063222489,4991588606335482610897814054689283721884227101173099440075⟩
def polyval7Tail25 : Box := ⟨22455604045739080060334621808807392492026231653335618033448,4642770316468382501264952424246792266998202260925492411997⟩
def polyval7Tail29 : Box := ⟨22809926265516637157141671210261282095571173717388717874798,4288448096690825404287914847113349528819583089528968728172⟩
def polyval7Tail33 : Box := ⟨23169839260548886960495826086175841139481697237107115161668,3928535101658575600920322918829778920484371902992815708234⟩
def polyval7Tail37 : Box := ⟨23535431246494356635854238243306883949920172120138675846006,3562943115713105925559783951571656732922646615485899405832⟩
def polyval7Tail41 : Box := ⟨23906791830947763745569415634353471732605083902430596799109,3191582531259698815844530502460057907652959772374330588572⟩
def polyval7Tail45 : Box := ⟨24284012035403082562442290338544287455235552633979580427937,2814362326804379998974823238911317081126473483758818750588⟩
def polyval7Tail49 : Box := ⟨24667184317563160954645535949475073740950041169306760703643,2431190044644301606806877516113844200342022410363095491199⟩
def polyval7Tail53 : Box := ⟨25056402594001355990695098340740267968198575838288722563197,2041971768206106571568841921259601911224579625350462104823⟩
def polyval7Tail57 : Box := ⟨25451762263180742744951677853770016781136298672734240075003,1646612099026719868165423162373045594104555820473735423314⟩
def polyval7Tail61 : Box := ⟨25853360228836549902688712389470115146501047856472171836173,1245014133370923641690311394503855901292525402473016316874⟩
def polyval7Tail65 : Box := ⟨26261294923739044704913309383847326903121910662551979362002,837079438479298888437343083353481402887183614797357606801⟩
def polyval7Tail69 : Box := ⟨26675666431781649551362757375889373815898062246889285339719,422708023962038705035900584159295975862197202362202864552⟩
def polyval7Tail73 : Box := ⟨27156250000000000000000000000000000000000000000000000000000,2⟩
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
def pend : Box := ⟨1030863848255479813959994750918906949224148945862511667479001,4257118888435531723356861318833496485680948544680496039⟩
def zend : Box := ⟨1003762835713896405578984375000000000000000000000000000000000,2576713209845709960937500000000000000000000000000000002⟩
def betaquot : Box := ⟨428751575733016987443035481309168588874665733698355844500431,394773953714772188630294100011469104863600598558048403⟩
def crit : Box := ⟨125623002784823427815799770522566959115294494355751227415,10705259339534993911060806679850719580403868332003090268⟩
def subsonic : Box := ⟨498284551530237666998520277911805871577953179314447276307,5540711053919672811014795391524951293027228899705798001⟩
def pendTail4 : Box := ⟨27096770479012973348380304109840278231713786589056699335356,1569197852914204666425604887204589375162004985840453747⟩
def pendTail8 : Box := ⟨27096805299972818800467174570330644382281519317126762178420,1569060775545308109568595730598987458186251052417398711⟩
def pendTail12 : Box := ⟨27096805301447503340961734501634468711638664669599102442245,1569060759259144500018507966458826044923226664439041746⟩
def pendTail16 : Box := ⟨27096805301448214962180846250469205059163544086164455481244,1569060759245953188097102707884010121554646073642974299⟩
def pendTail20 : Box := ⟨27096805301448216642014818587092113863547183389762592847259,1569060759245905589281245164405213627024400409397613783⟩
def pendTail24 : Box := ⟨27096805301448216656083206123640642270129951915165115932494,1569060759245904985918138762178531905141477982778850321⟩
def pendTail28 : Box := ⟨27096805301448216656427255133968605016882268378971309793462,1569060759245904962820046475977834521312694712217601833⟩
def pendTail32 : Box := ⟨27096805301448216656448299018837886092406200153423772424679,1569060759245904960383587273334724546919543054570591489⟩
def pendTail36 : Box := ⟨27096805301448216656450858519737119701147084310606600029777,1569060759245904959711627395719563647719267956570629388⟩
def pendTail40 : Box := ⟨27096805301448216656450851219302832671690411290463824773205,1569060759245904959238683470493601407854327019134152644⟩
def pendTail44 : Box := ⟨27096805301448216656448218597857384755859802239561120073864,1569060759245904958390056435936524553183324098967539415⟩
def pendTail48 : Box := ⟨27096805301448216656425897470464261837325558451602226097673,1569060759245904954423173712783663937567961756027746646⟩
def pendTail52 : Box := ⟨27096805301448216656035077805094634919628571683864720114904,1569060759245904903733528075811828403179220405363226068⟩
def pendTail56 : Box := ⟨27096805301448216637848950171531735661005121019592378184508,1569060759245902976304675307049797631536307545034007252⟩
def pendTail60 : Box := ⟨27096805301448213906796492153139402726156935847900700905993,1569060759245682843220722635306018565605566967572892129⟩
def pendTail64 : Box := ⟨27096805301446473400032621538874091776466551483637956365921,1569060759140018923505939666397954612615066974510790723⟩
def pendTail68 : Box := ⟨27096805293624335468690151159673307031873392872191981144155,1569060402020441664235910869953982508604161575921370595⟩
def pendTail72 : Box := ⟨27095799651118675063222992301953835601888513111582820889123,1537282312942011055832421182950903780976174620461483129⟩
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
end SepticProfile.ExteriorCertificates.C18

end
end

end OAI
