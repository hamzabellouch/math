import OAI.MathematicalPhysics.Transonic.Certificates.BarrierData21

namespace OAI

section
noncomputable section
namespace SepticProfile.ExteriorCertificates.C21
open SepticProfile.ExteriorJet SepticProfile.FixedInterval
def cell0 : Box := ⟨250000000000000000000000000000000000000000000000000000000000,250000000000000000000000000000000000000000000000000000000002⟩
def resval0 : Box := ⟨115307737568291626898068977208240115610770193111337731554,316582607701195406737344646330463465184793646597828011⟩
def polyval0 : Box := ⟨3814851779552622539507512322839776082082055126833062543627,14934437308371715565842232818137280100674948906655315391⟩
theorem cell0_lo : Holds Q cell0 (0/1:ℝ) := by norm_num [Holds,Q,cell0]
theorem cell0_hi : Holds Q cell0 (1/2:ℝ) := by norm_num [Holds,Q,cell0]
def resval0Tail4 : Box := ⟨59789731975798183923349739814510749020434872614185,1765241441821250222649636858477636551407288783000⟩
def resval0Tail8 : Box := ⟨7299440347710086679859684761284471195275163576,391055210666225710718777870439963340320308559⟩
def resval0Tail12 : Box := ⟨6700510774852192046950932850094003797469447,544927222085988705605103699650321412572199⟩
def resval0Tail16 : Box := ⟨27073155686999787310518960671325568864679,27207030293182249710572742455479953083507⟩
def resval0Tail20 : Box := ⟨372026740084821523253491017938063630368,385358758040734901541244360926647834600833⟩
def resval0Tail24 : Box := ⟨14921273047060111262153159983091629099,6164791005825480698843907984741214463015769⟩
def resval0Tail28 : Box := ⟨1589464090079317601813435187357111986,98636603956803374083905751391727439296319484⟩
def resval0Tail32 : Box := ⟨422795168529139224516101144585953225,1578185655662840904103725925693928647650875909⟩
def resval0Tail36 : Box := ⟨-279730381705976331402381139469765463,25250970487629291700918590389254693769227724577⟩
def resval0Tail40 : Box := ⟨-142091662889707343201242809058321690418,404015527667409340083232713452158666950361535053⟩
def resval0Tail44 : Box := ⟨-36485783709195986271054213816095512705490,6464248408469701608510989610075899761360292317552⟩
def resval0Tail48 : Box := ⟨-9340779226322474549173709878028713075350218,103427965778511936450625311907103540396605360282162⟩
def resval0Tail52 : Box := ⟨-2391243356240943652763190706715557101408159206,1654845210665084737073255882834799992741195590537275⟩
def resval0Tail56 : Box := ⟨-612158378785754699955573873514702376652228345741,26476949472130159057400229086656832432784258224659201⟩
def resval0Tail60 : Box := ⟨-156712542504892403211881172682369413927268661681806,423484273537162403003915743948747271620059870452369825⟩
def resval0Tail64 : Box := ⟨-40118392668371099251461873494949134046548344353918693,6738137371030893583679004481556049018871230990910557804⟩
def resval0Tail68 : Box := ⟨-10269880259926721789072977474231591397385015957946308091,98181962106665082808751256515799515436366399753593583776⟩
def resval0Tail72 : Box := ⟨802593272532103243784598398114775544215487175793662309154,2479199047735045394788838416932805883201042878793349019⟩
def resval0Tail76 : Box := ⟨-27701392561710594182461715827442534643947625328372,606890027039009963107745312450881719056148101338⟩
def resval0Tail80 : Box := ⟨-1511003749812017712463353043207107847865529392,69498300149047237922794478131095641409536880⟩
def resval0Tail84 : Box := ⟨-862502212320586818749841434469545637570639,62427969228331205975930886430079125706736⟩
def resval0Tail88 : Box := ⟨-2408078827306616105986267517041071586821,416210447097302223875934224844623110590⟩
def resval0Tail92 : Box := ⟨-24198295620943401428903725004102146821,2629801071565622465692287325526807684842⟩
def resval0Tail96 : Box := ⟨-734678910942998017423692001802387953,42020400399209637682692278712240709313318⟩
def resval0Tail100 : Box := ⟨-60535525077725711333525844106065941,672324054796958515680856077800802944127988⟩
def resval0Tail104 : Box := ⟨-12690183206005957202233056962125086,10757184610422612707946973871069463854829650⟩
def resval0Tail108 : Box := ⟨-8403418595884003284025354058056187,172114953688281331478148867281347372507843978⟩
def resval0Tail112 : Box := ⟨-490171331181101630480197262940911675,2753839258567812323734888534973305673544635116⟩
def resval0Tail116 : Box := ⟨-123427557398433168740467299535523710703,44061428021399628944553370936557460709774475305⟩
def resval0Tail120 : Box := ⟨-31591290816735427722278414933415346353605,704982818725711338951216815143252635228049976941⟩
def resval0Tail124 : Box := ⟨-8087325284086694398941177437745632561197776,11279717517746479030059548172490313382167694954806⟩
def resval0Tail128 : Box := ⟨-2070354496991945491482326979168357718350491845,180473539326743815809114851624004490051971604517100⟩
def resval0Tail132 : Box := ⟨-530010742664356701303333009860672453649101170462,2887079744186315218991380053483876657538275712061993⟩
def resval0Tail136 : Box := ⟨-135682795198908197945919882698960694410445226571743,46066073316607691694839375738170889036349127950118625⟩
def resval0Tail140 : Box := ⟨-34735362423830951290733551322445417003776009481884550,704493047630673516069242063586234874092184867154404056⟩
def resval0Tail144 : Box := ⟨-9234545133669008959019679497751936296306161935095932012,2766164251335103515389001877063896735002069252187404139⟩
def resval0Tail148 : Box := ⟨63350397305483013450211424025384248875276138,1147164659450077274429385023549977266689545⟩
def resval0Tail152 : Box := ⟨1139822690348110977421322134935609872352,46775041851924136255017219948093994188⟩
def resval0Tail156 : Box := ⟨365482616240733931502791666621755811,24107815362124398237559204670701679⟩
def resval0Tail160 : Box := ⟨646012663230890882757308229050432,63687981268783118350100404744510⟩
def resval0Tail164 : Box := ⟨4351620795156232669158386150330,30080086590321861665144466867407⟩
def resval0Tail168 : Box := ⟨91417850480574243022806479932,472014750069862943726134374551433⟩
def resval0Tail172 : Box := ⟨5300097325634949735232854254,7551970182127287418635442647152747⟩
def resval0Tail176 : Box := ⟨786374072317222391175195893,120831501929937359388138136679866186⟩
def resval0Tail180 : Box := ⟨292626879577381630829177130,1933304026592180914785330614871959856⟩
def resval0Tail184 : Box := ⟨2009014396995574901351322495,30932864422324395064183526728453299971⟩
def resval0Tail188 : Box := ⟨450979321464993237924778971463,494925830335082673266706391663140606769⟩
def resval0Tail192 : Box := ⟨115319305679885003263770605204668,7918813177251856693513730761503045139173⟩
def resval0Tail196 : Box := ⟨29521084701491267848382354492276325,126700983160037294901959840940584062139646⟩
def resval0Tail200 : Box := ⟨7557389764263637668344340081541475111,2027208645508481580375172173610478303122781⟩
def resval0Tail204 : Box := ⟨1934691595454209586763296112620276161762,32433524554853809209990735706642666583873860⟩
def resval0Tail208 : Box := ⟨495281086396243490167291124869552783132799,518472066900540955221886640765731596031786337⟩
def resval0Tail212 : Box := ⟨126792181952472599118459836016954018620325899,8176685519242174289710782805889707173685376801⟩
def resval0Tail216 : Box := ⟨32471976486092332030518425029924547365182177714,100390508096509573154111645340605036877187403709⟩
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
def polyval0Tail5 : Box := ⟨2122011163437315395625820837523884012376442233230706,52595703982697281393609205837248681126280392307760⟩
def polyval0Tail9 : Box := ⟨207647879313875247813345271931101239985045519232,10168545563668270605701809241782637174227178169⟩
def polyval0Tail13 : Box := ⟨164925368788593093358059438433278896434287004,12526109107330394792779967859764637674338573⟩
def polyval0Tail17 : Box := ⟨583932194084720833471613687275950471544022,441239723869324027778482330822025812940122⟩
def polyval0Tail21 : Box := ⟨7050727945398617303146343817873957051358,6043403816847507599100204604677574951443817⟩
def polyval0Tail25 : Box := ⟨248208113334351808953471711741707960380,96677432957251997331700963955266107943419315⟩
def polyval0Tail29 : Box := ⟨23124074803145991550641316989130804369,1546838106429517941010636394086264446153176689⟩
def polyval0Tail33 : Box := ⟨5398838193333071644763713958913553845,24749409597895720306035077364882351655939124933⟩
def polyval0Tail37 : Box := ⟨8758552105458392174554017695841552871,395990553530487809184273197311764682128019127381⟩
def polyval0Tail41 : Box := ⟨1472219897353396882720394183694962288287,6335848855114823462359043168186909748929364111532⟩
def polyval0Tail45 : Box := ⟨375858035334297788210208869470809065188521,101373581329485026352030220861140981240197404528668⟩
def polyval0Tail49 : Box := ⟨96216352477677890836995734604101921055657699,1621977211069016306588446120162073302714190599507481⟩
def polyval0Tail53 : Box := ⟨24631360579876069777923207387637682395759999194,25951612285205251161643786900317916292820028426833883⟩
def polyval0Tail57 : Box := ⟨6305627848544896696353501862231812019493255959319,415219885037265177219332241948544482983728448273955845⟩
def polyval0Tail61 : Box := ⟨1614240725172785168931367337658245510018142144216991,6642004809935870654205590490622811278693857625611185786⟩
def polyval0Tail65 : Box := ⟨413245656043286976308848996782556239354698238643794407,105884659176666086788217710229503811279779845468053956436⟩
def polyval0Tail69 : Box := ⟨105791259541089731133621845662523742892676938280915218323,1594975423519374703119389313012395017500517273726305190193⟩
def polyval0Tail73 : Box := ⟨27343750000000000000000000000000000000000000000000000000000,2⟩
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
def resval1 : Box := ⟨115078179096748510168989126364324433132335572918161990438,238377215403970462427233091374500048411697450235450347⟩
def polyval1 : Box := ⟨3796585696273911493178044961311437313251840554295840361414,8710890822203524787162866824040471337072217502082639031⟩
theorem cell1_lo : Holds Q cell1 (1/2:ℝ) := by norm_num [Holds,Q,cell1]
theorem cell1_hi : Holds Q cell1 (3/4:ℝ) := by norm_num [Holds,Q,cell1]
def resval1Tail4 : Box := ⟨58051374935742451530635714104919804012945912144576,3115310705319022176705435404083259337169752775835⟩
def resval1Tail8 : Box := ⟨6880828685788118273782348060274208804311864559,6290024234827326222434977493413361363402345150965⟩
def resval1Tail12 : Box := ⟨-323654603827074005557030709274557719790568405,19878712552192741514235569243802385367520375526323⟩
def resval1Tail16 : Box := ⟨-2161808500306667966424708307497195052966493871,62825428167507107854162503013287717914765224456679⟩
def resval1Tail20 : Box := ⟨-14167788298382927193123390626777821047788207426,198552042578741126148329535468975425671841086869217⟩
def resval1Tail24 : Box := ⟨-92850019524376467488456145071117125642455163782,627474432129098813733883425901093247321474184260396⟩
def resval1Tail28 : Box := ⟨-608501888037139526954867285663051641866408688727,1982814019470609454223945927890066444288824838073534⟩
def resval1Tail32 : Box := ⟨-3987877973448470038958677512453415734371615169891,6264606757431660112312592798493187262503147636013417⟩
def resval1Tail36 : Box := ⟨-26134957086793903213824730137967167933313470290225,19785719693082438848870945954972670128676355169708199⟩
def resval1Tail40 : Box := ⟨-171278054764013596121250740055088586141756783013428,62443966271696771611928768972778789462263343416401033⟩
def resval1Tail44 : Box := ⟨-1122487859701440419303832321092147475903316985280874,196772605320224003749644646622747149660808341461042990⟩
def resval1Tail48 : Box := ⟨-7356336437339356464868782076158381610083279094438200,618089883983165742349480600526688198574741068914281794⟩
def resval1Tail52 : Box := ⟨-48210486475746988515911366587017094445422177780591237,1928508432384120712312680322875040038099089742867741057⟩
def resval1Tail56 : Box := ⟨-315952244167434216510507384894368047383820458143338344,5931455696920520932708632681707872984087413639007003640⟩
def resval1Tail60 : Box := ⟨-2070624627369003298615875335387542119888505076838358646,17674269606186590878513506063236977313507894948310664596⟩
def resval1Tail64 : Box := ⟨-13570045547246544508607262093348802910912190778945486518,48833570786164247236397096392080229537096902568876450657⟩
def resval1Tail68 : Box := ⟨-88932454309734832783758205472883403827532447851557015740,108293617527036511871129670807582731178554093200065960520⟩
def resval1Tail72 : Box := ⟨805501684971060182240709346622010338016134330519552286866,1509635002319520967509441718911059068413044579935017683⟩
def resval1Tail76 : Box := ⟨-27082194368676398560750523688843270384632043784959,403009361147923112452342554897868575160698295022⟩
def resval1Tail80 : Box := ⟨-1444036807719537374076398187976977095042093194,64296777397594481024425699594328972219276406123⟩
def resval1Tail84 : Box := ⟨-3606072179613163024995776270902805077549911,203072188625982169714979120227450217059990396104⟩
def resval1Tail88 : Box := ⟨-18357653349625255968370516925414615542810441,641798904023495104205916467177150091944747848268⟩
def resval1Tail92 : Box := ⟨-120294366525693765891111997304319056891072081,2028339192442578670568639491755195097021852557739⟩
def resval1Tail96 : Box := ⟨-788361020512972819693188953360869526301022476,6410145325617719401432010897326507337834277112018⟩
def resval1Tail100 : Box := ⟨-5166602779938800541988019857794942696250108031,20256549740173503205201534857543797210842017231100⟩
def resval1Tail104 : Box := ⟨-33859847978286207230143866455664629356295252517,64003169581602810161794049274700962049756100929863⟩
def resval1Tail108 : Box := ⟨-221903899710434562518559843129066864896646829947,202166732322175470832332848390569920363981336669504⟩
def resval1Tail112 : Box := ⟨-1454269397142276837716727434217945692798893248983,638193766069558844559982078584027577863166852045383⟩
def resval1Tail116 : Box := ⟨-9530699921111603473667016667924234560283475087594,2012072967726733909815043059218780451368971523665518⟩
def resval1Tail120 : Box := ⟨-62460395002997018647179952686551242651281991898692,6326805517563033287660278536530443744308144943776071⟩
def resval1Tail124 : Box := ⟨-409340444691642969954166922676161301675866815801695,19783895032060256841999985620925962589286156256066427⟩
def resval1Tail128 : Box := ⟨-2682653538331284361793991726795466016368950108981097,61137942536341495871703703450768883140339955242810213⟩
def resval1Tail132 : Box := ⟨-17581038228837795918559041993127120928716587569125721,184123561710893023286841250839792792456854494964543377⟩
def resval1Tail136 : Box := ⟨-115219092166658455986370180007481008935274926810711246,522267050877218682453576564480400327367464278784414020⟩
def resval1Tail140 : Box := ⟨-755100112409235072167470370254806611873133364647039944,1259671126933879922751751715910427930833181792910553903⟩
def resval1Tail144 : Box := ⟨-5091621245869806411345436697408397814339547205527793074,1392963417197638750324868518656772673976248014948173078⟩
def resval1Tail148 : Box := ⟨62409006883760829567416276091809547514655896,815782805103848355026302085824368893877202⟩
def resval1Tail152 : Box := ⟨1096149803925661312212817285790266687003,3068354227979097087534940947777861893049⟩
def resval1Tail156 : Box := ⟨461318212162996389418158260955686316,9601804798629779776855233729799591822582⟩
def resval1Tail160 : Box := ⟨771285309134185796078490991499316749,30346046583521914979184706351771190828575⟩
def resval1Tail164 : Box := ⟨5050811630826182372040314225634358607,95905877867339546048102929732826182675831⟩
def resval1Tail168 : Box := ⟨33100973663319522464402270943742296669,303092797061212845652346993234619806112906⟩
def resval1Tail172 : Box := ⟨216930540483056687478580042629144216584,957810599050975811004877223177026341718892⟩
def resval1Tail176 : Box := ⟨1421675990081077922586137395800829907497,3026418417533528260506270667944728168875978⟩
def resval1Tail180 : Box := ⟨9317095768591367548797742402009228705270,9560152829441826381699888565100447397780483⟩
def resval1Tail184 : Box := ⟨61060518829039099447804714673725452490864,30183190108996478139529016719432545488322762⟩
def resval1Tail188 : Box := ⟨400166216197989783689710460631786413160134,95186601200139447085636521392225941342178617⟩
def resval1Tail192 : Box := ⟨2622529314475145229635159856635161374697771,299478859063085149243780312577614240301969346⟩
def resval1Tail196 : Box := ⟨17187008115344323260709273931179758875968439,937602565028549952752298540883796576325996871⟩
def resval1Tail200 : Box := ⟨112636776384721241852151883632554098429979689,2904969775773760004481016809322171333831693741⟩
def resval1Tail204 : Box := ⟨738176377714998339313571853376664473077199171,8798950503181014433320435387960751543580451728⟩
def resval1Tail208 : Box := ⟨4837712709035075991408765960495724932277797950,25304317926917132268314943900568486867428547406⟩
def resval1Tail212 : Box := ⟨31704434128689388236537297475108338237758305023,63559267730330467161355355815642620421961535638⟩
def resval1Tail216 : Box := ⟨207783998542098229535257813906146557246819602527,93301048464558546054283379219535805171761099345⟩
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
def polyval1Tail5 : Box := ⟨2064686164689381420063486951383179630359520773158960,118508151700072391320727081487522386226007955903131⟩
def polyval1Tail9 : Box := ⟨199886599351677003993990003569168678505473389744,275025402066232320286407765358778755845980632378829⟩
def polyval1Tail13 : Box := ⟨15567941533477960557963207126065442734519960381,869191863420858844411133466409818335591590098676235⟩
def polyval1Tail17 : Box := ⟨101021796111568579305084436478835366473265735198,2747023218233336682892607303564081481737782890285384⟩
def polyval1Tail21 : Box := ⟨662052979009425334479857907544746477673913026177,8681607148418791192712738551924158323956354591789812⟩
def polyval1Tail25 : Box := ⟨4338830362658612593314114082806665324489104511634,27435919386381359073182257099173764719571283635866616⟩
def polyval1Tail29 : Box := ⟨28434958663343891418226298336298439820855631729381,86696331751045488071816300953758731293192176690355510⟩
def polyval1Tail33 : Box := ⟨186351345095968932778561189416121475309397935587453,273906738502872627641282721959332459696082975204607964⟩
def polyval1Tail37 : Box := ⟨1221272175220916049396092365652128031667738289860869,865048246356630438926889090751822205775821743816300743⟩
def polyval1Tail41 : Box := ⟨8003729327527783124454330675896096739923113539189143,2729835736649681432337733415328437442004734962076070498⟩
def polyval1Tail45 : Box := ⟨52453240520886069117015389448273166164727771588982612,8600471491456466510531915691267828769362914567560025419⟩
def polyval1Tail49 : Box := ⟨343757557077678954497488861643202875641147312354975498,27003757645221114409865872341729136945375693185620357301⟩
def polyval1Tail53 : Box := ⟨2252849526064277848940352174909957217480845878618387615,84178803458978823121622346555966935980736555922190385236⟩
def polyval1Tail57 : Box := ⟨14764274654014935493297412469249866663367683544909435599,258402431076491724467719654695333302215642174911811006858⟩
def polyval1Tail61 : Box := ⟨96759150372571853019479173567992749920666043561578000886,766582536874477456898927340897002001733889328815907801528⟩
def polyval1Tail65 : Box := ⟨634120767901871686156834422405117080042590288107012145253,2094465305389180546946905041416674526792267949733845148145⟩
def polyval1Tail69 : Box := ⟨4155774041868224792107991886337088705748698829516724369979,4467905544196705137159200264771335335621993960425800738522⟩
def polyval1Tail73 : Box := ⟨27343750000000000000000000000000000000000000000000000000000,2⟩
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
def resval2 : Box := ⟨114965170197304584444905387650940793785217530344130102603,219645599726390862327219216093476583654664562023714104⟩
def polyval2 : Box := ⟨3787560494887982082088994036588659028854739737475830902161,7418982603577282962438419681072249702914873619629869022⟩
theorem cell2_lo : Holds Q cell2 (3/4:ℝ) := by norm_num [Holds,Q,cell2]
theorem cell2_hi : Holds Q cell2 (7/8:ℝ) := by norm_num [Holds,Q,cell2]
def resval2Tail4 : Box := ⟨-136784068283086388941769845169232295627813767570235,34381514030443322339309559943997770031684188447409172⟩
def resval2Tail8 : Box := ⟨-445168041942977802037625673327376418806022815153013,58537847206850913639903761884988033373924300323796167⟩
def resval2Tail12 : Box := ⟨-1021496998388895261795871615024997258863166441486301,99600934279816469012292388363308042059287024177804623⟩
def resval2Tail16 : Box := ⟨-2343924501204872672688384814070763716825993759270102,169313500962861557944911149929834286849599799220736329⟩
def resval2Tail20 : Box := ⟨-5378363366565783606152637986828929576387373508369503,287461626096535712372063393916690629690879034766282654⟩
def resval2Tail24 : Box := ⟨-12341179286134067288530524264358956495596995263127657,487230914358541020490854136833731924307101449509840874⟩
def resval2Tail28 : Box := ⟨-28318039483774481910344446732909968397746045286051681,823929897029590449883037707336559067200125499532348421⟩
def resval2Tail32 : Box := ⟨-64978503400043573998539679053737308345324609480555014,1388918851018424882592368494830808315574819831982459378⟩
def resval2Tail36 : Box := ⟨-149099513281231598344727564778840171121733597979207157,2331185186301461778913806728658900946445046021032061399⟩
def resval2Tail40 : Box := ⟨-342123374615692518941516032844948945669471025727641689,3889132822589935166674668321289988566121527583756856691⟩
def resval2Tail44 : Box := ⟨-785035449697630506994858051363640908271432066638041380,6433300820087563578189476109203023177809304660858761256⟩
def resval2Tail48 : Box := ⟨-1801340402345292976358762661256289986384974225339833896,10512822596838445029209558205589570159133390037865067260⟩
def resval2Tail52 : Box := ⟨-4133351234484125699050547304521915982431081298483541347,16874067193111288826828794737701801813567442101513575321⟩
def resval2Tail56 : Box := ⟨-9484377525407063081740989078056924186954730053573618569,26353350870857314663198172508346419852602537669167042433⟩
def resval2Tail60 : Box := ⟨-21762829225339415101544679292873256725131888816375742645,39374753244916916260125614739761561344144297955159807741⟩
def resval2Tail64 : Box := ⟨-49936934136301250504953486344973893215116309031224897778,54361082430904093064582472032011910397952492844221277160⟩
def resval2Tail68 : Box := ⟨-114585011480633140269577113004248317147410034356708581586,63342650950813906672796533223301223964931944718734752482⟩
def resval2Tail72 : Box := ⟨806954164935635237935245609281511504245195613022848954127,1025288539358502096680834634431919182060398912972999811⟩
def resval2Tail76 : Box := ⟨-28927250781405108233767735443165737513512057537205,409752422420030115211621352230083496789329139782362⟩
def resval2Tail80 : Box := ⟨-4916122788882476921320504167872464076099116074875,697650969489414865091703847895973347737632547728293⟩
def resval2Tail84 : Box := ⟨-11277283205903170445337220489511475092298389822764,1187268737647436876949773533659149500985651337576899⟩
def resval2Tail88 : Box := ⟨-25876824381210827126958151023124874962109915818045,2018789772119945956758426457082733623463267776846202⟩
def resval2Tail92 : Box := ⟨-59376897255347916631032435903889645704969614723340,3428734047875875324071622425425844430089173690155166⟩
def resval2Tail96 : Box := ⟨-136246081668189737196955434848140580456783861107005,5814317196656427835072949550905809104620735895158926⟩
def resval2Tail100 : Box := ⟨-312629922208831804490294422330743308013048568516096,9838768323529456898561212896095672471608696189682371⟩
def resval2Tail104 : Box := ⟨-717359846709779011500750522920595209541876058793346,16600477393833340666654216681377167717034297441063455⟩
def resval2Tail108 : Box := ⟨-1646052131016843836586861990735826080751923833010639,27897413648768503173150234077161286325077093433456394⟩
def resval2Tail112 : Box := ⟨-3777027150951292935454236063558341455706073544876148,46622821176412630988937514723712648973028879495442489⟩
def resval2Tail116 : Box := ⟨-8666757164130945481847872667508167096923440976340007,77313159016161696084566269232091399906203602516300192⟩
def resval2Tail120 : Box := ⟨-19886719565438382594500398733829969292322756357518069,126791221573453187588781628460427902151949182867968959⟩
def resval2Tail124 : Box := ⟨-45632017556828188661918622453433573616008662842816766,204594074448544520771819154928917664609979260243542531⟩
def resval2Tail128 : Box := ⟨-104707114688011470090620772784139946531831500983678540,322167551223694845639715296009077353978973116535270152⟩
def resval2Tail132 : Box := ⟨-240260686537384341570277486049368792374354528109301095,487968647729338506237286921375213575687965340233773853⟩
def resval2Tail136 : Box := ⟨-551301577452115297224246188991495485175279497166864088,691025516762118171581033627828181225203484835640835849⟩
def resval2Tail140 : Box := ⟨-1265015450047376606868432078402923946142550025593015733,854339916960246718511118083328881988865415475004836053⟩
def resval2Tail144 : Box := ⟨-3013471138141161264894121193013074649160819453268674323,702652794409890117810674472516178261802016118445014702⟩
def resval2Tail148 : Box := ⟨62213373954062822587766235845775641320610365,47134669062839161341077455477506145982158064⟩
def resval2Tail152 : Box := ⟨598183122585571809239846190040989010221768,79217298913670546012721522690789473094624382⟩
def resval2Tail156 : Box := ⟨1370121619302442799247688408480442511431771,134789719884313282589297362907632067411673223⟩
def resval2Tail160 : Box := ⟨3143876915353120384161143822716787278052064,229138800893355258224294383096912118395615197⟩
def resval2Tail164 : Box := ⟨7213932197308439216924417422959742779719427,389050061264627596114125568027949962045223860⟩
def resval2Tail168 : Box := ⟨16553070987800338203383741387213968422615926,659455807487865917494821587105734942570111689⟩
def resval2Tail172 : Box := ⟨37982635771033163580353215804648832812273749,1115258666284913807044830717591121651715563495⟩
def resval2Tail176 : Box := ⟨87154862150850080634542779342974274939194263,1880223885546425544156796850277234470234717724⟩
def resval2Tail180 : Box := ⟨199985331253041239861731205162876387848200953,3156275955947309012947794356722761748420131229⟩
def resval2Tail184 : Box := ⟨458885846749039273381235246460871016770810557,5266747736080046372158381632215474742276139209⟩
def resval2Tail188 : Box := ⟨1052958329629391051392155238740110067736440788,8714719785850798371361130082384833429512603637⟩
def resval2Tail192 : Box := ⟨2416115580357542521919368579820079151371847685,14247112058545771046297215775848592513663535118⟩
def resval2Tail196 : Box := ⟨5544012838286891467025340428714963887086950151,22882717860983401081281678122825129792595932762⟩
def resval2Tail200 : Box := ⟨12721278154475324324467047373490037407823539305,35773469427453505168007037281783190853890963441⟩
def resval2Tail204 : Box := ⟨29190213407503135181568227101944682513930514912,53539685007982347535484750414192737749753049255⟩
def resval2Tail208 : Box := ⟨66979791529537128348250105624123065100873761547,74153762785290492243225597737258241176502136812⟩
def resval2Tail212 : Box := ⟨153691664170925866886814929984584511325025274377,87075948771777811067505811611334895452661794938⟩
def resval2Tail216 : Box := ⟨352665060403483995921359036210557160329277564876,58077927588928870810896405301235776559366517592⟩
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
def polyval2Tail5 : Box := ⟨22152013227390286638321016944674188297005793014123978,3085826070464880626832564239068611634614988719175139021⟩
def polyval2Tail9 : Box := ⟨46155156438494055915924309941374804226754310585158575,5252439840218170038628896362726151651531537096581586106⟩
def polyval2Tail13 : Box := ⟨105907065456073524260928812376893831720687985939257775,8933261744855646831324098421287092300446665374415507857⟩
def polyval2Tail17 : Box := ⟨243014090264163015584385001844300061279246201795029528,15177408836194305972886479566176229026135332201755719452⟩
def polyval2Tail21 : Box := ⟨557619530811917890879124811094783830866919941245550057,25748941196706534474677220504183322654828498832540172931⟩
def polyval2Tail25 : Box := ⟨1279512397020043804092303360579875569702242953805479062,43598318814939788250956466977723911393938284832044464514⟩
def polyval2Tail29 : Box := ⟨2935965983372626246426254808030563492108635834399260353,73623632785551768296131215749852764078997954639304562907⟩
def polyval2Tail33 : Box := ⟨6736860288025924604756094741076740756643280385463388278,123870435237802613495485962038419136610195757996714128403⟩
def polyval2Tail37 : Box := ⟨15458382964044220955136510816555352320536472432567885870,207351897116669520005204280302953617700251945053680073371⟩
def polyval2Tail41 : Box := ⟨35470767337684327035281971423735433495444382240330416230,344633733791263395984148382160318673159079782230411672006⟩
def polyval2Tail45 : Box := ⟨81391135052781067072038219557908185521043451107105969529,567050362916469192608136248466298368834822633716842983506⟩
def polyval2Tail49 : Box := ⟨186759897301182031893433960970586487571114911623334793986,919452670663019993821054580173320585330172400873469461892⟩
def polyval2Tail53 : Box := ⟨428538798695083003928329968597262980861011753901779014992,1458611004878999253330874795398115986171083493165330450920⟩
def polyval2Tail57 : Box := ⟨983324068179719264163249756364295145560629593389476241108,2236070182315674772237447833015266100443927032652875227343⟩
def polyval2Tail61 : Box := ⟨2256332976164229157085520038174365860274809703501147020916,3235811484489318691076901155521552352758595508793031079045⟩
def polyval2Tail65 : Box := ⟨5177376069688201384449914051489797353564793298585825184126,4191979911516185909667614863756290247605436721221389221047⟩
def polyval2Tail69 : Box := ⟨11879994471616189120372181420152431136895443896866229437526,4103713317239039719317374442205627121050029467081950340192⟩
def polyval2Tail73 : Box := ⟨27343750000000000000000000000000000000000000000000000000000,2⟩
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
def resval3 : Box := ⟨114782165488345338770528510013154627063740861639911222158,1732712929349724324911244456932536579239987207820501064⟩
def polyval3 : Box := ⟨3805836974681654086911795707900665933383687273930919593058,241322713124093610249880642226740559021041303748015431469⟩
theorem cell3_lo : Holds Q cell3 (7/8:ℝ) := by norm_num [Holds,Q,cell3]
theorem cell3_hi : Holds Q cell3 (15/16:ℝ) := by norm_num [Holds,Q,cell3]
def resval3Tail4 : Box := ⟨-188340942964126034713384832636785085744660880579644399,1987436125939477166086978814563373434430839473638040710⟩
def resval3Tail8 : Box := ⟨-279308183739768854026846996462612159184780462262727058,2537391244957076620141615252119529035702021713827400723⟩
def resval3Tail12 : Box := ⟨-414086996644910678245939005818303406167613307195218852,3232238221884648527474728102054428840101106467512278038⟩
def resval3Tail16 : Box := ⟨-613902659056444875935160073423328508492785800160287392,4106404887055703190219253625113610076153709851725401458⟩
def resval3Tail20 : Box := ⟨-910138395662819295740747824797491979458076083712768618,5200480376524976424265285184054775437629593759457089772⟩
def resval3Tail24 : Box := ⟨-1349321243424518278779784174221328835138492524276812628,6561108620360161194121361543064953875009171920101344031⟩
def resval3Tail28 : Box := ⟨-2000429634254430261689253444146134004286702959301202960,8239924569261476001446062348356678064503985069687634509⟩
def resval3Tail32 : Box := ⟨-2965727206256033269793971995712547143601974055230623005,10290803224985812318621813400958129505448885561610701912⟩
def resval3Tail36 : Box := ⟨-4396824417773312646725128908157928955382235649482412485,12764261574164773130840628806295958270576106609604750512⟩
def resval3Tail40 : Box := ⟨-6518490615032878137334768615624494581628107445989934540,15697191983834369062933853058497762526191555259376017649⟩
def resval3Tail44 : Box := ⟨-9663956496991599131497019344679256248370763803429142132,19095094857069910250761477420557006126432130921821963670⟩
def resval3Tail48 : Box := ⟨-14327251612569068086844949444210347503855382309892231010,22902441020315377906777965191780794899644558551575757134⟩
def resval3Tail52 : Box := ⟨-21240797062131208085431509347312415504960171048108905199,26954464891226126050015885380190542843248355467741656206⟩
def resval3Tail56 : Box := ⟨-31490440178968870008788543004298722585759706528435073098,30900170929677555869982020890870513881859606133608340844⟩
def resval3Tail60 : Box := ⟨-46685998635759850654665266982343914409444714447870965427,34081035233197868168312292950237878627745435230944775915⟩
def resval3Tail64 : Box := ⟨-69214099770770818548333186532577127164056359931561855586,35341916648649683144752132366942275553789121381409164096⟩
def resval3Tail68 : Box := ⟨-102612887104743479322202735599688507288161908434983265237,32738737800259539413318358721498291580842184834544634161⟩
def resval3Tail72 : Box := ⟨807678420166151934579059768615775528425391301818486743527,802536629876077224137934044698455686678979654761874427⟩
def resval3Tail76 : Box := ⟨-2346396343767208741730897226522075460731628989018113,25437446520155819164086898378440723606864499542953066⟩
def resval3Tail80 : Box := ⟨-3439144853831642074814667252188245133304140238949972,32493471499014814696263029994378545022066544835630360⟩
def resval3Tail84 : Box := ⟨-5098685373489985469868686478138346028804509620795998,41417459869481315098518691036643576629961340789510615⟩
def resval3Tail88 : Box := ⟨-7559031153656651183653036036047655444826067655715829,52657899109897759836862920359804656025740333260886298⟩
def resval3Tail92 : Box := ⟨-11206604802015796161616954038529541591346869290965710,66746516022718329861156201333510746135428110611312841⟩
def resval3Tail96 : Box := ⟨-16614297339923587850463863113689405380609205851384431,84299000958738621972921809385697132710823521569618048⟩
def resval3Tail100 : Box := ⟨-24631445560544840713246800602970723714522266808317269,106004681200958893523930023961240545443436776836371542⟩
def resval3Tail104 : Box := ⟨-36517229587807203720884243341765535924631297512588719,132596236159193462436812630057443801639973810235878214⟩
def resval3Tail108 : Box := ⟨-54138440778508862025887590611777283139167545896505325,164785412874734311443070755211899741576709096866800680⟩
def resval3Tail112 : Box := ⟨-80262681561876691875939205922194221987156662509551841,203142625559485177089347856920684084454708987762317661⟩
def resval3Tail116 : Box := ⟨-118993047432952976349505338521696634052481510931595087,247885969011601521324839654936564611015560112782386043⟩
def resval3Tail120 : Box := ⟨-176412562623704157452886552769577310050486221654727754,298526365212549147496549040758666731273708805107255792⟩
def resval3Tail124 : Box := ⟨-261539585066915712315897128145194986395277298560143384,353287033692130147915643721315964533111260295382931937⟩
def resval3Tail128 : Box := ⟨-387744237369767163860763419484460642959286543887616580,408172351015276480617139271248414943292916840050479022⟩
def resval3Tail132 : Box := ⟨-574848329651520781104245807880034252614873823022200143,455496155018173506289979847931351677341559427461202995⟩
def resval3Tail136 : Box := ⟨-852238589935805089712254834447500229115547009935160936,481581778426583962106109904323465615444967704054363648⟩
def resval3Tail140 : Box := ⟨-1263482361482201993815391922433365581316163576945245817,463199332039878263529839504165006278200319686440638482⟩
def resval3Tail144 : Box := ⟨-1972722665361505709761334135971026418182716028040133816,356568967065759204522398086379035384860071183396672720⟩
def resval3Tail148 : Box := ⟨605940432148531677739177031241022823970799667,5316998638336736152495373862872404728648069453⟩
def resval3Tail152 : Box := ⟨806819425418679745687062135712055105636339150,6780210602553848272756094926345963273156905903⟩
def resval3Tail156 : Box := ⟨1196144627855025241406739619862672262420619463,8625554717886523952731239985846105849948100071⟩
def resval3Tail160 : Box := ⟨1773338388777545583137165667934350203603190471,10941227306049897783280200675286003575557814211⟩
def resval3Tail164 : Box := ⟨2629054186879358837468605703491848761035617129,13830437711909264063961986964456814367922536675⟩
def resval3Tail168 : Box := ⟨3897691473489612808046194972978996657579031137,17409750720663689901295144622079418846138194403⟩
def resval3Tail172 : Box := ⟨5778503500738524245060020847538580570561994583,21804795889602825711983651993352500290571923937⟩
def resval3Tail176 : Box := ⟨8566892206619997985217767567146514142242028613,27140744511314040741319263532990429616075439648⟩
def resval3Tail180 : Box := ⟨12700804294825919269558216104927508349414570408,33524098025105441954159198174941788029641230097⟩
def resval3Tail184 : Box := ⟨18829515516819175297944563344414941764797799770,41010389637531870413667036305499772221916128232⟩
def resval3Tail188 : Box := ⟨27915606474038159596076924126746748228053248928,49549440917478880043584880864894203823842299100⟩
def resval3Tail192 : Box := ⟨41386146346531346434250736505244688898111357310,58895322213477754007564254205813886944687014581⟩
def resval3Tail196 : Box := ⟨61356829593132649018458131401658624359058367812,68461369390546489890440438226987093572959602065⟩
def resval3Tail200 : Box := ⟨90964268724097863536785766349060017177693209922,77090358211100083622149104362519467294679758936⟩
def resval3Tail204 : Box := ⟨134858633331928457864142393383673694000292661002,82694512955975460356424687007402952927950560699⟩
def resval3Tail208 : Box := ⟨199934009685941710559219280218373851831474588689,81696864291846359482073456203340772208292335303⟩
def resval3Tail212 : Box := ⟨296411191876065147121467262884667030041739686681,68170753032893156183756473834789439553826186158⟩
def resval3Tail216 : Box := ⟨439447068039422530327536087718968396462706913150,32522025097751897303694340460513202426365994959⟩
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
def polyval3Tail5 : Box := ⟨33771466241348411029838777557515156732734777046449961596,304896530708384346212067276168078805650728196552700552036⟩
def polyval3Tail9 : Box := ⟨50064722135023826260081919266134195289014415614453288483,388351333113832044550952657153027665562166251229408836757⟩
def polyval3Tail13 : Box := ⟨74223209555561548090879173519374172039983208414446125804,493323152601509543683766901945610177953693612538043426652⟩
def polyval3Tail17 : Box := ⟨110039257639863197220645698066243836676677288619008408650,624671229082431287548136851315056367076904425597442040837⟩
def polyval3Tail21 : Box := ⟨163138165197392092645874696751275280707844459797596293292,787972678414109309886533435214487853566528521726001291099⟩
def polyval3Tail25 : Box := ⟨241859691848106488186501691155224468863572352052326652204,989389695745441275539404915704915588129253738734783201151⟩
def polyval3Tail29 : Box := ⟨358567907577497640636364777065099117273519647880906251242,1235331546552492408373961757711096427710755463567080902734⟩
def polyval3Tail33 : Box := ⟨531593104092973183236483912701307177718109443278071638798,1531770740368518724929856064468165597238339932484248464134⟩
def polyval3Tail37 : Box := ⟨788110766042624428738856416707355877344118184397693568305,1882992698858675989896402141728205734906671705933521244829⟩
def polyval3Tail41 : Box := ⟨1168409775766507163332497678748715841951338408832004603009,2289435886964784179593841866611629816966081596696022937038⟩
def polyval3Tail45 : Box := ⟨1732220219451874170663956332467960584551324364961715672488,2744093328256924040697463033583129456077687980526433057303⟩
def polyval3Tail49 : Box := ⟨2568094645313487016351415621877078856655623209775007239488,3226664557899230012425009272990134359884914449344091565075⟩
def polyval3Tail53 : Box := ⟨3807316202194368239004413013440005260618490187869839923541,3694221361099431726367023827444596112204161374902843454964⟩
def polyval3Tail57 : Box := ⟨5644518082674583257023323666088848707535829916127018941899,4066509388891292845542796241545032633750842123173593704080⟩
def polyval3Tail61 : Box := ⟨8368252777974517154361078603879681740198049295257293695305,4203043940574459564125522164244804876812573991928098363697⟩
def polyval3Tail65 : Box := ⟨12406312377863854620934756563310983586617314899865458862575,3867712348013055180344736815186636581316359805700642839094⟩
def polyval3Tail69 : Box := ⟨18392918087128491242096062442698802487443509887810947135415,2674429871688257177554197840382663684409467138160489220237⟩
def polyval3Tail73 : Box := ⟨27343750000000000000000000000000000000000000000000000000000,2⟩
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
def resval4 : Box := ⟨111574971938396956039399343481653682518713494598210572880,8790096803325618985751867445942612688454714602770660762⟩
def polyval4 : Box := ⟨4640834670354053248483328475430018306917659217622595406941,1915098725778712059793033901997357286980688936753479143649⟩
theorem cell4_lo : Holds Q cell4 (15/16:ℝ) := by norm_num [Holds,Q,cell4]
theorem cell4_hi : Holds Q cell4 (31/32:ℝ) := by norm_num [Holds,Q,cell4]
def resval4Tail4 : Box := ⟨-4006329096678659341069270880407766299310468859594164273,9535243808248463246696907251431201800268418390664379108⟩
def resval4Tail8 : Box := ⟨-4854598469871959081533738197135291293169085049401820527,10520717447040153339183687237808322043600349264930598293⟩
def resval4Tail12 : Box := ⟨-5882390765114426891805896602530788034934668761340259718,11574913692203570725215157718451717887410907361893249850⟩
def resval4Tail16 : Box := ⟨-7127782303929952548681627800730990681891242561235777461,12693435057280704667350730058268973898060000815491315640⟩
def resval4Tail20 : Box := ⟨-8636842161773404585853688681698552835804277868114896394,13868388164065259233114947176173263127730891453610698985⟩
def resval4Tail24 : Box := ⟨-10465392929615424343533823798629564741613005625463757615,15087295524839431622416621692173504916311821376122161823⟩
def resval4Tail28 : Box := ⟨-12681075689445716682507226107975652935594104919585478896,16331730569229998389753382825867472432231722912014632801⟩
def resval4Tail32 : Box := ⟨-15365852168472807760279632119463201485760316671683266635,17575610273092837859479588317465301879325055085159550632⟩
def resval4Tail36 : Box := ⟨-18619036637394339998782182706618743305204441026444061905,18783065665777042591835752859628753520615879188931151495⟩
def resval4Tail40 : Box := ⟨-22560969707616786826914375672011800171118129029192523146,19905792634171040056533963937547682303759681580150289681⟩
def resval4Tail44 : Box := ⟨-27337469927189231612030321009053287820163045927502324818,20879763670425237751843100695961545410817148338294344291⟩
def resval4Tail48 : Box := ⟨-33125227847261716462269355657922216448099041407166989489,21621154678801242387167804434965574850615586181355831312⟩
def resval4Tail52 : Box := ⟨-40138342094404003534848410805888868941545680186191901158,22021308637576095373025593417843287525190167237174165034⟩
def resval4Tail56 : Box := ⟨-48636239228784161684058131187703020939634223959728941767,21940518555756468656608961460261332627545896559073186375⟩
def resval4Tail60 : Box := ⟨-58933270356702610372117078258459955818700646263878318160,21200364255480247836883243313552913545408069455731491385⟩
def resval4Tail64 : Box := ⟨-71410339484426647189488623883930544366066004441161601145,19574279208561192125970334479031715043456957987913579905⟩
def resval4Tail68 : Box := ⟨-86528861000644296168709886920902554152130019882309562842,16775949919906614286230917742578516556754317891651046671⟩
def resval4Tail72 : Box := ⟨807999992023010242311220038817189948797839450221302066504,774482406855577816932022239737617326967327455842113312⟩
def resval4Tail76 : Box := ⟨-51885799425198250949144535202922576869303787044147974,126415078184211066793523914991268754316107002310975235⟩
def resval4Tail80 : Box := ⟨-62838620325725002704779589143004623501793110201106176,139575855699504059658335352092732193795937658692048693⟩
def resval4Tail84 : Box := ⟨-76142509728309310171512055951861585086485482730560944,153681132765760038530952537239375350427393255429272602⟩
def resval4Tail88 : Box := ⟨-92263036422359608298420405903410329986039115591744988,168681279679873761085659094063065460538109814227597280⟩
def resval4Tail92 : Box := ⟨-111796523654558831068284669484801927883720266957147672,184482550888644068864921578943965644204170700423736382⟩
def resval4Tail96 : Box := ⟨-135465547047784426652190932800628901282543890347339266,200933004656197944345630822598224288388156539769252195⟩
def resval4Tail100 : Box := ⟨-164145662468523337695392447387941100547384542211676520,217804989169668991515797600548432344472423676545227307⟩
def resval4Tail104 : Box := ⟨-198897794268871731008389747007573467922008748923503360,234773217535049522273892589867944666771504004999289243⟩
def resval4Tail108 : Box := ⟨-241007480612584176528788659772410148174620309859234520,251387402528468958240317718674378546413150353949598383⟩
def resval4Tail112 : Box := ⟨-292032427633188698888217539966341402839372278247895960,267038191209818587186109887997459257603167945310827642⟩
def resval4Tail116 : Box := ⟨-353860131530210087644298310272539219481939394752340051,280914858127767595600666272293184955191005705877083261⟩
def resval4Tail120 : Box := ⟨-428777700139034181235658643541665935980129167346688540,291952872913017268867841269383904015937318600941479874⟩
def resval4Tail124 : Box := ⟨-519556456788418017746691257620504184592857056798440050,298769040269719158138492119453037813628840243347532448⟩
def resval4Tail128 : Box := ⟨-629554456080635108228187645676386664983274428211377472,299581401580677776873823532481843428857367365385936730⟩
def resval4Tail132 : Box := ⟨-762840703820564991101761930419907405586598654822372924,292110467926571857675760694226742504849529681750352866⟩
def resval4Tail136 : Box := ⟨-924345676213112861486148789389798765535375799416772870,273457600468473941757325701492878367563321695966026779⟩
def resval4Tail140 : Box := ⟨-1120043890287424673979640391595913116927784117530987314,239955426754675681485009249970435549671299805809948905⟩
def resval4Tail144 : Box := ⟨-1451929887346872222446240899615361885859791293800681615,183294831997123267667022248661487803342615451207768802⟩
def resval4Tail148 : Box := ⟨18648454273872646607816784620365788599193305854,39621446917885149401360880557531896570949858913⟩
def resval4Tail152 : Box := ⟨22521953786394092558382740274017797047366725439,43567869278969958924001726089816242044613659525⟩
def resval4Tail156 : Box := ⟨27290192457238777774225850101133771289685115460,47748925424640580887669209782256888598498070073⟩
def resval4Tail160 : Box := ⟨33067941017897709948508610417316423568714450026,52132306807285554360273349375109127499133800709⟩
def resval4Tail164 : Box := ⟨40068926772488612372704698027039439766394460114,56668380839941179357133011307235786466450337723⟩
def resval4Tail168 : Box := ⟨48552127628088770370329437800334100525152880659,61284485797064720968451750757733742575803487023⟩
def resval4Tail172 : Box := ⟨58831351051627197404066619618668539605723767300,65878359673839518846608316382027437323726437697⟩
def resval4Tail176 : Box := ⟨71286842320735637673738874392374192499621672885,70309948259735177234962219370935459132353449497⟩
def resval4Tail180 : Box := ⟨86379350418145280748449115764493548821060799425,74391218177163071972521829662524415780345547508⟩
def resval4Tail184 : Box := ⟨104667171889733075404834051613150625150655191893,77873517207097479896719437053008382968220109456⟩
def resval4Tail188 : Box := ⟨126826803146387423372319485794385082680569388333,80431922546258652197091864391747234614921824341⟩
def resval4Tail192 : Box := ⟨153677965172099074488590205772796310680635479597,81645893789301967108814910818392933971343956696⟩
def resval4Tail196 : Box := ⟨186213926343136783552817754667863961515642715479,80975396622242518712076202237614831632449730779⟩
def resval4Tail200 : Box := ⟨225638245048957007641640601332269279485404632130,77731479643546538833297501550800102834416408679⟩
def resval4Tail204 : Box := ⟨273409291284457422285377618879245597009192477017,71040063347615541692675862214372882579168129519⟩
def resval4Tail208 : Box := ⟨331294194140079963245339333586103364808299820566,59797428554700457102419542809792491382035256225⟩
def resval4Tail212 : Box := ⟨401434210877682204034356595660710718726162900298,42615561060184682856029455048431194953478561294⟩
def resval4Tail216 : Box := ⟨486427842783315703684492918360929377559570498388,17754895302766802145948617611367374573554566408⟩
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
def polyval4Tail5 : Box := ⟨1042096619124396900850045769906389034677615083857328426360,2106794447616268738123013980139998644037743262924970367202⟩
def polyval4Tail9 : Box := ⟨1262721869108481288135931061126476043849476253497460633899,2312561719406199648075638959340313467601769956902086291978⟩
def polyval4Tail13 : Box := ⟨1530059282262371717852950708854905867396742105264781418174,2529357410925697366419775904064910226824905865496595069667⟩
def polyval4Tail17 : Box := ⟨1853996089606861829061608751886974074716774574353239365575,2755110707614012559079609873031757988657055099692515786220⟩
def polyval4Tail21 : Box := ⟨2246515242988105081290008659750460789328545956565259928592,2986715803195657995945862464630266190130805904676903114645⟩
def polyval4Tail25 : Box := ⟨2722136667530988134800311230785345478417221050991086187757,3219731982432776139643648081085102739783664510918404467352⟩
def polyval4Tail29 : Box := ⟨3298454377216058932645249855784084244684733366678791342206,3448009278190157155180083351044110711409398848716929309290⟩
def polyval4Tail33 : Box := ⟨3996787306217029314542087338339179299276106054618772587864,3663222454179570698334449164487256994332268780935262516555⟩
def polyval4Tail37 : Box := ⟨4842967931125400305288046405072288943222640535458079977476,3854292222696359302884786836698075244236173721476199810517⟩
def polyval4Tail41 : Box := ⟨5868297856487299255298752980175985864945494955193639640276,4006667913705046563474329693132843837947088539276327142819⟩
def polyval4Tail45 : Box := ⟨7110705712323608285177432544230381309110061052475762157742,4101440094263582703732327900318012942585191996004301674472⟩
def polyval4Tail49 : Box := ⟨8616150196155440330456081293612423716037285833657331116692,4114244674440864873675281705679257450849488319454127360623⟩
def polyval4Tail53 : Box := ⟨10440320160353003621404450267308220460300755680252860594162,4013911559153527715310031555055850248459340821759691112049⟩
def polyval4Tail57 : Box := ⟨12650694633817980356165313736575127115062936882031200294016,3760800588828045732594647124835819503494052009049164488426⟩
def polyval4Tail61 : Box := ⟨15329038981568931902212596713490649954478928095228299929762,3304754959858812283921198950769699327687238756093662196130⟩
def polyval4Tail65 : Box := ⟨18574429539267363796568334623669935565306791958099202019728,2582587048269717750163451405031310438732014243219045616756⟩
def polyval4Tail69 : Box := ⟨22506918729778049272195192190040311339904342488455430405536,1514992987612204187133201477345052791757240406502857632853⟩
def polyval4Tail73 : Box := ⟨27343750000000000000000000000000000000000000000000000000000,2⟩
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
def resval5 : Box := ⟨99814555252533938702919569217998111986422137750481244477,14024057422533223626496653789456800795186493941701876703⟩
def polyval5 : Box := ⟨8724476511254887048837487836227265880217728466239026048310,3834227412981456044838539852199388707355138882499673882659⟩
theorem cell5_lo : Holds Q cell5 (31/32:ℝ) := by norm_num [Holds,Q,cell5]
theorem cell5_hi : Holds Q cell5 (63/64:ℝ) := by norm_num [Holds,Q,cell5]
def resval5Tail4 : Box := ⟨-16550751707754407726058402578272616018577279691808384328,14240680662373514277181664805392533566380520178791373586⟩
def resval5Tail8 : Box := ⟨-18197806095232219281162215764275625976133450543349209752,14595739904697113838604138464890884506176241668385647534⟩
def resval5Tail12 : Box := ⟨-20008699408994784698891964365268914486578346811408362742,14917077704011171480071899330432635285142331724415987440⟩
def resval5Tail16 : Box := ⟨-21999797656870924999638521003457953596753758720589815645,15196847887598603163257001605007267222783981507510407410⟩
def resval5Tail20 : Box := ⟨-24189033332448805882372536381565582440771774938455279506,15426132145013065473163197559197104854277611878224876092⟩
def resval5Tail24 : Box := ⟨-26596123413688708628393814295035515076186007642012423334,15594813775270303712453456827336673303659157543899450054⟩
def resval5Tail28 : Box := ⟨-29242746947116257875760565141374634071176552299096920631,15691438217285416536131364195410498270626363182691144402⟩
def resval5Tail32 : Box := ⟨-32152740296465451287050242195565255845106453695421954607,15703058387170114266771745865855222161718372573335679690⟩
def resval5Tail36 : Box := ⟨-35352311820825717164110081224730998854513582237949911632,15615063224911369887638225141748903639861136977431975891⟩
def resval5Tail40 : Box := ⟨-38870277915760810735447040350647484375463439376119891364,15410987688549451232188690984755367031747578811334481858⟩
def resval5Tail44 : Box := ⟨-42738322543263673616549263730584821134224426437071004632,15072302252727619451135071465401304664333897566780931259⟩
def resval5Tail48 : Box := ⟨-46991282587959557954105793473301446370582077249148141825,14578179768819072919062237622249693686452772799237972751⟩
def resval5Tail52 : Box := ⟨-51667461609569419256947723194829362954675528209790968796,13905237323891036254462598780177416607942877968117249498⟩
def resval5Tail56 : Box := ⟨-56808974817391644633844459636644065696162021622961580925,13027250493496600939677326076922315015459188880314422401⟩
def resval5Tail60 : Box := ⟨-62462128373751286992281363360885604819956084030936178704,11914837116441908791866914921168819253375613908261416757⟩
def resval5Tail64 : Box := ⟨-68677836435266116490462153354943351487374863047737648965,10535107425478382741761309613466556446127589447133691585⟩
def resval5Tail68 : Box := ⟨-75511949918251074548191083455309956089667112611365859805,8851273277299227047773129707670729300874205372243943562⟩
def resval5Tail72 : Box := ⟨808024933591574147626288158737163971660959716875026004102,784321101088385029362244627496240679860271976767192144⟩
def resval5Tail76 : Box := ⟨-219085988347768938223807055112455778425859146369123093,191629420043238278885335637654722212715295938876516724⟩
def resval5Tail80 : Box := ⟨-240858420542949015440979059741461228817408658906965948,196533222268870021543347542327793216480823061076860850⟩
def resval5Tail84 : Box := ⟨-264826632511353783369707131089880284389579001230414192,201004143336040036321003355540519206756240982905018144⟩
def resval5Tail88 : Box := ⟨-291179961790163204120483801113281426841271278466501543,204939056458302785909095068559545522692270509260209354⟩
def resval5Tail92 : Box := ⟨-320155753763653620347442156594373152205792220517734969,208220843554299553966050482112107951044868573679184203⟩
def resval5Tail96 : Box := ⟨-352014973962527009716353181431558649355728266006627825,210716585047129698824196843337198806235360641335656931⟩
def resval5Tail100 : Box := ⟨-387044557023064328707337989844954525453672066334134429,212275717782526612306059525687057784035479016457336744⟩
def resval5Tail104 : Box := ⟨-425559990914270312793111089543145028652995752963424974,212727992125410749348580115414912994884104982349953175⟩
def resval5Tail108 : Box := ⟨-467908158326489122081093259496041156421282856976929258,211881207092562302635742080553937124208037150200760613⟩
def resval5Tail112 : Box := ⟨-514470460811228382678826544041826781452126901631245756,209518700219409366476413966744334157359171476012397001⟩
def resval5Tail116 : Box := ⟨-565666253809222536505835740082718221969346398455581317,205396566461188349132035808836150842202627556063433192⟩
def resval5Tail120 : Box := ⟨-621956623503730231759068359271388233786735947224640389,199240577787243689791991820679799969421777789492640747⟩
def resval5Tail124 : Box := ⟨-683848539514651209335858938379978180892957274321219488,190742772217419247585651533077814069687011065120922502⟩
def resval5Tail128 : Box := ⟨-751899420833994515158052766228200407066195541802282403,179557677844297248364564859281591774768950548079747193⟩
def resval5Tail132 : Box := ⟨-826722156125038694173226156840771438838656841215697260,165298133854688384302730418145034732856234179112027525⟩
def resval5Tail136 : Box := ⟨-908990623620362089513613925610056946919830545152362718,147530666674268018635422086230949202609006358110651721⟩
def resval5Tail140 : Box := ⟨-999445940250910908856207487149108822593817545840090105,125770366433590077840166383851866924897181014616547918⟩
def resval5Tail144 : Box := ⟨-1191428775319609940797884032724974205333324808161712983,96599709679928937082972811232187672945801374481756589⟩
def resval5Tail148 : Box := ⟨101888898466744975886779768595329917950180290115,76614369002326628192262935471283678007304819891⟩
def resval5Tail152 : Box := ⟨111960341549695108304005234186496113051507920929,78083117758404713805565508268179258815730802664⟩
def resval5Tail156 : Box := ⟨123101696220204552063609464418899833563569847845,79298357218819325323144497790429012217975627952⟩
def resval5Tail160 : Box := ⟨135351746392706204951948190260381235180951351474,80208326088428223004221686615247440172074934798⟩
def resval5Tail164 : Box := ⟨148820818998568132856964256820796627892714612660,80754934854414729702742993707462723220160602336⟩
def resval5Tail168 : Box := ⟨163630220944073110141072347302396675349578814058,80872511637714254700957410255908585927068814974⟩
def resval5Tail172 : Box := ⟨179913330583564352716610027739147045233724823362,80486930492107978651801713891574715742714857093⟩
def resval5Tail176 : Box := ⟨197816798968536445443738403771476041145179868158,79514645356308074169347384534551542497459422821⟩
def resval5Tail180 : Box := ⟨217501870635333264937810316146298413132069259714,77861619760528863582501354435386936571476709561⟩
def resval5Tail184 : Box := ⟨239145835826580253431959855705568691697909149129,75422141386421444242755765677214579868749667820⟩
def resval5Tail188 : Box := ⟨262943627225535312898606068329592621248974987069,72077509460171424409799305805645838861374028153⟩
def resval5Tail192 : Box := ⟨289109575584074082559239702346994564360712716346,67694581725883457771902171906963345425410044608⟩
def resval5Tail196 : Box := ⟨317879340056073800472885900693428226677557578395,62124166388659770897272885437513108207907160049⟩
def resval5Tail200 : Box := ⟨349512030621414344073809733599403421995045280745,55199242921425455863733627031261113303208413562⟩
def resval5Tail204 : Box := ⟨384292541715846509527124747985910719608900402264,46732993982699912252855194973078998572488983167⟩
def resval5Tail208 : Box := ⟨422534118084196458520905483386527226537782986156,36516628878908328776893273705097996975480155263⟩
def resval5Tail212 : Box := ⟨464581176046130119191666074238349514010554422448,24316977003059639347650501904837695325606394125⟩
def resval5Tail216 : Box := ⟨510816223105444828570261746753686693788301871199,9873649138418093161943640334799400346869765411⟩
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
def polyval5Tail5 : Box := ⟨5436841460638025957793533990827732980524239599826362326943,3910692630665733702482270986532081932423980530792888899340⟩
def polyval5Tail9 : Box := ⟨5977868189895687476954215586640067896619299312058013157867,3977438914945082395843739404319661293896679846950181218819⟩
def polyval5Tail13 : Box := ⟨6572735583894929487401059176233919749796774924414448682878,4029863993482570086763832519135595095600894723780361092447⟩
def polyval5Tail17 : Box := ⟨7226799200789393981833884915347035075849806355731721149949,4065179702171679381152280779018105270533647164388593751457⟩
def polyval5Tail21 : Box := ⟨7945949752870241910898284979961127954360134466859064506207,4080231808959369619904917813672752140508532378548038192504⟩
def polyval5Tail25 : Box := ⟨8736664147004664605578906634249522618925194744591583788816,4071457812926090492036368507486805215582873044976112965380⟩
def polyval5Tail29 : Box := ⟨9606063817605317334954938758464044255104768074947268879633,4034840179814699340811859766541528328685714016228454889218⟩
def polyval5Tail33 : Box := ⟨10561978864615359229254726062153926891621792295166778272962,3965854524928299419598234938173425314698225448290753458329⟩
def polyval5Tail37 : Box := ⟨11613018573968941954286768589017800193709564963506331767034,3859412214654612854363735457471984881430171312652227496591⟩
def polyval5Tail41 : Box := ⟨12768648955657513629026620137236674107465298131669879288618,3709796803573891927843955507935431490595140396814671786064⟩
def polyval5Tail45 : Box := ⟨14039277997735315254620724290650481644691167627357564591928,3510593664291225978565463908729014027194562755691320725943⟩
def polyval5Tail49 : Box := ⟨15436349404089738517257090527202446604197080234782279370049,3254612101248735944954531977089523618848032339088797299606⟩
def polyval5Tail53 : Box := ⟨16972445660209795989774409337502709884006054828753319550854,2933799167207014042197149229129278680262181754578113397792⟩
def polyval5Tail57 : Box := ⟨18661401355196979849696564288593600351226581613487415869207,2539144321165358944480975259845723866846963078971196984013⟩
def polyval5Tail61 : Box := ⟨20518427780633897880872284437264261310054236677585482850914,2060573978476485195097130486829086913550818826741267210879⟩
def polyval5Tail65 : Box := ⟨22560249928503022532241474232144388435112178450026019684598,1486834906988017295014125572472977156601191958356697031803⟩
def polyval5Tail69 : Box := ⟨24805257240237270863600884755576102578361849470177532287160,805365310963572300336559245280202321598978080545501951409⟩
def polyval5Tail73 : Box := ⟨27343750000000000000000000000000000000000000000000000000000,2⟩
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
def resval6 : Box := ⟨83774247368751063171082128882237405287185175581352967344,12587084932914047585700202317806602583145369674058507703⟩
def polyval6 : Box := ⟨15451444890371814459784039822294459921986026648910030937133,3837328793266964199873714611400332265111485662876764570945⟩
theorem cell6_lo : Holds Q cell6 (63/64:ℝ) := by norm_num [Holds,Q,cell6]
theorem cell6_hi : Holds Q cell6 (127/128:ℝ) := by norm_num [Holds,Q,cell6]
def resval6Tail4 : Box := ⟨-32587049460054192924963873751903589414879682122192687063,12309889348343107172014093872743288035632821514557028685⟩
def resval6Tail8 : Box := ⟨-34160448886156742897139296110207355449420009378350646106,12167414015757792862109560176711771783293621677513180823⟩
def resval6Tail12 : Box := ⟨-35809754656528120613649317958029284079549574658574755139,11994578185081595271462227090743678413522651642987750573⟩
def resval6Tail16 : Box := ⟨-37538690799600039774353138777359800971823555170309334547,11789167102015530827328571235754005963343321301648526997⟩
def resval6Tail20 : Box := ⟨-39351101968269445795380596437800219547745821821286632806,11548835767996989776058277122008470729577920078315032916⟩
def resval6Tail24 : Box := ⟨-41251018432790877069144775229164018000576152623148967300,11271101354432756117143122059198458470876268067685257501⟩
def resval6Tail28 : Box := ⟨-43242665049496362852368619084638996873964500742806606446,10953335763643581671105349629050983798408342915720106958⟩
def resval6Tail32 : Box := ⟨-45330470655641034703770799788259095896719407538824535135,10592757805757836857712754359700638329644587313011831294⟩
def resval6Tail36 : Box := ⟨-47519077917836734059177856201951301145856721274952716667,10186424972102807249725214579301187818610578470928136368⟩
def resval6Tail40 : Box := ⟨-49813353655979300186321951744985472628982413981767123204,9731224784789881692198840104889196090747661873803600774⟩
def resval6Tail44 : Box := ⟨-52218399665626941893962815908575045126450622343865149127,9223865701183533083668760499128654188776347870353846184⟩
def resval6Tail48 : Box := ⟨-54739564062895484874727004718923432490669797805056915532,8660867550888083759055448675401593415720760647865656031⟩
def resval6Tail52 : Box := ⟨-57382453177098210272111932164754822207771263130769857168,8038551481778495444381960432185659918290817598598157428⟩
def resval6Tail56 : Box := ⟨-60152944017576008114089007316991288006959951544221534581,7353029390439297968165548321298498361810885314756751493⟩
def resval6Tail60 : Box := ⟨-63057197342435763286760289000732590484332450059440397870,6600192811156334594334630836015056380369529733835106996⟩
def resval6Tail64 : Box := ⟨-66101671351051716820794775417239806245102285345322927806,5775701235998264048373693894218155977536441153327080460⟩
def resval6Tail68 : Box := ⟨-69293007708395644185696253001122431515361788342450273905,4874965617207358972404567131178891545682764828131705973⟩
def resval6Tail72 : Box := ⟨807899858628693345545353775393857181229150509003818606143,735567188315850462407339386026452587667038355930436979⟩
def resval6Tail76 : Box := ⟨-435053038021389854262761291656158668950950190691127783,166536631793033691051564571164814794635967382401493143⟩
def resval6Tail80 : Box := ⟨-456030105939528098323365368089540515914978993575674286,164704719936002627503704254514149535403703288166891936⟩
def resval6Tail84 : Box := ⟨-478047762527995544692450857528167700089288308667321800,162469893428271812603316878014339253572666395438247961⟩
def resval6Tail88 : Box := ⟨-501128458350841467871036465954770700633588582565507812,159802508328057113135831323285952151727335202419252282⟩
def resval6Tail92 : Box := ⟨-525323516716135683609139488671053131549871862235319461,156671333314122649189701314712508272896565508366627847⟩
def resval6Tail96 : Box := ⟨-550686740328375913122807764726633983378027708307629782,153043299444090528312187008924406989040101548468569641⟩
def resval6Tail100 : Box := ⟨-577274529549302040037670204230773916210305953485824580,148883400904549459071986811948242220718378696465215746⟩
def resval6Tail104 : Box := ⟨-605146007814992279618057728848371679034869447483937764,144154590652442281561995561668937045385762602800287693⟩
def resval6Tail108 : Box := ⟨-634363153109022281233720022237147091444637856951002383,138817670672309034289831075844979100568539829915506086⟩
def resval6Tail112 : Box := ⟨-664990935783301576799870492881990220744093935385477153,132831176578403064155966843340037494826883686942030755⟩
def resval6Tail116 : Box := ⟨-697097463033058551310450516190068629185037025809332293,126151256277278586228159449118184029109196404921969246⟩
def resval6Tail120 : Box := ⟨-730754130347243862798171183957288384337682910983544735,118731542392354701707148310164502077979014731779578371⟩
def resval6Tail124 : Box := ⟨-766035780271133538578387944933366238438478576393970867,110523018137175438773394027082026030410992355512811333⟩
def resval6Tail128 : Box := ⟨-803020868834173255045576345251619786838211501122637858,101473876308574157597130394771155587389980847633749236⟩
def resval6Tail132 : Box := ⟨-841791640013171384105031375492787645267212929733645923,91529371054676732296031916326830195541095783065145146⟩
def resval6Tail136 : Box := ⟨-882434308639291819265719899254900378011149853069404817,80631662054446150657039576095877956624191174320655323⟩
def resval6Tail140 : Box := ⟨-925039430096489837179531623322963390313896773373502105,68719642820813419382615053447202733003237270622463480⟩
def resval6Tail144 : Box := ⟨-1061151960633989788246138619573182477532526524677268284,53237609564024572911282800682706952238658496198059977⟩
def resval6Tail148 : Box := ⟨234793067863228443334779855700251663051520696248,75627367381809548965208521123722159556592576619⟩
def resval6Tail152 : Box := ⟨246064643038965658352456761428111706883024598312,74184910904406988740142544112891004125933336715⟩
def resval6Tail156 : Box := ⟨257944925919569522040363827697772540990393832759,72510986717040340245491414221876203400195102219⟩
def resval6Tail160 : Box := ⟨270398803629935258993822950260126143443833650168,70588745663519653772146414484647728432036777347⟩
def resval6Tail164 : Box := ⟨283453968880901708444740793277132583093259203717,68400860544206057982835543351279784719148431514⟩
def resval6Tail168 : Box := ⟨297139452526188651833496240399331815433699582691,65928997469408298246847628683150527037085722147⟩
def resval6Tail172 : Box := ⟨311485687062863225667826411575468008509385025338,63153761818888927235049273584946458235980205508⟩
def resval6Tail176 : Box := ⟨326524574303954876882662799532163205323699066640,60054641433807828913254191827335062175454783100⟩
def resval6Tail180 : Box := ⟨342289556318719466071282285772078318722301327685,56609946887609156127789387883207356471642277986⟩
def resval6Tail184 : Box := ⟨358815689797981472432085548198902448621983511257,52796748689130340821978621053604015071402336247⟩
def resval6Tail188 : Box := ⟨376139724009920458432284185109536603774042567516,48590811263953623463033592180422189321065990387⟩
def resval6Tail192 : Box := ⟨394300182519652569502123159881315777196211897879,43966523552399378169498279671517413176133739001⟩
def resval6Tail196 : Box := ⟨413337448854327422111854702494196576330564014665,38896826054565409674597955984850371492510259971⟩
def resval6Tail200 : Box := ⟨433293856304234401810151120688223082056976991884,33353134144429139534341672352282729771546128560⟩
def resval6Tail204 : Box := ⟨454213782059609726083833996053964358234412365126,27305257466231046906059416270792057532342498740⟩
def resval6Tail208 : Box := ⟨476143745892505886279220289854317703526283754091,20721315217125861124707024655570284342265060270⟩
def resval6Tail212 : Box := ⟨499132513682610861745088016509758296368830867777,13567647106099768637906524909498529007345944453⟩
def resval6Tail216 : Box := ⟨523234980281392720773571681324239306438087746704,5808557410841322155646129827916782520494931369⟩
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
def polyval6Tail5 : Box := ⟨12235858312321099206873241433700282039661630247852408910507,3765665467793047275584484473645677059799491541465762159234⟩
def polyval6Tail9 : Box := ⟨12826617515728292357280408991273854637590658517187249089243,3684873065679327671446937285184020688315527477415061842965⟩
def polyval6Tail13 : Box := ⟨13445901362318467664431824424970613603018231152426304075588,3591810759564696886860362150328855048728605043762435582565⟩
def polyval6Tail17 : Box := ⟨14095084945517561932145526909483819588448579776945329123118,3485619408236147329064423570460603831050678008229186711438⟩
def polyval6Tail21 : Box := ⟨14775611858802238155813054793267070102405957066485595815184,3365389900296317037866250033100575898089260172021941592481⟩
def polyval6Tail25 : Box := ⟨15488995394199862650291886581943332563744352668773477178593,3230160459948302603818972991770132954204268576456385901020⟩
def polyval6Tail29 : Box := ⟨16236821907217614500348616592410969154230966581232479080144,3078913824749019521151052260499854136835085110974754218335⟩
def polyval6Tail33 : Box := ⟨17020754344431180179585958362845835093774441110682137307266,2910574278194404409498245501427759456367492567092794969311⟩
def polyval6Tail37 : Box := ⟨17842535941389635371457273531158152178262097795345313075728,2724004529841331544508369705638844512059426956829749873032⟩
def polyval6Tail41 : Box := ⟨18703994099059428278463136733177747145652474139058729099757,2518002435312154203638137401462320729507704339501041297866⟩
def polyval6Tail45 : Box := ⟨19607044447427537122090201809100193385349226609509205907999,2291297548148898438715420620093349666217594136539399633195⟩
def polyval6Tail49 : Box := ⟨20553695105300062028476660629413128140811060826981048686738,2042547495086660766363251780232070753919713306999915721085⟩
def polyval6Tail53 : Box := ⟨21546051145768792535945480999375754087472390245364953255364,1770334165898787462468963593767612038074971871731784956633⟩
def polyval6Tail57 : Box := ⟨22586319277275637206904233752756878614995479170262428456206,1473159708528990507893499925672102582708637395775692616256⟩
def polyval6Tail61 : Box := ⟨23676812750684241796700245396827203982132395470358874091589,1149442319766685412156212166275985089906212544153386987670⟩
def polyval6Tail65 : Box := ⟨24819956503284402891219922742936967830080226973629880947021,797511821239724991135110007323681096709558735512897175301⟩
def polyval6Tail69 : Box := ⟨26018292668103088811496549574718009715388674478901901932270,415605005122793408889341439260818926780664356493524809885⟩
def polyval6Tail73 : Box := ⟨27343750000000000000000000000000000000000000000000000000000,2⟩
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
def resval7 : Box := ⟨65095522991556754719300961606155713764074979731723979977,20356370512746043938657758962121619173365178261783386661⟩
def polyval7 : Box := ⟨24355697543441015355875829216379499383403152806949330425483,6702264329963483049800125159072415024068781558714454517009⟩
theorem cell7_lo : Holds Q cell7 (127/128:ℝ) := by norm_num [Holds,Q,cell7]
theorem cell7_hi : Holds Q cell7 (1/1:ℝ) := by norm_num [Holds,Q,cell7]
def resval7Tail4 : Box := ⟨-50545419700056735023304005619542463205639453983202770990,19408183861110275195070394902030030381825100358760193259⟩
def resval7Tail8 : Box := ⟨-51343022498926071149579140502782010055326851933995598515,18610636986003001899721408913359985635776705483138463688⟩
def resval7Tail12 : Box := ⟨-52153153182356991847936872334780430543709480117171704609,17800506309062721021188164214306810072591797068897458838⟩
def resval7Tail16 : Box := ⟨-52976066739545845324951333751405112037073681841382220927,16977592751879506320774782577245088420785588899829983210⟩
def resval7Tail20 : Box := ⟨-53811964875441329935959088077742208918456846706422628006,16141694615984043007725024901915859790076476010704382491⟩
def resval7Tail24 : Box := ⟨-54661052470966341275482039059218378063937038643244375807,15292607020459031934824149151633863021410320309970250218⟩
def resval7Tail28 : Box := ⟨-55523537639810654634052364505046243989188157074539562787,14430121851614718585430623179086564023469828330435674256⟩
def resval7Tail32 : Box := ⟨-56399631779445852808035282835835537293901687109499169419,13554027711979520412157401455571137855957231681471337578⟩
def resval7Tail36 : Box := ⟨-57289549622939445036757873652286124446675363510471507681,12664109868485928183491869505218505600783456706177405280⟩
def resval7Tail40 : Box := ⟨-58193509291586528842747379232206830305423231930396535810,11760150199838844377364763774637755612480612883900131090⟩
def resval7Tail44 : Box := ⟨-59111732348371915472950262971139229134877620551386923624,10841927143053457746343706103598110744606316401728082216⟩
def resval7Tail48 : Box := ⟨-60044443852275822881046317677679529383336853174993134211,9909215639149550329574963580130995049346742304787285083⟩
def resval7Tail52 : Box := ⟨-60991872413436446562819541442878795289549498972691691319,8961787077988926419734342056520856547914539492745599655⟩
def resval7Tail56 : Box := ⟨-61954250249182913590070414456015558525163918598701327073,7999409242242441727611454191256049927643455084300726285⟩
def resval7Tail60 : Box := ⟨-62931813240947732004317874674462211856003456482581548300,7021846250472614787395436076664701734951655254621744255⟩
def resval7Tail64 : Box := ⟨-63924800984916358195710282688491502066023690598879836285,6028858498991696180165455744486492229830198655164792578⟩
def resval7Tail68 : Box := ⟨-64933329461114712291849072714140910942661915865681143991,5020198414635877923753561348556938921846305231563502795⟩
def resval7Tail72 : Box := ⟨807708734678867791699946251319172830742026843689430873501,838452727577433514032861562796521074128026768393101710⟩
def resval7Tail76 : Box := ⟨-677110615170362970915145777984797040744421841777507927,262227502526533165667099885320394228702552571345145380⟩
def resval7Tail80 : Box := ⟨-687767680843289654725164599871022951482439230733692669,251543779657444057535223763325561241259851509263864989⟩
def resval7Tail84 : Box := ⟨-698619819994774243478834391150717266957848832679079502,240691639106187030145535334620835431577578746967866503⟩
def resval7Tail88 : Box := ⟨-709643194154727637360527057321825279204606750590911625,229668264945464573239429607023770885397281798187703667⟩
def resval7Tail92 : Box := ⟨-720840503801385942453288620668852716605870165373704219,218470955298804211648108081463038020887707831831146729⟩
def resval7Tail96 : Box := ⟨-732214493425189577487302010323155379940661872233656359,207096965675000557030524551652243387361346097791654498⟩
def resval7Tail100 : Box := ⟨-743767950822072250199337960029876745654198200401216469,195543508278117883769138616563800204462460004278388889⟩
def resval7Tail104 : Box := ⟨-755503707776011179423647605904502618142113976690657991,183807751324178954505644352014068543928453097264702092⟩
def resval7Tail108 : Box := ⟨-767424640753103160467366149665831932846093928908578992,171886818347086973456109370034392709061710176593577030⟩
def resval7Tail112 : Box := ⟨-779533671606594248354004549231672587797198372436957181,159777787493595885569028110192846532126415512149369229⟩
def resval7Tail116 : Box := ⟨-791833768293033971859121507697615569483277964766753394,147477690807156162070416613510279228696578655054757134⟩
def resval7Tail120 : Box := ⟨-804327945599729593632954411459273313429941360424666261,134983513500460540367673667775116175966793693825251154⟩
def resval7Tail124 : Box := ⟨-817019265883678718468705120381913181796731364961593434,122292193216511417105266319478830636099625339192615755⟩
def resval7Tail128 : Box := ⟨-829910839822161460043666233171552594324926285140247352,109400619278028770762681098316815978109899089150566911⟩
def resval7Tail132 : Box := ⟨-843005827175196931496121704762127344182647961368213852,96305631925013125028619124617973551054830680735707187⟩
def resval7Tail136 : Box := ⟨-856307437580407184677944021383949218385447656925715637,83004021539125296624530756173984625445871910355330030⟩
def resval7Tail140 : Box := ⟨-869819108027182710509303583379531580828353233078943393,69492520018265244037844031228812726892480614634542889⟩
def resval7Tail144 : Box := ⟨-974290969623575561588239481524527394166755660005474725,53299199976370597709269740722137180323150190658766321⟩
def resval7Tail148 : Box := ⟨407436508017887372975258034549983873979978773534,130085843000865180294169079194589028730667451488⟩
def resval7Tail152 : Box := ⟨413802876906440833984063535242338963461631338283,123657481781781635423883541700851570371149221575⟩
def resval7Tail156 : Box := ⟨420332183778213879416950256038775670419880450216,117128173840127419469715676228529084105342623190⟩
def resval7Tail160 : Box := ⟨426964516272565510245377206996176515975337356907,110495841345444994006485611704437165630941744275⟩
def resval7Tail164 : Box := ⟨433701498936839001724151866024646573436420465646,103758858681170940768906904780581987685648417144⟩
def resval7Tail168 : Box := ⟨440544783023570715408656908047454128088065629242,96915574594439223476274704800879803423514927479⟩
def resval7Tail172 : Box := ⟨447496045840388711474925685798973810163306487640,89964311777621227338990725247180319624604077943⟩
def resval7Tail176 : Box := ⟨454556991160803376384060708569185930153459087313,82903366457206562426162198835796810147785120207⟩
def resval7Tail180 : Box := ⟨461729349641806433518677386374129572590856497493,75731007976203505291109477657110986084265839657⟩
def resval7Tail184 : Box := ⟨469014879248059697578821355799369224291777003365,68445478369950241230887977250221303515622570373⟩
def resval7Tail188 : Box := ⟨476415365682777016690513390960039325225906227967,61044991935232922119279957912307846053050769237⟩
def resval7Tail192 : Box := ⟨483932622825405009465587137172822455503938285567,53527734792604929345112360423909092119317988013⟩
def resval7Tail196 : Box := ⟨491568493176209873717739533207594982905119955956,45891864441800065106943835684670656111918594143⟩
def resval7Tail200 : Box := ⟨499324848307879236784340889445359956885933473541,38135509310130702565418280405302367393016770230⟩
def resval7Tail204 : Box := ⟨507203589324249799258146021065260675110765765627,30256768293760200504270740337763474565633925276⟩
def resval7Tail208 : Box := ⟨515206647326302013063817405590684047178832153096,22253710291735187281041317622279118446493041289⟩
def resval7Tail212 : Box := ⟨523335983964423014977867880977948283155446090636,14124373728395349978499132101765841237085460315⟩
def resval7Tail216 : Box := ⟨531597338043546069936687793190078266449984189380,5866605133341348370997412153514178919270941360⟩
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
def polyval7Tail5 : Box := ⟨20901610227234246770637356026113774545842657462708492689932,6375255550175952752126697779886440225374432872037791920656⟩
def polyval7Tail9 : Box := ⟨21231410264676243209670837245350445032896998076003818269285,6045453491226840736823324058184080078286916519011401667477⟩
def polyval7Tail13 : Box := ⟨21566416189895087936626720968488548622924300592916667973406,5710447565817384170458858206687765719659349441074267436448⟩
def polyval7Tail17 : Box := ⟨21906708102839508098013659150557111119409131974753060688053,5370155652872818339878820099172190969511795450022630387612⟩
def polyval7Tail21 : Box := ⟨22252369409799091546842434922130179407234974382257128502240,5024494345913234397495591596615421666991259693654707694453⟩
def polyval7Tail25 : Box := ⟨22603484833304534804156719843946786695313632681191543302974,4673378922407791134545746601280193742200876073499736940109⟩
def polyval7Tail29 : Box := ⟨22960140432705544409779274649228298764524923291956655234593,4316723323006781528740818341794443937948134905026021456251⟩
def polyval7Tail33 : Box := ⟨23322423625264077632063760838747003559945418446861592068136,3954440130448248306441809221683140419143664469455340711280⟩
def polyval7Tail37 : Box := ⟨23690423207580551778032676519667246182867063587020083768542,3586440548131774160470599232609634966650711820694453036600⟩
def polyval7Tail41 : Box := ⟨24064229377358133583268136859216304722331325211019838172234,3212634378354192355235106293404096392182345926404007225440⟩
def polyval7Tail45 : Box := ⟨24443933755510442718791456686702860439715799296567663298073,2832930000201883219715492505242089406300916035851159149975⟩
def polyval7Tail49 : Box := ⟨24829629408618088068962516190872615952491950295592388988948,2447234347094237869585552593041126091079807269184797824869⟩
def polyval7Tail53 : Box := ⟨25221410871739540939532992705677057996991820432993018822542,2055452883972784999965287111368817829989046650337620539511⟩
def polyval7Tail57 : Box := ⟨25619374171581936263806066416728924997804708834223984346155,1657489584130389735807916455442109668120113073516488489841⟩
def polyval7Tail61 : Box := ⟨26023616850037494639239286661930382365863742018303466793986,1253246905674844350195240494965337768460533811497243402447⟩
def polyval7Tail65 : Box := ⟨26434237988104960902773455013953719341859870117916448149175,842625767620338061480874251757568250325283787346089321844⟩
def polyval7Tail69 : Box := ⟨26851338346287181905216965310640117121526730467042250352812,425525520773509209568235107550625277160913634303558710043⟩
def polyval7Tail73 : Box := ⟨27343750000000000000000000000000000000000000000000000000000,2⟩
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
def pend : Box := ⟨1031053865929857767285124758423784724443672895431272727349823,4095943546731120551195951667189963799038934391057592739⟩
def zend : Box := ⟨1003774510823535657746660156250000000000000000000000000000000,2411195425106153183593750000000000000000000000000000002⟩
def betaquot : Box := ⟨428753944391079121515506216453242007251489171291846682979043,394778733676366636486288151320976605223282900492086966⟩
def crit : Box := ⟨134882571286323578079313860235755594879836966692621938861,10232399776174434966548734671410420502110473510657450918⟩
def subsonic : Box := ⟨472578330671132683855548746616156722799266448384832593552,5211162446947017834884609905593025151200638373661206784⟩
def pendTail4 : Box := ⟨27275248563762715153848368805434081865792927586492840768153,1580073674747358854375648478854669919602676520482918646⟩
def pendTail8 : Box := ⟨27275283811951386799853639447184413202335418878729178060048,1579942265238666193385553737963151175449460757119568982⟩
def pendTail12 : Box := ⟨27275283813462326957110894128914442241900283420789602156569,1579942249272392273871801935906108441863468454626662290⟩
def pendTail16 : Box := ⟨27275283813463064886817079483037191000335063819898800777450,1579942249259321906457756209707705253583787981624622232⟩
def pendTail20 : Box := ⟨27275283813463066649551992583795962430650930950472088596453,1579942249259274254685511547402839516355361635478502671⟩
def pendTail24 : Box := ⟨27275283813463066664487288080206576341043943525656119848544,1579942249259273644049281617707950508932199201140420344⟩
def pendTail28 : Box := ⟨27275283813463066664856634781458548916849621028383643274176,1579942249259273620408100229589649543953378769674182676⟩
def pendTail32 : Box := ⟨27275283813463066664879453376999354661859764153024784716267,1579942249259273617885556023137523184748119960482075786⟩
def pendTail36 : Box := ⟨27275283813463066664882244334519828504409730230504235117780,1579942249259273617181760463323590670852173766362131230⟩
def pendTail40 : Box := ⟨27275283813463066664882213469838533691421671233810346681354,1579942249259273616680671366645731612944554062498186568⟩
def pendTail44 : Box := ⟨27275283813463066664879200666568637714823249962452589159666,1579942249259273615771299473133394992379494176493684480⟩
def pendTail48 : Box := ⟨27275283813463066664853533398778080159389026722229301971824,1579942249259273611473522986910022035251148613661516306⟩
def pendTail52 : Box := ⟨27275283813463066664400401358414747320721259896484334394224,1579942249259273555978119314620742825004745634517914765⟩
def pendTail56 : Box := ⟨27275283813463066643153335280660884953530507223773836217489,1579942249259271449344711933235957783941327816589379950⟩
def pendTail60 : Box := ⟨27275283813463063425788560543613022119000969325472791818508,1579942249259034489708903128890072484569607284554761744⟩
def pendTail64 : Box := ⟨27275283813461001418261606104520588010216607197632459146512,1579942249145087313924215037014296723447618407088876701⟩
def pendTail68 : Box := ⟨27275283804180423655261508116444022866512418798151821349863,1579941866099774083805601837340711056512292973374469560⟩
def pendTail72 : Box := ⟨27274106952549541098727391623203983976640009316749466083836,1546935730091289310925255374930590402292978715477047698⟩
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
end SepticProfile.ExteriorCertificates.C21

end
end

end OAI
