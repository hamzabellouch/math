import OAI.MathematicalPhysics.Transonic.Certificates.BarrierData19

namespace OAI

section
noncomputable section
namespace SepticProfile.ExteriorCertificates.C19
open SepticProfile.ExteriorJet SepticProfile.FixedInterval
def cell0 : Box := ⟨250000000000000000000000000000000000000000000000000000000000,250000000000000000000000000000000000000000000000000000000002⟩
def resval0 : Box := ⟨114314619847070265953294967015774445004524361171798944794,320689167222504255198544394313911260416504612520759417⟩
def polyval0 : Box := ⟨3807122535856627758760668302830579817310978312291311269895,14991796128560581962165487481893001210363850132944709514⟩
theorem cell0_lo : Holds Q cell0 (0/1:ℝ) := by norm_num [Holds,Q,cell0]
theorem cell0_hi : Holds Q cell0 (1/2:ℝ) := by norm_num [Holds,Q,cell0]
def resval0Tail4 : Box := ⟨58798914191108729367366270556153640306677526282377,1749176189309503569743710146539965261171207016925⟩
def resval0Tail8 : Box := ⟨7121161294241874443314305008218544961377526707,383680818029857455834845433875760683805391874⟩
def resval0Tail12 : Box := ⟨6485051616763372174718979077566579040209684,530096766406841911184081734796959636382875⟩
def resval0Tail16 : Box := ⟨25996751053503034941854300379736091106600,26892003956397457252773053524122582625136⟩
def resval0Tail20 : Box := ⟨354457296429765550006155867741961215107,382087367780740124145242182965697963599543⟩
def resval0Tail24 : Box := ⟨14107353466355675269609290756252403564,6112489949308572260391686814323510504634037⟩
def resval0Tail28 : Box := ⟨1491376741906245680871170162567451158,97799789723569130875097788723909365355620009⟩
def resval0Tail32 : Box := ⟨393614493821483396654839799411735642,1564796628381689688436599660340727138752459763⟩
def resval0Tail36 : Box := ⟨-296930756037064319093202720032723592,25036746051303333833972831361313529342534154616⟩
def resval0Tail40 : Box := ⟨-141177072694843180003893486457726600646,400587936687152057453139425292042955506255497363⟩
def resval0Tail44 : Box := ⟨-36242606536545173295580004753389538770727,6409406953013827725677582439548082817509057459712⟩
def resval0Tail48 : Box := ⟨-9278488982256887958422406297892772885199133,102550502549616989913010552364951054663397356010933⟩
def resval0Tail52 : Box := ⟨-2375296690823185096246594293333094170530185598,1640805813952806918722555960909917431115006274263328⟩
def resval0Tail56 : Box := ⟨-608076024657935646302885135804028478532120316140,26252322951943730723211198711706024479311831442137578⟩
def resval0Tail60 : Box := ⟨-155667460160056777951562534287142218441636096889800,419891228979738562877118645892801085860652798628340762⟩
def resval0Tail64 : Box := ⟨-39850853643491098903153901065286347774874579779948922,6680899477295527250095062797715707517701050391396473937⟩
def resval0Tail68 : Box := ⟨-10201438529358388089442507811259183645090957042466210422,97330344461849405022778813727795234578374181990790734650⟩
def resval0Tail72 : Box := ⟨793652084405407700827273277309374455911917714717903243780,2471828556701441941677878913162359638820749893426185211⟩
def resval0Tail76 : Box := ⟨-27171935472700827549062784523472656719483479491291,600104211999860566705542222438573358795288735438⟩
def resval0Tail80 : Box := ⟨-1470252195202550680787307482914671359651480438,67997865336672038188189726670812845807510017⟩
def resval0Tail84 : Box := ⟨-832563091876635871219976407314768110076618,60559625253816701020882356477077684157267⟩
def resval0Tail88 : Box := ⟨-2306144300919363086989516089554659245981,404521144904024172567894948753525372431⟩
def resval0Tail92 : Box := ⟨-22992798373333855446563672889530330006,2596011336090591930984940466226144299842⟩
def resval0Tail96 : Box := ⟨-692680857955741543329980317301040516,41482359035816025599310412765689693169836⟩
def resval0Tail100 : Box := ⟨-56639293554853506997100513101707697,663715519533880877265664219071244174822248⟩
def resval0Tail104 : Box := ⟨-11784598245046119969096037050448634,10619448062597224779887769060186751340916362⟩
def resval0Tail108 : Box := ⟨-7873598544006473054191931071902614,169911168928462896778310749146099626042553385⟩
def resval0Tail112 : Box := ⟨-484461786550775159719482167247838592,2718578702414602037874256417668341285619469327⟩
def resval0Tail116 : Box := ⟨-122140323477644969183205173834731604465,43497259124152107467370358822948759647169650438⟩
def resval0Tail120 : Box := ⟨-31262320534534014615760751357007328137509,695956116678143917647686336287630250780451659499⟩
def resval0Tail124 : Box := ⟨-8003113269022995774641513257891850999067428,11135290363933876003617587008953518198071007742562⟩
def resval0Tail128 : Box := ⟨-2048796299719542501411893540276287558061656896,178162725076535443430252195236740925052940633301058⟩
def resval0Tail132 : Box := ⟨-524491844827121351171978911352202475148409424758,2850111890146122576835164742767244439517954731035834⟩
def resval0Tail136 : Box := ⟨-134269951994033633915777340705655993102319763037936,45475912188785305214641166935427203446384099538538087⟩
def resval0Tail140 : Box := ⟨-34373605797983571044825797313864732125805898106175107,695389581969512232044508336739075477745053916794338282⟩
def resval0Tail144 : Box := ⟨-9109317053265472795862311951736208458886374407283840816,2722997068447039781951292858244505985766321978756721810⟩
def resval0Tail148 : Box := ⟨61443045613977531763888735735324207943414028,1123870924995889541511340915237116407672415⟩
def resval0Tail152 : Box := ⟨1096604601838675735627746313338668594661,45260992454261354313833549203937369262⟩
def resval0Tail156 : Box := ⟨348811462453075256402322383982506434,23126183286953857400321394307549949⟩
def resval0Tail160 : Box := ⟨611648092597046438871341258290463,60622319651853937056797342376363⟩
def resval0Tail164 : Box := ⟨4087683907257792080201175018144,29250969442529277642122844616057⟩
def resval0Tail168 : Box := ⟨85203253782811996030314281099,459273993572188554312679830517071⟩
def resval0Tail172 : Box := ⟨4901694174801379404987424344,7348135210894851856036136439862155⟩
def resval0Tail176 : Box := ⟨721729045673929515967592786,117570143903615187263428462392645795⟩
def resval0Tail180 : Box := ⟨266995392848172690386285344,1881122298512453034871563140871458225⟩
def resval0Tail184 : Box := ⟨1940240749412408269516783025,30097956773231766830562982936171484240⟩
def resval0Tail188 : Box := ⟨439435386805906653642634656877,481567307960342771113514743799716155088⟩
def resval0Tail192 : Box := ⟨112377479588133523399547735245097,7705076822013688938788273874412097519591⟩
def resval0Tail196 : Box := ⟨28768048363981700559918655911035823,123281202182195093898017767273968730946183⟩
def resval0Tail200 : Box := ⟨7364613360933047671759773715454708653,1972492330590782851780080681208549931471636⟩
def resval0Tail204 : Box := ⟨1885340857273598665184065393403523587535,31558109782475718344551393674994387191226437⟩
def resval0Tail208 : Box := ⟨482647292266781965575575874307352119027209,504477274718853389309328981273873443637746833⟩
def resval0Tail212 : Box := ⟨123557900174501209792861965247893798448311787,7955800966844111286024768911299523839145362484⟩
def resval0Tail216 : Box := ⟨31642186299211924710977249722376632797699906523,97633437034226550213568854599985046384405523196⟩
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
def polyval0Tail5 : Box := ⟨2100688901510084296712700135539104442779666262365047,52306238000023179856116828973350541791425794415566⟩
def polyval0Tail9 : Box := ⟨203920399001129694639784204120999548394369078164,10029117116578227087647893467299132194367116984⟩
def polyval0Tail13 : Box := ⟨160681075892759191742198700439301787906208138,12255030852336609050022378765897667633061647⟩
def polyval0Tail17 : Box := ⟨564435226029220845121136545495532746864537,437786120791058419448642363265387495993383⟩
def polyval0Tail21 : Box := ⟨6762308783811830579009379348346942399989,6018231397743245011043004125158154200551091⟩
def polyval0Tail25 : Box := ⟨236225495846699668925333582913595651611,96275312038299195439947498853810343340198710⟩
def polyval0Tail29 : Box := ⟨21840990542624222738505132930339445818,1540404208842606269269281684714012184849170613⟩
def polyval0Tail33 : Box := ⟨5062608948126623241477758168069337170,24646467242054170697828602744500379238760688851⟩
def polyval0Tail37 : Box := ⟨8527210452842044676720021306220184838,394343475839085922221711410204410800470912489825⟩
def polyval0Tail41 : Box := ⟨1466373714020550732425975481921928689487,6309495612057228506583232274207557528381829467803⟩
def polyval0Tail45 : Box := ⟨374439595161619478416355908010003155274841,100951929441891883792340007088761723458051972183758⟩
def polyval0Tail49 : Box := ⟨95853503131954457004256879480532203512177864,1615230781207688635571676128219718538927977802640503⟩
def polyval0Tail53 : Box := ⟨24538473399709547753942467084585735301083289459,25843669494505581042076257310973335924177233471053745⟩
def polyval0Tail57 : Box := ⟨6281848772663587256588107319820464874006295960927,413492822678944383577127180514691868175589098338020532⟩
def polyval0Tail61 : Box := ⟨1608153281997531705562691526513760121388340197886728,6614377519178564453090231255721647064351743374683361841⟩
def polyval0Tail65 : Box := ⟨411687267350416515452245037395950819238747109835036042,105444083511711806713016670058578958509015983351261624493⟩
def polyval0Tail69 : Box := ⟨105392272955631083965472600877309225856328009478611836778,1588300242986921352617997557855854747510815189749685696137⟩
def polyval0Tail73 : Box := ⟨27218750000000000000000000000000000000000000000000000000000,2⟩
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
def resval1 : Box := ⟨114087488918591850065489053186763917809311367475239708960,243368931855149669962749467222663375540406723242611666⟩
def polyval1 : Box := ⟨3788929973553100004148763164387313489746333974415988079723,8794354986511180835599565269962906815128155104584150988⟩
theorem cell1_lo : Holds Q cell1 (1/2:ℝ) := by norm_num [Holds,Q,cell1]
theorem cell1_hi : Holds Q cell1 (3/4:ℝ) := by norm_num [Holds,Q,cell1]
def resval1Tail4 : Box := ⟨57092600808032535543333904045019820385165079301634,3098292757763913734114223741231832057958632449449⟩
def resval1Tail8 : Box := ⟨6712456473199409734436147448665503176902234974,6248045570534374340212775794695311132264877347259⟩
def resval1Tail12 : Box := ⟨-322137784767518754162451912848110121174124619,19746050400823096735400638424169692445990023838539⟩
def resval1Tail16 : Box := ⟨-2150564445471699886631262213930064168932125916,62406156095432506561676248181061534922663197004605⟩
def resval1Tail20 : Box := ⟨-14094092923727435003672631517320996777192662010,197226973938726451863769787473446097648085513728421⟩
def resval1Tail24 : Box := ⟨-92367049416862087711036427596195650784641839775,623286810928053897194567334125016489077449486742358⟩
def resval1Tail28 : Box := ⟨-605336695136078649069777926118497546347131797974,1969580707283076183758430962440208645662973373354344⟩
def resval1Tail32 : Box := ⟨-3967134565251571488605088012265007323414753352602,6222793695785644593441816187541277748222882967778870⟩
def resval1Tail36 : Box := ⟨-25999013086834572805412879398071502703226505184545,19653640154441924316881426542776977286392301757406071⟩
def resval1Tail40 : Box := ⟨-170387132165880049865938929840335971350549057349103,62026990977554642069404154884013672691179210145144709⟩
def resval1Tail44 : Box := ⟨-1116649109362312343234590399085042210745396269156138,195457780471976621357285360658373878739366703430276602⟩
def resval1Tail48 : Box := ⟨-7318071603116847078429226966759799395495141090631660,613954199666300021889095828233365222368208629154938680⟩
def resval1Tail52 : Box := ⟨-47959714058186373133530891536778143063487557163578672,1915567464274785219231432951415437248042910509287565561⟩
def resval1Tail56 : Box := ⟨-314308782051711200698963293719511211140032053093218328,5891406744531488048969747268407792378930950796204399982⟩
def resval1Tail60 : Box := ⟨-2059854034048131223487703445549830901619170379842695047,17553271580826431769520537186079478438844171836301914960⟩
def resval1Tail64 : Box := ⟨-13499459388057235801954209378033494078842938572783956342,48487703040456420873954203237362145123760611705414891120⟩
def resval1Tail68 : Box := ⟨-88469882976182182821131560771481366209597378555162315105,107440007909248840668617027792661537270110580189286454433⟩
def resval1Tail72 : Box := ⟨796522267120116803990409297413082236076768701852566606689,1515129834502629179130090731718032218390184212936286920⟩
def resval1Tail76 : Box := ⟨-26565737632676214804035894776231446202778532037337,400852774979884102390184324542791383866791556086⟩
def resval1Tail80 : Box := ⟨-1405219250193186232908339191521532639970290388,63585299403224859788226439376274043932624413076⟩
def resval1Tail84 : Box := ⟨-3551849085705202373537490945802097486631707,200825851646486368953645505491315837710805600001⟩
def resval1Tail88 : Box := ⟨-18184755596625733123558922546568570439818065,634699457590581427004967640627299289831776799840⟩
def resval1Tail92 : Box := ⟨-119161868873286133374261069194644855408058483,2005902022155154828113816734577025924886926571773⟩
def resval1Tail96 : Box := ⟨-780939090838831806877273194435536668603530961,6339236630106451784216955935360516382537183915834⟩
def resval1Tail100 : Box := ⟨-5117962421859167921039710681212426679708362502,20032468429113405955770259139797352524350113901557⟩
def resval1Tail104 : Box := ⟨-33541078527596016363430102894794865061324937746,63295127023114580317877613682101690079729509592988⟩
def resval1Tail108 : Box := ⟨-219814812238395697036391241296237822530085478863,199930049805297344594184611640623926431766984009135⟩
def resval1Tail112 : Box := ⟨-1440578353485525001996548054473206907279206348936,631131833277244705020131995549366074699973280837412⟩
def resval1Tail116 : Box := ⟨-9440974297402716391605245188316474221122865120872,1989800227893547140488874067853140424006560380889092⟩
def resval1Tail120 : Box := ⟨-61872369155458454185700545117462111803773286636594,6256717109373963352562681925989524243691950135359513⟩
def resval1Tail124 : Box := ⟨-405486758497214053164093338997712263297782018781514,19564376284756268598031350954059605643620352541173081⟩
def resval1Tail128 : Box := ⟨-2657398020487460510162661949851574353071855919575974,60457230856955741796307849230192849301016760293288947⟩
def resval1Tail132 : Box := ⟨-17415523667093126251510669749715573876768571212860358,182057871303612953073068806442789854173651009016752408⟩
def resval1Tail136 : Box := ⟨-114134375931269224103897705523062996223070671777575501,516300057577916941690112858635373480083994779322244975⟩
def resval1Tail140 : Box := ⟨-747991283385870534058093317092116952599362761019152224,1244493044362695013871027368438023803797042779560653968⟩
def resval1Tail144 : Box := ⟨-5031295048690664647390751750087260582420177098963149961,1371378742193371123243258973954188521122878309982494425⟩
def resval1Tail148 : Box := ⟨60531780711422790150830160001152423937487166,803285266293978390125228747629192246875312⟩
def resval1Tail152 : Box := ⟨1054666298752137496009002228340107385819,2983919465743279972529053369473359375948⟩
def resval1Tail156 : Box := ⟨442461282149363744052154926780955230,9337614334470234974645932913568725094796⟩
def resval1Tail160 : Box := ⟨750180655190284703859044254948907991,29511084573719327802838553721357272140432⟩
def resval1Tail164 : Box := ⟨4912706183322537108299989148178348922,93267057091552765667598298467977093099981⟩
def resval1Tail168 : Box := ⟨32195887340502423984463517030556373291,294753288893991709539480944408818205793138⟩
def resval1Tail172 : Box := ⟨210998966792839317421411038571423095949,931456706020889262929326297801895048571711⟩
def resval1Tail176 : Box := ⟨1382802828747014003912633213266653367852,2943147227749593546826181942538784126145396⟩
def resval1Tail180 : Box := ⟨9062336618472771219973934743823003222056,9297106648913070964711356930514565534665905⟩
def resval1Tail184 : Box := ⟨59390929262821979555153911104023821047888,29352698704022056450666625722603631415483876⟩
def resval1Tail188 : Box := ⟨389224394016829346254544847007652929446589,92567503335871181190350749703452999365663468⟩
def resval1Tail192 : Box := ⟨2550820988628692238023238785424077850416196,291238343194721069588736944507047963171931789⟩
def resval1Tail196 : Box := ⟨16717060431077007550249584303597385867792401,911801779457040768691797897141658195449684522⟩
def resval1Tail200 : Box := ⟨109556927241106878659488726979407515511906016,2825021134627512765297959566135071518578923471⟩
def resval1Tail204 : Box := ⟨717992278367396051636024468835030814773672478,8556723571489044671241439119266794341411449651⟩
def resval1Tail208 : Box := ⟨4705434195545153930394270017469716800734429927,24607247996623110300868629163269646386501491180⟩
def resval1Tail212 : Box := ⟨30837533646592856941857949328198195195264934075,61805017561990279388583029337783946018458081518⟩
def resval1Tail216 : Box := ⟨202101877708571265667965878850754530677209681940,90698379224708347452181837071708831342000265680⟩
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
def polyval1Tail5 : Box := ⟨2044047633266659357391622984305914516807985355938862,118109546066766104011845414626679159972347410462364⟩
def polyval1Tail9 : Box := ⟨196348728681478893753656832283405305036359844495,273844463042793913389583432374204838963629216590393⟩
def polyval1Tail13 : Box := ⟨15498662794693883039859407382381069732876882746,865459705250546371682371293341295313046732545515162⟩
def polyval1Tail17 : Box := ⟨100593483213045480162776728019960617554838879196,2735227976790986298621419350423130712577490119702889⟩
def polyval1Tail21 : Box := ⟨659246102646504383757521622016490922888084128627,8644329813900209112489563024586179698540838950666622⟩
def polyval1Tail25 : Box := ⟨4320435219376912715547530549020196240783402319290,27318114124771013534876431123295632403731643050304932⟩
def polyval1Tail29 : Box := ⟨28314404252398899878590355324065914933577903303588,86324071365593147720136197698877037379405504235112255⟩
def polyval1Tail33 : Box := ⟨185561279708406521604660166800678792291508634537469,272730620906470056679677118001814966137798938056796212⟩
def polyval1Tail37 : Box := ⟨1216094402696988630608635097006245956596666232256178,861333814728928760325619254277211306282107003323955852⟩
def polyval1Tail41 : Box := ⟨7969796277514973221912707610199788373953142326856296,2718113867150833067965638322708972637567917060577634412⟩
def polyval1Tail45 : Box := ⟨52230856884322118864130824502661578325040071448610057,8563539733704037119936213733941969967828989689096273975⟩
def polyval1Tail49 : Box := ⟨342300143677093448697254032476468071605663692871868367,26887789624108338242893414565788723712827411665269207779⟩
def polyval1Tail53 : Box := ⟨2243298221602200576860266948573812745090820041751574328,83817232402509781922964273259796432069397126715464295213⟩
def polyval1Tail57 : Box := ⟨14701679225092257500480624320569382909306892284805389294,257292096574570366386138241039659402621075158822370647329⟩
def polyval1Tail61 : Box := ⟨96348924969582174112245495017475567801069769523714592830,763285724471341059251929803357341362640308941706963515353⟩
def polyval1Tail65 : Box := ⟨631432314698704928688196526520796368603118196509681104873,2085437688487242156425571303899304034067063833845421103491⟩
def polyval1Tail69 : Box := ⟨4138154976286092155422345442591045770460653617212703524387,4448496026937015442675635723084368578957517688933533544856⟩
def polyval1Tail73 : Box := ⟨27218750000000000000000000000000000000000000000000000000000,2⟩
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
def resval2 : Box := ⟨113975670783464756058376807115286380133940851919449894023,225006929803068408626331677290126679989865972315231040⟩
def polyval2 : Box := ⟨3779940904462265769464141597184853420739464122550424096400,7507601492900708191374355465622755193596147464223579168⟩
theorem cell2_lo : Holds Q cell2 (3/4:ℝ) := by norm_num [Holds,Q,cell2]
theorem cell2_hi : Holds Q cell2 (7/8:ℝ) := by norm_num [Holds,Q,cell2]
def resval2Tail4 : Box := ⟨-137419202179270895260620697452378792161957094922348,34260886558283550453044247004546713189482915519340127⟩
def resval2Tail8 : Box := ⟨-444460317988254698500035358162093478995054349360128,58332237907551547221611185325691134122976409998071585⟩
def resval2Tail12 : Box := ⟨-1019872680113073140706267101641604760244876134655597,99250590586569382431600025326063175312498668744885520⟩
def resval2Tail16 : Box := ⟨-2340197344065188125981786370912926061671467218512140,168716786230800684320970673359029251048494825235090085⟩
def resval2Tail20 : Box := ⟨-5369811041004126572282206672873111174061080562680742,286445851067591268009887427001930768828496208276155974⟩
def resval2Tail24 : Box := ⟨-12321555141040769183928400427187594424319070853255861,485503081259129092793348925299259358271061293145954919⟩
def resval2Tail28 : Box := ⟨-28273009968952366974548385249640635685371889597150114,820993841632503607210366933046192286249633749234591403⟩
def resval2Tail32 : Box := ⟨-64875178786641307666964315183761132858089186880990036,1383936576381856682203022325406972624574990865693901520⟩
def resval2Tail36 : Box := ⟨-148862424878727101748768241387135778489519861586450010,2322746466903933359336363411999891944956658963312151191⟩
def resval2Tail40 : Box := ⟨-341579352153365055295723809467875795228641504733431908,3874876299967325177325541539640648909773367400006230043⟩
def resval2Tail44 : Box := ⟨-783787137100344254538732553943635752980459780538739305,6409300056188430085821545986058377855141170796911884251⟩
def resval2Tail48 : Box := ⟨-1798476027345266653017239300283197599573788035529786693,10472613162038664908207992251281909261866847705356607204⟩
def resval2Tail52 : Box := ⟨-4126778646689520311106046531024865103149685767671862477,16807157763021676330980342982374316593008881679936170814⟩
def resval2Tail56 : Box := ⟨-9469296081700358034674523469857791156838136056810515100,26243075236157625811950238722048912124020022571005903127⟩
def resval2Tail60 : Box := ⟨-21728223381890468165722809809910365397858780512160776320,39195505446903484032787744568676897417964191702268473568⟩
def resval2Tail64 : Box := ⟨-49857527654427687655895146118518822394742252714811876847,54075664042637064660359620052426804203113280554689347148⟩
def resval2Tail68 : Box := ⟨-114402822944700588275605091026482040450873634160902988032,62902480863317027671221673320089900343542365225517814904⟩
def resval2Tail72 : Box := ⟨797955658172605826921387004454030913654790358280092184353,1037211480931547504726566688195652505585237807824810975⟩
def resval2Tail76 : Box := ⟨-28404383404272357135722005356652377194629332887456,406511335634588209585274540974210281787300840660759⟩
def resval2Tail80 : Box := ⟨-4887129322663037932433136269867243827592552794945,692120961703759608571076042769483514940351691733339⟩
def resval2Tail84 : Box := ⟨-11210841851333963522470380510007273395225411045167,1177851832390188799086651426341776221027870367555559⟩
def resval2Tail88 : Box := ⟨-25724368274946898105213713657615877313404754151472,2002764057625286002320536457020465492169152756655428⟩
def resval2Tail92 : Box := ⟨-59027071850973183481850737484627972828896696992347,3401484628473491727630995074756155608293083323380282⟩
def resval2Tail96 : Box := ⟨-135443373160047951903144053107858342653130866494665,5768036811983195990082304768984573804893900694024644⟩
def resval2Tail100 : Box := ⟨-310788029250266700976628810951602370068954513146786,9760288538157781994512576472573902953132377889999809⟩
def resval2Tail104 : Box := ⟨-713133443680034869242573721530803217974363684699923,16467678559694961918427418199152640628431361248337598⟩
def resval2Tail108 : Box := ⟨-1636354237072048063547936791103005065503314147309010,27673352537531861479543483565263491327656527830170068⟩
def resval2Tail112 : Box := ⟨-3754774387477810362308844745933777560733952730528911,46246291397102620074852319307681637900550189565511743⟩
def resval2Tail116 : Box := ⟨-8615696028071348341551294841420363575990914483905655,76683914739792642943851993508545552676114646843240389⟩
def resval2Tail120 : Box := ⟨-19769554808854167811948258573577633651766819107590912,125747815330742212213997363831658075200153834728831666⟩
def resval2Tail124 : Box := ⟨-45363171595989873979252994152287819694953011531328510,202883037521788874893400706295756152556737709983596456⟩
def resval2Tail128 : Box := ⟨-104090221410832794184854291481924702781728206546705438,319406851703045578811645656722123913139115744121278216⟩
def resval2Tail132 : Box := ⟨-238845164748467198638232731295476425628784680304220390,483622145320042646619165568604301989837370437181072996⟩
def resval2Tail136 : Box := ⟨-548053524651438519689042777909600005941594465401492294,684443810661447039223275449237473802897484070128986529⟩
def resval2Tail140 : Box := ⟨-1257562450300480410493893442922846614599792806922106300,845023758391207495989674664435602657235558109059579777⟩
def resval2Tail144 : Box := ⟨-2985714015833954667428157285674755483228482483359401393,691925074781626527378687032559515109319897137505300523⟩
def resval2Tail148 : Box := ⟨60343516566887929226141571424136815448921321,45841484189847309691942675432089864059335721⟩
def resval2Tail152 : Box := ⟨581639670608824612963822456191215745930932,77025595930177662683742706576198532591621169⟩
def resval2Tail156 : Box := ⟨1332254367790875418823932259113279872006489,131060485442763076988357845993011817832776597⟩
def resval2Tail160 : Box := ⟨3056986848432010410438662577312877944053530,222799181808771400960954230094328935399954871⟩
def resval2Tail164 : Box := ⟨7014554464604105421300682542901298215673223,378286098104186961469069194814435261967815162⟩
def resval2Tail168 : Box := ⟨16095579335179746698138562224861447556864974,641210323589332455280223695603326513535192876⟩
def resval2Tail172 : Box := ⟨36932876555804608479566676100110566674279717,1084401974913917046109668035809328945650566224⟩
def resval2Tail176 : Box := ⟨84746087250488798883554309825086630353894552,1828201664361331226869489988793054816906907152⟩
def resval2Tail180 : Box := ⟨194458162320928325111185859820568079858892577,3068946248592030785051148389518493899334278280⟩
def resval2Tail184 : Box := ⟨446203218580034267241157530146282536916539087,5121020632773352036257931323769206774986118937⟩
def resval2Tail188 : Box := ⟨1023856802383009199135060920713829724937215829,8473581304715479055355399140406326324050263689⟩
def resval2Tail192 : Box := ⟨2349339287874125237079667278420524866655382438,13852870827359280798684017340881900286497114796⟩
def resval2Tail196 : Box := ⟨5390788122618909420392587341252762362011359098,22249467034397346785989022309638572536888228968⟩
def resval2Tail200 : Box := ⟨12369689100660091185827910552494487810358812120,34783365927719161870630735011525699453356236960⟩
def resval2Tail204 : Box := ⟨28383458033712462829743616384074159968433944582,52057572118824629332912831533889482986835331962⟩
def resval2Tail208 : Box := ⟨65128612643052986996203847205846651686735306723,72100233464758257224290468327854760253994606660⟩
def resval2Tail212 : Box := ⟨149443953661101394769950004305603846964445730397,84662399454923226242762166940934137350895501325⟩
def resval2Tail216 : Box := ⟨342917647616532751956710150098907547405644732420,56460954798498006513078818698001329455113353673⟩
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
def polyval2Tail5 : Box := ⟨22044908682997528938402312510994183644875907484508016,3072455934907020178490113877051729219985713523960913296⟩
def polyval2Tail9 : Box := ⟨45956006946592853473478777932744051159520956191691763,5229681491038668880578807877702018512026023794885133067⟩
def polyval2Tail13 : Box := ⟨105450105405987617558155478380376218308581261004138036,8894554231474634379617103936855046495840331052031992268⟩
def polyval2Tail17 : Box := ⟨241965550871465233814442120076804074848066332344914926,15111644512963705663407409540784508767223532633703190686⟩
def polyval2Tail21 : Box := ⟨555213554913358705386499099188915848824608490807252361,25637367378642177509950934158036080954301307619430455359⟩
def polyval2Tail25 : Box := ⟨1273991650670547659315799091324064845085624637833176035,43409395064799445327245560409481964841639855142583107455⟩
def polyval2Tail29 : Box := ⟨2923298092445817705155483606554208646468621173454185122,73304586949855344522605900636172243381342526189103278915⟩
def polyval2Tail33 : Box := ⟨6707792576819057740722812202356226679157451251212804650,123333613975977927024273904763179744098757079894032307413⟩
def polyval2Tail37 : Box := ⟨15391684265761484818817286658664781853031248571530412141,206453214209980476691101284332931209573176701533402259017⟩
def polyval2Tail41 : Box := ⟨35317720669477422675276848325155646882998002025006036010,343139882061317693668287747704407723409124540845816117144⟩
def polyval2Tail45 : Box := ⟨81039954546229906953577975747363777252150738718830295737,564592007463489708434667411456376445801244338488813762870⟩
def polyval2Tail49 : Box := ⟨185954079378933622186533502028969750395275994230606325320,915465544274465605098682380894510422301118893088886294952⟩
def polyval2Tail53 : Box := ⟨426689770882594933424351095926742740905737548292712981454,1452283481297464723834718212010081655317768022196212013584⟩
def polyval2Tail57 : Box := ⟨979081293531800129601014994883281031200470335064638641171,2226364121266002659037267712816436193522117522847261485428⟩
def polyval2Tail61 : Box := ⟨2246597515944836401866667169165864600168950905085574998008,3221750846825605473765272554644044490315182445044702522095⟩
def polyval2Tail65 : Box := ⟨5155037106732165311856893105146362033203677601156693213676,4173723782038655780805850085983214586466719373624353537650⟩
def polyval2Tail69 : Box := ⟨11828735527688420548793863169915626948463666415902963916746,4085718812115967506212453477143056524947477196441263774797⟩
def polyval2Tail73 : Box := ⟨27218750000000000000000000000000000000000000000000000000000,2⟩
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
def resval3 : Box := ⟨113792829469823641895781059486762898094338421847594068937,1739771160960499635352536022810677727185880539228282259⟩
def polyval3 : Box := ⟨3798136488764732313155052513009775862881900527730035929894,240393774181508650762746390744535441798027584262319100617⟩
theorem cell3_lo : Holds Q cell3 (7/8:ℝ) := by norm_num [Holds,Q,cell3]
theorem cell3_hi : Holds Q cell3 (15/16:ℝ) := by norm_num [Holds,Q,cell3]
def resval3Tail4 : Box := ⟨-188973730655116301544321499357381664532192496059844577,1989159518984799581349199854834022442387986110031980150⟩
def resval3Tail8 : Box := ⟨-280244932144142705898726515394438560103045438149893356,2539503443159333853179965039965882122265913324705541408⟩
def resval3Tail12 : Box := ⟨-415475768186928718162969611662587008865805561815943393,3234796428203578047847306165160836285940335563527668219⟩
def resval3Tail16 : Box := ⟨-615961575538361165705976217059510559435272214239891728,4109455484471719814733961803924309380312300159705158065⟩
def resval3Tail20 : Box := ⟨-913190832260071192896249896746293237738324195055614215,5204042401217894876501196491091037189550103724920383819⟩
def resval3Tail24 : Box := ⟨-1353846618427381343072296282906686070166738766874181417,6565145918643473006852260994128904170026627223168476503⟩
def resval3Tail28 : Box := ⟨-2007138706912966458619571973590759491144918740860541056,8244300204879142406096985571021043018936505241230119375⟩
def resval3Tail32 : Box := ⟨-2975673709232922584185010007660977282605828589194971117,10295206301102043274726836736380059612824105107453153690⟩
def resval3Tail36 : Box := ⟨-4411570557292817185537023602032114465936355314681449181,12768091513962734864556739587840516639270064379690321828⟩
def resval3Tail40 : Box := ⟨-6540352432320213710170011055683556122429366104495083713,15699377612159862519960535926784907909326274132573401178⟩
def resval3Tail44 : Box := ⟨-9696367627679239808482646612419760982730444246979454155,19093814065062415021762990521752156840267696205598046451⟩
def resval3Tail48 : Box := ⟨-14375302576431979024678600801046048405324900870094959261,22894689471281938813282775692298661775353284534781004449⟩
def resval3Tail52 : Box := ⟨-21312034784455879205911753367902574073382716197555462027,26935396303721489851961721304945610707450138504370672278⟩
def resval3Tail56 : Box := ⟨-31596053317062945252778515418547601218583197466521502617,30862092733204535500064796224918216991716530112703892240⟩
def resval3Tail60 : Box := ⟨-46842574878993480853842460149011121894032532302913867091,34011885556563856748615252938181582961509170562257648913⟩
def resval3Tail64 : Box := ⟨-69446231118062994966911035969803098520737197103263224313,35222962338646868415935674260250966924800453062268518257⟩
def resval3Tail68 : Box := ⟨-102957048002192255662012527866305175650043116210032862439,32541104374240694013342272128569907710665663912760921470⟩
def resval3Tail72 : Box := ⟨798670376812897377185058362248465710942169131060149970981,817606248106025248946376209320853092310024950064738511⟩
def resval3Tail76 : Box := ⟨-2343582986304720362389352653055206382541626092268461,25346738926859416801629779235202721795669412015106280⟩
def resval3Tail80 : Box := ⟨-3435725852670607664796634641954318110749066852046462,32376475648435051037068490928162415449482680702115784⟩
def resval3Tail84 : Box := ⟨-5093616605530713909567546888622491381736169151236239,41266647051663397585287345898658520033787080922948208⟩
def resval3Tail88 : Box := ⟨-7551516476457700230877393463324282477493205955529430,52463619108503788459875646870007693904858030014245876⟩
def resval3Tail92 : Box := ⟨-11195463953953318649742294781578756128636163912595745,66496425936336162851076252958029132933929614895980368⟩
def resval3Tail96 : Box := ⟨-16597780529917438363198457499676016449694209178712099,83977344326379059650863705721750220779319621902184437⟩
def resval3Tail100 : Box := ⟨-24606958644355931110644994077071842124579769804899925,105591389653565002393571758700987585515863594785759844⟩
def resval3Tail104 : Box := ⟨-36480926629535028909330477338807025702146220680258082,132065818141873292978311206736965218589640743516739514⟩
def resval3Tail108 : Box := ⟨-54084620004625209029732219883859406103512389045555691,164105591656392386680120746075906121295626441688691901⟩
def resval3Tail112 : Box := ⟨-80182889835821806584171869498335164664567106085611615,202272689648947559388186056205993733916374623749404741⟩
def resval3Tail116 : Box := ⟨-118874752598311967471585539558121916581681858971416428,246774805073072628451160717263999872805583789067243653⟩
def resval3Tail120 : Box := ⟨-176237185193052788999659646023092635161994190987253894,297110161207971623474475185803825930042769591951113417⟩
def resval3Tail124 : Box := ⟨-261279580111710228974443066077087879178043585262407810,351486675567055913607147039930862374537636323471824205⟩
def resval3Tail128 : Box := ⟨-387358768290420265655467685361148486731738308145624505,405890601233799435237658548472261024320907112850873775⟩
def resval3Tail132 : Box := ⟨-574276854346306735011387065401300737498272207557049505,452614813429301993202117959266369964924913760199672835⟩
def resval3Tail136 : Box := ⟨-851391352004228048042390568060933316032397875193491058,477959212741464862281877127121703655209965471772701290⟩
def resval3Tail140 : Box := ⟨-1262226269655099891453207922555366535113918191127405079,458669069867427562159879308671200397307711983225869358⟩
def resval3Tail144 : Box := ⟨-1961279640893667364592694275115537778784217252750668053,351286169444851314172495564953989202953843786425559287⟩
def resval3Tail148 : Box := ⟨588988241823639296853789281761723418927921671,5169588006751800753210371876542873132538162921⟩
def resval3Tail152 : Box := ⟨784437866975860841649385810012223930646624514,6592219412650057026142879427304518990929523937⟩
def resval3Tail156 : Box := ⟨1162963017153146293822458018819897411484281329,8386400806753645295749667210505573531926174783⟩
def resval3Tail160 : Box := ⟨1724145153546183086272314178792165401241850286,10637871785568072499924573849860430846033063920⟩
def resval3Tail164 : Box := ⟨2556122995703672992590790519054372601855499273,13446981046207566617603042886938826030749754776⟩
def resval3Tail168 : Box := ⟨3789567691402668954994653193985257669100910549,16927062955327104329550089320324614918771271393⟩
def resval3Tail172 : Box := ⟨5618205114488081729676186639213512752674681071,21200266116407373430943364534050114148206018623⟩
def resval3Tail176 : Box := ⟨8329242615211570485073822748047858889269424633,26388294779118593449161347555646821266060438648⟩
def resval3Tail180 : Box := ⟨12348478051139628708445113000921511479873158571,32594702801696353979254421310146649965754265989⟩
def resval3Tail184 : Box := ⟨18307175961112750536919673791117381827237667026,39873491700545698083611362492460560226340890211⟩
def resval3Tail188 : Box := ⟨27141214511063867836192014334136956097839040235,48175886444480785769664003649614707355674433500⟩
def resval3Tail192 : Box := ⟨40238075315402656484293216416028850953018205679,57262794377882764132996414322498166350933718489⟩
def resval3Tail196 : Box := ⟨59654762480433739823498706860377678645493821898,66563844852290276496449435976454728864987978283⟩
def resval3Tail200 : Box := ⟨88440877420266187779684070715404168389215470954,74953940360620748665333351991059221221274624230⟩
def resval3Tail204 : Box := ⟨131117591850810472895553109467240842750853504205,80403253148462792220680014827523769549847037079⟩
def resval3Tail208 : Box := ⟨194387746868040939123692280169258261527397761232,79434082225759135324734541557367114312434711540⟩
def resval3Tail212 : Box := ⟨288188606950437823852797265313092859858800389292,66284230480576103662253945737104442093780186755⟩
def resval3Tail216 : Box := ⟨427256149756607906250497119169056316838893372260,31625782596227795837785453349144080039996418697⟩
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
def polyval3Tail5 : Box := ⟨33624859218107481200170827890516811993787081475905433500,303570466692764614204692818155660505121948301859042687822⟩
def polyval3Tail9 : Box := ⟨49847400489266131980986075773866626214227595175093275084,386662251460924306663670738963748187253422647557838081667⟩
def polyval3Tail13 : Box := ⟨73901020413668795971181847045208970675605303899133228059,491177429716504867100298888628255662178650572188243574304⟩
def polyval3Tail17 : Box := ⟨109561597697569474246521252898799552439692412332121857130,621954082454956929711668604100561645680865456285171161327⟩
def polyval3Tail21 : Box := ⟨162430012777560984747250757739487602733725889636055023195,784545031459000765720817882070781601640837128342055447132⟩
def polyval3Tail25 : Box := ⟨240809823928882270995956906449037206624948182695092358477,985085613090126331783798406450461285007701387015270387877⟩
def polyval3Tail29 : Box := ⟨357011431009813152072712685016754508988749660059214674651,1229957129197154705308919999586645147433253101375078018909⟩
def polyval3Tail33 : Box := ⟨529285557342196150799164775919900750768212526124152993868,1525105979679509439332087334065940669074415216121707069200⟩
def polyval3Tail37 : Box := ⟨784689723851836357852113014779213045829774341381082267277,1874798745684054951869799794775031060908911587659675792082⟩
def polyval3Tail41 : Box := ⟨1163337926337146283826150376631745040302859739715545231046,2279471680369108982818818007498704494565472888427534750371⟩
def polyval3Tail45 : Box := ⟨1724700973795280096187904139873964925892022731621020348794,2732147823935112894527750149513710891256159546348915582541⟩
def polyval3Tail49 : Box := ⟨2556947024306265292254726370194506172661524970236771905966,3212614315112184782636537120834248775560997393966893457634⟩
def polyval3Tail53 : Box := ⟨3790789350991991069759147152675412756617043062596283102684,3678128613257441901149884822135404867350810095081708157650⟩
def polyval3Tail57 : Box := ⟨5620016279959136570960329819501745667803745506420814029827,4048783872239398579933794190065305510530934126189064365575⟩
def polyval3Tail61 : Box := ⟨8331927749754964642416906450743369921096677686514380966278,4184704087765703326353263731960955505452362348111641766358⟩
def polyval3Tail65 : Box := ⟨12352458884285691424765004315570325724166530379443483849906,3850800060985852711166175296414781504286586296475868696594⟩
def polyval3Tail69 : Box := ⟨18313077839303360414645394809802122631542226128519152718916,2662661095467715584614491917642432549724117906012724000091⟩
def polyval3Tail73 : Box := ⟨27218750000000000000000000000000000000000000000000000000000,2⟩
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
def resval4 : Box := ⟨110557641001866120718325916776965623933842231618397713837,8844201808699925942246954947155864010678036071029873971⟩
def polyval4 : Box := ⟨4629499235328789565310905670201805481111714549857333369081,1906874576196510871636308285723938627688866952196413697036⟩
theorem cell4_lo : Holds Q cell4 (15/16:ℝ) := by norm_num [Holds,Q,cell4]
theorem cell4_hi : Holds Q cell4 (31/32:ℝ) := by norm_num [Holds,Q,cell4]
def resval4Tail4 : Box := ⟨-4041123945051009379661398779667621029750190609271908174,9587934893316669098425723317660095538256382497568569008⟩
def resval4Tail8 : Box := ⟨-4896758786602979077495050536330046727785406211441538188,10577888563863171652706036916627483752300614414608454437⟩
def resval4Tail12 : Box := ⟨-5933477061549931592977934497277731597816530599981964014,11636609408414739395308279056049133288039778559348871567⟩
def resval4Tail16 : Box := ⟨-7189684345845309839530327772440051888725820821872357527,12759586965078244150180348530863770578006740912613634412⟩
def resval4Tail20 : Box := ⟨-8711849806889001984933323927337024371220851721050958498,13938774395617490216366824493285590701531590884326181981⟩
def resval4Tail24 : Box := ⟨-10556280833337251158439862855053666583121120201253802636,15161489443426837407679555506140867039816620405632309027⟩
def resval4Tail28 : Box := ⟨-12791205943904676046475308611372213069280078018130122637,16409036049215329824154423031133020297764253419061922942⟩
def resval4Tail32 : Box := ⟨-15499298671808569335442394431951563752475506642678126577,17654980384301473940829155892535603422514812580589641141⟩
def resval4Tail36 : Box := ⟨-18780735793907027994466904749855114835051764125857034107,18863000856953802174569700804265169402329403751001767141⟩
def resval4Tail40 : Box := ⟨-22756903033431460940554909752442995530225819281816668842,19984213630307691558657686642380753152171196777152733890⟩
def resval4Tail44 : Box := ⟨-27574885316315191066205233783916469012364050297164320535,20953853225414716072161287613226336631085056685735293192⟩
def resval4Tail48 : Box := ⟨-33412907683039859009184728987171370737711083474230230564,21687161016137505772068526578125275278229679959165053041⟩
def resval4Tail52 : Box := ⟨-40486928124222952479797063663199204174838010462281050889,22074301816740603582877425427816396360984797330574127603⟩
def resval4Tail56 : Box := ⟨-49058626219711976880353782152061703322545899289051450835,21974089058636633191073558417056440063561383391214240200⟩
def resval4Tail60 : Box := ⟨-59445083093999923619687611141825791509628822943755597458,21206250720505023379972167940609159126901525005355599016⟩
def resval4Tail64 : Box := ⟨-72030510758731132923201732251093969525335622611779633911,19541909358973206556660286018788563928018264566029613073⟩
def resval4Tail68 : Box := ⟨-87280346935873054145831846177960697167267416362959037689,16691875245989197064743634092891698284441575324269940525⟩
def resval4Tail72 : Box := ⟨798986995366894469722299586742357116402439222479818715726,791354907383890419875618518403275996123293453176844229⟩
def resval4Tail76 : Box := ⟨-52108535925364268602445565043184554883493359228391991,126550845603824040196918894001339588423881070344862978⟩
def resval4Tail80 : Box := ⟨-63109126269650092939360835703707198521199642289502542,139712969447862488133779635181550649509962079704708038⟩
def resval4Tail84 : Box := ⟨-76470285937465029014468337496796498490941871102174685,153816172524411951434289626279383657970972749308225893⟩
def resval4Tail88 : Box := ⟨-92660207837306972251880288133910174298408439786954244,168809594654826933308152587408131799736485381234477015⟩
def resval4Tail92 : Box := ⟨-112277782295157042228030272865679847994679693615671172,184597935331177084779609681301798789248553438420923399⟩
def resval4Tail96 : Box := ⟨-136048695457850855525224870921125395323958853541939747,201027291429021141758996609516645621294805241865318549⟩
def resval4Tail100 : Box := ⟨-164852272261004780465850739621695861115140996691230954,217867546807417801013288074710658357840054711149841792⟩
def resval4Tail104 : Box := ⟨-199754004095069817595574547472421732110590502021428677,234790328951488167287442821664686664861400052844038840⟩
def resval4Tail108 : Box := ⟨-242044963073595230856637236078784274327474420784573400,251341498705430460546671061534276505031636838313259923⟩
def resval4Tail112 : Box := ⟨-293289560901192718062335474834572812319047701812505371,266906907339814950835208932559047418451553046218880615⟩
def resval4Tail116 : Box := ⟨-355383419019795539228032002356090608659996596120223860,280669872548325659344285253902390401461978025923220629⟩
def resval4Tail120 : Box := ⟨-430623490744521624834300506596359188309436844291799759,291558480493094253929811464900829250878305732380402748⟩
def resval4Tail124 : Box := ⟨-521793029321573181375557303327744160071094990781185381,298180401355644022131101317556765169355932911550418536⟩
def resval4Tail128 : Box := ⟨-632264545015529794558652296957466452936723418572030034,298742394778794087464619008569675918333835221766647439⟩
def resval4Tail132 : Box := ⟨-766124559777014542118973841812299611226291120822326959,290951059404129700556156777231899620369037836353268620⟩
def resval4Tail136 : Box := ⟨-928324774388491128239915890868321596791167429708254700,271890623501334489427393031860374703916923084682873554⟩
def resval4Tail140 : Box := ⟨-1124865401731521115866561298965032066409183723373526278,237872643026718449705857900442809406186083053411772792⟩
def resval4Tail144 : Box := ⟨-1448651305692731537540603443412928138974532428113703524,180738608048563537992473061107428026957856528771662550⟩
def resval4Tail148 : Box := ⟨18130178789166251778020571539664748579584207155,38522273813723882953093671924204883611670135422⟩
def resval4Tail152 : Box := ⟨21896195503225415764065621106030898461872626965,42359261842946308823912014911882146142512232500⟩
def resval4Tail156 : Box := ⟨26531951682398779438379309630575946265785712959,46424407035131973590681328300571484559771470551⟩
def resval4Tail160 : Box := ⟨32149169145589675909216480055186733167846767765,50686290793340476747253692272775895859098151211⟩
def resval4Tail164 : Box := ⟨38955636929247178608056328061440487718733298333,55096664253858632512693623635669752356334323374⟩
def resval4Tail168 : Box := ⟨47203137402744735950697985963293968930634672356,59584889902943337638513997365362065454906625937⟩
def resval4Tail172 : Box := ⟨57196759090583766406083908727022009129392233628,64051553097324442915981611716012116448080922806⟩
def resval4Tail176 : Box := ⟨69306182395326323264456444805495869720916034975,68360497843399204898311972322795786623443735276⟩
def resval4Tail180 : Box := ⟨83979354679992866875148350558050134139526757139,72328922985595527344752202485088831055011424646⟩
def resval4Tail184 : Box := ⟨101759060573268984240296862398530141484810509323,75715093843871520477445566348835030052657822872⟩
def resval4Tail188 : Box := ⟨123303000460197222740135788363108695610603554081,78203125488327523177887950630497439676328131365⟩
def resval4Tail192 : Box := ⟨149408119894546543508986277087641409112731854626,79384173429157285615037191189835567948955699353⟩
def resval4Tail196 : Box := ⟨181040089917593635713858821918208093009462960611,78733220883347616665819111111371573067814877047⟩
def resval4Tail200 : Box := ⟨219369028808498568921658763976781490878530843951,75580473310465455812558563442714408901463076256⟩
def resval4Tail204 : Box := ⟨265812786672214707374397130118199767309466240468,69076153735090454949000470870370921857439287303⟩
def resval4Tail208 : Box := ⟨322089394032621933366312341460454473092962400887,58147228173643807778123286561253646472234629177⟩
def resval4Tail212 : Box := ⟨390280614661039129673152578317432899039253063535,41444269156190083937186014421679760514722934175⟩
def resval4Tail216 : Box := ⟨472912322140078330834350855100033922338008105070,17276083234201151659185871789263186979488030445⟩
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
def polyval4Tail5 : Box := ⟨1037561440002328731270366232815309443161488680860841873440,2097614738281448436780254536957901435308553561568154146647⟩
def polyval4Tail9 : Box := ⟨1257226547959139797214300589739797492325877245647379699823,2302485026385575620443648066254914432247675795239029264107⟩
def polyval4Tail13 : Box := ⟨1523400518099518807033210695613202415894245871349261881595,2518335537261379394171711689791634242248638663636045227653⟩
def polyval4Tail17 : Box := ⟨1845927563855830827182759023190176622591200095156972563116,2743104440815377979651400895917265030426197537871582269882⟩
def polyval4Tail21 : Box := ⟨2236738487691940039942979114233238777905151206792223498681,2973699416080813304106739580752183091649872082888833299549⟩
def polyval4Tail25 : Box := ⟨2710290024529461187711460582167822063564693393760134007777,3205699038400800933828743403556351143833462023012123588710⟩
def polyval4Tail29 : Box := ⟨3284099619819126097652361312259714861198743838476684110514,3432980065051236930551838166659812328647379221136895333561⟩
def polyval4Tail33 : Box := ⟨3979393428483207301841252710929308183085602260122297218448,3647253445429379182545411360194676894559327942466155070995⟩
def polyval4Tail37 : Box := ⟨4821891505083968628249817325189690882883447189928134316675,3837488056896499910581157721055062727936795042419165684461⟩
def polyval4Tail41 : Box := ⟨5842759230685867316645627116839145519941540588990802815743,3989196494829017324388976403010218066960126901991420262150⟩
def polyval4Tail45 : Box := ⟨7079760171246414292837952037133248086597648016137638470996,4083551552945559335655945571406385707980102988078448765724⟩
def polyval4Tail49 : Box := ⟨8578653013652119926629291441383404151366082143188845384565,4096295097442617431271158093974766286400626420549406832640⟩
def polyval4Tail53 : Box := ⟨10394884254347032071273453300246191858600998233535052974679,3996392598631162599553946076459294247072647644150449812616⟩
def polyval4Tail57 : Box := ⟨12595639255873232754336871744370468098202047027676219608339,3744376312141423659393081374967458549743537291744535563941⟩
def polyval4Tail61 : Box := ⟨15262327543257551090692349077641632097683329307257430935979,3290307604450565277584452768575808653646052892226744694845⟩
def polyval4Tail65 : Box := ⟨18493594275433152058048352355931000010652986615916373206080,2571273716365781767143850594283150857294983300769117618284⟩
def polyval4Tail69 : Box := ⟨22408969399132580789053170536252331355057249414965668642607,1508315766902850760292618359460744111834729611170183332061⟩
def polyval4Tail73 : Box := ⟨27218750000000000000000000000000000000000000000000000000000,2⟩
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
def resval5 : Box := ⟨98626875627503534915647293827329498684735927129315836417,14162440812900973422737485277189906527728234050747445056⟩
def polyval5 : Box := ⟨8695343184660977132215452079941014748170890492141595278691,3817626493584868111188625990440335685802786289938011550069⟩
theorem cell5_lo : Holds Q cell5 (31/32:ℝ) := by norm_num [Holds,Q,cell5]
theorem cell5_hi : Holds Q cell5 (63/64:ℝ) := by norm_num [Holds,Q,cell5]
def resval5Tail4 : Box := ⟨-16769786008938431726733581091150883216091886469666425569,14374992619183690111703106049348266911980192171789268510⟩
def resval5Tail8 : Box := ⟨-18438635832962184947001754588675054854651356494759695231,14731229942565927684385201527773610263491164900473363501⟩
def resval5Tail12 : Box := ⟨-20273494505766766744513602435006005043211567928263872562,15053070634175577021559019029652874614875927170507455831⟩
def resval5Tail16 : Box := ⟨-22290942944749586932614565065691111401275147635565973569,15332549799946139862306865416189807420975891302531101323⟩
def resval5Tail20 : Box := ⟨-24509150961843584624483889615340635687425214576246254397,15560615252406130539442687487016129617608500088651828586⟩
def resval5Tail24 : Box := ⟨-26948096469464356094280498703730820484730134388254129497,15726999523344218340336114579647924129891127651088565127⟩
def resval5Tail28 : Box := ⟨-29629745414605432858639280178094338250600303347191880704,15820078481491554881574568499440155745113402934097735856⟩
def resval5Tail32 : Box := ⟨-32578249611401291488077738681482079788699254619899106381,15826714551639594620790930179651458509965205749388290878⟩
def resval5Tail36 : Box := ⟨-35820164260324673452535740832981322861627787379385381104,15732082916291593361110776013556214253741393706109670502⟩
def resval5Tail40 : Box := ⟨-39384687113073280721993671753518869773821298246584239030,15519478914347294841184386838424664335490572167530121354⟩
def resval5Tail44 : Box := ⟨-43303921437143653056019344584511638503853604408053177380,15170104667656385429191122795639027780174808671812891342⟩
def resval5Tail48 : Box := ⟨-47613165148437839232694200947584600259215506996674610192,14662832763946307617516777058160221660680294136765348890⟩
def resval5Tail52 : Box := ⟨-52351228715926401091373283752067455789898371801840870280,13973944601751329679455283068906998124572433422918723782⟩
def resval5Tail56 : Box := ⟨-57560784701521896776020701436869716930538410521124978710,13076840757470584329054783967373751504030027297708454997⟩
def resval5Tail60 : Box := ⟨-63288752083229948620552146014420342962261774967213133777,11941720464283149990997078459351614056207287136481239222⟩
def resval5Tail64 : Box := ⟨-69586718816453273270492350160755090734002046127547295270,10535226994548282523964351088840149089624630938061705705⟩
def resval5Tail68 : Box := ⟨-76511291302400167633253098272317323250343983606744882906,8820051775875774627901279549536370907864314472474947599⟩
def resval5Tail72 : Box := ⟨799007976887247003843006609343081458477888939379497124327,802791133146729744099000173728993231336445432560220855⟩
def resval5Tail76 : Box := ⟨-221021631754483845437681949257828853374357133858736242,192578624176501654847290712093958461467554970672380199⟩
def resval5Tail80 : Box := ⟨-242987238153549522094099658965779572257256415910883582,197477358989100788061820353200035325568306138130681951⟩
def resval5Tail84 : Box := ⟨-267167292268468409832822619758287684859678368279517427,201936240947428817222391125777223641921226836366405353⟩
def resval5Tail88 : Box := ⟨-293753544409806766404736180247254405808557874723503380,205851025366871072612725605645230266179612309341303022⟩
def resval5Tail92 : Box := ⟨-322985437778994028461724452190574571566728166701565733,209103341069018269837494066423942927444658396888747394⟩
def resval5Tail96 : Box := ⟨-355126244440325670620913361729463376024150185956136735,211558861547642761774797792924445271843615729379083119⟩
def resval5Tail100 : Box := ⟨-390465435090560147659886428678462296311754611008805116,213065445684364628875298861550553170922358474196215412⟩
def resval5Tail104 : Box := ⟨-429321286126685857888163960805006178801489266879153083,213451075807756838888256705352691345404475037096393751⟩
def resval5Tail108 : Box := ⟨-472043746148038213753830895845318131171688605244147183,212521571762945185706422259196969763247626461357359210⟩
def resval5Tail112 : Box := ⟨-519017587708710426273757817884524010020679069405760805,210058057479596538058028918125472916792963039660676074⟩
def resval5Tail116 : Box := ⟨-570665872705977050933819005584343001856155593183939190,205814154106987611073882849742154404387312130272084260⟩
def resval5Tail120 : Box := ⟨-627453762615160437192969535013882747093162976382259103,199512871119722784816309154218223613200496386947829593⟩
def resval5Tail124 : Box := ⟨-689892707887170948573637372526985025281295002798163697,190843163861830561215550450081092027761099014462676067⟩
def resval5Tail128 : Box := ⟨-758545054239815898810714791323271437311533157995556923,179456122763116912168518184980888067565516580088880585⟩
def resval5Tail132 : Box := ⟨-834029107328673469134865450851820315124233227009129559,164960755899751677227341595026628119779521372388403759⟩
def resval5Tail136 : Box := ⟨-917024701429905852024847530669628527149061180097325082,146919322646905310979896949439354837871250369804435607⟩
def resval5Tail140 : Box := ⟨-1008279480418186805115119297915825035328326599862442612,124842163831766113696163911111346190180547898987745204⟩
def resval5Tail144 : Box := ⟨-1192234265807033524272281132847323586673255146638476306,95407800598630540530467727701994958028407807164687314⟩
def resval5Tail148 : Box := ⟨99055761935682228057905779711273714799354498332,74490545569231836882462081175872002286539781320⟩
def resval5Tail152 : Box := ⟨108847309250173691780049134158795221179650779195,75918861067720281569119544544036071110676562872⟩
def resval5Tail156 : Box := ⟨119678881053195696717409629843814365604616196038,77100754953842695650145935725214712350424005514⟩
def resval5Tail160 : Box := ⟨131588321316868152908229864257598844583794799450,77985895091472334417485419444449719538146218662⟩
def resval5Tail164 : Box := ⟨144682889367420451886383650497110686773095668771,78517809010075918156322631423580183241232747940⟩
def resval5Tail168 : Box := ⟨159080519199707380396638704696929959138659563031,78632652821102299904198016548292274666860314922⟩
def resval5Tail172 : Box := ⟨174910880612721482573623863851691743279120512193,78258363762242722579736762117507791377105773402⟩
def resval5Tail176 : Box := ⟨192316547058226997554376367997001988505155813930,77313721018711646683234984798245192846933721959⟩
def resval5Tail180 : Box := ⟨211454279704250870333138703707477008885090322807,75707305198086173040142098549972832260501084202⟩
def resval5Tail184 : Box := ⟨232496439277822474306605045256295066181801756302,73336345860720526052092567693485529875299628490⟩
def resval5Tail188 : Box := ⟨255632538402482530621729863952753386681230705372,70085445419792268529168341582102510092488868239⟩
def resval5Tail192 : Box := ⟨281070948411424397884302329749719830369515333666,65825166526637717341120750673505170063503388934⟩
def resval5Tail196 : Box := ⟨309040776008389361087052498708871106882217426653,60410468737071173522782488908137551914076946453⟩
def resval5Tail200 : Box := ⟨339793926678142394769142366396508039163104085362,53678978800608959717604863141474182974598073778⟩
def resval5Tail204 : Box := ⟨373607373430283195768622474791048597274650946037,45449077313459248696724821908735245891022746911⟩
def resval5Tail208 : Box := ⟨410785651309472388939261110567772887435881199017,35517782712963369342647525249093857267422197065⟩
def resval5Tail212 : Box := ⟨451663600207884391947124782386049313583303950937,23658411645358381934771493966649438375330067038⟩
def resval5Tail216 : Box := ⟨496612672037285410566718603793796674722592153976,9617830455014910010958176932340749144117412250⟩
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
def polyval5Tail5 : Box := ⟨5413152341069751864932329586050116109813960237291897813941,3893637389056326073414996369598196645204114837009226907414⟩
def polyval5Tail9 : Box := ⟨5951821749511875122152748979191699149233334386103890612569,3960091823394582421858932073978865204537535073620410260589⟩
def polyval5Tail13 : Box := ⟨6544097219834444933549645687676165025991752443919138266177,4012287385119204096622400384163308813177954769305821033584⟩
def polyval5Tail17 : Box := ⟨7195310986504412932691397680683876107002304845316450507911,4047448053931201053871380773064325482019801892941055258280⟩
def polyval5Tail21 : Box := ⟨7911328095126002919115273296375507300001090709282161838928,4062433336603626951722579075369900934430471532042375607453⟩
def polyval5Tail25 : Box := ⟨8698597231741992835678553475339654281921945787499653601274,4053696249629366736132729702493476242237435808268917733209⟩
def polyval5Tail29 : Box := ⟨9564208801640446038629981001084521723961708122801016844728,4017236758490076454696622407667704593727752872361491528062⟩
def polyval5Tail33 : Box := ⟨10515958787881233122998911310630999937299519584667820923069,3948550186307858315947916596309998994291394320339551742958⟩
def polyval5Tail37 : Box := ⟨11562418964488626533228696903696163030525721930666048706794,3842570065440972855414703699023003472251049816243987089797⟩
def polyval5Tail41 : Box := ⟨12713014096672982098989107001596044919887254323573271214109,3693604851520906893482546094534948314962545422039148853821⟩
def polyval5Tail45 : Box := ⟨13978106823372144773623975895914706313449907488322229101205,3495267859872591597320493317943775281308745120585661196828⟩
def polyval5Tail49 : Box := ⟨15369090986592719421507849776291562032076344506526845552302,3240399718661265715570481769221439388544173430632382594081⟩
def polyval5Tail53 : Box := ⟨16898494248106010724077455981708241071359670052672679057665,2920982560859519217825016703534339813673679323624653676336⟩
def polyval5Tail57 : Box := ⟨18580090917698413116906921043545523779993972151201941207746,2528045097556460760235272122879089181362863216184899597101⟩
def polyval5Tail61 : Box := ⟨20429026009144668601500591916179515818670581676469090059326,2051557627500562668632598524587760868408575055831812985435⟩
def polyval5Tail65 : Box := ⟨22461951641205368485302773275232485802473405904571072142501,1480315941266711428653484812040190730020771195164240461092⟩
def polyval5Tail69 : Box := ⟨24697177117904658706751143678051164638365756928451114093991,801812967108572219779412807959070222417717815269011608094⟩
def polyval5Tail73 : Box := ⟨27218750000000000000000000000000000000000000000000000000000,2⟩
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
def resval6 : Box := ⟨82275636652082869142641378940874774285550454304246283041,12746199684083441838563488781619735217357587259871370148⟩
def polyval6 : Box := ⟨15392971800919156467727899457030976914489989657434862476919,3820706730479118632541007616893531259321407455991716973511⟩
theorem cell6_lo : Holds Q cell6 (63/64:ℝ) := by norm_num [Holds,Q,cell6]
theorem cell6_hi : Holds Q cell6 (127/128:ℝ) := by norm_num [Holds,Q,cell6]
def resval6Tail4 : Box := ⟨-33121898001756366288619768701930767525842165416301046417,12459670353338421558752188454020489723835843873003731420⟩
def resval6Tail8 : Box := ⟨-34721119555958818970284814641921538820310065256661443145,12313191082487861843768295811003050547042621961074603715⟩
def resval6Tail12 : Box := ⟨-36397495150981724875369727701544276769378922851516224483,12135799930726870356058462539764452475873360875770336739⟩
def resval6Tail16 : Box := ⟨-38154808081142634951758644392467900185028494661477292084,11925244101990634601623528422573905858789874293502627565⟩
def resval6Tail20 : Box := ⟨-39996966100820757593766782949194619921468230830327038052,11679138364014942098680448436998478459128768560049905740⟩
def resval6Tail24 : Box := ⟨-41928065628532326325680602833397381949710331441358759394,11394957336687268877914545628992314034156857889205820939⟩
def resval6Tail28 : Box := ⟨-43952400862585414507258541909740056428579440121307304615,11070027929123557045050549439166838701186255403839091225⟩
def resval6Tail32 : Box := ⟨-46074473330121558970448564092560823623294771805474207973,10701521386332841480247416660417084880072932017817594109⟩
def resval6Tail36 : Box := ⟨-48299001897190329724323872591507209711879336178357779111,10286444925698586477509043116682112937346408250789869015⟩
def resval6Tail40 : Box := ⟨-50630933262121792460051961031385259286835913378914030895,9821632942637879902188595150087286850324452941232258584⟩
def resval6Tail44 : Box := ⟨-53075452955531062744156758182924103219874410897898561057,9303737763776708891908290368788126298138864974914055833⟩
def resval6Tail48 : Box := ⟨-55637996871415732241682221877376840565549063814659525884,8729219924906240354371025281823705499150837442301874245⟩
def resval6Tail52 : Box := ⟨-58324263354987941546453717937939438943011972668417156230,8094337949859033113111491933266197592410338913441674405⟩
def resval6Tail56 : Box := ⟨-61140225874120875074652196505895803655398207580812390210,7395137605262843977622097522990525604539694734447458094⟩
def resval6Tail60 : Box := ⟨-64092146302583109554999821585680937912422081595243032116,6627440604890191702410450802149320305396405309190868926⟩
def resval6Tail64 : Box := ⟨-67186588838200951659563286448004535077389279809732761189,5786832735709939842350713893899895818847440456883459842⟩
def resval6Tail68 : Box := ⟨-70430320734273978976731833992794940844224329164403536411,4868647343382109235955255459329067591161602123868662208⟩
def resval6Tail72 : Box := ⟨798878484732410399677560696634222504615442161617081033754,754790141922120533490222505262346723270387671156976087⟩
def resval6Tail76 : Box := ⟨-440279809539054943337499904115584936137408159853579224,167807365662331356626424431332684198795033272474468995⟩
def resval6Tail80 : Box := ⟨-461509760915810051467085818425380625274588763717301161,165930163547552025163254469355489643770571354231665447⟩
def resval6Tail84 : Box := ⟨-483791981588097618383405714971141751844124023821580096,163644464622596066265705832957710043925386788405228370⟩
def resval6Tail88 : Box := ⟨-507150014914172284775905349986584546068352826006043866,160920244005315990087585033996504242370738641504298037⟩
def resval6Tail92 : Box := ⟨-531635800956316508938353279477859428753858324502443440,157725870703452073547932086890169401713439320909758539⟩
def resval6Tail96 : Box := ⟨-557303788912038887457156930551158777278895055821602984,154027853245111108479411478694320343492279616078283347⟩
def resval6Tail100 : Box := ⟨-584211056849489312431188958081585972416748709590990335,149790739211661848009435599960013693111091793421155562⟩
def resval6Tail104 : Box := ⟨-612417438631600892984066222454190413752151752040628155,144977009599581834427294156812960700464335160971432687⟩
def resval6Tail108 : Box := ⟨-641985656969029856100261333908572879363323944075693934,139546967732648810616888842125950833551442741288979645⟩
def resval6Tail112 : Box := ⟨-672981462897046343933345279833650348978525747540599278,133458622450212363831198290937054683778345234531482652⟩
def resval6Tail116 : Box := ⟨-705473781986529941118503647185503535236476313526541046,126667565283700044400277263457345206734698256199325601⟩
def resval6Tail120 : Box := ⟨-739534867614200237919190949096280134813070051088361887,119126841319248602197860305612673240773550956447280544⟩
def resval6Tail124 : Box := ⟨-775240461632910417137146386490450245846562225102276752,110786813429386996922000872066723242196714476992112761⟩
def resval6Tail128 : Box := ⟨-812669962799287505044677410841500178148978921051040871,101595019540999323405639707608908818075791410366795271⟩
def resval6Tail132 : Box := ⟨-851906603333271460006370271495569603380038792040485713,91496022590325492192370060946388604478194808347443013⟩
def resval6Tail136 : Box := ⟨-893037634020260679504402458820371942840659274932739948,80431252797396132957778678862843411390008725418239951⟩
def resval6Tail140 : Box := ⟨-936154674659581685945591424581398114394731182286657733,68338834506232347269573562585455998166028414314734286⟩
def resval6Tail144 : Box := ⟨-1063999952022349325093762846085661069604630366028804101,52728115613600482057562763864436907697579497942627186⟩
def resval6Tail148 : Box := ⟨228262248689876954626336785464919861435469283493,73536035787997609959093745919583130363612282968⟩
def resval6Tail152 : Box := ⟨239220446952814432601125437155252180788942503012,72134077841137913473525890079522245961525020367⟩
def resval6Tail156 : Box := ⟨250770284216068107464540416007032384032752817841,70507114552583936600022526497861130863646732271⟩
def resval6Tail160 : Box := ⟨262877761972757632073663916637589705266768671336,68638754029092435789576776281736030796895335959⟩
def resval6Tail164 : Box := ⟨275569802681841003601087698469932813018920779853,66512151428018121428435629517934972159762753264⟩
def resval6Tail168 : Box := ⟨288874629714698205641996635419386090250447658991,64109483230573295874778378360525202133096412144⟩
def resval6Tail172 : Box := ⟨302821829099865088330784082947609125034355915478,61411894704652793456307717698557805740473497193⟩
def resval6Tail176 : Box := ⟨317442415313365487049748182324750401597912834299,58399444677299523254059351983666040069472459190⟩
def resval6Tail180 : Box := ⟨332768900245798407933767851738352199730734329057,55051047467375194531629021580844586227974363304⟩
def resval6Tail184 : Box := ⟨348835365499236034700718163287379498857434264242,51344411835796260602035880048453249044606276674⟩
def resval6Tail188 : Box := ⟨365677538174699129999128069572082690822214045325,47255976803638859151834390494878196932415857387⟩
def resval6Tail192 : Box := ⟨383332870318738919662287251319196832780146154851,42760844181007351259617668125692291367601189121⟩
def resval6Tail196 : Box := ⟨401840622205791329514279601628169155509603749513,37832707641788356443674301434997160119103488176⟩
def resval6Tail200 : Box := ⟨421241949641499076249039615691920308406252901100,32443778171258226011107074425186303028131803252⟩
def resval6Tail204 : Box := ⟨441579995481138620666267770011737724939897467938,26564705704958089281415856193876293626639742284⟩
def resval6Tail208 : Box := ⟨462899985566687316527029394907481575110109850018,20164496768275643731035473785240742562833815309⟩
def resval6Tail212 : Box := ⟨485249329364556670823067697447356152191525376075,13210427912829701505192685385694635947008282041⟩
def resval6Tail216 : Box := ⟨508680979584396124240662800557658806378566358966,5667806443009804941026143565181666873043129150⟩
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
def polyval6Tail5 : Box := ⟨12182514303831090771518341500308404013039945788939119533148,3749235130989283465020739150125727584768189705307380649337⟩
def polyval6Tail9 : Box := ⟨12770698018138698953765040722685420386061252144984631684284,3668794528580241480411613730817434596656847723128763497883⟩
def polyval6Tail13 : Box := ⟨13387282007070361151566332645629494365332549368456307478150,3576137501297590909106697261398402881016102094511394652707⟩
def polyval6Tail17 : Box := ⟨14033635380374312914904965358532090525217257127837914862474,3470408652760349450909166144777653624909030812805247245717⟩
def polyval6Tail21 : Box := ⟨14711195437974808290128991047092026064647869834644397637774,3350702834527303614206429095561638324917912043336410925725⟩
def polyval6Tail25 : Box := ⟨15421468874483353124926092318674159029999013074345096618875,3216062463341578923339234748409041603291048502011158376895⟩
def polyval6Tail29 : Box := ⟨16166035129460436195918527352520814985166469144494949578627,3065474711187504280003694486095697160111071152801028252267⟩
def polyval6Tail33 : Box := ⟨16946549899625192747955401958495346957286599321179743853454,2897868550812220787352829153920018761642333421021069973617⟩
def polyval6Tail37 : Box := ⟨17764748820638734183750092071030512059699353665626528384505,2712111649448675772968704212599979840873847123885639580719⟩
def polyval6Tail41 : Box := ⟨18622451326648212146276296560838546666751304315035756037360,2507007103119281129092453595638714641465715788217461813007⟩
def polyval6Tail45 : Box := ⟨19521564696174109253218330406776239300567642091799073307540,2281290003522283998070656231653621343433317981716813452499⟩
def polyval6Tail49 : Box := ⟨20464088293337621792976570558841271531281798880921076124847,2033623829107154549637913886309893480225849369329128239329⟩
def polyval6Tail53 : Box := ⟨21452118013859378702243401815623392668637337803757187771636,1762596651530139633332231736705254489396742569641452828151⟩
def polyval6Tail57 : Box := ⟨22487850945716092522941430462937599491904332087382073811038,1466717148245615441330754151367086143149964250434681359002⟩
def polyval6Tail61 : Box := ⟨23573590254819086474157964318004301507220607301525172750441,1144410411532003033895948084458053239768954210903256726818⟩
def polyval6Tail65 : Box := ⟨24711750306591282673269832150481812546149158836362262684975,794013543771037224138733980499982245056989946835897752718⟩
def polyval6Tail69 : Box := ⟨25904862139453544413526584541518051160539892154350331455680,413771023662310737558681950840113602853271194439346186776⟩
def polyval6Tail73 : Box := ⟨27218750000000000000000000000000000000000000000000000000000,2⟩
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
def resval7 : Box := ⟨63159596936296229830707860573689707624750105453596879382,20646853102241060599948778278566842446131277467112349749⟩
def polyval7 : Box := ⟨24258371306923079205716635781192857056582867938177060062888,6673131759183684906237540789297727765702668903686846607630⟩
theorem cell7_lo : Holds Q cell7 (127/128:ℝ) := by norm_num [Holds,Q,cell7]
theorem cell7_hi : Holds Q cell7 (1/1:ℝ) := by norm_num [Holds,Q,cell7]
def resval7Tail4 : Box := ⟨-51507950210599260773924285966873798353409662785218122977,19677868284586072548154489441319521350928710441219204796⟩
def resval7Tail8 : Box := ⟨-52320739630673260637294100071925108089031836185732132588,18865133851017106615348052217092494292643744574184691076⟩
def resval7Tail12 : Box := ⟨-53146297505467231855515134410245988690058031523387716753,18039575982553406238049844659434532517298544766583333893⟩
def resval7Tail16 : Box := ⟨-53984881676566222666693607026924027744874080440788103077,17200991811459870346401626778213666987342032373868530578⟩
def resval7Tail20 : Box := ⟨-54836697689669629525751636132342649246111767008038583811,16349175798356483923936764659869263554696199873828859287⟩
def resval7Tail24 : Box := ⟨-55701954327215363921688106078337129463037141438866390406,15483919160810749781762763860779620370279458831803985811⟩
def resval7Tail28 : Box := ⟨-56580863665969580701760899521196127241085005665795595575,14605009822056533010352849357338125106226962567505885841⟩
def resval7Tail32 : Box := ⟨-57473641129012785813354974706512214234425558849005845053,13712232359013327899423110013341235419876001401208904602⟩
def resval7Tail36 : Box := ⟨-58380505538540642167981157472297243869026372199706921531,12805367949485471544849721810433878539261754346996970641⟩
def resval7Tail40 : Box := ⟨-59301679169497887954078540752698769694194598922875786760,11884194318528225758625139771157147847921226654857388104⟩
def resval7Tail44 : Box := ⟨-60237387804058532954460820038826993364785822817614144063,10948485683967580757492964146320343431257780109826008215⟩
def resval7Tail48 : Box := ⟨-61187860786965686330420179004100881705290202654007966306,9998012701060427373643165925497549358831837759793320537⟩
def resval7Tail52 : Box := ⟨-62153331081744579670321795516158252039574662158163191751,9032542406281533827646158933588330305379303146018756376⟩
def resval7Tail56 : Box := ⟨-63134035327802549707535892949693120246955311150930673422,8051838160223547901128698206772860157614130236334357251⟩
def resval7Tail60 : Box := ⟨-64130213898425858302082445360353329803699309736096335629,7055659589595759833812546275024942128722235757764641576⟩
def resval7Tail64 : Box := ⟨-65142110953334045657407784258570152220829272679779606164,6043762527998004852979993308861312590781674207108014688⟩
def resval7Tail68 : Box := ⟨-66169861473485486735326642562164094994826216630506394035,5015894953361122997398458594295329144743771888086653814⟩
def resval7Tail72 : Box := ⟨798681785951650964946435862572892372907812783152852510969,858936631433166489612725070253226503491816301315899770⟩
def resval7Tail76 : Box := ⟨-687031218274506170617714104975004528434497830889942690,264679737711447397285590548093393682699942220553305520⟩
def resval7Tail80 : Box := ⟨-697845331308281986678211793894051898295907027029182154,253839468817973578176336256158317995389921756568170034⟩
def resval7Tail84 : Box := ⟨-708856483609488809176119479321106234155942194243412703,242828315153997905425766862176128253612262334849847036⟩
def resval7Tail88 : Box := ⟨-720041379916354254102126908707186749907994505699016295,231643418846389453523161094003874758908734508408348411⟩
def resval7Tail92 : Box := ⟨-731402760333641414133914439459032770517261838933985235,220282038429100321501456458134107209354731286177462068⟩
def resval7Tail96 : Box := ⟨-742943409566010729486549204139129941944014331800675545,208741389196730987504479773464033278151158855507216166⟩
def resval7Tail100 : Box := ⟨-754666156258121438637838896270384156404193619955089587,197018642504620277833621906073964534577213335434163635⟩
def resval7Tail104 : Box := ⟨-766573873687219596450737911661558823175186728838608788,185110925075522119983853472995757039543593609969809163⟩
def resval7Tail108 : Box := ⟨-778669480467384333422324164247637818609779890775884016,173015318295357383006794593241743621342768767002522077⟩
def resval7Tail112 : Box := ⟨-790955941264888125384939235853790177416728970382766069,160728857497853591043706538436327465240938001621407095⟩
def resval7Tail116 : Box := ⟨-803436267524844597323495421626717325031843981257515984,148248531237897119110951240156373146729424479553625346⟩
def resval7Tail120 : Box := ⟨-816113518209321949384042405467055925502566139406587367,135571280553419767114062350125467445702542861469468669⟩
def resval7Tail124 : Box := ⟨-828990800547102919597388733757017590105576537354654624,122693998215638798304786804824855688816031382265778191⟩
def resval7Tail128 : Box := ⟨-842071270795275137028560805527335768342769833660620277,109613527967466665329400646615733454353497590714643877⟩
def resval7Tail132 : Box := ⟨-855358135012856973100102791530015484377847481323259373,96326663749902333939908931267439783222155556015560370⟩
def resval7Tail136 : Box := ⟨-868854649864616092711520134958215202410109105938601287,82830148915139043559168006497532493634297280163781931⟩
def resval7Tail140 : Box := ⟨-882564278709972605572074138617526459621462735846779140,69120668123575905607812866969512442636226826028654398⟩
def resval7Tail144 : Box := ⟨-978500801987502317211541114507427461745064021503887228,52791321651943673391909946372348448229000760756818950⟩
def resval7Tail148 : Box := ⟨396101052354546407567515745314637685704260121437,126487908157074161996215759749519819369613041619⟩
def resval7Tail152 : Box := ⟨402290439334269242852033427010701753917738515804,120238379013757567111446673622876103104698266789⟩
def resval7Tail156 : Box := ⟨408638093932639488086643201483397950622319914214,113890723385575266862482852731069657303719890378⟩
def resval7Tail160 : Box := ⟨415085907860330135943073716264534207989727724442,107442909457568670172576609146197415959496684810⟩
def resval7Tail164 : Box := ⟨421635460478548394856614126310228856317466828787,100893356839349878770835366984445256088036461989⟩
def resval7Tail168 : Box := ⟨428288357100228856820176411694869768771580195586,94240460217669413412187791930696296293832969949⟩
def resval7Tail172 : Box := ⟨435046228368511701902884797073570881460818126604,87482588949386568263116647005780748307318209186⟩
def resval7Tail176 : Box := ⟨441910730656110337795522362561279050995695960779,80618086661787932367047937335690219227925101956⟩
def resval7Tail180 : Box := ⟨448883546471292373639240415341131522879539944365,73645270846605896522926069383742830573103433745⟩
def resval7Tail184 : Box := ⟨455966384870266990768695110531998445697626773533,66562432447631279393398509648414129096093249674⟩
def resval7Tail188 : Box := ⟨463160981876079289443828459497896005992207613539,59367835441818980718337568566147741295631187544⟩
def resval7Tail192 : Box := ⟨470469100904114280801042492719866725715875002884,52059716413783989361922431697490613415922584325⟩
def resval7Tail196 : Box := ⟨477892533194314816177216836335863226961317945291,44636284123583453998055731110365635106713144465⟩
def resval7Tail200 : Box := ⟨485433098250219392048625123373978372378214240169,37095719067678878586688147197751675025178803537⟩
def resval7Tail204 : Box := ⟨493092644284927495015956442223920742295246928388,29436173032970828195511047456044164151059974140⟩
def resval7Tail208 : Box := ⟨500873048674126852220329332668773564892917335182,21655768643795039149827456478980523115381294902⟩
def resval7Tail212 : Box := ⟨508776218484498816492036815774770871362937051875,13752598897873123496387970345072126902185847734⟩
def resval7Tail216 : Box := ⟨516807320735065734527474238529697949058237105858,5724579696945625858212633238399845471921353046⟩
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
def polyval7Tail5 : Box := ⟨20810452459574494735876689714695834162312143381982094927138,6347428840479805895666722516353362223208969648554121729588⟩
def polyval7Tail9 : Box := ⟨21138814158231909162510393574268280062390250008115740621760,6019065140080722027770728767726998942154305634830248206174⟩
def polyval7Tail13 : Box := ⟨21472359029103923038170118618278170144189305503228834852351,5685520269021418698208274624440659063428370644357620253375⟩
def polyval7Tail17 : Box := ⟨21811166834031051152634114217244336553963926802862099774432,5346712464094148542811980716424982017154713664756375953391⟩
def polyval7Tail21 : Box := ⟨22155320615547292104225432859199694850681619650466179589064,5002558682577907113529134777318338579113744849002713167390⟩
def polyval7Tail25 : Box := ⟨22504904726684740620538202072443968018060136021173754336193,4652974571440458591800600961174022817131068534968884415310⟩
def polyval7Tail29 : Box := ⟨22860004851464257624689995633358469297412337872889786521211,4297874446660941587474676503983282576224269298914728771102⟩
def polyval7Tail33 : Box := ⟨23220708025896720398618667660370069614361056536314238897415,3937171272228478813532205557888814269825748229259036088757⟩
def polyval7Tail37 : Box := ⟨23587102659315786226772264761400824747950130179057689247754,3570776638809412985376426008054378741039677191174959892773⟩
def polyval7Tail41 : Box := ⟨23959278556047261645119701145306537278935198309397886373019,3198600742077937567028927882977394025135374960442264040338⟩
def polyval7Tail45 : Box := ⟨24337326937420388082166545563724903343321846489781319543523,2820552360704811129985428227362321370978014126307450105189⟩
def polyval7Tail49 : Box := ⟨24721340464126438913899629988706490667141521811216403670266,2436538833998760298289553920479472657543657634895838663913⟩
def polyval7Tail53 : Box := ⟨25111413258930108086548327382064221645370905423612038817147,2046466039195091126497772709334206093935406680145805727402⟩
def polyval7Tail57 : Box := ⟨25507640929739256985157646602949609737072629554960763254013,1650238368385942281762850514495800849136556896707421388142⟩
def polyval7Tail61 : Box := ⟨25910120593038686210942153766166222668991289727009976395280,1247758705086524658050739957510441816374190686074760314044⟩
def polyval7Tail65 : Box := ⟨26318950897705862794688109200551898286610542525709416981707,838928400430898703277051977657934926035172057686005922963⟩
def polyval7Tail69 : Box := ⟨26734232153076094761679909947306426491105205732988377823007,423647244398593895894722647069187509299995743467926021119⟩
def polyval7Tail73 : Box := ⟨27218750000000000000000000000000000000000000000000000000000,2⟩
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
def pend : Box := ⟨1030927305010989354693145164824662252334990934157864598106888,4198055117409418809011745828332487294602683999308563697⟩
def zend : Box := ⟨1003766837595751142220449218750000000000000000000000000000000,2516452374905908769531250000000000000000000000000000002⟩
def betaquot : Box := ⟨428752365282517727682907752858079277373484254701740586215337,394775547025467683641254810677029713657402786183666509⟩
def crit : Box := ⟨128613715657821086514663050747510451392637624439085298587,10532351980149913430590424227040434864320666602479758476⟩
def subsonic : Box := ⟨489496434744713368418941399339014280109972892141262699124,5420729827399804883816294684112036690361641968886522293⟩
def pendTail4 : Box := ⟨27156271688973250189648609591140955985623397678298648438410,1572775702394541499736170144488524400017911490346958278⟩
def pendTail8 : Box := ⟨27156306655949752398412004471415617116564119642754032179677,1572640703874269396245058255115400748590967690185910899⟩
def pendTail12 : Box := ⟨27156306657436780195208510924395793847814378304520885227049,1572640687709939471458414195166785418582843465245756460⟩
def pendTail16 : Box := ⟨27156306657437500738531367703798908498184107975008826471335,1572640687696799249235998097107759850887127058823215956⟩
def pendTail20 : Box := ⟨27156306657437502446372508174458380522248877739745780234240,1572640687696751667427340982265718676697473603936358107⟩
def pendTail24 : Box := ⟨27156306657437502460732677975782811984241529798345679822190,1572640687696751062032963906247795387650475593431549923⟩
def pendTail28 : Box := ⟨27156306657437502461085211317700852530023622573645210798506,1572640687696751038767548268207824751086092052537577466⟩
def pendTail32 : Box := ⟨27156306657437502461106848537710138848418142844914863146553,1572640687696751036303754676389229730579126124866617120⟩
def pendTail36 : Box := ⟨27156306657437502461109485315363218367174436466480412659358,1572640687696751035621551871464464257421427812119131240⟩
def pendTail40 : Box := ⟨27156306657437502461109470464778079765111744921064931523302,1572640687696751035139493885668008174574824666871539163⟩
def pendTail44 : Box := ⟨27156306657437502461106712869438220709273113676114736538920,1572640687696751034271134362711726672967564019848535199⟩
def pendTail48 : Box := ⟨27156306657437502461083293647329645024278117749989847668605,1572640687696751030196617194869875061799469180529893095⟩
def pendTail52 : Box := ⟨27156306657437502460672075939638066702276960053647904931914,1572640687696750977943129382291053175607507613700363795⟩
def pendTail56 : Box := ⟨27156306657437502441486172908276842156937132309413562860875,1572640687696748989613502769728104186665396304686018020⟩
def pendTail60 : Box := ⟨27156306657437499551922408164964949999598454479897506069261,1572640687696523393826568770974011047424254443843008718⟩
def pendTail64 : Box := ⟨27156306657435654350338971492767624139933491664713226514568,1572640687588162821115820232159980214123920793955857572⟩
def pendTail68 : Box := ⟨27156306649137994017462762934448148173536285519468471602298,1572640321989938419124078880869094854615325728067850680⟩
def pendTail72 : Box := ⟨27155244645306517596846420227039238799321904429760625783769,1540455574649009612917201796949724802685826542625044666⟩
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
end SepticProfile.ExteriorCertificates.C19

end
end

end OAI
