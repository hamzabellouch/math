import OAI.MathematicalPhysics.Transonic.Certificates.BarrierData15

namespace OAI

section
noncomputable section
namespace SepticProfile.ExteriorCertificates.C15
open SepticProfile.ExteriorJet SepticProfile.FixedInterval
def cell0 : Box := ⟨250000000000000000000000000000000000000000000000000000000000,250000000000000000000000000000000000000000000000000000000002⟩
def resval0 : Box := ⟨112256535589345682257234737942972232986875670412831873150,333019548760950922820814390768774682743955212167542467⟩
def polyval0 : Box := ⟨3790190527836262845982821735179505634231394338321001137916,15170733681307709197990951951545397877438969326394624933⟩
theorem cell0_lo : Holds Q cell0 (0/1:ℝ) := by norm_num [Holds,Q,cell0]
theorem cell0_hi : Holds Q cell0 (1/2:ℝ) := by norm_num [Holds,Q,cell0]
def resval0Tail4 : Box := ⟨56726000017737614472311570035489033153650503891421,1722839288285564548849935518420628071265179710093⟩
def resval0Tail8 : Box := ⟨6750011512832705530509439377046679547200968787,369502970358840466174734965119745256040598725⟩
def resval0Tail12 : Box := ⟨6040315190038675820524332694783772797740346,500875121719606647262158608307720421587472⟩
def resval0Tail16 : Box := ⟨23796815367183799803780589286126221676281,26266666875236026166736511610244442402834⟩
def resval0Tail20 : Box := ⟨318924194469609596140318935779075561537,375586250728847993371906884456381492945005⟩
def resval0Tail24 : Box := ⟨12478833362711962593280208334515023190,6008553514860312387079648357758649982097334⟩
def resval0Tail28 : Box := ⟨1297224949398037941607051114639807022,96136812025751143653159041190408722693976337⟩
def resval0Tail32 : Box := ⟨336469867630890406605910281098026288,1538188986096478262653574302218822549548589920⟩
def resval0Tail36 : Box := ⟨-330107790165442953296927858689494841,24611023775074026590216768797836060240453931932⟩
def resval0Tail40 : Box := ⟨-139364419069064813687304129019633434421,393776380269374819675476256356497550040550693015⟩
def resval0Tail44 : Box := ⟨-35761220113625115260110218030919935559536,6300422050781192240257752467092343194450957815860⟩
def resval0Tail48 : Box := ⟨-9155183961776946603263813576817956584634731,100806744229496910984553313178929995607098799953670⟩
def resval0Tail52 : Box := ⟨-2343729921769023991752335080130441688771348794,1612905710424810925964054386392819391529519343712037⟩
def resval0Tail56 : Box := ⟨-599994917270685512256397419523542801360911502727,25805928871539605694674039663017716362454123866354854⟩
def resval0Tail60 : Box := ⟨-153598697232824403328510298270554846420539554489957,412750863160102936993193704073445234785910054761683122⟩
def resval0Tail64 : Box := ⟨-39321254108729644475499081435739733406333995519244753,6567150126221916293520806952850850865308175038857947054⟩
def resval0Tail68 : Box := ⟨-10065950119486124225581721636058663762557334671002893878,95637420510529253014521278078448801006507965547137540929⟩
def resval0Tail72 : Box := ⟨775656064887901936543270861364377523397573798442598681059,2470568082270629817220573793353913514546222963436200388⟩
def resval0Tail76 : Box := ⟨-26087492650321671636844535326807013790908847272979,588958408981757565934297562321913217096118794279⟩
def resval0Tail80 : Box := ⟨-1386826174997173143702537796110240362828585774,65135859542010390963506615785157073757305573⟩
def resval0Tail84 : Box := ⟨-771636028455443634944307039947305477520016,56917560413713347378002892035387598354580⟩
def resval0Tail88 : Box := ⟨-2100408072624959908875618980744255627974,381584253246396076831753271868178130014⟩
def resval0Tail92 : Box := ⟨-20582404583215865340731426645830793222,2529299227538917245354273711143522044278⟩
def resval0Tail96 : Box := ⟨-609536244039281572331228868534471891,40420041822970544809485028132627826502855⟩
def resval0Tail100 : Box := ⟨-49004213873427332093510553250573456,646718690554674477106019610602213842705453⟩
def resval0Tail104 : Box := ⟨-10028190212716643907035419334796143,10347498830617126147266303384604008859576304⟩
def resval0Tail108 : Box := ⟨-6855418058800526408197300599782427,165559981227119201229889254769967391698937354⟩
def resval0Tail112 : Box := ⟨-473243731037415442361962747066561280,2648959699200773215339862192211799284491883671⟩
def resval0Tail116 : Box := ⟨-119600010638419907731003677189523071964,42383355075106778441208347868551735603146770706⟩
def resval0Tail120 : Box := ⟨-30613057717663374690615287269302244092249,678133652502071093728717813229429766751216285765⟩
def resval0Tail124 : Box := ⟨-7836910155862051434193436248135259534711041,10850131092931593853109026413214679416482224314098⟩
def resval0Tail128 : Box := ⟨-2006248448792339094754284475806447861279767188,173600216629078966687114091511360592328991299281244⟩
def resval0Tail132 : Box := ⟨-513599596275909953365107666380976070606850031555,2777121966463310604181964262506723287301482199312974⟩
def resval0Tail136 : Box := ⟨-131481526676839416318140493048368470099642173977373,44310687551924707929604524733648615861099084786429839⟩
def resval0Tail140 : Box := ⟨-33659644889323557722282472858573698157474204708198879,677415264021882729207844178788808001006009111523129891⟩
def resval0Tail144 : Box := ⟨-8863269137410019849963263613456576607892651138880257547,2637212717901224622594840322865365579758573458523298168⟩
def resval0Tail148 : Box := ⟨57681944268383573218752984719465373015967851,1082931219147643384321978956080649539301075⟩
def resval0Tail152 : Box := ⟨1011346222963655128998781168696704748052,42400539872747438483389460084171519388⟩
def resval0Tail156 : Box := ⟨316058013059568507880029863340562454,21253820124917407924785588217968663⟩
def resval0Tail160 : Box := ⟨544571417406098219687304201429429,54765546864815178134567123157536⟩
def resval0Tail164 : Box := ⟨3576565707978125427905311245314,27636683381322386542208394007995⟩
def resval0Tail168 : Box := ⟨73273619179201140395463645960,434445507703206201339126688281705⟩
def resval0Tail172 : Box := ⟨4143976104412541665885496778,6950911896415326851617520067691983⟩
def resval0Tail176 : Box := ⟨599952119755105892628098157,111214573719810387479388492725030827⟩
def resval0Tail180 : Box := ⟨219161574237036183758238315,1779433176209065228374279351037983577⟩
def resval0Tail184 : Box := ⟨1808352298415452890280435353,28470930816720134322556007641163740718⟩
def resval0Tail188 : Box := ⟨416873283248924059348707096444,455534892677159803989097274435365730741⟩
def resval0Tail192 : Box := ⟨106626146834855315158196693430843,7288558182874103603215039988390055751288⟩
def resval0Tail196 : Box := ⟨27295836226347171818052070545386141,116616905336155045394147637416250349757967⟩
def resval0Tail200 : Box := ⟨6987728671597369008481134534670085840,1865863934383357024548084934712730764436321⟩
def resval0Tail204 : Box := ⟨1788858415113672466135231987395492201006,29852145895425372638162330889673438188885673⟩
def resval0Tail208 : Box := ⟨457947778094462714460396081991940317538601,477205008310703729028983784388332666194602284⟩
def resval0Tail212 : Box := ⟨117234771542584517421780768930205153639390553,7525372608441609372260261725375662307188042855⟩
def resval0Tail216 : Box := ⟨30020301220080325993852471540335793344702094078,92265626642846338563577475803757073672668890206⟩
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
def polyval0Tail5 : Box := ⟨2054562677305090523946193856558538534207512781135875,51825729032355973103533697587169555533594449467531⟩
def polyval0Tail9 : Box := ⟨195956764795225143154373929659829736072312695003,9756509873642051386891723445522019575342026579⟩
def polyval0Tail13 : Box := ⟨151724735189892978107090793128739197120657103,11711694048164920371235542649713109513475506⟩
def polyval0Tail17 : Box := ⟨523791927494991069081320993640206175652578,430850178692609733170309778880032052918157⟩
def polyval0Tail21 : Box := ⟨6168263774169459035062979848520066945091,5967844949618866895874623787129215828351671⟩
def polyval0Tail25 : Box := ⟨211835716657991664448663465274048239004,95470410154537042362858044203556836579370910⟩
def polyval0Tail29 : Box := ⟨19259481406467883493699765426618523710,1527525852834234027564098795895630129387664779⟩
def polyval0Tail33 : Box := ⟨4393747200512826224304586800379366027,24440413556919181877083962992501662827443521243⟩
def polyval0Tail37 : Box := ⟨8071265837801947651517929717284717176,391046616880980316453556863106671147311795560745⟩
def polyval0Tail41 : Box := ⟨1454680526470677613657378926968810360816,6256745868737216380966010461760197236474942179127⟩
def polyval0Tail45 : Box := ⟨371598367890956167989578795945009403848011,100107933551432577206687109418720846593163802889837⟩
def polyval0Tail49 : Box := ⟨95126672070534875907807533844112483509340955,1601726847641727163548516574375630798032382886753072⟩
def polyval0Tail53 : Box := ⟨24352408951819041841320292549078391559668296977,25627606731885315125486459708093051585298031542358299⟩
def polyval0Tail57 : Box := ⟨6234216354588177633897415645918035067181019467473,410035863132394096147160039266070498528271131696861159⟩
def polyval0Tail61 : Box := ⟨1595959383477358700553410480400248935267353017842347,6559077598209598186675042831997825150258861590647017382⟩
def polyval0Tail65 : Box := ⟨408565623285107466891001017547860929949971766947452273,104562211313344458852046247964969162803919120862425329284⟩
def polyval0Tail69 : Box := ⟨104593058621906053476952809867414030104175817573588849204,1574939514031994831821342750320756273444763615196366477494⟩
def polyval0Tail73 : Box := ⟨26968750000000000000000000000000000000000000000000000000000,2⟩
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
def resval1 : Box := ⟨112034463116572679588365738180310090233825913914035780038,257570706399442306218823904893046966845482555440629339⟩
def polyval1 : Box := ⟨3772158516823765016824788357260305737684394005822445456516,9030637733022217053258173377299495807349483120048047775⟩
theorem cell1_lo : Holds Q cell1 (1/2:ℝ) := by norm_num [Holds,Q,cell1]
theorem cell1_hi : Holds Q cell1 (3/4:ℝ) := by norm_num [Holds,Q,cell1]
def resval1Tail4 : Box := ⟨55086688851990208242674214356813296864626987307123,3072039828287513640490167992391705058085379754546⟩
def resval1Tail8 : Box := ⟨6361852422723711407657662976728253145984805280,6166303672613882870389026872151141103397375460962⟩
def resval1Tail12 : Box := ⟨-319265804142836224339011196634803188797622768,19487724966027554245214157930566895225890932103050⟩
def resval1Tail16 : Box := ⟨-2129051704472991770927162875717415203072633943,61589731321814777178870676224554195013713415521411⟩
def resval1Tail20 : Box := ⟨-13953094069726521184477518368444190929999249461,194646741483321471599169946960896972206650570487013⟩
def resval1Tail24 : Box := ⟨-91442999124614871352106337949542860530097708185,615132480604299576670414959313663285433464034463524⟩
def resval1Tail28 : Box := ⟨-599280839131889422118721460777833644720191710342,1943812132030978642117570464535719844965155608804009⟩
def resval1Tail32 : Box := ⟨-3927446907341514553875804567589967409366042942237,6141372820929059873089943286945011080878575338781640⟩
def resval1Tail36 : Box := ⟨-25738916051954956767441231017476736296999116149337,19396444646492721576183195016383348429144008958542118⟩
def resval1Tail40 : Box := ⟨-168682560238092845506232536906104178216586370365196,61215008699162366481666030238212330466485980273424714⟩
def resval1Tail44 : Box := ⟨-1105478026776365989562133093665375934485582090051541,192897299286884344628501177414704242534606067848560315⟩
def resval1Tail48 : Box := ⟨-7244860796281589745124992489149227822936349329724524,605899719355534970672227341185653939920840579797317700⟩
def resval1Tail52 : Box := ⟨-47479919714510871889200597751121439094160776035891331,1890359741012217817264050976652778236007126063490784039⟩
def resval1Tail56 : Box := ⟨-311164401841003575843152839452116631376523508542820020,5813365883912592510597002115140294975166339679401824322⟩
def resval1Tail60 : Box := ⟨-2039247023900583466575071244536821338843289262575176201,17317293138476708743505144042171651397295000062941296939⟩
def resval1Tail64 : Box := ⟨-13364409288556142312796020388209759697517438427382970661,47811816403144587276278734458661529929866138377056499517⟩
def resval1Tail68 : Box := ⟨-87584859453458354411144713938828361656243538143099532224,105762106028148941347784746610520966174060998951085987978⟩
def resval1Tail72 : Box := ⟨778448688334640513366702262896008435030304067140760734131,1540033777194899055301068342529225733135281575023670990⟩
def resval1Tail76 : Box := ⟨-25507941949381295865386410433007835807000796059169,399266539579428736580946385406739034744995603740⟩
def resval1Tail80 : Box := ⟨-1325748795311472313707586011093332842810210823,62196251910047012498775447554469924397019300289⟩
def resval1Tail84 : Box := ⟨-3444024285077396126413997673259805887876123,196439771184658767552243191843156623833466642201⟩
def resval1Tail88 : Box := ⟨-17849471900778790692893357459820403368409711,620837446804873620433665691928878402523972753934⟩
def resval1Tail92 : Box := ⟨-116965775105852509765293073519752057430951791,1962092359639576932270537276969257742961631244383⟩
def resval1Tail96 : Box := ⟨-766546784606752812321332494667289493073723876,6200783913727898896884915230061798515183547677348⟩
def resval1Tail100 : Box := ⟨-5023641004197741522661958037531802908171638517,19594938308268256824512608286013435462790807464169⟩
def resval1Tail104 : Box := ⟨-32922933684850273077678784220456200744870304939,61912635819571177667468926488289862928252585257093⟩
def resval1Tail108 : Box := ⟨-215763738196985679692682257989226760445600704027,195562792321476363401466804409921382183078484239235⟩
def resval1Tail112 : Box := ⟨-1414029234647744303834280986674356015525933723818,617342888682344559483729853500099352744888318903930⟩
def resval1Tail116 : Box := ⟨-9266981992187440162512654282962205399803841466420,1946310437597319094846117831302016071193962357182086⟩
def resval1Tail120 : Box := ⟨-60732093183999616194392061659047339068398747527239,6119858269963082793171354139515251133195169501346103⟩
def resval1Tail124 : Box := ⟨-398013845890661079649288711981831857933045876588773,19135703845043328832448798252708661065132902012692384⟩
def resval1Tail128 : Box := ⟨-2608423540429128454677468134537472367554918873466436,59127770643263555445370973892649000799989388724362424⟩
def resval1Tail132 : Box := ⟨-17094564514576674436328753530496078893498590637565091,178022296115381808198989635569966583860035852695884811⟩
def resval1Tail136 : Box := ⟨-112030938022926305159112939714333315905340965389701080,504634695589156841396729597319555249867472147350096235⟩
def resval1Tail140 : Box := ⟨-734206133717190507469043624982288040845074314886591431,1214761938017368979756648906364553433810866758693922217⟩
def resval1Tail144 : Box := ⟨-4914365616965896995515805492386930075552181981951348346,1328577130918091322401327383975702489919104056342891030⟩
def resval1Tail148 : Box := ⟨56830126358517151922547478983743191317615245,783706930910558528432531073372604839064738⟩
def resval1Tail152 : Box := ⟨972827630738368191077879080806504478781,2819648990004350136820421139437608778955⟩
def resval1Tail156 : Box := ⟨405464142650621585299114400922886668,8823286766690999173259352492051905709006⟩
def resval1Tail160 : Box := ⟨709066141018527469726155519725968968,27885575392008644239930912880211708618476⟩
def resval1Tail164 : Box := ⟨4643660284269989166090952114742263088,88129784651012880985748912563310257758201⟩
def resval1Tail168 : Box := ⟨30432671115432823314083648124932429519,278517883956951378271061015997328165413934⟩
def resval1Tail172 : Box := ⟨199443553007427404866270672083339326293,880150791715743972325549519900343007627066⟩
def resval1Tail176 : Box := ⟨1307073268967019625074750723400169274966,2781034411037199391205432926071716143023904⟩
def resval1Tail180 : Box := ⟨8566035375499212819511533094295374396652,8785007050826704277957696374485068177674789⟩
def resval1Tail184 : Box := ⟨56138369436870678461993499607886150251481,27735895088189846079066217079278800738471029⟩
def resval1Tail188 : Box := ⟨367908417941475047030437944553882994658063,87468641769125678892924145871039808714282107⟩
def resval1Tail192 : Box := ⟨2411124607821250399748334138065967354893721,275195750057477409026441993663697569689401640⟩
def resval1Tail196 : Box := ⟨15801546229817354251348964476328539957084919,861573267527175947463018914676749859470518185⟩
def resval1Tail200 : Box := ⟨103557013371731467191658340420356809771285818,2669380669613334153332730126881748212609514829⟩
def resval1Tail204 : Box := ⟨678671242833037581501567032703564147183744671,8085181187342030533117039297136862015831152840⟩
def resval1Tail208 : Box := ⟨4447739857057570441041664122113233755688917604,23250361650677623424295601015472011825473872989⟩
def resval1Tail212 : Box := ⟨29148708001872952300061791732159863678966555316,58390970896986452729779419137848130226047199262⟩
def resval1Tail216 : Box := ⟨191032592150860203162621176375829676378610711443,85638919723692135883273756830818685797556629184⟩
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
def polyval1Tail5 : Box := ⟨1999396190287076056263430888114078745411553099426592,117455139239764593057625679541424262656908534589924⟩
def polyval1Tail9 : Box := ⟨188790342443050596644544990733325491081356755372,271481284472832554180144147327092557885250541214186⟩
def polyval1Tail13 : Box := ⟨15359583376493566566324979679100073044515062933,857991220746323652247291350617809006921833703575295⟩
def polyval1Tail17 : Box := ⟨99736282660577478992407181514141937195697574930,2711624320622801175526914657563377403020808883246123⟩
def polyval1Tail21 : Box := ⟨653628593007555507978142379663638814164958677305,8569733512726488866400038352869983392137270018662249⟩
def polyval1Tail25 : Box := ⟨4283620311607583978055422391961133620907919601400,27082372036187271097821866526220691608754113501060398⟩
def polyval1Tail29 : Box := ⟨28073134072976152717017904639854345067476912746322,85579134866713039331322639385656709773775349057927216⟩
def polyval1Tail33 : Box := ⟨183980091460555068233525673694957227499800035407867,270377072355468038005807706290652689761484443854087927⟩
def polyval1Tail37 : Box := ⟨1205731927395872531817184268795736592134449331178995,853900804201168559857179937074506753413716960253913218⟩
def polyval1Tail41 : Box := ⟨7901884759381580393947647969349062555146845191059542,2694657044239538102863086434007758532270632349831117131⟩
def polyval1Tail45 : Box := ⟨51785791959083117052941777045891974055897575608883837,8489635020679477854844151345258554211959770618833996421⟩
def polyval1Tail49 : Box := ⟨339383366183047123801547174522178663907814836862707814,26655724387341293743337406117329249736980380537820677514⟩
def polyval1Tail53 : Box := ⟨2224182828617218390936897509855197287056438196417275855,83093688589928847244271035657164910530254808993776564223⟩
def polyval1Tail57 : Box := ⟨14576404585625862602295136077205805734285312993364593719,255070201379161751176393986657334650723611016228871260972⟩
def polyval1Tail61 : Box := ⟨95527925092371438931604780439331840488423668636382190923,756688508574128800109187071359713912810672524954424752339⟩
def polyval1Tail65 : Box := ⟨626051809899434754611849687755061457643857658576102262782,2067372968119557315137930576143620922432674381663162050380⟩
def polyval1Tail69 : Box := ⟨4102893264963138415984190361198692495960225441440556740020,4409659219553322722449548713185701803363410987764489521432⟩
def polyval1Tail73 : Box := ⟨26968750000000000000000000000000000000000000000000000000000,2⟩
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
def resval2 : Box := ⟨111925126048694028731270444513034971651803794473150130870,240013469102679497228306186062676018982789114644097817⟩
def polyval2 : Box := ⟨3763248362322058204786180628360740007798761117311130594130,7756744771731654951799150698397879696639257103965011354⟩
theorem cell2_lo : Holds Q cell2 (3/4:ℝ) := by norm_num [Holds,Q,cell2]
theorem cell2_hi : Holds Q cell2 (7/8:ℝ) := by norm_num [Holds,Q,cell2]
def resval2Tail4 : Box := ⟨-138950771714448017641554069891887909625620472514491,34045316244880099377119417073575246088417167980275541⟩
def resval2Tail8 : Box := ⟨-443444870622393797751266334841205853153612301253902,57964720215798609883308747047129492451275230027414704⟩
def resval2Tail12 : Box := ⟨-1017541852877371330060477266802644945601729988116727,98624219566827956936375646612540066491710150704255750⟩
def resval2Tail16 : Box := ⟨-2334849032745042143283736001747771251671908746024848,167649596946610753809601742164119138913263894859446782⟩
def resval2Tail20 : Box := ⟨-5357538819065118505813330464814359973080021969397761,284628421502267971408006485957875408633870484811301952⟩
def resval2Tail24 : Box := ⟨-12293395330915188205675669955344175101808152974268613,482409850598356500748255620719967438790375344145027230⟩
def resval2Tail28 : Box := ⟨-28208394538246503898849290776449290808936786360514132,815733502723851318931780912595153876461387862569222617⟩
def resval2Tail32 : Box := ⟨-64726912379066662136837480171523412341284794788504741,1375000705774016505404012820003516818417264240159625131⟩
def resval2Tail36 : Box := ⟨-148522213146406385689332249796321797884148098074006797,2307589541936904174376608238027489009693552479203489523⟩
def resval2Tail40 : Box := ⟨-340798703153352084873929098853271759367841880990314102,3849219517930046521522408876088839315685220449609178591⟩
def resval2Tail44 : Box := ⟨-781995861834602507838089885264209846118730552550917542,6365990241271436930087474320313098472311781556142227781⟩
def resval2Tail48 : Box := ⟨-1794365771548352991933983713575048582200033458702705741,10399782949119009574393412956852688984579881818105025543⟩
def resval2Tail52 : Box := ⟨-4117347263898072795406267418497582857813039027447899124,16685332102971363539827702848470508677060146946985943297⟩
def resval2Tail56 : Box := ⟨-9447654854060562479716651910172693841613213977215730117,26040797743480952611753977853443276789681587300783808015⟩
def resval2Tail60 : Box := ⟨-21678565474444305483156437199169553184634179672346802322,38863167903115309072494741226625505270684312664174446427⟩
def resval2Tail64 : Box := ⟨-49743582744519077260049847471295457225147555564824937144,53537941578879850869972912529191135083115571125204467054⟩
def resval2Tail68 : Box := ⟨-114141397301814017666750388294409789074399987431335425969,62052221184471193113314053036662993162204495638852512870⟩
def resval2Tail72 : Box := ⟨779843352647436397573680743491851404612791416980453820353,1075188773276549113837410582257160186002923565083041469⟩
def resval2Tail76 : Box := ⟨-27336055265187801090348568030995508716724697758825,400373032836935961895366806936396469171453375426622⟩
def resval2Tail80 : Box := ⟨-4833684337622530179290392973751701318438867296228,681641156100793359502450197463851985490803810961407⟩
def resval2Tail84 : Box := ⟨-11088385201514516125351949693646542770338604599426,1160005159432873161274282409456540655184407066351376⟩
def resval2Tail88 : Box := ⟨-25443379674545313733081243081552249017567971055197,1972390504514206165960400947459634233745732621606308⟩
def resval2Tail92 : Box := ⟨-58382316103475663073316387440113623472284053114606,3349834089406533373322948893169934129736697236427619⟩
def resval2Tail96 : Box := ⟨-133963918215617872421517396460587294627318554204740,5680302802721044134240939919195485190799912271091961⟩
def resval2Tail100 : Box := ⟨-307393275591845585147486437734280488903972414241186,9611489060500018459103957028640915820095300113061104⟩
def resval2Tail104 : Box := ⟨-705343850326920976175286080734745289546913205494985,16215831513534917831428062863346300955681619330256345⟩
def resval2Tail108 : Box := ⟨-1618480255419106218679094546180027376710833992406561,27248297874684222282152673031614998302316717436043085⟩
def resval2Tail112 : Box := ⟨-3713760793359705368599210168933177561566168064036652,45531688278236810054793543078064892362457185890407294⟩
def resval2Tail116 : Box := ⟨-8521586336389539970461204997315366468911892353042704,75488975678295727492246738372289963123416787146959375⟩
def resval2Tail120 : Box := ⟨-19553610942951048389909258544014998639822625260105813,123764698932996829841364552365046852510151582205898564⟩
def resval2Tail124 : Box := ⟨-44867667335080702560090361011933446710145852355314394,199627042057623384033056902298340024412551056953807064⟩
def resval2Tail128 : Box := ⟨-102953238558588680262717333107473010719805064728487717,314143941646540893196000647351583070938932623871323357⟩
def resval2Tail132 : Box := ⟨-236236246706213164140447100171672878385855667414884400,475313128604176599312654286545010092194661424721990860⟩
def resval2Tail136 : Box := ⟨-542067107755493714630478024537674759249056877245418668,671804712863268843520915794225431483049946155176756761⟩
def resval2Tail140 : Box := ⟨-1243825986313301329670358902304269270811720662867281942,826985874048221215220773988512190986505921717718349370⟩
def resval2Tail144 : Box := ⟨-2933580180438803659521189100201119709810211641575129710,670746377381246844880127872974436643808353610016152513⟩
def resval2Tail148 : Box := ⟨56656591894787679692310655023800355047789704,43329556239385590619456923316634727795927350⟩
def resval2Tail152 : Box := ⟨549428154469362503355555245022472359293470,72760018260193443561436699533487866672401536⟩
def resval2Tail156 : Box := ⟨1258525991793061758598484685860770214800340,123802511574560238964713045308497769784590491⟩
def resval2Tail160 : Box := ⟨2887809967482879819035190456007296216691796,210460798393751356911466485471691268988618503⟩
def resval2Tail164 : Box := ⟨6626361611901838613517483847647223765943254,357336945279234256596840814625103054810160097⟩
def resval2Tail168 : Box := ⟨15204832974944893002730029451913310178848533,605700500230419866334771482512114080245940711⟩
def resval2Tail172 : Box := ⟨34888972159447661873292114853452401667803703,1024348114391645135448867870594515017414621870⟩
def resval2Tail176 : Box := ⟨80056149274940014995695453553866798603432815,1726955556894687675437492095291017284982296683⟩
def resval2Tail180 : Box := ⟨183696642235302293253582021798851366080429809,2898985552046578180857159618599743929590305614⟩
def resval2Tail184 : Box := ⟨421509861192982426533255443274873118974265960,4837409867161279306709306088982049858001778459⟩
def resval2Tail188 : Box := ⟨967195485562245590281528497271083412133740021,8004289398793879382338049730567446666881179078⟩
def resval2Tail192 : Box := ⟨2219324370358437275354204530123340685326403302,13085632766802199079888142725030286536503664845⟩
def resval2Tail196 : Box := ⟨5092456214271578221987013605746314902378435395,21017124974320661066999689459508135953896844432⟩
def resval2Tail200 : Box := ⟨11685137441213618672478697911734109576351546838,32856655373644279286092351966036274052765993431⟩
def resval2Tail204 : Box := ⟨26812687488091353377699516924005175711782488868,49173644610891591793619790286510501682488914330⟩
def resval2Tail208 : Box := ⟨61524326431854154716902532578811910440607371760,68105001463805975643552955160717148779570424060⟩
def resval2Tail212 : Box := ⟨141173567407989325818110303096918758337955086651,79968343123473146513612315107124631524244399910⟩
def resval2Tail216 : Box := ⟨323939347264562541465047754655159421957606470208,53321495238545539101970522261572364212000287025⟩
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
def polyval2Tail5 : Box := ⟨21827285696994462452389633755187986684216825176757144,3045702997411388453055301290784666340182335278088435189⟩
def polyval2Tail9 : Box := ⟨45557500190206485349294840644134115573953327258006670,5184142893321548832179562857421433267206023607939226647⟩
def polyval2Tail13 : Box := ⟨104535709630928301455681751078741725430270104927347423,8817101967345015379033090345491174035607296474713029367⟩
def polyval2Tail17 : Box := ⟨239867380604610100719119856025116226249723318375863738,14980052621199110909109490080013152041072582496160793818⟩
def polyval2Tail21 : Box := ⟨550399098605584515533301756676139541131686267077113432,25414112491309518994031795644844795452041210370308006986⟩
def polyval2Tail25 : Box := ⟨1262944411127595466183698941944397239069681948504815320,43031366072959136205198276410779929501187767046030842062⟩
def polyval2Tail29 : Box := ⟨2897949123898255865129082902915578879804581055874297031,72666189044706180718082321618775302110325714419815415045⟩
def polyval2Tail33 : Box := ⟨6649626896249994590520425459050392010921245774796883038,122259456793297598990344014934748409047763915126059287183⟩
def polyval2Tail37 : Box := ⟨15258217438907588856212953942984012338002101995544638138,204654988222228164286851695490713826968948355267268020033⟩
def polyval2Tail41 : Box := ⟨35011468018495421842049279470345983422073832611424637347,340150752051480440244835565960202821545688573947189025412⟩
def polyval2Tail45 : Box := ⟨80337227970313223132360060991968129212781808234631446231,559672956705497327101170565823048070546940022804689644668⟩
def polyval2Tail49 : Box := ⟨184341604714906599633858773625580803936454429538533993221,907487514998596113327818344802984592648573089191493941419⟩
def polyval2Tail53 : Box := ⟨422989790504398268184978683673490260010538693773314182909,1439622485358370209102019111105885253702254611154666482664⟩
def polyval2Tail57 : Box := ⟨970591327701979848351984440411603170040736767434773336776,2206942983807349511119872513946044044945072008027979126358⟩
def polyval2Tail61 : Box := ⟨2227116461338093225954684811222598773720033572661433630931,3193616791449177443080449964855676233510288140852580609802⟩
def polyval2Tail65 : Box := ⟨5110335926983578615068593099592875046230060509041161110202,4137195686277811664529989189060852733831539174911100627429⟩
def polyval2Tail69 : Box := ⟨11726164283431834587763284027271913757278891938562487162539,4049716473015820293296362280817597829292717202152922910738⟩
def polyval2Tail73 : Box := ⟨26968750000000000000000000000000000000000000000000000000000,2⟩
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
def resval3 : Box := ⟨111742471947573021992099176173069164952750618030960246341,1760198333666737482298505953305130785793904467570381820⟩
def polyval3 : Box := ⟨3781285362659136246870553868591945526133774648280599437021,238608163559694521047635553343344527084016345691753588428⟩
theorem cell3_lo : Holds Q cell3 (7/8:ℝ) := by norm_num [Holds,Q,cell3]
theorem cell3_hi : Holds Q cell3 (15/16:ℝ) := by norm_num [Holds,Q,cell3]
def resval3Tail4 : Box := ⟨-190519536528550398890799941757066813570850141448486558,1995179898639389783885007524850621431601522126030703200⟩
def resval3Tail8 : Box := ⟨-282533755351735784252350429112334851407501919784211974,2547006775429027450847092562712532611993284261841386364⟩
def resval3Tail12 : Box := ⟨-418869051379963946168744137789949365620856235236843383,3244079464599749603295996191248831977123525759309194605⟩
def resval3Tail16 : Box := ⟨-620992271000297240679435434649177779471855886568094057,4120834769860607579199724248007385351775073931800478250⟩
def resval3Tail20 : Box := ⟨-920649065302798435722050666560126074866086162287329433,5217827516422860927560258127398850179781099946352365734⟩
def resval3Tail24 : Box := ⟨-1364903785481226607340382698112922666066327764149956310,6581589078913298378471726730885535875011527042172002124⟩
def resval3Tail28 : Box := ⟨-2023531456047543593616696396249447806363567590262321455,8263507681946719912519100471792840287862276396290030776⟩
def resval3Tail32 : Box := ⟨-2999976699581225951285816756704209582395828557799114563,10316989166050222012777805414732795397089568390142025532⟩
def resval3Tail36 : Box := ⟨-4447600837206263964735672742363815800259192764393091355,12791721137510231319772199705154159611091136624995894653⟩
def resval3Tail40 : Box := ⟨-6593768948231884418060007056433722766524644333678189944,15723193124558638741675111016165903125472326480728799844⟩
def resval3Tail44 : Box := ⟨-9775560023047694530534917707124412406816573677755722854,19114601486135509929040411425558290246219082629201683115⟩
def resval3Tail48 : Box := ⟨-14492708876284333010706202532731141781086791305588196516,22906710870201207475817908502986692879595122072891862061⟩
def resval3Tail52 : Box := ⟨-21486094922186119324975565008524246012113175501011727044,26928885275456870751254203071422529941145797375938752181⟩
def resval3Tail56 : Box := ⟨-31854105326067324912829039236992967220717230294528496563,30820939458776730936412838544932033465280505771930036890⟩
def resval3Tail60 : Box := ⟨-47225148627467565666556947467248611556598885433995253840,33910095521062858032424712279362205952237899223342821345⟩
def resval3Tail64 : Box := ⟨-70013413966206430353121302554651011848868987051229769047,35019264754591396876043919788846981872846208050656396219⟩
def resval3Tail68 : Box := ⟨-103797951133058412885150067137660632021019032513665233954,32170775369043770023572385353341574149675109221385630965⟩
def resval3Tail72 : Box := ⟨780538721736795258739024519317960678470784852426197016036,862010073201638150622185244551521288399072028353083121⟩
def resval3Tail76 : Box := ⟨-2341127237360428513488564225093398606147298770598132,25197314438369687168284408268057342491633320899443686⟩
def resval3Tail80 : Box := ⟨-3433625156469108096533364349012304730384210677143356,32183292438095716763093194984123371425354270728236764⟩
def resval3Tail84 : Box := ⟨-5090502342347934151580552455717474095022457237096218,41016958922544162162307248965679444466665966884254082⟩
def resval3Tail88 : Box := ⟨-7546899440831487489470624702698145465514349228394146,52140973772210982310585364282736782380402911268868373⟩
def resval3Tail92 : Box := ⟨-11188618990284550708688925600842968922563843768763674,66079617234699775311154912867620630080888277442439733⟩
def resval3Tail96 : Box := ⟨-16587632562385523885356276155791600584444001072844009,83439056410267743630812603354514807189031017257075834⟩
def resval3Tail100 : Box := ⟨-24591913824542102247923236505593591736375836629338604,104896463232481196690261122854562096284041337961436200⟩
def resval3Tail104 : Box := ⟨-36458622005232799090468217194338179420061711169408149,131169037823094685689029945448518896794061972180565743⟩
def resval3Tail108 : Box := ⟨-54051552392555416495065263891396409244104852384720231,162948868634788189275708927734087092234300466019238107⟩
def resval3Tail112 : Box := ⟨-80133865608684792050020917099847999364461155656040509,200781484365596502719565314858396668631744054202276866⟩
def resval3Tail116 : Box := ⟨-118802071969262944306726527798914439635707317442594300,244853599653739503775990878375435551050637337319070953⟩
def resval3Tail120 : Box := ⟨-176129432880625750064781266620958515331599280365835899,294636751721548836403750816962154876705088337560225928⟩
def resval3Tail124 : Box := ⟨-261119832445993922401015905222934273357033363218689053,348305010498956472756825574825245718298393182861045175⟩
def resval3Tail128 : Box := ⟨-387121935167056061559996983035646848833973391159977378,401801847692011049573069133958589780724693772381524962⟩
def resval3Tail132 : Box := ⟨-573925738553336047689731862200188738121388133030219665,447366291737084234538941291515867126445218963550990929⟩
def resval3Tail136 : Box := ⟨-850870806991609550465676831216382956459286163639022004,471230812717941198589709754707110590212046878096421139⟩
def resval3Tail140 : Box := ⟨-1261454496043521879477781135363965648801885247761073938,450056766761390489555540056682463232700798287967108032⟩
def resval3Tail144 : Box := ⟨-1941602746631917332384452178747611043807556272589613700,340951853147184016930659168718380647091300069766931513⟩
def resval3Tail148 : Box := ⟨555941611690845063056432713775327831670018901,4882738561440740729529333053523977738154317264⟩
def resval3Tail152 : Box := ⟨740868989862013036319984344020277542923089978,6226398795128457567887033773838132485326051487⟩
def resval3Tail156 : Box := ⟨1098370308481920215836829445892597508192000861,7921023249443200554543559929192958653788097231⟩
def resval3Tail160 : Box := ⟨1628383548106664840010321645651901512958211247,10047566598919729783784633530428302107768188091⟩
def resval3Tail164 : Box := ⟨2414152094201599628692518641056873997960918392,12700812228474750761965220244841001561610150773⟩
def resval3Tail168 : Box := ⟨3579089423198889066357127937056676736996439329,15987810366448856122054373086506728573600413298⟩
def resval3Tail172 : Box := ⟨5306161583614148044155849023955753128549502353,20023939050743474174126710254206712401602859135⟩
def resval3Tail176 : Box := ⟨7866623999089172332583732256423784296128498544,24924160695691294422895622261739239682100228876⟩
def resval3Tail180 : Box := ⟨11662625076128056553846293961545794346819251850,30786300667222712221706164061995730492524983600⟩
def resval3Tail184 : Box := ⟨17290367975141496843455814278934149391929543951,37661390988142176884324440747244237986426021058⟩
def resval3Tail188 : Box := ⟨25633750786323922449719604231730083249021729675,45503404283656499109282695478234567310609377993⟩
def resval3Tail192 : Box := ⟨38003192316095573480910702685042856118137296865,54086577455089353083404257609356279455667305380⟩
def resval3Tail196 : Box := ⟨56341447580300095812440121133386444534225352791,62872283811786330810531533335833619093042187089⟩
def resval3Tail200 : Box := ⟨83528738560714558374597498074687104191173788803,70797999227172376402381619791301773932936253645⟩
def resval3Tail204 : Box := ⟨123835124321224324714690388846402062330352292133,75946744077135383013398233681243066253311734039⟩
def resval3Tail208 : Box := ⟨183591160119197944309947974131513846179696158545,75034114495237964200358658599597830509611961648⟩
def resval3Tail212 : Box := ⟨272182179856963380986610916898835790200359419040,62618136184951170042875402499025228352101360162⟩
def resval3Tail216 : Box := ⟨403524914316634230821378074467084967554810336912,29889255909032447203785911209837222234724150057⟩
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
def polyval3Tail5 : Box := ⟨33331504544612020156307384386264947363108144309264531576,300917149517683161910039332519404419149207140556966154301⟩
def polyval3Tail9 : Box := ⟨49412553602012460315713680102142463819468692689622930725,383282574329705996632306816156891291349281434336174049636⟩
def polyval3Tail13 : Box := ⟨73256340290702467409334140803259903558612247298952174722,486884062518841755672364832753301125640701145926878456661⟩
def polyval3Tail17 : Box := ⟨108605830322775956916128957433237083682221393330276039909,616517358586209417800345290474063117552920504764784071848⟩
def polyval3Tail21 : Box := ⟨161013044513474360483290460228311172726413850267467042136,777686675157424126886457866117841395154032041964055396167⟩
def polyval3Tail25 : Box := ⟨238709104533786268649897384106923978633876902780892844315,976473608125018727610026249897667535380740666424454875571⟩
def polyval3Tail29 : Box := ⟨353897019707329152449270529376731434085029545488085349614,1219203508822200610004171327305039340317680882119990304016⟩
def polyval3Tail33 : Box := ⟨524668302042091295179552789378464115038438871211988238097,1511770537221341050722361650689665652082080507835550898346⟩
def polyval3Tail37 : Box := ⟨777844434506353092946234963506374273798504886343736479714,1858403580702897321293302205709151526603533549415402986403⟩
def polyval3Tail41 : Box := ⟨1153189475974801671173010523126633930459787256094843954611,2259534473156130381124664091573364027333854465712656054674⟩
def polyval3Tail45 : Box := ⟨1709655438163549759083054484168908855053527668295665328341,2708246324409186299770970556046020431770859136299005812162⟩
def polyval3Tail49 : Box := ⟨2534641338771693785363079679299428318921994737318976466344,3184501573069626320405069506041750574477523871015296501225⟩
def polyval3Tail53 : Box := ⟨3757720165597361703847246381654014510820189779782486923626,3645929214559334681073982338986853531578611343935785395230⟩
def polyval3Tail57 : Box := ⟨5570989720297051923915398270606879355315122377088267659771,4013317751859970426742423370612686624762308015699695059555⟩
def polyval3Tail61 : Box := ⟨8259243662632262180436773138998721641027736687724872551981,4148009166904194015200182552837041212627302809062878594099⟩
def polyval3Tail65 : Box := ⟨12244701445105437806440644713543180249780844224923478000311,3816962188217582598191188267046010238874553426715173816276⟩
def polyval3Tail69 : Box := ⟨18153322547875667641519733535318513975745532355622755159834,2639115812588107799126895456019440515222068777958591629457⟩
def polyval3Tail73 : Box := ⟨26968750000000000000000000000000000000000000000000000000000,2⟩
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
def resval4 : Box := ⟨108444509874430579347868136744700924787974424865093337401,8973241760149693428277375464805444448259949077612624965⟩
def polyval4 : Box := ⟨4605376607813998195094875841285838174289141670793687744115,1890494028021452525338673685929020639831103007477466083551⟩
theorem cell4_lo : Holds Q cell4 (15/16:ℝ) := by norm_num [Holds,Q,cell4]
theorem cell4_hi : Holds Q cell4 (31/32:ℝ) := by norm_num [Holds,Q,cell4]
def resval4Tail4 : Box := ⟨-4119192416257342353791090719319059873440255903860685909,9711543190885333498774392303156665629111887953221746324⟩
def resval4Tail8 : Box := ⟨-4991353175786518894416450178718251962390312435755153210,10712277977029426378592297504695957705723695438450123460⟩
def resval4Tail12 : Box := ⟨-6048098520376344709022385444889322366709655229517443687,11781978701482183947289889958159791399960939446656004340⟩
def resval4Tail16 : Box := ⟨-7328572909780096988869200313521646830290398986298433201,12915894788293777872390003800893575179114322612142129864⟩
def resval4Tail20 : Box := ⟨-8880143190950230457734374728177269630057468175645930342,14105650267970066070155825164786931279299768853285821986⟩
def resval4Tail24 : Box := ⟨-10760204484906425386191018064829941200586960283176889423,15338120687970866082413640551537310071326506246833914123⟩
def resval4Tail28 : Box := ⟨-13038303332202344273487315499219649433549442643674507415,16594024916397285607380112762254729298556297211058657238⟩
def resval4Tail32 : Box := ⟨-15798710333151918008818409094586800361026396211812060793,17846164256168309146387259266209162364527429082972646606⟩
def resval4Tail36 : Box := ⟨-19143537455090065619718552399071165279339629777858408729,19057226812718729751001968037398909343011669445232526022⟩
def resval4Tail40 : Box := ⟨-23196515320964348092379773362252843983398529999214064130,20177056685391625853596142946332320277813119215250607979⟩
def resval4Tail44 : Box := ⟨-28107570207337221064332364662065674619677830719206572988,21139265154432269543688085957673667472535832909728343354⟩
def resval4Tail48 : Box := ⟨-34058370062436896578506134193889685116201219860379026748,21857033741377857366227120147234993009546076317210365147⟩
def resval4Tail52 : Box := ⟨-41269044700530455187858791299860332207372005195939969111,22217925773328676631174291978347920486415049959623306523⟩
def resval4Tail56 : Box := ⟨-50006328763594396191537988572720033936481950530029065741,22077482597053928085907049866284957783650663361234930351⟩
def resval4Tail60 : Box := ⟨-60593428671742613032153391174263015075038644661007299050,21251331308051947878345712712578228134737032013771027810⟩
def resval4Tail64 : Box := ⟨-73421978551965698949080634425543342453537187430686256149,19505470889523366188358798188637092670047071077176163993⟩
def resval4Tail68 : Box := ⟨-88966437238381168765704761743993035777241338180048985837,16544327959949882570601769831644977283295743164877823495⟩
def resval4Tail72 : Box := ⟨780845219203566999419500378626035621467005838941160222638,839590613216122394001368993848680774512304069542891440⟩
def resval4Tail76 : Box := ⟨-52650422895740688849832064316602008911362411253145837,127042675428821302005919481333677045442103074372814458⟩
def resval4Tail80 : Box := ⟨-63766993931682235148834122618468876152988112337914796,140229960247015758790154881327851563507934575564299938⟩
def resval4Tail84 : Box := ⟨-77267434275729110939957814019022466313916152569675831,154352971617022787940634687302120385046738514574057105⟩
def resval4Tail88 : Box := ⟨-93626124595703394951408688696514344358302213890131872,169358256624291437165273482955711172902280240640020278⟩
def resval4Tail92 : Box := ⟨-113448198313486262560107710880187322268502884899594964,185147188821332975962675760668237137546961721832728824⟩
def resval4Tail96 : Box := ⟨-137466906337881134667080921384739200707139660092240199,201561612407529310880533674944395463978937960677887171⟩
def resval4Tail100 : Box := ⟨-166570739941503067329904446322562090702425563036715422,218366005483871670071070038177258872159779524037874313⟩
def resval4Tail104 : Box := ⟨-201836297504674820745935388364398531009323915984819288,235225158348692607401313972032812731662184588650203520⟩
def resval4Tail108 : Box := ⟨-244568109649402335137679463543124114079728808095143600,251676321319574660871602842846438189214743814233210775⟩
def resval4Tail112 : Box := ⟨-296346895959567009870047103318234212563974078385343082,267094542240242223018510504259735982118635113622725422⟩
def resval4Tail116 : Box := ⟨-359088038382297109373529421890683836312198456306393283,280649628115598624658512415029839382165330855260255391⟩
def resval4Tail120 : Box := ⟨-435112434337220049036683926010271872666864217606279152,291252817114233158041009794551299995120899159088815547⟩
def resval4Tail124 : Box := ⟨-527232350505928648181964508558111925121928142093585178,297490822985479775752759211552764203247187455329317223⟩
def resval4Tail128 : Box := ⟨-638855453173676864785675504710977750330394892612603967,297544397362398807042454541518448105018667190326030565⟩
def resval4Tail132 : Box := ⟨-774110863375714857178078545123950028873395257229632640,289087926555135263704820006268593551155734973190581282⟩
def resval4Tail136 : Box := ⟨-938001899848357334202355730439606129034005022409763630,269165814110128426682768282397603893048533853088658582⟩
def resval4Tail140 : Box := ⟨-1136591281521764270623499117661231914025239514368572182,234040461360720090131358387549426659751080456300435673⟩
def resval4Tail144 : Box := ⟨-1445217675332564301683318548021692845305880275497167508,175834716586696320974766715631410879248549932868459384⟩
def resval4Tail148 : Box := ⟨17121319264869230236077120641930880313796875896,36383668468459901522193085362153208232971598577⟩
def resval4Tail152 : Box := ⟨20678169924897190428183899911672495993836478889,40007762570124604480285701574528674548503594667⟩
def resval4Tail156 : Box := ⟨25056051670642266212407695729889496799945301250,43847428977733708485854790395934150072128810896⟩
def resval4Tail160 : Box := ⟨30360798667324547944960428160321830736953013685,47872978500762967102374563993124812682376711643⟩
def resval4Tail164 : Box := ⟨36788641237047881926404299798135963201161040158,52038858221875122991257446254487475072087540559⟩
def resval4Tail168 : Box := ⟨44577355783621917148658879383345894292571965220,56278373617918108089535736850510704124085406486⟩
def resval4Tail172 : Box := ⟨54015059590145095947379082698590113459819544114,60497655673448513123880803291080873189303856352⟩
def resval4Tail176 : Box := ⟨65450868748004237951597382836733430318221231032,64568139937491741265287218023489563679067739030⟩
def resval4Tail180 : Box := ⟨79307812531786019283639381294872340389894091840,68317213917425890248407622336395567343846342680⟩
def resval4Tail184 : Box := ⟨96098481943659537279171232304430004508130012525,71516612606446878546127690438778190022121043865⟩
def resval4Tail188 : Box := ⟨116443991292466516652460866170475873459984362126,73868048588567466419348267130226236971201186212⟩
def resval4Tail192 : Box := ⟨141096954227325730712675069325006448768918726918,74985449454122866378284566603805368922108693727⟩
def resval4Tail196 : Box := ⟨170969324146793025189271336840034246965404584622,74373036798630678388486035652895299596353623624⟩
def resval4Tail200 : Box := ⟨207166128845821810066428470885794835645509587529,71398312537437050019276894582705740915894792554⟩
def resval4Tail204 : Box := ⟨251026347300260332681542310720257673036668730201,65258813175670457208891291838126323591043141024⟩
def resval4Tail208 : Box := ⟨304172440687983741020157190587456112609139926450,54941243171101097838725305391492051658578555587⟩
def resval4Tail212 : Box := ⟨368570369931710453419583249380506578127660586511,39171295076842874461227928358400552798870184195⟩
def resval4Tail216 : Box := ⟨446604749851868008085273301316971030029363220195,16351940806222525421904713492639443540899350978⟩
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
def polyval4Tail5 : Box := ⟨1028487032114939181031887029579107857458166240559315262387,2079247396628923640997070765629386341118334009523274330198⟩
def polyval4Tail9 : Box := ⟨1246231002628111787473961402170916015686344387068043753852,2282322953038283059865171741392975548802262478333970432334⟩
def polyval4Tail13 : Box := ⟨1510077048695552708607569822193613141138241099970254091457,2496282300390352043279654672719658532613414680150310796611⟩
def polyval4Tail17 : Box := ⟨1829783313458935441920561334142937948773738945417213607299,2719081586014882639321933911573486652040032033438016075938⟩
def polyval4Tail21 : Box := ⟨2217176254089315320583820554367964348645129868765148853954,2947655472347503981228352032748518779928410167743094324139⟩
def polyval4Tail25 : Box := ⟨2686586168722241310207595819089974874164730828220173789054,3177621133959792158390147092065828666077878290291425223853⟩
def polyval4Tail29 : Box := ⟨3255377297432888797650752946861935383269191654613494041864,3402908801764764451382342165591353767238540335175577370199⟩
def polyval4Tail33 : Box := ⟨3944590153861207915212522629340237600993683151900221678138,3615301829918563690679198220458200192353670904665501848498⟩
def polyval4Tail37 : Box := ⟨4779719848205877794956719140248086304552893031349458578387,3803865470139734044316316712026740670894451203847303071566⟩
def polyval4Tail41 : Box := ⟨5791659193026788638956139955535963976549805711075673883624,3954238906496198147459365303407232328379719965246038768814⟩
def polyval4Tail45 : Box := ⟨7017841478881356992483188015708074477005120541119690738757,4047759461005679027872201420923600690040156332574589849692⟩
def polyval4Tail49 : Box := ⟨8503625192933528894091603614081211406328249678878578484852,4060381008487974983034370407475118019980998079729562657688⟩
def polyval4Tail53 : Box := ⟨10303971903540383564241531275935590096477756994956231965842,3961340273076883233259677121752867218968979325622571774206⟩
def polyval4Tail57 : Box := ⟨12485479378509993033917543021053084079161616575784811773635,3711514497004074528393411926405181428726523121400557790718⟩
def polyval4Tail61 : Box := ⟨15128845145398394552971088415913811714366150276866704159146,3261401584249385436641338507296763802461079276269658883100⟩
def polyval4Tail65 : Box := ⟨18331851624978052150595543326304590471566386225616504597173,2548638753470961722840917660417811626634970844042626948216⟩
def polyval4Tail69 : Box := ⟨22212983347116083882291098358395323242019385199677988750834,1494957405829183952976527078321340383643194537587458876988⟩
def polyval4Tail73 : Box := ⟨26968750000000000000000000000000000000000000000000000000000,2⟩
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
def resval5 : Box := ⟨96140134500488211102723225537158698516855310392442715835,14478407056261722655019682932522346835702834092843650748⟩
def polyval5 : Box := ⟨8635610157741298858097427698919525373730872448544476645711,3784485265337389549403944877672783897490214644202959188987⟩
theorem cell5_lo : Holds Q cell5 (31/32:ℝ) := by norm_num [Holds,Q,cell5]
theorem cell5_hi : Holds Q cell5 (63/64:ℝ) := by norm_num [Holds,Q,cell5]
def resval5Tail4 : Box := ⟨-17251749531635833231847275458203201782471308057187024744,14679394060086398664768476984336002886028600776413832999⟩
def resval5Tail8 : Box := ⟨-18968558189379727917309041960362681997750014928769101931,15038799774517005286626591650878316057437539288028677591⟩
def resval5Tail12 : Box := ⟨-20856150298099089812751716146250476137275184704710092303,15362360637743950124125596816053162599688938222855986605⟩
def resval5Tail16 : Box := ⟨-22931579763409594314466410649074227542114966839690998904,15641852949912442112098274827328091753577356370533495828⟩
def resval5Tail20 : Box := ⟨-25213538593141685505217128467368007044747311111723768967,15867932534278118136041957479791056707948093258825105211⟩
def resval5Tail24 : Box := ⟨-27722578860538211888062944316971914551748361967018091500,16030002936781388675608117895939103873600878956788784721⟩
def resval5Tail28 : Box := ⟨-30481297809098896653897645792144967749686635051634918945,16116069845864456573486992916281043259682733389136106583⟩
def resval5Tail32 : Box := ⟨-33514541370807350364481921610168367039848950858440023861,16112579662421491450722150581084427928749424380784116149⟩
def resval5Tail36 : Box := ⟨-36849627936782484206671259841909989031947514641042944185,16004240553885616638903796323474587476075266720441635504⟩
def resval5Tail40 : Box := ⟨-40516594395711673634075081398630017827220763269364256434,15773824155031435054786576506055384714684287359310558922⟩
def resval5Tail44 : Box := ⟨-44548466655968901350886451662758971284156308482027948270,15401945889090030425481365171237523181065895329283411840⟩
def resval5Tail48 : Box := ⟨-48981557087829226105223981688309977539314907400135195117,14866821674586514722142212333963369684513601591290618755⟩
def resval5Tail52 : Box := ⟨-53855791564642182445005305659500631613214468758620429143,14143998553981329860547388604290909504652592631631142457⟩
def resval5Tail56 : Box := ⟨-59215069048404684366605278005450632153230517191143533434,13206056527594144539502536172427375623480205839470436581⟩
def resval5Tail60 : Box := ⟨-65107656958276361805247849389082293219252639934216338162,12022278598067669056867430374576010266501533958773635630⟩
def resval5Tail64 : Box := ⟨-71586625877892050383955062969613061652654887478054169958,10558285723942129368781480019501070914396386300070249478⟩
def resval5Tail68 : Box := ⟨-78710239374718343850722861395223881366345229747800583020,8775629665334466426315683529818457436700569637147692022⟩
def resval5Tail72 : Box := ⟨780857839424520754675331716140751123102937944155770041121,854460938152670938857453695137790174766581005977592986⟩
def resval5Tail76 : Box := ⟨-225390183254808396040129015530748400028058272160354217,194904393476433943021724098108902332896044366053426122⟩
def resval5Tail80 : Box := ⟨-247791648408505820012906323728267385218254769483865861,199803624812113432005559005702467779742635045275641261⟩
def resval5Tail84 : Box := ⟨-272449797292024754325899941431741034643359808472491693,204248047498431725486513067060821429500408591393215684⟩
def resval5Tail88 : Box := ⟨-299561720107050484297411561532219811677146203345432759,208130942165925045874747399993152304127503848768357645⟩
def resval5Tail92 : Box := ⟨-329371594494279659606041014018645658089316524347916632,211331163328121544310487084173558796337603173396441066⟩
def resval5Tail96 : Box := ⟨-362147898005582010350365936173662248462939611745828354,213711266489404954570018711417142729564408809977826100⟩
def resval5Tail100 : Box := ⟨-398185824831774299658323075318964102448195457232130402,215115610264264293965928102632035518576279188493800676⟩
def resval5Tail104 : Box := ⟨-437809944418113361551412610368112235148581850838102107,215368251713789728224466605400427233511293950667314964⟩
def resval5Tail108 : Box := ⟨-481377124643679907293990794825263278820529567846325217,214270613136874658171727575379960552511061344578712215⟩
def resval5Tail112 : Box := ⟨-529279745891102938859655155294029797606469692351209042,211598896330871999349889197893439337000269238376131629⟩
def resval5Tail116 : Box := ⟨-581949234953594239947775207269986651979241553162415711,207101217868881070249132026249754996968601813405033612⟩
def resval5Tail120 : Box := ⟨-639859950606824278647583615626356432380410920821430608,200494436222450416733102240872191523772427900351398777⟩
def resval5Tail124 : Box := ⟨-703533455840380322865677219011347074204936282611214625,191460638563985732823495140210884917590318817148387373⟩
def resval5Tail128 : Box := ⟨-773543215225931257019518871199902986401481719693438788,179643251784711484380638347022794123974762013804166220⟩
def resval5Tail132 : Box := ⟨-850519759728159186774382013215381532294807590075026195,164642738631015266476982755773856031627461493337314021⟩
def resval5Tail136 : Box := ⟨-935156365488324196791196222424417123488576286287476771,146011835859699062771505731978774095044047218590815239⟩
def resval5Tail140 : Box := ⟨-1028215416550978721686282923778548811468473025247205629,123250280031587822295171315071668700277128960620324392⟩
def resval5Tail144 : Box := ⟨-1196925970158765977076098857473247893274288494966106101,93221179880920307279667630275501623773385507584292020⟩
def resval5Tail148 : Box := ⟨93541286722067562137460531789302063279286713722,70359381844446263169527681402104535546754254528⟩
def resval5Tail152 : Box := ⟨102788090894020115408569547658722298765855010336,71709165054874591053833840883912769880651125777⟩
def resval5Tail156 : Box := ⟨113016700102091895845931602261023187922295485295,72826338453326032496225934240473036263471833915⟩
def resval5Tail160 : Box := ⟨124263175894813656278185906701127663625830662578,73663347248089530324110464411217959983246513175⟩
def resval5Tail164 : Box := ⟨136628806800721460011680038329110697535726424268,74166867161619818314154772020816066890317483360⟩
def resval5Tail168 : Box := ⟨150224961766553868196223581347625863829604013646,74276613139381304366520852094531524669425038503⟩
def resval5Tail172 : Box := ⟨165174092244531008074835010394926462425879910470,73924539088146960918545485723948178559289808866⟩
def resval5Tail176 : Box := ⟨181610835030207466119122128492561280264276202407,73033950999079735454819733789211746265329968635⟩
def resval5Tail180 : Box := ⟨199683224845822013203303427955112836650864718278,71518524367366142778016826599701286342939016946⟩
def resval5Tail184 : Box := ⟨219554027589790768369895565934394560219643628998,69281215900464031444509108016548578178058536410⟩
def resval5Tail188 : Box := ⟨241402206260027661729733692125834455136441650467,66213058479636117766940415911672237281348321612⟩
def resval5Tail192 : Box := ⟨265424532753680711472023471658544499625073733812,62191827207759109016417256694105790066838050250⟩
def resval5Tail196 : Box := ⟨291837360059683706737123490985254373620340224477,57080563129920301009881569767487183468809187181⟩
def resval5Tail200 : Box := ⟨320878570805073441306281106013723849182070609938,50725939840474109906359201679678514761036972550⟩
def resval5Tail204 : Box := ⟨352809719704322814227193775347788402853768673355,42956456678304637310653274663434382755895960739⟩
def resval5Tail208 : Box := ⟨387918389207313322581887945648335152575195987111,33580440547023890072252071221411093458951594457⟩
def resval5Tail212 : Box := ⟨426520779612187789593113891294785154901182642590,22383836559853912834980057529344860276724565310⟩
def resval5Tail216 : Box := ⟨468966931201208480180459782637377148869880455956,9127632687014417140778686117513975716557488900⟩
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
def polyval5Tail5 : Box := ⟨5365753454392186407855577120703428802140626659618213559270,3859512537634951128778145808501508221604300242313960413554⟩
def polyval5Tail9 : Box := ⟨5899706170139318992149933473834620634197654148401048921938,3925383049728687170947170478955184123410860230031714710382⟩
def polyval5Tail13 : Box := ⟨6486795534333925584788424763383313435305795760747316411077,3977119412066806907124271850019530156143249475188494748831⟩
def polyval5Tail17 : Box := ⟨7132307117005436972093003355364998795774237869521020726971,4011969902495293738428311835025725621203732195131644398339⟩
def polyval5Tail21 : Box := ⟨7842054608016997219634856933264628665626867415332858214562,4026821517557106835978534809866873063970061389812021184687⟩
def polyval5Tail25 : Box := ⟨8622430227169050227191585054631370316063552473031995745302,4018158322247143189635840393812741702034488667182978945940⟩
def polyval5Tail29 : Box := ⟨9480462294459627875464563066196866801468598679887722452200,3982015296939357423186692396975253297724515334361338351742⟩
def polyval5Tail33 : Box := ⟨10423878529450297271655009389710447740855079682785155822191,3913927197743499407971493989684736209875348724866024318718⟩
def polyval5Tail37 : Box := ⟨11461175649655193507642760622590223985790904410964562349172,3808871908462128102824136757936469876177076145388514040962⟩
def polyval5Tail41 : Box := ⟨12601695894779036106720766716238049165630065623885073504849,3661207708728066970616080977421313694884653654740792492321⟩
def polyval5Tail45 : Box := ⟨13855711166006634809544401495060417095683473771735535064319,3464603823868413180657869549011569596521487849366217473033⟩
def polyval5Tail49 : Box := ⟨15234515538130053997094141319104626089180980205810741627759,3211963557017295960952149358435793757656436738935822098331⟩
def polyval5Tail53 : Box := ⟨16750526977708140266323641782889288652411905208287525027301,2895339232382244778398900325872780051018177742624175685110⟩
def polyval5Tail57 : Box := ⟨18417399183365679018287599573471010088235925999346406502002,2505838099694170497645496707076533721945590957844305548897⟩
def polyval5Tail61 : Box := ⟨20250144555502780855049757719060607740997466888146614136559,2033518263007871193294714535943941853999627186247755967017⟩
def polyval5Tail65 : Box := ⟨22265269402929889283618880000717695929971270850690601399117,1467273601363995972790855062458108612871064522689970019332⟩
def polyval5Tail69 : Box := ⟨24480922686544058480806303378250356634427533011011914681403,794706538963506419087731442988723056369779329655046958065⟩
def polyval5Tail73 : Box := ⟨26968750000000000000000000000000000000000000000000000000000,2⟩
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
def resval6 : Box := ⟨79112895161718828183656382764222244873154179564886875875,13107384436211127054386044596179092246400767981260444968⟩
def polyval6 : Box := ⟨15274534597246007633553630439060719907129285946527524583296,3787523365845830817353540445011595512121558062829915071969⟩
theorem cell6_lo : Holds Q cell6 (63/64:ℝ) := by norm_num [Holds,Q,cell6]
theorem cell6_hi : Holds Q cell6 (127/128:ℝ) := by norm_num [Holds,Q,cell6]
def resval6Tail4 : Box := ⟨-34290203214780191910411518046218157795958591948141817327,12797559062001340877491219752151936575157639791812742030⟩
def resval6Tail8 : Box := ⟨-35945829849236790787399126201402868432062352855111936597,12642675109280695978164480796346408755658605802325251374⟩
def resval6Tail12 : Box := ⟨-37681335865526910535574767055247046075900888653346145828,12455685740499158467844328814646077297036147276976386274⟩
def resval6Tail16 : Box := ⟨-39500634102054551046752402659897260130238791671517607378,12234255402345519786030714005520025895069358585222086989⟩
def resval6Tail20 : Box := ⟨-41407770149986460034433824197896498795617838785324305611,11975911335204126857298684777477802391015563126736565234⟩
def resval6Tail24 : Box := ⟨-43406984919893399908674635865682543250243197719336808710,11678035580051830562255296002489831798695457852093841830⟩
def resval6Tail28 : Box := ⟨-45502724078380953916664673447591892776056620736086696642,11337857145324307490396203350054792481763469331535924349⟩
def resval6Tail32 : Box := ⟨-47699647933951792624312978685319558101275675704042319109,10952443769487756051841106877554794738653767897438440356⟩
def resval6Tail36 : Box := ⟨-50002641800163365076322258244078437119047141012526953416,10518693258845642214090129056840791044418085077598885202⟩
def resval6Tail40 : Box := ⟨-52416826859130743714244143545534692952569882093631468677,10033324379210044478590301986425406771282369329734643566⟩
def resval6Tail44 : Box := ⟨-54947571549531881591592839865297829772282378155781066937,9492867279008023490602641024042448293761477882468200136⟩
def resval6Tail48 : Box := ⟨-57600503504438861839416774651620983169127711335351385488,8893653420282163773638909538089487130109111571914364684⟩
def resval6Tail52 : Box := ⟨-60381522065521370581550900513797331953801548186400974147,8231804992878599072445890664714775070732725104831508699⟩
def resval6Tail56 : Box := ⟨-63296811401450296516476096932922672679645152016376232947,7503223785892775403604342176113807803977800342081345233⟩
def resval6Tail60 : Box := ⟨-66352854259669724780945646216672285697329098267201630231,6703579489159893372783695366986771532940780560608671574⟩
def resval6Tail64 : Box := ⟨-69556446377204774079710427284855912316722279599889032447,5828297395950391483134078594662011124217997396161974481⟩
def resval6Tail68 : Box := ⟨-72914624423787471568443895071594343182182845652467510762,4872541797670403222525767937461927014013920037952018471⟩
def resval6Tail72 : Box := ⟨780718869667982863392389051127777669460097573794721899759,808022024879461043991037695365652322883053806360266227⟩
def resval6Tail76 : Box := ⟨-451845814977731188289436107604845723831472469520736035,170805817006154037711602769727347355288860133966857094⟩
def resval6Tail80 : Box := ⟨-473635269699682158329464742702353922972663956097603610,168834338183510599447902783903946643494738783425098964⟩
def resval6Tail84 : Box := ⟨-496502923962385985802822420138311623429515568008432041,166442202062452185706775891023258571911656578931080966⟩
def resval6Tail88 : Box := ⟨-520474656206426210960903623461867744569919656901660018,163598544468383796492605546616745812357379387127103173⟩
def resval6Tail92 : Box := ⟨-545603771256114252712638917680877826476607638317376200,160270856238217439025626167084241715096320057705801294⟩
def resval6Tail96 : Box := ⟨-571946148883819157063418087568126743881184649130143745,156424717346214236447287935579201145366791253142643236⟩
def resval6Tail100 : Box := ⟨-599560366802295953465462329802529472468600195603336418,152023693749518430279823670843057127869522519277508151⟩
def resval6Tail104 : Box := ⟨-628507830923649137964117304579947971526131440695425177,147029228925136698524714217181947776592957473263712634⟩
def resval6Tail108 : Box := ⟨-658852911908048482449870126000568632257044324525394764,141400529812506187991733198892229129469035551385330308⟩
def resval6Tail112 : Box := ⟨-690663088305175653377421300142959125863122072151824929,135094446880131191105118729701275684030545844798479580⟩
def resval6Tail116 : Box := ⟨-724009096606704528822569810071802320640909147327635002,128065348020828226310080975484708673570042743500197119⟩
def resval6Tail120 : Box := ⟨-758965088543487855430987705261868066995173149867033738,120264985965479274481456601763562781182489020711460843⟩
def resval6Tail124 : Box := ⟨-795608795977233000848484722472491609491340864847447635,111642358889834077775151856562475729872229243237368482⟩
def resval6Tail128 : Box := ⟨-834021703753337537084466256952734498315775885386793772,102143563872789681806395307728517234111665113726222202⟩
def resval6Tail132 : Box := ⟨-874289230899272848820751071022653590473878173690066503,91711642847670764953114316455529810300904606023867039⟩
def resval6Tail136 : Box := ⟨-916500920585181930707435682791303674997428996800622021,80286420669356850352670600372883934784461513354662092⟩
def resval6Tail140 : Box := ⟨-960750756789075841721990836097565796070874214664057140,67804328523598189849180034543405108445701055466569981⟩
def resval6Tail144 : Box := ⟨-1072755253601293529335410500620082223522156212887234074,51900646194579025793765407798993195982744947568128411⟩
def resval6Tail148 : Box := ⟨215550826884705096596913955856124517981804099531,69470040835743209768573743578924244262794394180⟩
def resval6Tail152 : Box := ⟨225899125615446110648792832952811058975497523646,68147046230356879570907020754222858600491492544⟩
def resval6Tail156 : Box := ⟨236805794244977040992927806514317374810908890140,66611634096514465783070674481940866336702628770⟩
def resval6Tail160 : Box := ⟨248239050363987421034003509937324838631384650117,64848297589947605609528204982687089658850351395⟩
def resval6Tail164 : Box := ⟨260224317239206939778988394577241405456526806802,62841130862201722466657549938215243477119344022⟩
def resval6Tail168 : Box := ⟨272788246584572607926034941123751676202847273769,60573303918964259818214914439012415409270581443⟩
def resval6Tail172 : Box := ⟨285958776889718058026950553739952969279742669565,58027013008925092151430844809186644160676182526⟩
def resval6Tail176 : Box := ⟨299765195546691657666832411568067462797341304508,55183428472676351527015100293156329078042447545⟩
def resval6Tail180 : Box := ⟨314238203976516123535579252675312032375866345786,52022639909987786339963096286809611865190083280⟩
def resval6Tail184 : Box := ⟨329409985900133811167129788201805063644248264660,48523598530761650920079165957418329521313080860⟩
def resval6Tail188 : Box := ⟨345314278905551770995405174571610926545809957060,44664056548308006395599981616838201153927706566⟩
def resval6Tail192 : Box := ⟨361986449470330884030309093020615587178548205879,40420503466584761693750677617215402491946697955⟩
def resval6Tail196 : Box := ⟨379463571606247063606241874314437637809293920971,35768099105706947377559398617018653664584937532⟩
def resval6Tail200 : Box := ⟨397784509301007157100990866829074932767197774393,30680603202329860244375838032912828225986274489⟩
def resval6Tail204 : Box := ⟨416990002940345757255771704469132145469985378241,25130301413433277162833291799316330969698806978⟩
def resval6Tail208 : Box := ⟨437122759902698891741500176161334585964998588412,19087927543558983178996592743782571135874380613⟩
def resval6Tail212 : Box := ⟨458227549577871223048758960271404806746849031728,12522581803403695198740271653781630420432002022⟩
def resval6Tail216 : Box := ⟨480353650343737624633463534166381263338980904446,5401522021923350723670789617232843866137594739⟩
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
def polyval6Tail5 : Box := ⟨12075780330490328027524475127912421018283498238727229417578,3716360909120112926156725667126428022422880537437491330314⟩
def polyval6Tail9 : Box := ⟨12658810851208080005801303304832385882691778561408294788449,3636624228284671583416634188442496821007049910967257783515⟩
def polyval6Tail13 : Box := ⟨13269992799035631689534785865301793257643716541955588929554,3544778127702818178518304107312562307875763155318942855683⟩
def polyval6Tail17 : Box := ⟨13910683314470057211632099062916972692624735964190161044614,3439974703715073317001635284781584428539837142269817234839⟩
def polyval6Tail21 : Box := ⟨14582307104909679197452419748311484153236072235959159127684,3321316737226594854252974680376041680142727881527401293607⟩
def polyval6Tail25 : Box := ⟨15286357664450950891251182561813834390222725233741401696878,3187855033693089438505312847233159099439734980907497229982⟩
def polyval6Tail29 : Box := ⟨16024400594803250573650148560538614773385581088065158580221,3038585637795274565901443886268065047092308641491584747075⟩
def polyval6Tail33 : Box := ⟨16798077086727235099739398661621525972923093331648224538488,2872446904844465817058081014385488934755205246245393296299⟩
def polyval6Tail37 : Box := ⟨17609107569561177445069698452091396616100076698330117829611,2688316421719464358716722389664589298230343994199155780105⟩
def polyval6Tail41 : Box := ⟨18459295536950633929331156263360513452736415114078398335384,2485007769780789788799655370124200252542324068966517148345⟩
def polyval6Tail45 : Box := ⟨19350531557288740118153358957657953296634551275884932167107,2261267121834377375957668567730754051896313303516251297170⟩
def polyval6Tail49 : Box := ⟨20284797477785177004919518850227318369135654881565678301355,2015769664824582635222299541799649241982454159518996748693⟩
def polyval6Tail53 : Box := ⟨21264170831512422385213078636262641000713608968968170141640,1747115839524817467939225536666682855367812000322444185960⟩
def polyval6Tail57 : Box := ⟨22290829457229264260297804521178498164962822990459163002154,1453827388062442071666754981196574974913627839161637059433⟩
def polyval6Tail61 : Box := ⟨23367056342254716861562852653477388290838426650514844305154,1134343199661670333471602436180777691869992446907672371115⟩
def polyval6Tail65 : Box := ⟨24495244699171033489093355839605031585124761899486501033617,787014944512545175698798737639060987499467810663091864210⟩
def polyval6Tail69 : Box := ⟨25677903369140137936469905976077163516700798292808584210077,410102480990024360487075698383819528256065881167335392340⟩
def polyval6Tail73 : Box := ⟨26968750000000000000000000000000000000000000000000000000000,2⟩
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
def resval7 : Box := ⟨59050360708414328164390700122907561612862766960266575847,21300109860562764226772740443365389102241083833588439194⟩
def polyval7 : Box := ⟨24062195198855104826903333912353382264016957372939099357987,6614917242085819557794028123580337550072829730484756677081⟩
theorem cell7_lo : Holds Q cell7 (127/128:ℝ) := by norm_num [Holds,Q,cell7]
theorem cell7_hi : Holds Q cell7 (1/1:ℝ) := by norm_num [Holds,Q,cell7]
def resval7Tail4 : Box := ⟨-53601564103598648454658919477314935650721431827371045077,20282593265850826802862713224940626066515685563472381093⟩
def resval7Tail8 : Box := ⟨-54447386239125315909086903012492384400591587729908276813,19436824148313022423194406582709248141942650188773988654⟩
def resval7Tail12 : Box := ⟨-55306500019957566754280226675682794125600204641403082399,18577710373475866333152409664332904112028274609194367509⟩
def resval7Tail16 : Box := ⟨-56179169568966479743471516242877887307758819235387057470,17705040824472027116146919398652573494626955414637595265⟩
def resval7Tail20 : Box := ⟨-57065608785938399887133821283936232272340496915951162287,16818601607500125639867466057576462995868263974208143080⟩
def resval7Tail24 : Box := ⟨-57966034939552736003105962851723531087758280976154298261,15918175453885789751490150102886845216625972045101107416⟩
def resval7Tail28 : Box := ⟨-58880668726720128619828115021199710171345978555698525194,15003541666718397142393771949074781817145292960156820718⟩
def resval7Tail32 : Box := ⟨-59809734326681005048054228537688448724958843984319609213,14074476066757520714740821228689116185224918440842442623⟩
def resval7Tail36 : Box := ⟨-60753459455952542289567593001820911078405758599219146375,13130750937485983473271303846886226855554109006729728689⟩
def resval7Tail40 : Box := ⟨-61712075424142607833589768051914316105231870923816135360,12172134969295917929141400268958394040285240276031326567⟩
def resval7Tail44 : Box := ⟨-62685817190644376593297367578143829686243749670940556904,11198393202794149168812791275104526986353650692487432289⟩
def resval7Tail48 : Box := ⟨-63674923422225520184538822546087798069017509319526531576,10209286971213005571150007320681382492547675694772345853⟩
def resval7Tail52 : Box := ⟨-64679636551526083700143418842462481393460457310477596998,9204573841912441890431415532888355789422585923674072107⟩
def resval7Tail56 : Box := ⟨-65700202836479377355727876112974967285629498029734554601,8184007556959135642846488027864491443108400566909718793⟩
def resval7Tail60 : Box := ⟨-66736872420667258110266659255626288128431179673654826285,7147337972767750409097587343033754391883131761932827829⟩
def resval7Tail64 : Box := ⟨-67789899389746192513670207157095025634179944098583488739,6094310998511245396908457492839789667446229468757235295⟩
def resval7Tail68 : Box := ⟨-68859455308507131778982311142497605874228211128697346784,5024664882912522252369750893189048714825205898442001671⟩
def resval7Tail72 : Box := ⟨780510196337209959723387062491399587666390138103830977491,915029982375293593310493328275006904557842817490936115⟩
def resval7Tail76 : Box := ⟨-708765104720925610892150268891787104387954726036978070,270358277992277064410040268040844699355446817258723076⟩
def resval7Tail80 : Box := ⟨-719923201338485156121427406865528510780389097649620734,259175049455035780395988491610054000724692001726977170⟩
def resval7Tail84 : Box := ⟨-731282715751521630706972926314846901568645518117903809,247815533754768829457440593024963429314112685493694328⟩
def resval7Tail88 : Box := ⟨-742821470825171240937931938892057658881607769591599141,236276778680429077978928284283917795576060563345208936⟩
def resval7Tail92 : Box := ⟨-754542293471717070111318249008013624043806527363777646,224555956033881446837394663997389092290986476313756216⟩
def resval7Tail96 : Box := ⟨-766448056496144678852036827154375456743220621404810718,212650193009453821323945783922284983670556751823198246⟩
def resval7Tail100 : Box := ⟨-778541678033501560451216403550124011046909750707669007,200556571472096939263946242215478555356069096076199662⟩
def resval7Tail104 : Box := ⟨-790826122263471738830624063264941894310886523991549967,188272127242126760852189653519750254661347083624095979⟩
def resval7Tail108 : Box := ⟨-803304400136902625936974548099028662641641199751216392,175793849368695873741031589319858433739633023215231062⟩
def resval7Tail112 : Box := ⟨-815979570113797287297157214279147905880674957549365212,163118679391801212380319917231608972908430154744935789⟩
def resval7Tail116 : Box := ⟨-828854738912951345532426060293097480341600608605899098,150243510592647154149524383353802650982352830363511451⟩
def resval7Tail120 : Box := ⟨-841933062273418246147197209482507710819823866224896842,137165187232180253584532931505117462124483081680421133⟩
def resval7Tail124 : Box := ⟨-855217745727989523487012521029343346980732074128418152,123880503777608977335521669519244883785232911480521672⟩
def resval7Tail128 : Box := ⟨-868712045388879715411155948757969060813686503643513701,110386204116718850253694816091417228463430488501628908⟩
def resval7Tail132 : Box := ⟨-882419268745822652972766488559469026834954092798143090,96678980759789188363828098217322590715620592758754163⟩
def resval7Tail136 : Box := ⟨-896342775490415236882582906554388123116094608389358290,82755474027978779110914073031270363352302973204974197⟩
def resval7Tail140 : Box := ⟨-910486095032316647476874904539053228805521777072300653,68612264906230862286661863842811082331247045824540893⟩
def resval7Tail144 : Box := ⟨-989965515796673898816931694480549350799257552779981352,51968539670264689079898773460555492095652881913294739⟩
def resval7Tail148 : Box := ⟨374038311369607445780798778686529373061692596614,119492882898004885553293968025653756412105807250⟩
def resval7Tail152 : Box := ⟨379883277866397391770792770846451914251029812982,113591417355720633657415495420198300318592098729⟩
def resval7Tail156 : Box := ⟨385877374690120977392533000363106082736899698053,107597319581102374953662435671395278194342450508⟩
def resval7Tail160 : Box := ⟨391966052050001800875532740153191172770786705700,101508642220934714984644924214374975095694547146⟩
def resval7Tail164 : Box := ⟨398150801360548374199498364591397892109121048505,95323892910387666187843441542121993057080590493⟩
def resval7Tail168 : Box := ⟨404433138520436583528399418030330182761645685785,89041555750499453875499536413786384570274331347⟩
def resval7Tail172 : Box := ⟨410814603347670043486609805842957671128281730879,82660090923265993859836789643876818815937110923⟩
def resval7Tail176 : Box := ⟨417296759956714948646780221965975541853692951362,76177934314221088696733146989625740502286050737⟩
def resval7Tail180 : Box := ⟨423881197141868353660100537003956034780845853584,69593497129067683683069664928591826711541244342⟩
def resval7Tail184 : Box := ⟨430569528766675994119285840519773332693392967661,62905165504260043223820281747657847093572142216⟩
def resval7Tail188 : Box := ⟨437363394159494651377493668675532742451913931979,56111300111441385965663715573784612192449546574⟩
def resval7Tail192 : Box := ⟨444264458515296012179168296760609141821807816429,49210235755640025164593572611602144529091260688⟩
def resval7Tail196 : Box := ⟨451274413303810506293154203571880763169700554380,42200280967125531059902237001719160745204169505⟩
def resval7Tail200 : Box := ⟨458394976684111159655245577849627999666958391765,35079717586824878041946634359144265279033202703⟩
def resval7Tail204 : Box := ⟨465627893925739119773744475751580032114682382651,27846800345196956655600427432820843949446611526⟩
def resval7Tail208 : Box := ⟨472974937836492551484322776427921141970626720695,20499756434460719936174884442738639311568976653⟩
def resval7Tail212 : Box := ⟨480437909246591913475908055099959250878884050278,13036785070839123898319850055043875938230734947⟩
def resval7Tail216 : Box := ⟨488020967269828398438979782294872723613866677791,5455935237286885558285488825842720409047633896⟩
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
def polyval7Tail5 : Box := ⟨20628058990563399397270367341100376111187922325138770127356,6291752653236576055814062042726106576163643541505290435473⟩
def polyval7Tail9 : Box := ⟨20953542785279136646536538310446259781500696814668774356692,5966266899396541244646707385632633766568985341416406825302⟩
def polyval7Tail13 : Box := ⟨21284164298408071098823058843578752247737415290960824894526,5635645386087391372064510927616589207779688458758563669894⟩
def polyval7Tail17 : Box := ⟨21620002618542245215584494878080321962512114704387201237906,5299807065953082843666394903611899235883270711393369300169⟩
def polyval7Tail21 : Box := ⟨21961140060393961283904454970361036169275263525728165844703,4958669624101366330599094649876670540329474667425845842134⟩
def polyval7Tail25 : Box := ⟨22307660237682227876436072725038162070925396333213313765812,4612149446813099733102609202988249853399294810572253274212⟩
def polyval7Tail29 : Box := ⟨22659648083449347463665336369480659732908863331871985988342,4260161601045980145715920290242790183665855492570622058551⟩
def polyval7Tail33 : Box := ⟨23017189870878107238247397300138160729781563943679468517421,3902619813617220371121510648053618248641885008257846292792⟩
def polyval7Tail37 : Box := ⟨23380373234437571540747358906514112623158686921906363201801,3539436450057756068619588239106563134626364463369255541814⟩
def polyval7Tail41 : Box := ⟨23749287191362529680030884835948704139570020425873430357135,3170522493132797929335943921109698231223289391175318970665⟩
def polyval7Tail45 : Box := ⟨24124022163471863415281251051453546973186295231172323215607,2795787521023464194088224400139858797225007586466259676038⟩
def polyval7Tail49 : Box := ⟨24504669999331181837160857929603292112510854825640945136254,2415139685164145772238346662679015545936162030424712523555⟩
def polyval7Tail53 : Box := ⟨24891323996765155770999690551000828127371102078684097197647,2028485687730171839079516746797403421646263595425683094967⟩
def polyval7Tail57 : Box := ⟨25284078925725069580027253082190576305711508431537361826941,1635730758770258072308303005222654144459781608476339074847⟩
def polyval7Tail61 : Box := ⟨25683031051517204854035255464771631192151343347674378187084,1236778632978131804391847161651994869227507687399857201582⟩
def polyval7Tail65 : Box := ⟨26088278158407248697538433820384793890659869178538582980168,831531526097008289783632714478012346346256209466201293419⟩
def polyval7Tail69 : Box := ⟨26499919654509412967612781510525381481050845786062065128787,419890106802438694997604854894132255182408082759074049533⟩
def polyval7Tail73 : Box := ⟨26968750000000000000000000000000000000000000000000000000000,2⟩
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
def pend : Box := ⟨1030672635066761745632799214883823712939545834800523144125712,4477374179178751898147152110006874543952302900711909423⟩
def zend : Box := ⟨1003750028872165396510488281250000000000000000000000000000000,2798573759692365410156250000000000000000000000000000002⟩
def betaquot : Box := ⟨428749207103634357367537067763334030085702383991187800282856,394769173841700653948075364074947106899764997718312717⟩
def crit : Box := ⟨117353566477637252613264412047771962619966713138732336774,11347331638690967522576464124178876054187550802370903953⟩
def subsonic : Box := ⟨526244177417861592802980439523304134730685866551455154838,5982449160864914464937888240548250284369693044381280179⟩
def pendTail4 : Box := ⟨26918216659519993606104918798838058511013879798013933797455,1558811756974140900146960862662782912161263854997358380⟩
def pendTail8 : Box := ⟨26918251016162834235086963685142640499752876680740339087003,1558666912829948978143386723238675563578952492310303739⟩
def pendTail12 : Box := ⟨26918251017598600431284166203484782754484830277533778830297,1558666896055325444877318290210167657799988117990646272⟩
def pendTail16 : Box := ⟨26918251017599284157441746707593389470989543880444533560118,1558666896041893971722076921243295133884326884656584650⟩
def pendTail20 : Box := ⟨26918251017599285750434880171748292991126350837815886237661,1558666896041846044413797633349491519145929483441360494⟩
def pendTail24 : Box := ⟨26918251017599285763605834644560722210558271236589549417014,1558666896041845444039124907288985664670115632465764372⟩
def pendTail28 : Box := ⟨26918251017599285763923988397350490895969927200008288879885,1558666896041845421337043468212204583722177621914613871⟩
def pendTail32 : Box := ⟨26918251017599285763943233554912138244054781286767829846068,1558666896041845418972392855340134319765192760149502988⟩
def pendTail36 : Box := ⟨26918251017599285763945559489108264702753085187190258569212,1558666896041845418328505200752834338096306318258920369⟩
def pendTail40 : Box := ⟨26918251017599285763945573012442887055310290405164399080819,1558666896041845417881059776200203730538659351725481957⟩
def pendTail44 : Box := ⟨26918251017599285763943305807600928876134283523754328404142,1558666896041845417088227138939558951485122875712187960⟩
def pendTail48 : Box := ⟨26918251017599285763924184023513757963067183584854690191437,1558666896041845413427317175505114196585995791390039066⟩
def pendTail52 : Box := ⟨26918251017599285763592479834065895797278724580665557651761,1558666896041845367194138412490831076753081594126047458⟩
def pendTail56 : Box := ⟨26918251017599285748304142639796641051092857365486358710609,1558666896041843628479174896184227261466174202637819498⟩
def pendTail60 : Box := ⟨26918251017599283472396472422445182382925903737218654250840,1558666896041639013049290272681820234022612408241269782⟩
def pendTail64 : Box := ⟨26918251017597842892206427118286169035658243156922160160822,1558666895943667828943907695228643203735441833980483763⟩
def pendTail68 : Box := ⟨26918251011140815005376937357404668084401960048035157884966,1558666563256033630892695691485636314993808512193173945⟩
def pendTail72 : Box := ⟨26917410251137622830119888099662128459777256811854321256220,1528090578257375920165610431610388644452483088808146458⟩
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
end SepticProfile.ExteriorCertificates.C15

end
end

end OAI
