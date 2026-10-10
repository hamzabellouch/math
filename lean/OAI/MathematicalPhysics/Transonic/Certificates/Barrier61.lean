import OAI.MathematicalPhysics.Transonic.Certificates.BarrierData61

namespace OAI

section
noncomputable section
namespace SepticProfile.ExteriorCertificates.C61
open SepticProfile.ExteriorJet SepticProfile.FixedInterval
def cell0 : Box := ⟨250000000000000000000000000000000000000000000000000000000000,250000000000000000000000000000000000000000000000000000000002⟩
def resval0 : Box := ⟨133381422910832515842655828455996707021174721247362180308,312972636891982466211007549258264369799428268965547310⟩
def polyval0 : Box := ⟨3926985510197096625411527915098685190709542383578130623242,14934499981106103709234511253783710266581332487836662537⟩
theorem cell0_lo : Holds Q cell0 (0/1:ℝ) := by norm_num [Holds,Q,cell0]
theorem cell0_hi : Holds Q cell0 (1/2:ℝ) := by norm_num [Holds,Q,cell0]
def resval0Tail4 : Box := ⟨77582915142383315954659264891667754789803701833444,2195519025325531727365899886706571569666599558356⟩
def resval0Tail8 : Box := ⟨10615313302126391417383946913541920054026268301,553146633998911400812377485245891629203651857⟩
def resval0Tail12 : Box := ⟨10908053725497878936156079946877537952562237,867080441816249132337241652639525714049110⟩
def resval0Tail16 : Box := ⟨49269286778891462678476811821676731079006,33927742847962835308676200966325505307272⟩
def resval0Tail20 : Box := ⟨755653972422495606538312323869246603537,453509943194561977307450095757721916549011⟩
def resval0Tail24 : Box := ⟨33765472385405167894682824109218448072,7254255922429450053470095840014275489920265⟩
def resval0Tail28 : Box := ⟨3998612057616344970047369649747224307,116067977731048090603913887929902235917693699⟩
def resval0Tail32 : Box := ⟨1183036114980220454476460126772850038,1857087624517861361842339648302364143124245311⟩
def resval0Tail36 : Box := ⟨220470477425954045439737835728507895,29713401984455459218827970972858700287785281300⟩
def resval0Tail40 : Box := ⟨-160785044400974108356159801014190105330,475414431596212445689548090705616883586216233855⟩
def resval0Tail44 : Box := ⟨-41535132127898103628069904224050568354626,7606630866588773681086321713885735339539797633150⟩
def resval0Tail48 : Box := ⟨-10634546858805001115035012354297239442886194,121706083895448108189292637142178582759135533804188⟩
def resval0Tail52 : Box := ⟨-2722459560040770028460860979932190374474862940,1947294790019469702663623908716677789413293434068881⟩
def resval0Tail56 : Box := ⟨-696949984175430639155162737454213734837196759217,31156063249565469287711388279590644863387734396615361⟩
def resval0Tail60 : Box := ⟨-178419181358186951697238538703845108563826788524914,498329743971377685713556877646523631160554337322412218⟩
def resval0Tail64 : Box := ⟨-45675217862707134895559376774458230911431225907316647,7930455325807616316411028667499540214121455992050795316⟩
def resval0Tail68 : Box := ⟨-11690779957807982829441936890671023207978040569001085736,115926117865090052320138814582439375089815529892228823602⟩
def resval0Tail72 : Box := ⟨984317840413601131277729407202396480641074664877889439737,2900285121405092399286201539901788395568382960726601434⟩
def resval0Tail76 : Box := ⟨-38136439983808027367116381132054698133727102903285,797961023376769820637156114022277959734580456101⟩
def resval0Tail80 : Box := ⟨-2332568847464549728914497484261078867679656189,104484801580002240454081257002665009679396343⟩
def resval0Tail84 : Box := ⟨-1491404966292379014295926571232552568315983,105648118756998726854352898625273763561466⟩
def resval0Tail88 : Box := ⟨-4658194923973909470505273788425967239418,689233308758132311406369103107164631704⟩
def resval0Tail92 : Box := ⟨-52288428960058228975647789697925865602,3366946987037769800328380827484987853199⟩
def resval0Tail96 : Box := ⟨-1770350529706452780934040964406203073,53750832040019810288919558230759425502799⟩
def resval0Tail100 : Box := ⟨-162353439959093796789924715765789978,860007694582392399848389021441869853796890⟩
def resval0Tail104 : Box := ⟨-37779818250034964861336706850031902,13760122401674225297083413491565335841235435⟩
def resval0Tail108 : Box := ⟨-23807294742420585043453203848733268,220161958193695517032041778665163602926936018⟩
def resval0Tail112 : Box := ⟨-619296101646552889116423718643192912,3522591330478664944192393454645329384934363047⟩
def resval0Tail116 : Box := ⟨-151063990248152958512848363886531070682,56361461146157027175064730959434660443121968360⟩
def resval0Tail120 : Box := ⟨-38647791755195404862264890734335034379863,901783342106927121203101351068793405517246772987⟩
def resval0Tail124 : Box := ⟨-9893638564902454736169248813483704241601192,14428524198437768687163114610472975047283393487695⟩
def resval0Tail128 : Box := ⟨-2532767878475792114061281719034562583393372022,230854012705901835336420811137499880474306037724179⟩
def resval0Tail132 : Box := ⟨-648388551422344659000057336657260166023485496404,3693056339198265187270821482927412328005004007944507⟩
def resval0Tail136 : Box := ⟨-165987731775585918030841762929810361703026631020410,58933288107782945642037530048788946180489385829586989⟩
def resval0Tail140 : Box := ⟨-42496208066890382781596958525223978641135574159471914,903094092578687258222279429986685307003874220279527819⟩
def resval0Tail144 : Box := ⟨-12023963834741797936576381070981815268334488480645048593,3701315227213284624075445117548250507321014678638892227⟩
def resval0Tail148 : Box := ⟨108533264500822307864158651856259080709701310,1813670847672981018975193890875251279481562⟩
def resval0Tail152 : Box := ⟨2191508142288763583779633309552488107485,86883959856186652560749829168335392965⟩
def resval0Tail156 : Box := ⟨787813177144234021544710546796456498,50587963208747787924646963219686193⟩
def resval0Tail160 : Box := ⟨1559372471428023588787718420873205,149141939779336664543902193626086⟩
def resval0Tail164 : Box := ⟨11747359783664767818722971341158,50476551818413451039153061517039⟩
def resval0Tail168 : Box := ⟨275579751247463544543543601871,783030897368661893402073542052823⟩
def resval0Tail172 : Box := ⟨17810471876724432138344530804,12527702795215071660542343096368633⟩
def resval0Tail176 : Box := ⟨2939773458974875433958362781,200443174715547266804544170141172592⟩
def resval0Tail180 : Box := ⟨1196724513506725465615037525,3207090779455385073089730351958190691⟩
def resval0Tail184 : Box := ⟨3978529562405217921707920728,51313452461248988425400698791270281587⟩
def resval0Tail188 : Box := ⟨727935144860019905437048384596,821015238701322298857653129642917950016⟩
def resval0Tail192 : Box := ⟨185687175298152531335617026756064,13136243645153870049491736159879886414147⟩
def resval0Tail196 : Box := ⟨47532276873204684572524346213110012,210179853761113370700783146288882088030074⟩
def resval0Tail200 : Box := ⟨12168215460123129171945433373734878140,3362866252481510347960003734383593824491561⟩
def resval0Tail204 : Box := ⟨3115062025719698458735172598246995428269,53802939669732587287270459493766867902372728⟩
def resval0Tail208 : Box := ⟨797456189301628715555590366266675817176274,860099419868064346813487011312043886534248336⟩
def resval0Tail212 : Box := ⟨204150639549819462813171710024794238982145334,13570200505796055591209119940212972385863663891⟩
def resval0Tail216 : Box := ⟨52364994562009234280233583664908528393678917486,168079238824667145548207670768639041452148222096⟩
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
def polyval0Tail5 : Box := ⟨2450786121263610947624602929116860395069615176680198,59568727695881343785968763368376535291212192983398⟩
def polyval0Tail9 : Box := ⟨268768908684281060254360368840860492316813601019,12936247457479606244753344451434043001208427284⟩
def polyval0Tail13 : Box := ⟨238966431294135579218059746432224773792988812,17861335952280284395703047301410282270947306⟩
def polyval0Tail17 : Box := ⟨945828746489714990667141920965725323589906,510552401652732834041759567206340011197739⟩
def polyval0Tail21 : Box := ⟨12746680944369343755934321280376524398124,6543820971760761672224774423889453038988852⟩
def polyval0Tail25 : Box := ⟨499916021966879631083936223847404245511,104670654074946549626090792754618456982702651⟩
def polyval0Tail29 : Box := ⟨51776384978795916225457159324630786954,1674728822000363394513511644190461136868539124⟩
def polyval0Tail33 : Box := ⟨13372963574483979415644036198973740304,26795660917401454012512332479850941557156507138⟩
def polyval0Tail37 : Box := ⟨14461494804483909320563371048150475898,428730574591698271151378893872604525768794191064⟩
def polyval0Tail41 : Box := ⟨1589910163705375926733135804989131984133,6859689191999966243502979141322083358847155122348⟩
def polyval0Tail45 : Box := ⟨403906572881493948757210585842477510826768,109755026693389730780041228238301033091891360859980⟩
def polyval0Tail49 : Box := ⟨103389165910947477726500803884152426574330392,1756080330167228137916042969538136008684717001138286⟩
def polyval0Tail53 : Box := ⟨26467534548352401023427947475444120504262000972,28097260469368467699029546034745559696304461884345762⟩
def polyval0Tail57 : Box := ⟨6775687093012356127712509632113493607877252786436,449549815303648296048259768195523042404172334878605885⟩
def polyval0Tail61 : Box := ⟨1734575886272624880540806409830107300870672965714206,7191170880054818883291397365258160707014025060034125323⟩
def polyval0Tail65 : Box := ⟨444051562418262789096242735489136894902798892829468407,114642435834311087691772632624499198517419883013224304420⟩
def polyval0Tail69 : Box := ⟨113678759625638121419551904834609202341876170236256292844,1727705925541319824919775663131163192951376900050280683116⟩
def polyval0Tail73 : Box := ⟨29843750000000000000000000000000000000000000000000000000000,2⟩
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
def resval1 : Box := ⟨133108270711744937963008004103722096172683767682698514415,219373098949965058354762844829856469862570403090662069⟩
def polyval1 : Box := ⟨3907636488972191859494326558682032181908692372385265075463,8331662165774270973572863965981577886343360558570731527⟩
theorem cell1_lo : Holds Q cell1 (1/2:ℝ) := by norm_num [Holds,Q,cell1]
theorem cell1_hi : Holds Q cell1 (3/4:ℝ) := by norm_num [Holds,Q,cell1]
def resval1Tail4 : Box := ⟨75265621268115722334718663367840205975811547744170,3614815811905640337003806493838365408500630229044⟩
def resval1Tail8 : Box := ⟨10009602344981954059243503384269518691074041413,7203126815566248630353078996890111572639570704849⟩
def resval1Tail12 : Box := ⟨-358244109846223491293342452374108258732475826,22764279085861704656284969334501992511871320648509⟩
def resval1Tail16 : Box := ⟨-2413922876197443656637444969679529901070850400,71945112425569115709827182266285841171680930688555⟩
def resval1Tail20 : Box := ⟨-15820175555453901698929550175793154558885073846,227373892860483992584398986987560602061134974658320⟩
def resval1Tail24 : Box := ⟨-103679106835111185771696916407370487010011094046,718560105305286203033976369565954871136404795033874⟩
def resval1Tail28 : Box := ⟨-679471394739593696655749158935233340078618225677,2270652983043649416011529166555319419288013117983972⟩
def resval1Tail32 : Box := ⟨-4452983732586039326214060686073369299199169121084,7174079217949244357492869976440785762826963853665381⟩
def resval1Tail36 : Box := ⟨-29183074189881388473533911054698152392338262010807,22658523637298374631015745518933956689325850562630412⟩
def resval1Tail40 : Box := ⟨-191254195010809858602476485626534466766014721187194,71513102819075530791891499781488285779379091175580042⟩
def resval1Tail44 : Box := ⟨-1253403492422846196642847129849047943837705416484056,225367774231109290521298164841767658712168801348333858⟩
def resval1Tail48 : Box := ⟨-8214305127942348223245297543648513681693829271219915,708020528171122148583899312997511565978711559573072023⟩
def resval1Tail52 : Box := ⟨-53833270086481997204820136164263987236730999109535357,2209822499352535545266024332483740902879728581637972561⟩
def resval1Tail56 : Box := ⟨-352801718838668533881525177719140566998929015962294869,6801468367289486720310743200134914435858539196180475631⟩
def resval1Tail60 : Box := ⟨-2312121344548124742351292205553548361828700426943448605,20298905100468638502681994496592113632170183448979438090⟩
def resval1Tail64 : Box := ⟨-15152718389618922251498806979331053014271974566269174629,56309291067796426618011870870024699862809888910311330997⟩
def resval1Tail68 : Box := ⟨-99303900959119836502260657734984260004789093798140218652,126550515122364936453102762370117956050230046815798750514⟩
def resval1Tail72 : Box := ⟨987989718712228395024109386349323201409161232570549654699,1675071201821588255272382738719274914913090338475537663⟩
def resval1Tail76 : Box := ⟨-37260347745293157951724699259537598182229197851812,504135823226248738921796580423120258352489783175⟩
def resval1Tail80 : Box := ⟨-2226297688359787549733800042768870866148345134,80143625253196762400984784936745119016510925999⟩
def resval1Tail84 : Box := ⟨-4781034647639368315463143612976015105919010,253094954476776704675665092867970425512267212959⟩
def resval1Tail88 : Box := ⟨-22228213311816450735818880164902506855591938,799893569186636281588449015277467091069357832498⟩
def resval1Tail92 : Box := ⟨-145647128484211036769139185134112897705331122,2527983279599813798509456467396862684524919878476⟩
def resval1Tail96 : Box := ⟨-954512719842365717878340055525841681022833211,7989181354327651319526333374859223735901602099136⟩
def resval1Tail100 : Box := ⟨-6255494550937741606512298928395051253809557305,25246519591421688780388262820252586283685735861722⟩
def resval1Tail104 : Box := ⟨-40996009088171696822424709317752217049557466132,79770243768800225438472119577074164672416561414018⟩
def resval1Tail108 : Box := ⟨-268671445160059989102104155990556724865253799459,251974259210882199746607206141037554530245332429229⟩
def resval1Tail112 : Box := ⟨-1760765183000882192661073208226014110584533474244,795451460100293138453145697233520321804221630638622⟩
def resval1Tail116 : Box := ⟨-11539350703314508141707955254270974624892256017410,2508044966241417198336761384930918204125365408071490⟩
def resval1Tail120 : Box := ⟨-75624288769242065217561014924252360189452036908512,7887506391944971954034900545707584371734927286903101⟩
def resval1Tail124 : Box := ⟨-495611338878113199426015692119660559029589673697587,24671814022391509514660175415827864239670068813408993⟩
def resval1Tail128 : Box := ⟨-3248038470472287044557690393393243210089232207804580,76293454029343408589269246570346476960351026447799509⟩
def resval1Tail132 : Box := ⟨-21286344920249955518332123264834884957099934869733753,230104051128687284955503466916253330643176834201079619⟩
def resval1Tail136 : Box := ⟨-139502190241978379649697874819756644546661345347373858,655015604822110838627821914512115015636759606987693612⟩
def resval1Tail140 : Box := ⟨-914243148015902000068295569606423086741803198629180859,1596826761058109474908873856583178774075278500726609190⟩
def resval1Tail144 : Box := ⟨-6478060991269742802793373953687930371396444597175725568,1862535902218261101671256760273025330099185809129878282⟩
def resval1Tail148 : Box := ⟨106874831957065110204623585414426549083312855,1226489138133334817434710885951864481660447⟩
def resval1Tail152 : Box := ⟨2105271185989918161297226287099290446161,5146659272942510105483489569764359602524⟩
def resval1Tail156 : Box := ⟨936074820528504870764591965587940103,16095296615072109234140905151115228017964⟩
def resval1Tail160 : Box := ⟨1288394563028696565396015009318729197,50868430793070365365628655549093141654868⟩
def resval1Tail164 : Box := ⟨8434269173264552694184931685450666739,160764994737535702429059503819920717583207⟩
def resval1Tail168 : Box := ⟨55274757985831410827386125197968204419,508068155156478221572778183010375760112361⟩
def resval1Tail172 : Box := ⟨362248652384327252106322370053161825122,1605558715027159923767731848061456161693366⟩
def resval1Tail176 : Box := ⟨2374032768170135945114453973595809123856,5073129259848615957149054194170240936847219⟩
def resval1Tail180 : Box := ⟨15558461149465058693960494328558858691293,16025538364898642220501451462684360027171219⟩
def resval1Tail184 : Box := ⟨101963930989128975702059484467107924858338,50595823568619701648403727989220519674927487⟩
def resval1Tail188 : Box := ⟨668230818130351910174705101839624417260456,159561813625077802909062922125800531066942672⟩
def resval1Tail192 : Box := ⟨4379317489699072099453974365299346544558371,502026748898711888475695693043042447709894000⟩
def resval1Tail196 : Box := ⟨28700295100491914623796424502926180572227404,1571792951756708240087905861443925785625513700⟩
def resval1Tail200 : Box := ⟨188090253970588392985248872716952968550844321,4870258773133653177584303165664953721301409903⟩
def resval1Tail204 : Box := ⟨1232668288422283201091217671678217099367054969,14754212587364497955295246887638797736743039127⟩
def resval1Tail208 : Box := ⟨8078414895324170611458172595701433829359688858,42448023428416623338575961755862510695006077853⟩
def resval1Tail212 : Box := ⟨52942700832760845434513375691995260103502133050,106745796404938306499392373174987446664245561749⟩
def resval1Tail216 : Box := ⟨347010815180946315010891458990142283627727157986,157721280249719498516101355091701673938706011839⟩
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
def polyval1Tail5 : Box := ⟨2382766200101745331022006110219443461080683603058941,128837519089000478063309300349760182610890111844392⟩
def polyval1Tail9 : Box := ⟨257887506148767875445953824697955191824810582057,298546198219421817666663956921387932699399803435300⟩
def polyval1Tail13 : Box := ⟨16936917553567625860965502133921438135726470773,943524461532278735521856936863505084990774396999757⟩
def polyval1Tail17 : Box := ⟨109545482243764480001848525294551837397612720047,2981946526873189604587865478942044851426701017734531⟩
def polyval1Tail21 : Box := ⟨717911676231241117080355454294514042447602559300,9424051894587192617034077584946155239883102558577818⟩
def polyval1Tail25 : Box := ⟨4704905888247234699184371006901457471122701129687,29782221889181266130637373603437645275361491675227913⟩
def polyval1Tail29 : Box := ⟨30834071226460132108821990221045535133107111437662,94110564194670951183045174331364424259497442351114398⟩
def polyval1Tail33 : Box := ⟨202074169189458942660344681679054592833955161656035,297331233930436802200185593353930371173944921772149066⟩
def polyval1Tail37 : Box := ⟨1324313275199974576644098969980908556909845216726782,939027870348310155805164501141740806834998887269622436⟩
def polyval1Tail41 : Box := ⟨8679019480350520619701897508907180280847151353429663,2963298252218644446569133937270807699640911906986537306⟩
def polyval1Tail45 : Box := ⟨56878822066425143472530554101682932202685228845123794,9336036999599534255318405031946552594208609328148147243⟩
def polyval1Tail49 : Box := ⟨372761048294523881447299479046084560274344794559210273,29313491425118878777995295766711509480881606190554903458⟩
def polyval1Tail53 : Box := ⟨2442926806102995935906610332856653836501048868019958445,91380290887648009082750361702887459458167339108588764305⟩
def polyval1Tail57 : Box := ⟨16009965116476946278892917828318400912288215378388357353,280517735248958633526144281778813287389581940852860778113⟩
def polyval1Tail61 : Box := ⟨104922907387428753411148289593745246160821115937516568927,832251059199698942188592378956446612250707247395439282667⟩
def polyval1Tail65 : Box := ⟨687622765943838660675460774909805136272806578468966343838,2274309770505177061580602362554742779738294795245910830364⟩
def polyval1Tail69 : Box := ⟨4506405306735575698350659192045112071859648661116188105900,4854764813398713468950207197502567180133410493759091260638⟩
def polyval1Tail73 : Box := ⟨29843750000000000000000000000000000000000000000000000000000,2⟩
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
def resval2 : Box := ⟨132973874071106471906783120484856393549847310460834496722,194780464022311598542728550607622388171978258102278335⟩
def polyval2 : Box := ⟨3898079394747542870674780691134258893368390150404504663848,7007233630739770590006210726833220628950512455728886676⟩
theorem cell2_lo : Holds Q cell2 (3/4:ℝ) := by norm_num [Holds,Q,cell2]
theorem cell2_hi : Holds Q cell2 (7/8:ℝ) := by norm_num [Holds,Q,cell2]
def resval2Tail4 : Box := ⟨-130067134199263024042052642433200349169757412080722,37440299372236272180068640471500633643727854118928970⟩
def resval2Tail8 : Box := ⟨-468624787930284494504772621682060694988912210487398,63749839079893048740301498929787194845701716268394718⟩
def resval2Tail12 : Box := ⟨-1075327788845804222967457235206578352174371147231268,108478552828155823284657545022827382064772231605368089⟩
def resval2Tail16 : Box := ⟨-2467444508485811310576048885535237251820861282623781,184426639225737217849616930652974487538853069912665374⟩
def resval2Tail20 : Box := ⟨-5661792069986550835154486668394079485116451877784454,313171263729906316049174378143828972220190435595915569⟩
def resval2Tail24 : Box := ⟨-12991534088396021572397955059204854365498757857993612,530923583177894500150718970927795484836831009218797160⟩
def resval2Tail28 : Box := ⟨-29810342005431299208666012353191689204482856898754665,898084835138561233744525490066726605973848417772109026⟩
def resval2Tail32 : Box := ⟨-68402737077411358109026722977227126872147027150140960,1514545470161986152993239453159801656947129011886231107⟩
def resval2Tail36 : Box := ⟨-156956751412948804466552069763959161822256818654731181,2543483005710154988586119410443238172615799048140693585⟩
def resval2Tail40 : Box := ⟨-360152573810406248394211198403151640859545410954878951,4246678432093897431735512387296074256532432233790182106⟩
def resval2Tail44 : Box := ⟨-826405205603402676647293998698786894814204913404565415,7032645106843089563019031357865850933845844933424104720⟩
def resval2Tail48 : Box := ⟨-1896267341984685303471068585877254902129785596834591933,11510925527561683763214651817322347496415607401355173770⟩
def resval2Tail52 : Box := ⟨-4351170355530559430418843274661734693497772434401449687,18520908775523970014330302027284301230417112431545324003⟩
def resval2Tail56 : Box := ⟨-9984184742132567082415293026925239928042312275628587886,29034572492685900738180692701841856488134968805069832648⟩
def resval2Tail60 : Box := ⟨-22909685629341455151920019906133307473643785038693366611,43654591602541998464631287276673269809432405434946519795⟩
def resval2Tail64 : Box := ⟨-52568507971215545314836287923939129104612618873000788754,60987210246747387023562222029450737422329313581208197453⟩
def resval2Tail68 : Box := ⟨-120622818261311715624983738827340654313241002457331224907,73097510035017109364178710178506710607759450226899624950⟩
def resval2Tail72 : Box := ⟨989823418024931776608769418455165791474562554169286592204,1062999759134206041654964409165614448277009683718234908⟩
def resval2Tail76 : Box := ⟨-39289208724512073866841101884894548504640273733924,485724308098900280191870663335988984398811630592012⟩
def resval2Tail80 : Box := ⟨-5620088979090714479914200515941538234918432261692,827139277024187075789364212621628735713406637994593⟩
def resval2Tail84 : Box := ⟨-12890849788673961195012848400322615096075428456267,1407756142789596577024480457812986047035709206305847⟩
def resval2Tail88 : Box := ⟨-29579308979048179582901308602806318121369719744337,2393981738950338662353632726206017066170072604205437⟩
def resval2Tail92 : Box := ⟨-67872609256917445374554637577625601667737639206015,4066615542472430541469604534461506319672711741520787⟩
def resval2Tail96 : Box := ⟨-155740321426368753928723875414767960566364507307568,6897513934918167420430898015129504827723110151859039⟩
def resval2Tail100 : Box := ⟨-357361356570092545656770097514304662040546169286196,11675179015769438698140772107026971926920911376194611⟩
def resval2Tail104 : Box := ⟨-820000485423394758670326422819868386547040354948237,19706982173928008618586680288365700642090688261187856⟩
def resval2Tail108 : Box := ⟨-1881571086891481303919548596978889694934095653324535,33136555099157393392809473781941361936737235854149666⟩
def resval2Tail112 : Box := ⟨-4317448364921400452024142794342347609570004725977576,55421928918733822677400243729391088925960473935510070⟩
def resval2Tail116 : Box := ⟨-9906806345838342512676010872952940607134502806388286,92005933909826711206882286035291025493612330606997696⟩
def resval2Tail120 : Box := ⟨-22732133352503820761956833312143035258939870860438117,151126502252329190806859813467547921559045698693359228⟩
def resval2Tail124 : Box := ⟨-52161096999043824041539516179456470325828817583993091,244434059784544695252358011837569441835069280192708083⟩
def resval2Tail128 : Box := ⟨-119688724236873833366562575966485446645139517660611548,386289519072405588965037306223593130719007982592580310⟩
def resval2Tail132 : Box := ⟨-274637450775240592836748211661939142390189725620590135,588539094245627193121781552848896978768815064128228334⟩
def resval2Tail136 : Box := ⟨-630182415811354663126787163699278209673956360260333616,842358662368556670114713480417815826626301497846357317⟩
def resval2Tail140 : Box := ⟨-1446016272261065264332810043838818947699336978591422791,1066074946721740483009165211478284366003837606824038685⟩
def resval2Tail144 : Box := ⟨-3695892804970533207819376016847819578057641917249346734,938031690622852349952307011049315618396285823371751892⟩
def resval2Tail148 : Box := ⟨106509575257309740282480683640826155971562134,79091381313248141608023465060030247600918490⟩
def resval2Tail152 : Box := ⟨1005043700062261834823658740116431987745441,133194970376766171725819051467692329579773901⟩
def resval2Tail156 : Box := ⟨2301433371748234946472618065194446552371796,226634329680532859781981454376503911628010861⟩
def resval2Tail160 : Box := ⟨5280861679876660845051362034397519827338335,385273441738179344876197630671590669046627844⟩
def resval2Tail164 : Box := ⟨12117452153733275912684166476261526064683218,654150947177675148648461372785725513998892737⟩
def resval2Tail168 : Box := ⟨27804675758776587133571325653779163270501201,1108819798902367978004313961370177787370171594⟩
def resval2Tail172 : Box := ⟨63800540265647845371032086452552208988478238,1875230633500302688552501931208467062351930720⟩
def resval2Tail176 : Box := ⟨146396561984856844880592625574560524244364839,3161505015585044584961766240449457575297449479⟩
def resval2Tail180 : Box := ⟨335921189252462381100785504859724032212159020,5307212863944670583935367388353872811717300952⟩
def resval2Tail184 : Box := ⟨770803930494358550986551529822794159189112163,8856133629645356827083710266005125900474126889⟩
def resval2Tail188 : Box := ⟨1768684793560389411963485941518301898786113479,14654445671384331199727763478816593621496814795⟩
def resval2Tail192 : Box := ⟨4058419755287758854688965517629568369034482785,23958715765084409257166411293477304871092566171⟩
def resval2Tail196 : Box := ⟨9312439938466390084842091845249594073775649336,38483556351181423659683190266382758452848079232⟩
def resval2Tail200 : Box := ⟨21368301663363799061233062915312286296791496205,60169557896152008670699162757468401767857673695⟩
def resval2Tail204 : Box := ⟨49031652176402277919846578604221922472666301624,90068336476566450982559594164819308429486871452⟩
def resval2Tail208 : Box := ⟨112507907882783391234375881592511521842305756109,124790531735345651782399211726679148065818402956⟩
def resval2Tail212 : Box := ⟨258160368096405219540286789690059656647014011798,146660294281974922546808811832373282074606173067⟩
def resval2Tail216 : Box := ⟨592409763136210242381942807821228654942091990233,98228930216299322312706212363920651029806326572⟩
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
def polyval2Tail5 : Box := ⟨24194120789758116894891319928472124957314887726824324,3352274047180147247216453994174037286958872310989576466⟩
def polyval2Tail9 : Box := ⟨50122748944978283515009546734341227323825545536168990,5705975222143269387107621402172472135595388069759234058⟩
def polyval2Tail13 : Box := ⟨115010964326834618632726114833705614400751701612976347,9704637627141712629457346061428436606296536532063753481⟩
def polyval2Tail17 : Box := ⟨263903873958095199254029528046562486145860143418977995,16487983102209099687344752967667527418785589385549950713⟩
def polyval2Tail21 : Box := ⟨605553176837802888832584474924685607151840442833599749,27972426437646781715213022526157020250416450189425934940⟩
def polyval2Tail25 : Box := ⟨1389500822703741726658997485662398224786913602279570335,47363270731202470507682583144512746435480610143158830211⟩
def polyval2Tail29 : Box := ⟨3188345153065802766412633445876820781599591937780346176,79981730767300646103300195792817172732790134199577094350⟩
def polyval2Tail33 : Box := ⟨7315968906947251419398888877895647176295515760452902130,134568508798101051131561196132590512787288440991817636771⟩
def polyval2Tail37 : Box := ⟨16787204169521202638190925795460118408614749550138388174,225261450840840249764747959416965043439026939249472673970⟩
def polyval2Tail41 : Box := ⟨38519877191055689084794372161355316707598545062795960019,374404442226870387147825031335521626980139167667714214303⟩
def polyval2Tail45 : Box := ⟨88387614985225504713079299809408294930685459734568158963,616043044046771666578173865753387856037790491658009577509⟩
def polyval2Tail49 : Box := ⟨202814002859554591282274428570645175427864793852220088592,998913602053007013867840423261319086716134132992504782263⟩
def polyval2Tail53 : Box := ⟨465376509625145121794321396478257989107231305422640200687,1584717730159049940410841850028390837990818672187270933726⟩
def polyval2Tail57 : Box := ⟨1067851788620619714876398059882286697230005201996252745820,2429518476334009044860230017593865911766233358214869418777⟩
def polyval2Tail61 : Box := ⟨2450290074543712422277602456446103225325442157272479763854,3516069194616768393552136053126401134327992070042704923202⟩
def polyval2Tail65 : Box := ⟨5622429548242846451779019130158823808405446654816268072851,4555915960561692624073651577715458493125609302579045885250⟩
def polyval2Tail69 : Box := ⟨12901213534344681679216577608874476083573319791445230554456,4462595088607768773404219801018830207851434710497691081382⟩
def polyval2Tail73 : Box := ⟨29843750000000000000000000000000000000000000000000000000000,2⟩
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
def resval3 : Box := ⟨132784804729276625452981996630917340343913193821209990069,1718630189929226642686460464254370750838096769074496290⟩
def polyval3 : Box := ⟨3918061565714475353605107660299616281764213965591099925069,261229264152044518211514070247560973773176286588939706747⟩
theorem cell3_lo : Holds Q cell3 (7/8:ℝ) := by norm_num [Holds,Q,cell3]
theorem cell3_hi : Holds Q cell3 (15/16:ℝ) := by norm_num [Holds,Q,cell3]
def resval3Tail4 : Box := ⟨-181619137385692478207507893922280332429376025208028529,2009817196771308706006940640852080137880589772843588467⟩
def resval3Tail8 : Box := ⟨-269367719089257249907117241537171818977230755523211718,2567624933202574935948585564141225671313661662700661677⟩
def resval3Tail12 : Box := ⟨-399349813678878323297725436734879991113711085709566448,3273245763307138907557781629020443706778939042401057318⟩
def resval3Tail16 : Box := ⟨-592054120269240892989973310858344220925195544684725504,4162261410278230828563925897619868052146902962436087127⟩
def resval3Tail20 : Box := ⟨-877746950950870371654136837994544193708700043213198340,5276896458628620018011377883928857693887684293666023227⟩
def resval3Tail24 : Box := ⟨-1301299464908940674710589720906123232959070862376164622,6666121976872817722317503339164688654530101159932150594⟩
def resval3Tail28 : Box := ⟨-1929235180524229269541164148552444580816159314807523601,8384896801868053589667598814444093345502169166589698568⟩
def resval3Tail32 : Box := ⟨-2860178215805845531002168203710543484737828016257768695,10491860373785475942442150499472740408390957553497137993⟩
def resval3Tail36 : Box := ⟨-4240343276317093607745946703748916486396145202510641217,13044381681854893436240870551801253129714622162807864207⟩
def resval3Tail40 : Box := ⟨-6286500261292856370772304246297116279769658831350877881,16089237711225846698807265721826905027092502008495669148⟩
def resval3Tail44 : Box := ⟨-9320020328533380877235795734186909827732922309491676839,19646228832295966761744085708945850898305678960295043655⟩
def resval3Tail48 : Box := ⟨-13817350722007544900412283920731899208144655008620674069,23680567401530472385647784213218245322222446356002273212⟩
def resval3Tail52 : Box := ⟨-20484845981554407278257737805745511806823268225992031660,28057644134873986798972267510152879595522083764806374189⟩
def resval3Tail56 : Box := ⟨-30369708588176886801443864581254109789164582345596885063,32470402666544041510897467310917348298581065831929975199⟩
def resval3Tail60 : Box := ⟨-45024463477088266090093412524230623928285360853890406557,36324465534034889702037416866629754542652934619995089873⟩
def resval3Tail64 : Box := ⟨-66750798886212872951777674521186424736955121508956720190,38558503033379650276452831455091287749994447180894414878⟩
def resval3Tail68 : Box := ⟨-98960393898283348398636903209356838785309047866152667243,37365858758480083366418119085698380089387062811789165285⟩
def resval3Tail72 : Box := ⟨990738083388493657027998362133055497770080428251566597247,778311202391918600875745393740190902601537658543329082⟩
def resval3Tail76 : Box := ⟨-2467112157239684092278380750117221884666479282370953,28007563557907810418200426829773504722596355703890884⟩
def resval3Tail80 : Box := ⟨-3603293426099930759668784340570261642783180811578248,35799792424084386360720970962726538615509244251943647⟩
def resval3Tail84 : Box := ⟨-5342041920278624601664174063731904480033138218991238,45666757928855592836632001457846381205980101966017563⟩
def resval3Tail88 : Box := ⟨-7919818215410290430761095742329005899701616432998657,58113025376203590891053104352943628807210681154650882⟩
def resval3Tail92 : Box := ⟨-11741487902315961196212078012048478321812113750672957,73740555309925928343970792687333961894984350588797704⟩
def resval3Tail96 : Box := ⟨-17407285673811141090110108852567019100102321915904263,93252490799423065056117631884383986674111836138427508⟩
def resval3Tail100 : Box := ⟨-25807086550751666909522888570976234597080720593651396,117446229221097752281847035310268098337261220104418675⟩
def resval3Tail104 : Box := ⟨-38260170408990174731580997634735095214446530861245168,147186729391976215967096545775039718662467863619128827⟩
def resval3Tail108 : Box := ⟨-56722429199677753879542087955138797621751654306486146,183345679943159448681108286365323857888700377016709291⟩
def resval3Tail112 : Box := ⟨-84093561004015801993973579454698525566778926999196343,226683794073218349252210214729947602286501550408639194⟩
def resval3Tail116 : Box := ⟨-124672499082184978266365907954430048310198109701052478,277640681013451907409708569951200293793421530833758695⟩
def resval3Tail120 : Box := ⟨-184832605990548588229827929810641997692225410083236100,335977202814343440531345126910324613591889235851506342⟩
def resval3Tail124 : Box := ⟨-274022679329920473917763722746200797285246565826746156,400185550395262822870918066379287821960560209349024846⟩
def resval3Tail128 : Box := ⟨-406250987939801997145111692282535400111407886525117659,466537368470462481409789192436102667557154243218823232⟩
def resval3Tail132 : Box := ⟨-602285422526625682124277387102727576633167184750876086,527572507857749655457745771506136799362554055807569662⟩
def resval3Tail136 : Box := ⟨-892915318382903017256406883892702036690458982370616314,569729014095673327816741080978119875914850474596487001⟩
def resval3Tail140 : Box := ⟨-1323788392994024906993971506976792620744959803012140936,569661752488918098968381922414623995280977952097811192⟩
def resval3Tail144 : Box := ⟨-2302502565749620524372799653518734311486497266349106329,474499579969865774477534056407947186365159693918908053⟩
def resval3Tail148 : Box := ⟨1021679713317547201557870446310161052462270005,8950756120156722388541461761937208024154039377⟩
def resval3Tail152 : Box := ⟨1358016385437779392161143953713061309214079128,11414220105341751305550323637993410905788610673⟩
def resval3Tail156 : Box := ⟨2013317543005699124328969459858191391332261702,14520828741440156531531348350805314394063630148⟩
def resval3Tail160 : Box := ⟨2984834111525336726150878559387751918992603406,18419251041079262328042008927789807872053685475⟩
def resval3Tail164 : Box := ⟨4425151267071203522291018078946616770949582042,23283256131664715116031395548553575844790977450⟩
def resval3Tail168 : Box := ⟨6560486447423929497770898050996269099200199445,29309107375461137627595286656345545898748969091⟩
def resval3Tail172 : Box := ⟨9726217213659060653911206217201858128107267850,36708344776989744186043208149401260748111148881⟩
def resval3Tail176 : Box := ⟨14419555934670609236881471272265721899691772032,45691761687436256405965686638529693951500137919⟩
def resval3Tail180 : Box := ⟨21377642385067842554142766671615330679375744089,56438758833349847256419054598410385264189405231⟩
def resval3Tail184 : Box := ⟨31693319545647201145978016526036476738496060703,69042989990159647632312401167396426043081871785⟩
def resval3Tail188 : Box := ⟨46986776452211440133698339467703747304006611074,83420231582132019452523170900364091914742238969⟩
def resval3Tail192 : Box := ⟨69660016464678201526587206569879100789912247504,99156846321272079316955216862307816258394231853⟩
def resval3Tail196 : Box := ⟨103274117959433958944021793089249893284206651002,115265771809258141992278042473714344329133649289⟩
def resval3Tail200 : Box := ⟨153108540330408177018580372091121657272047060973,129799710847488232190671025122154806685641037247⟩
def resval3Tail204 : Box := ⟨226990320375492117964376995647400227113439149681,139245238127118106252066330549824306656261474194⟩
def resval3Tail208 : Box := ⟨336523393358822738980470005387163586242914037996,137582553545639369654954017469028314265064694726⟩
def resval3Tail212 : Box := ⟨498911117665520110245572708737202376653004341950,114837176061877465407030758574347870729643588257⟩
def resval3Tail216 : Box := ⟨739690371294581226480925594982531376765603702931,54860745009478025487780007331663516260200692464⟩
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
def polyval3Tail5 : Box := ⟨36693322319655236271650092977215088105811719799385827980,331329170604981513033492964173641265412014850540949406625⟩
def polyval3Tail9 : Box := ⟨54396045240468318186465213495086106718356754409580945268,422020128992424495970395069080003214486653281519381507059⟩
def polyval3Tail13 : Box := ⟨80644591436882173396539399503313026449085868348310269014,536094378998912033185501766887090735350604166664306439368⟩
def polyval3Tail17 : Box := ⟨119559246056800694029483407718487132250298583113099727837,678832954762287229539557049902875770309681474666452920754⟩
def polyval3Tail21 : Box := ⟨177251977634426789397562102986830379669925821017790477504,856297282076777033429040870287594476781383446575656759997⟩
def polyval3Tail25 : Box := ⟨262784055700629162368632977556055681002180184176099295414,1075185016584476083282431509205248317546107221205130248369⟩
def polyval3Tail29 : Box := ⟨389589221243526864403889269135365014963436400537262738265,1342462949053295996923192442908495980589859236237344311111⟩
def polyval3Tail33 : Box := ⟨577583601503012841198769205806888699219441859743321272487,1664624221362618428682834305632426599951028051401671540130⟩
def polyval3Tail37 : Box := ⟨856293753868155928078034328445438668192223238443407613375,2046330085723389966293578596728170770428777565549632836886⟩
def polyval3Tail41 : Box := ⟨1269494132114471434182485425411183291236268769626814867692,2488063516309657982775479574215923824204474610038800460871⟩
def polyval3Tail45 : Box := ⟨1882082339375812440288143988452485286492009566462359309853,2982219844271076359126501072398342249715437406282252990299⟩
def polyval3Tail49 : Box := ⟨2790272000935034173845538436530439685851275420314491326546,3506753340447336282771805014092637767853062568534964639989⟩
def polyval3Tail53 : Box := ⟨4136704158110361224136577754116921815624931028896845354885,4015036143575269006871472693239149924234869993405247613512⟩
def polyval3Tail57 : Box := ⟨6132850591624446773962031064633208164549664603193351032794,4419889209091987330272033720706078774865961923993670232488⟩
def polyval3Tail61 : Box := ⟨9092227759494800972901658179369168804993844831058457058123,4568697782821353689794479956871770653590806605447707989724⟩
def polyval3Tail65 : Box := ⟨13479637958868818654569520731538742738884362367312416769160,4204952981267125867570329996733775231458643109740613678141⟩
def polyval3Tail69 : Box := ⟨19984172105166572085263873291778083791923424973957594182267,2909208192749852449109943953628290517664903662015281371142⟩
def polyval3Tail73 : Box := ⟨29843750000000000000000000000000000000000000000000000000000,2⟩
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
def resval4 : Box := ⟨130000817322045259870491101042658692777955058363440924613,8133693424930553002353327417317115992201575738012732106⟩
def polyval4 : Box := ⟨4825564434857172762645436094450607124284797274842231737850,2080490886008759652614192803836463501499814807440375592169⟩
theorem cell4_lo : Holds Q cell4 (15/16:ℝ) := by norm_num [Holds,Q,cell4]
theorem cell4_hi : Holds Q cell4 (31/32:ℝ) := by norm_num [Holds,Q,cell4]
def resval4Tail4 : Box := ⟨-3481639602923769438848618534038303872718611054697163489,8859901441731125570118186036533588610940853264950293391⟩
def resval4Tail8 : Box := ⟨-4218844518800611443809525664631845016337000432596285623,9793960883921086444127917723296643641162894700487258631⟩
def resval4Tail12 : Box := ⟨-5112038042602582729146185665670397511969518345809348313,10798256848266659871262355111532389995572950411837021858⟩
def resval4Tail16 : Box := ⟨-6194334200509693790611556308178693803193706464184394145,11870391317911442023429691206773110252353994110053252024⟩
def resval4Tail20 : Box := ⟨-7505768906210834126487612180949195756712995916752894157,13005121073772297839686214454670637536830785939976493522⟩
def resval4Tail24 : Box := ⟨-9094854273249484475327691624113496230583147576193573263,14193438003429435833419621992593691362221264983025392679⟩
def resval4Tail28 : Box := ⟨-11020373166991418095772400012127198062898389579125310931,15421412523112949389188846005018499494862386081814708716⟩
def resval4Tail32 : Box := ⟨-13353553678914779649421438027782767142950681760836174826,16668743455407966927966005534678364279922648674996564248⟩
def resval4Tail36 : Box := ⟨-16180703970148718577416668652221578326882406142863753012,17906945623005750368444404427684706302339155928962329074⟩
def resval4Tail40 : Box := ⟨-19606404951439396400218186316952274472358372251118866115,19097090973170374713807809228494445022979718884407494404⟩
def resval4Tail44 : Box := ⟨-23757378901994343592584476539795601473881377098779555133,20187000210818050877024341799877203256189718726118172426⟩
def resval4Tail48 : Box := ⟨-28787177133740155820138432825220680668900602633088368317,21107758956068705387715950059840359070799874757555943559⟩
def resval4Tail52 : Box := ⟨-34881860105357231050867964611859713153953840207305317674,21769404462863107786328010121885711303867024145159713995⟩
def resval4Tail56 : Box := ⟨-42266880102794762404486517737710790742397707217614599969,22055594855420735202648292102863486130650329827042626629⟩
def resval4Tail60 : Box := ⟨-51215421087845594649464839842890966546072106932853766297,21817031343407218240689911101003296544561902894785625408⟩
def resval4Tail64 : Box := ⟨-62058504181789504641745709636200962814790970453157967548,20863353366902435205641193623946851127998678628579869497⟩
def resval4Tail68 : Box := ⟨-75196586329433255495815998436751651245120247791037715484,18953162921340993943937894630655029406255970112620841880⟩
def resval4Tail72 : Box := ⟨991157326128727871650218848980483203599845637757982289750,717564937822699147188281911543454122557607951214488968⟩
def resval4Tail76 : Box := ⟨-49006158532187406066079451556001335833175517043578930,127900850007982665624933890270063455489330814111586995⟩
def resval4Tail80 : Box := ⟨-59337240632735958903901193739135809871348315598986650,141483314506974966415741162907441197339685475748575388⟩
def resval4Tail84 : Box := ⟨-71899833823053675661322565774725740773333515433468614,156114052340528716481116939197171226730050469840230878⟩
def resval4Tail88 : Box := ⟨-87122121537544102188207581689729595100413407268661842,171767377127319558946486747828452883366802805580307719⟩
def resval4Tail92 : Box := ⟨-105567198945413593977728546772103930753763565082590511,188378813058649035342001312571661516354908527623695656⟩
def resval4Tail96 : Box := ⟨-127917379610395308572045382387222332477138723700970096,205832186975715815603065495009329143535314090912034812⟩
def resval4Tail100 : Box := ⟨-154999433250576683368822884653989731547990189773292480,223943531265225401011679278963793749405948893783439816⟩
def resval4Tail104 : Box := ⟨-187815169300478543688772726659480471623133182060834045,242440881141386542566015656038656004960498503002604732⟩
def resval4Tail108 : Box := ⟨-227578495479667680034017900965583702984096366261238275,260939002604435577679885891049319259786677340618746952⟩
def resval4Tail112 : Box := ⟨-275760322223648839833184794258819353890814537702895548,278907870563560825739803311820173870829725037217390436⟩
def resval4Tail116 : Box := ⟨-334142974065335351930387767925673355646167933292478148,295633452155661422711151264080115351265659963160893175⟩
def resval4Tail120 : Box := ⟨-404886120733043902275818813722127894778425267577066564,310169027878745016729525308908200513354544032989686818⟩
def resval4Tail124 : Box := ⟨-490606666864104246608607793108221616546298175233794232,321274890253443903143437261354928166444553892511519366⟩
def resval4Tail128 : Box := ⟨-594475555585184552532982552613076019138864919861856812,327343781101356030446663115255366966316267856844868711⟩
def resval4Tail132 : Box := ⟨-720335066882128263967294290144251704614830982197043031,326308845693255626848690338882690784234204236728438439⟩
def resval4Tail136 : Box := ⟨-872840949938775734310076783066805117884584216724112046,315530172515515460638364642726945423196004442160340145⟩
def resval4Tail140 : Box := ⟨-1057635733562212111313914134058074181459316160833007531,291655084165512582927093046747512769052129203346437241⟩
def resval4Tail144 : Box := ⟨-1605230640571869010387896261000430103807732533022349457,242413399909553887398550304704773547878475788482474502⟩
def resval4Tail148 : Box := ⟨31417759054103181559681446753828596678328748932,66731349963697103982451776946624548344115603604⟩
def resval4Tail152 : Box := ⟨37941564269400744349949590061372379344535564418,73377605051609435272641140186299800364026398750⟩
def resval4Tail156 : Box := ⟨45974367680565755892303938868063146221747955294,80418651142445999659847175092364878384329304986⟩
def resval4Tail160 : Box := ⟨55707840139757709328411460615618810890483480642,87800197148633749201859260970179166243745483014⟩
def resval4Tail164 : Box := ⟨67502036670662552029180410696222668037789163425,95438582663073167755889875374651132147737808837⟩
def resval4Tail168 : Box := ⟨81793243881944501643568526584103584785481328218,103211344923823050969978442092396961608398865004⟩
def resval4Tail172 : Box := ⟨99110116889834384250957085473030027730152123050,110946147896344291736855261181324774315560544539⟩
def resval4Tail176 : Box := ⟨120093235134362706361634503337107204910402208856,118406980783231036866491966310166795722631748553⟩
def resval4Tail180 : Box := ⟨145518798459984637043717661057065785573114208900,125276995469992891239359286556394100457033784215⟩
def resval4Tail184 : Box := ⟨176327340016661292900933864147331232523110871383,131137211862419005973317431981483931989962449822⟩
def resval4Tail188 : Box := ⟨213658518118543330798588865316542854064914757954,135440148778212133855503832025880700389630716969⟩
def resval4Tail192 : Box := ⟨258893274067982946377513304147256479190661246169,137477229407230132816217614180629701100580027659⟩
def resval4Tail196 : Box := ⟨313704915431698845673873788441490912022879912609,136338556294472004595001339595111614531518205996⟩
def resval4Tail200 : Box := ⟨380121014422984117488840118408735544654651233407,130863341545901624022460088200111283252009254647⟩
def resval4Tail204 : Box := ⟨460598411112299109955857242001647422056223199655,119578901633627354823650243521692894070229590638⟩
def resval4Tail208 : Box := ⟨558114095957842144072229988200589343707768932260,100625668368116720474867524445509655765461977764⟩
def resval4Tail212 : Box := ⟨676275334222506502272153363416538417295746675570,71665110784726382526209244210267605125998539862⟩
def resval4Tail216 : Box := ⟨819483724515112745341534580493827892061691148246,29765691420586497325585604217688475730720034236⟩
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
def polyval4Tail5 : Box := ⟨1132499808759391541591020110360330179712173528594345560532,2289797225797190139812455759597648524539219614028070148155⟩
def polyval4Tail9 : Box := ⟨1372264413335481139073410415002568570656690929226037819379,2513446998006620352308912828378768035061579486680868778705⟩
def polyval4Tail13 : Box := ⟨1662793648109896443506880309333939441189131887791747736448,2749086242657110734001633199127524336814058988996968405840⟩
def polyval4Tail17 : Box := ⟨2014832338300305058011885120131418577777802531969597143714,2994465087898649231519815539078153203526504133528892583905⟩
def polyval4Tail21 : Box := ⟨2441402970281781923241220032581714692842584040389777354262,3246208960550320278940489577676681991764103089939259905606⟩
def polyval4Tail25 : Box := ⟨2958285089035692091642352088921490880830120266721865659791,3499492663699981908337968712684841014854813179957421248236⟩
def polyval4Tail29 : Box := ⟨3584599009069296543642711090476150916863372484441484255776,3747633571297107793477979714163469769217222620494215324341⟩
def polyval4Tail33 : Box := ⟨4343513106104681332123307772370189700962653722253178000771,3981585197226031011361206487770273698055880011690953803875⟩
def polyval4Tail37 : Box := ⟨5263100853169493808293889885599314292428914172339006705802,4189308218755568021676267178996777609119229688862030102394⟩
def polyval4Tail41 : Box := ⟨6377379304255254861905648000201908111808438606488995643703,4354990934215655527162808972916391093780763538327685701959⟩
def polyval4Tail45 : Box := ⟨7727567440751351250780701293739421114916678780936845595775,4458084921430855035963145718992798531360979413398142912610⟩
def polyval4Tail49 : Box := ⟨9363610928946289519622648955199076190727433885840861437944,4472114096610865260260711441133005686144649323010996945479⟩
def polyval4Tail53 : Box := ⟨11346029691868666679655070137859483609475064616773133211055,4363206161348119006945926378977489507957959743652729356309⟩
def polyval4Tail57 : Box := ⟨13748156640170435905624021464283053904345468349839541706360,4088284213933200625734541718148700098918626637467881986299⟩
def polyval4Tail61 : Box := ⟨16658850376367499363092548827641945601635081675367638765984,3592842660426065709134998001015851477517535922221773665600⟩
def polyval4Tail65 : Box := ⟨20185782219864717770313887532721100144762267750829698607350,2808214968942840725017935880727813324722173987535169522181⟩
def polyval4Tail69 : Box := ⟨24459419655533236646443374193249981266503616644066433255560,1648220616538835421010937041616938938738090472083304329170⟩
def polyval4Tail73 : Box := ⟨29843750000000000000000000000000000000000000000000000000000,2⟩
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
def resval5 : Box := ⟨121002245655190864855400402514553880994978611426097421901,12041320860634453032411388298043001662315883264822428837⟩
def polyval5 : Box := ⟨9264042015126815119299119611768406967626556435029480855954,4166629544137535071477369459939611044220700912917962124387⟩
theorem cell5_lo : Holds Q cell5 (31/32:ℝ) := by norm_num [Holds,Q,cell5]
theorem cell5_hi : Holds Q cell5 (63/64:ℝ) := by norm_num [Holds,Q,cell5]
def resval5Tail4 : Box := ⟨-13035074463941443444811372248560658510929945825722075842,12274880434802405037200022930202868060682950091765333046⟩
def resval5Tail8 : Box := ⟨-14332296455727821989544156300124121441606254917609837807,12623385073005855776989476500829159836028263992931348934⟩
def resval5Tail12 : Box := ⟨-15758526616355982978591720199550515516177449479819245596,12949809016136935230351152080174120201686875611126556109⟩
def resval5Tail16 : Box := ⟨-17326683251311334507690328956444215583232541418946911225,13248263763855210005890394298624000892146295534678831133⟩
def resval5Tail20 : Box := ⟨-19050889705608525687556192962726824895429289574622754376,13512035465221583510966320557874624558591246322369043086⟩
def resval5Tail24 : Box := ⟨-20946674750794672144226916297933971428518334134677389839,13733486596830936178025318496518388834942046765298759576⟩
def resval5Tail28 : Box := ⟨-23031112451740689143770053046085741391297153095141530212,13903947429634369063213468829555864375494371315196100383⟩
def resval5Tail32 : Box := ⟨-25322975941305507367438220969623985113529645402079154861,14013595615163383057786213497488024953989630589884259182⟩
def resval5Tail36 : Box := ⟨-27842906497357304240419749772702104225343515003155335796,14051322638507043544561605676689778055438600797504248736⟩
def resval5Tail40 : Box := ⟨-30613599444924296227384219513343975021844013144142485244,14004585756314347699991038194479621307401197439396624394⟩
def resval5Tail44 : Box := ⟨-33660008557771163003561043760427807589735881560401355708,13859243895731654445829728776947759077829271984514129085⟩
def resval5Tail48 : Box := ⟨-37009570800309061537600971061720694344864106376929558393,13599375833339477579398383520814153850508811306534973130⟩
def resval5Tail52 : Box := ⟨-40692453433938934387083847169600180614280782600334582116,13207078800362565727065107000348300430078099152697985074⟩
def resval5Tail56 : Box := ⟨-44741825713349201498195672798603166845258579142118342779,12662245470083399202365964075178642525689819238493472218⟩
def resval5Tail60 : Box := ⟨-49194157619731104975907857961309562564180257487300060127,11942317073721225136327334671980976753731021537141566124⟩
def resval5Tail64 : Box := ⟨-54089548284574646472641890942554122847332917071230209446,11022010159356961599786616668190350322266410147645132461⟩
def resval5Tail68 : Box := ⟨-59471455344320457596227784415004243663905194627102899054,9873007151119908493749428389163978171005758638278957572⟩
def resval5Tail72 : Box := ⟨991256231028719302927271829377757073798529625429870067852,698747455989183625960548951223070396540552399056699742⟩
def resval5Tail76 : Box := ⟨-187484997238467578989745288439766926608146984662854423,179918598947304716103924130689316380188404964022932080⟩
def resval5Tail80 : Box := ⟨-206101822735531659993215420991782841634546085017294869,185151285752264815246027096994921043431867696840776403⟩
def resval5Tail84 : Box := ⟨-226611348257359317601056430858281138216910013000543338,190080972356907357009411477617893162465402406828789360⟩
def resval5Tail88 : Box := ⟨-249161812393529629283670166043204137716014743202354157,194623776135801975819954765009250887298424563634537524⟩
def resval5Tail92 : Box := ⟨-273956309924423845772960868966957324059035826397084391,198684146459849082436264252638697545481884300815262685⟩
def resval5Tail96 : Box := ⟨-301218148264509561668946441576304226619767397069860868,202153314858996248955371691626775930803858952237491931⟩
def resval5Tail100 : Box := ⟨-331192856513983416201578047934217808745173669844781012,204907738482670967715331702408334559006650180303145922⟩
def resval5Tail104 : Box := ⟨-364150396773473110751053184125521105704925081255594175,206807373006277494523747920590503829060137838287533062⟩
def resval5Tail108 : Box := ⟨-400387595511677678324408527146001185809003502349704931,207693756970128651962305621667807058135965164486247511⟩
def resval5Tail112 : Box := ⟨-440230816882363395713711501852750719115754786552939227,207387887700184664513653999744578959260824014142700045⟩
def resval5Tail116 : Box := ⟨-484038902067485558763019597983451157720951058187061436,205687866914015673752865777926367614932036868704656180⟩
def resval5Tail120 : Box := ⟨-532206401119128898891800458295173962607917746766092426,202366291861241343081202322833284782134668792753783312⟩
def resval5Tail124 : Box := ⟨-585167126407300212280921984572254993564929348702943218,197167365364332779946038149740756785375830185509313209⟩
def resval5Tail128 : Box := ⟨-643398059677095556653224972435011985224423373344069087,189803695389962467454977622923325772358046409485444710⟩
def resval5Tail132 : Box := ⟨-707423647903601368297715286091604390359666568396003216,179952751767603191785693851572957705876173395897190041⟩
def resval5Tail136 : Box := ⟨-777820526752920457393998623824968481743019480156571120,167252944348436787624301236713141829915373072831378540⟩
def resval5Tail140 : Box := ⟨-855223776456296531373875108996572521403924056183967088,151299252243487267019792980517115535025983527808136516⟩
def resval5Tail144 : Box := ⟨-1256450334655432545855684749423465409829641095272594525,126290283654487148198040115966352536351371128576088973⟩
def resval5Tail148 : Box := ⟨171718495873498399775501537118221793632248242301,129026368282241965720358047428597480365355127041⟩
def resval5Tail152 : Box := ⟨188690613653359517266020406517397664338486337805,131495748581076247828381894627059704376359397330⟩
def resval5Tail156 : Box := ⟨207467521531636047221063551573874296760255257941,133537304485411986798148786667032230284448096297⟩
def resval5Tail160 : Box := ⟨228112952309133143018523763218649826075750540910,135063952852920519825057331754589352241859676261⟩
def resval5Tail164 : Box := ⟨250812843510202591864008372041584479726007462020,135977765830813787230380272986418204935402076581⟩
def resval5Tail168 : Box := ⟨275771637835029999176123639288021702457784734138,136168034946858389296405478393066026682323663376⟩
def resval5Tail172 : Box := ⟨303214122410447382726959542414804381030405417533,135509801887407628642948471601498806857770669925⟩
def resval5Tail176 : Box := ⟨333387453296182322558201481878030557118875205187,133862230259357608140108631800186328751911007526⟩
def resval5Tail180 : Box := ⟨366563381453780602120977862802341022627028942405,131066801655473678006093723023766837563416517400⟩
def resval5Tail184 : Box := ⟨403040700225321119147060601235341941292361208214,126945317650525247552640791759716357428656359844⟩
def resval5Tail188 : Box := ⟨443147936364721673686444243654893272192506305344,121297687469612435116624225199073570883734708053⟩
def resval5Tail192 : Box := ⟨487246308857950391462541486418991826264953844665,113899478992560478185524438272947788898432729600⟩
def resval5Tail196 : Box := ⟨535732982180252682575830765411861222435303357165,104499208470012786362830240384296916638656712101⟩
def resval5Tail200 : Box := ⟨589044643290300432408778208063528764723437369831,92815341806640027682219181238195718084313175439⟩
def resval5Tail204 : Box := ⟨647661434576851981381494067829326872107769253477,78532977491340030935851628378892700802281119932⟩
def resval5Tail208 : Box := ⟨712111278179559115427705868910409674821148126594,61300178197718317258462194931751398002097632158⟩
def resval5Tail212 : Box := ⟨782974631288681349194771493530269679485057392202,40723914688349796754092982813297193454204438208⟩
def resval5Tail216 : Box := ⟨860919634110235170438087635450163097098661426249,16364742075026378610940059738644985015324133165⟩
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
def polyval5Tail5 : Box := ⟨5909091642719451188673693989365542087267031847930188828036,4250721206711967396695520897527566929027094992603896576041⟩
def polyval5Tail9 : Box := ⟨6497112416881263002619168473321524061862639721501879773013,4323287353408993155323963406319540683644808716626309898434⟩
def polyval5Tail13 : Box := ⟨7143650649060691033678192917876454047699141531292527857591,4380289780194699478147203464706476799535406826344282191037⟩
def polyval5Tail17 : Box := ⟨7854526953411571609717053387391487384295001459304991931473,4418698235982783030741763312226546787389178220654358219233⟩
def polyval5Tail21 : Box := ⟨8636143715956022362922747718973283534585286117902365081092,4435084608618004302558325945134564051204110995343575317188⟩
def polyval5Tail25 : Box := ⟨9495540434838279521562364524198267673410395743605198501668,4425577060894526087977472778580282847317401359206182029380⟩
def polyval5Tail29 : Box := ⟨10440457120121863575691409814142631824711204109628203053938,4385809204494083736767623394040764118308572205753153684022⟩
def polyval5Tail33 : Box := ⟨11479404002870719383563441558399124699147580566148435321340,4310863782443283812738474888000963145472454139120990364181⟩
def polyval5Tail37 : Box := ⟨12621738181094714846305326260236844622102194613680024126739,4195210285422447193831816119464000791072317217525641152205⟩
def polyval5Tail41 : Box := ⟨13877747892857939390293258804816089239212564292023461930517,4032635868241145109083686904492164380303788478235362001403⟩
def polyval5Tail45 : Box := ⟨15258745175541186983762925887707699542645074106239010181709,3816168867783857625216476764646052149817800835478098202335⟩
def polyval5Tail49 : Box := ⟨16777167745778477362424802670652080148071262848272668344270,3537994152121075084695825225377983972793693325656914721997⟩
def polyval5Tail53 : Box := ⟨18446691017631898201296462256499234786858058796027860792369,3189359451611994281505391793516617292829687450896228042941⟩
def polyval5Tail57 : Box := ⟨20282351267877366587497079556477361983526296004929731833122,2760471735963380875822065785354331620524520306504402493830⟩
def polyval5Tail61 : Box := ⟨22300681057668522662599571585088859662625338612482033663960,2240382605550473456705564446213721295753681233634349435046⟩
def polyval5Tail65 : Box := ⟨24519858130292419303741066222988598704316694482768445451778,1616861559962439077109979161715361447385510873289276412035⟩
def polyval5Tail69 : Box := ⟨26959869625067447493013808294243811183242724958148479189367,876255877325998008234511795825503474213526726134892163758⟩
def polyval5Tail73 : Box := ⟨29843750000000000000000000000000000000000000000000000000000,2⟩
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
def resval6 : Box := ⟨110137581827214764604184420226640695777694768053536874074,10252871846082705774164058322469344508549256231658850752⟩
def polyval6 : Box := ⟨16575957514133193357964618082799350269523026225710544468631,4170163353176849662849896542554960776996502429967131424182⟩
theorem cell6_lo : Holds Q cell6 (63/64:ℝ) := by norm_num [Holds,Q,cell6]
theorem cell6_hi : Holds Q cell6 (127/128:ℝ) := by norm_num [Holds,Q,cell6]
def resval6Tail4 : Box := ⟨-23808273615774397740442915422031454326908545972727860320,10073637616441644970200074644504798182462834717622539708⟩
def resval6Tail8 : Box := ⟨-24957841143317148599730097464990161515926196339664821010,10003962251653990212954592736350956574347519963312944894⟩
def resval6Tail12 : Box := ⟨-26162834430177171059172911126609658639784830792677635595,9913202359869304352938418112467342629786484393728999494⟩
def resval6Tail16 : Box := ⟨-27426006168872320664808753772651863459140530921264426588,9799774647467358190663964176427381664301582867459011584⟩
def resval6Tail20 : Box := ⟨-28750165291997381072846002700498412855611245794328430997,9662001916129748448552275056131378234758998599956280221⟩
def resval6Tail24 : Box := ⟨-30138256340629852414067330029307709803002656847242164250,9498107417721998721172211997066421887774686195477917232⟩
def resval6Tail28 : Box := ⟨-31593366021667539915797139809611680628963229839827564272,9306209455864795541949629342853571446621603710594307851⟩
def resval6Tail32 : Box := ⟨-33118730071767553539341947444103122773396197635352298763,9084315708129216365012136267701243856557063738937154434⟩
def resval6Tail36 : Box := ⟨-34717740452674540436860315455760242400232337857383970728,8830317254635544271916439399762861665100207714962216391⟩
def resval6Tail40 : Box := ⟨-36393952893947601284288917114938370547772159572885504109,8541982298259941142392271553675005610150212451197423206⟩
def resval6Tail44 : Box := ⟨-38151094799858737253281495999313689824670236320697424678,8216949560919308899814615071671421649988727121937769362⟩
def resval6Tail48 : Box := ⟨-39993073538045448451624366433057139274587213437703763621,7852721339634477789886216487792272041045911003890546459⟩
def resval6Tail52 : Box := ⟨-41923985128349012623740754607115851846644297470663363392,7446656205263833051250782313905378791558189659624311099⟩
def resval6Tail56 : Box := ⟨-43948123351159797567510950605719774870332729459304865701,6995961325951776999914704288131343199059620680581350205⟩
def resval6Tail60 : Box := ⟨-46069989295500994741251966243490915283119505787339207796,6497684396446314204803606795022423418978389193879933835⟩
def resval6Tail64 : Box := ⟨-48294301331641850291195147683581791096012095078385910859,5948705152641820017784032248529846170530987183845985972⟩
def resval6Tail68 : Box := ⟨-50625380847413886253517190657724355613829335633682577465,5345717050140704609332892890828557930885610797148423969⟩
def resval6Tail72 : Box := ⟨991211860158566645352672117533050580951328391247873280364,635436344767208953345018907903358101525280200125596576⟩
def resval6Tail76 : Box := ⟨-345270413453022151068652186626720949886858662603968924,148625539482436691350865494911920908245408301183916411⟩
def resval6Tail80 : Box := ⟨-361902249863802926900503483197755713407179590729427366,147696398003377418425016754831725736297898651440836245⟩
def resval6Tail84 : Box := ⟨-379375304512084543016822855604802434703501049678746635,146464260407359529984060565727133936961617694153155324⟩
def resval6Tail88 : Box := ⟨-397691980568650109176532002957393437058821297502021273,144906101978965795580602858933724944235704336028345315⟩
def resval6Tail92 : Box := ⟨-416893006814360221053010757025852951936729066025806980,142997687660464111667562910536984219527769149395610406⟩
def resval6Tail96 : Box := ⟨-437021080692167286779747651254362053897538366685225245,140713341603720557714223367236534162247346857289011388⟩
def resval6Tail100 : Box := ⟨-458120961128031784869539841980446470326929195100597716,138025868957517508128646334583773938974836905729536290⟩
def resval6Tail104 : Box := ⟨-480239568060345032740059335606498472934748747060169518,134906473625629745612162673354793985783513350978773675⟩
def resval6Tail108 : Box := ⟨-503426086776091060614213979670556895599873981310890387,131324671770457851101893552346457269955479725963402197⟩
def resval6Tail112 : Box := ⟨-527732077284482225708574164344062847641010066354901530,127248200847746353787480393379147598094573562310548919⟩
def resval6Tail116 : Box := ⟨-553211588971279791715696817265343650599274257907020388,122642923947291561983547828581936868760041243079563560⟩
def resval6Tail120 : Box := ⟨-579921280788756982001824187168090296307928891003997550,117472729203378863242861688742918384558037857577336060⟩
def resval6Tail124 : Box := ⟨-607920547248571698087078125939850185999046018297378002,111699424026975523592302709902503812064257911036288740⟩
def resval6Tail128 : Box := ⟨-637271650497720551334985265630445757876936103963131965,105282623899415895737042389187928812547072772620962220⟩
def resval6Tail132 : Box := ⟨-668039858771386177295928343211558210950431693900080648,98179635454418461433015372849163297052198700822923817⟩
def resval6Tail136 : Box := ⟨-700293591647839563451586521283517514871198202207012733,90345333557820135374336930512301483878334376957411359⟩
def resval6Tail140 : Box := ⟨-734105623019987412525495326897040792123173328222989158,81732005259107210828338038131967635784542867938116978⟩
def resval6Tail144 : Box := ⟨-1082023965201586353769034988298305590849083489001037358,68208676853989488243246125222072537778302693713283836⟩
def resval6Tail148 : Box := ⟨395784247008643597044821740139444834642296389152,127282819742342762558302460276405610177065745393⟩
def resval6Tail152 : Box := ⟨414782746325437507486327487249080245923422987857,124845140607494747491424873422642508282385276743⟩
def resval6Tail156 : Box := ⟨434808932273740719909910077488648824332696667983,122016904277443866784220492318931616678809654971⟩
def resval6Tail160 : Box := ⟨455802007638827401744103728327650169301756742988,118769879648323964541105988674328613153526784497⟩
def resval6Tail164 : Box := ⟨477808652829428673745466144104660393811108795004,115074852192328507885000540491894780351986482808⟩
def resval6Tail168 : Box := ⟨500877804161796253360339344590256808825272638852,110900910224227467928941044863763204321546904239⟩
def resval6Tail172 : Box := ⟨525060760654543933669616523230104518008774292254,106215353802513198615608672215032688620613788117⟩
def resval6Tail176 : Box := ⟨550411298101909473361985037612363167175393438208,100983598963021123151144499757596517764970317167⟩
def resval6Tail180 : Box := ⟨576985788655329160879335559382606011493798429141,95169077028402937537978006754413791089657253554⟩
def resval6Tail184 : Box := ⟨604843326178549670998024406339886272074158728079,88733128746121937441624375607720762700449987899⟩
def resval6Tail188 : Box := ⟨634045857655028913643898886720279814876382532464,81634892995405084194616449379953870956205020629⟩
def resval6Tail192 : Box := ⟨664658320939837340165645849592788771232354945502,73831189790739450032792695564866164937988886439⟩
def resval6Tail196 : Box := ⟨696748789162379486488559550837298781243365508074,65276397296023375029875807423487753195879160379⟩
def resval6Tail200 : Box := ⟨730388622101045007331282149953835815485120016759,55922322549344304772177713476180090585032786494⟩
def resval6Tail204 : Box := ⟨765652624866402426447699725322029040270196236561,45718065583523588769541171412171793527783670209⟩
def resval6Tail208 : Box := ⟨802619214246020707626235249723920224847589977634,34609876612000591345136140969446370407959877926⟩
def resval6Tail212 : Box := ⟨841370593732285969292887241941801676014133565203,22541005911972951089282018575885998124535731171⟩
def resval6Tail216 : Box := ⟨882022518491450569273359949005755643813483661348,9450826476374713758215762047034953024401525683⟩
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
def polyval6Tail5 : Box := ⟨13299327971499767459982930193830849903411849116974613903870,4093249885677587963147179285213481127312748850300309920749⟩
def polyval6Tail9 : Box := ⟨13941432389950880465262275794817658407816271342698893358991,4005444873274079012400001686057032508500163617009048309081⟩
def polyval6Tail13 : Box := ⟨14614540780866979561025403109068418973033123138574147089421,3904303825522061408277894563049964483655543318047960768067⟩
def polyval6Tail17 : Box := ⟨15320147619358309152639004489793307317776658051214543465559,3788892941308579352956423012804502929575212484149372430885⟩
def polyval6Tail21 : Box := ⟨16059821967598617677671369796314801461760240437906347675979,3658224104413727437630204799454204283699819635611101581517⟩
def polyval6Tail25 : Box := ⟨16835208644142695795313967290153925522367097769847736603844,3511251957248830451662106262590918786808683333278782698256⟩
def polyval6Tail29 : Box := ⟨17648031881277237948026906627147746075035005042660390356782,3346870833326706488202541665502625964209032307241811546474⟩
def polyval6Tail33 : Box := ⟨18500099159206946630269453587294838959605237094571666601490,3163911531946778439660388450260799295032425244344925534537⟩
def polyval6Tail37 : Box := ⟨19393305225359764494670146915568513406959606128567832403234,2961137927166008101367694308919410146941406194332190993823⟩
def polyval6Tail41 : Box := ⟨20329636307748786818557341876811986037628997254157532504839,2737243402736324879630216933754317814459480837030156907063⟩
def polyval6Tail45 : Box := ⟨21311174531760133306471724926780048122454616337538289904443,2490847104277408362193663446135074630139852423399265975811⟩
def polyval6Tail49 : Box := ⟨22340102550188418516900732499779780422963237214349449758355,2220489999521661926339734683880717078858484604868517125246⟩
def polyval6Tail53 : Box := ⟨23418708396815660254539909925158508899924718067245735888501,1924630737015000176338195672667783025027383167679422420484⟩
def polyval6Tail57 : Box := ⟨24549390574326560486118598336772966228407979741678318531697,1601641293181632494466144820248976956966238916843250118133⟩
def polyval6Tail61 : Box := ⟨25734663387874248097057666016729808078613780636049128323241,1249802397162271796512620145247775704426867275834643434447⟩
def polyval6Tail65 : Box := ⟨26977162536217664174723582151019709935943848309039533922057,867298722310060567963984316658107087519216323367565117947⟩
def polyval6Tail69 : Box := ⟨28279651466422158373656297978435436470767998198610716515849,452213821216441666993370595999495605485609286095113845231⟩
def polyval6Tail73 : Box := ⟨29843750000000000000000000000000000000000000000000000000000,2⟩
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
def resval7 : Box := ⟨98837521904862481583295651988736436144512891489272827288,15964241008480162220099616624797740949181904583623759318⟩
def polyval7 : Box := ⟨26254840497495933451223245483116434300681884392922955253585,7284543805742406814419214108462093145642489468036904552727⟩
theorem cell7_lo : Holds Q cell7 (127/128:ℝ) := by norm_num [Holds,Q,cell7]
theorem cell7_hi : Holds Q cell7 (1/1:ℝ) := by norm_num [Holds,Q,cell7]
def resval7Tail4 : Box := ⟨-34542853095566732472411582663172465321835407846917084279,15298480297403247061887776960545816070620705330549814375⟩
def resval7Tail8 : Box := ⟨-35087971728558071005163576438234165165571886331078756702,14753434267491803599976970099436116014013325060265739140⟩
def resval7Tail12 : Box := ⟨-35641617411984676764761870143909684150293532005384811110,14199788593509849635459438168125816468071848287978401384⟩
def resval7Tail16 : Box := ⟨-36203998943666827563405316747917204042960064716319709343,13637407061836888290207471417989994478032865118908873414⟩
def resval7Tail20 : Box := ⟨-36775254174406405336160600777407602634355123122325252583,13066151831097349341038873569118357607966245760504503458⟩
def resval7Tail24 : Box := ⟨-37355523120430684868987741127135091164834751899554698399,12485882885073070350743618997040913342825949919590253580⟩
def resval7Tail28 : Box := ⟨-37944948007243932245146054166446793239664097843095990198,11896457998259822995347440336122086664688879897539880510⟩
def resval7Tail32 : Box := ⟨-38543673304496480762912137671336062854819391928497845013,11297732701007274479346652622082026570853602325602375760⟩
def resval7Tail36 : Box := ⟨-39151845761394674807131635728833657077057950923630478392,10689560244109080435265095616320773754895334390080737081⟩
def resval7Tail40 : Box := ⟨-39769614442669501797523383364492577135191326096879154097,10071791562834253444407461178192172120873405158080761022⟩
def resval7Tail44 : Box := ⟨-40397130765112765080292531863416551248712884226136914936,9444275240390990158681996005841032389285141728846861287⟩
def resval7Tail48 : Box := ⟨-41034548534689753316504363818638674645404988278587714511,8806857470814001888392218599019654545384138076974568484⟩
def resval7Tail52 : Box := ⟨-41682023984237502052890929162206476053021651275103177473,8159382021266252189772009388654196745946847188138038870⟩
def resval7Tail56 : Box := ⟨-42339715811757816342473032239822409005735890010387560058,7501690193745858139143832429487562795605579992875427185⟩
def resval7Tail60 : Box := ⟨-43007785219291691107522634314384093201125351692936221225,6833620786187996256917608364765171320058351012912703513⟩
def resval7Tail64 : Box := ⟨-43686395916196379341788748513216587826489081246068514945,6155010052093590408472867433701670705306486110748487960⟩
def resval7Tail68 : Box := ⟨-44375094007183699870693011097402386393908924154242075825,5465682323107005805201130515527151869545345888837251759⟩
def resval7Tail72 : Box := ⟨991122882891559895007918573126125232750917230185423983900,718270824120343931170269184497264478463721268373488907⟩
def resval7Tail76 : Box := ⟨-502467964240360805321688614709477713019285269089423868,225509338087274033473635301753161569475590136383633437⟩
def resval7Tail80 : Box := ⟨-510359285558092335971684832769876855929580274312737640,217581421188717595315642579105656895380579572821000441⟩
def resval7Tail84 : Box := ⟨-518412134460023264194163626853047875177543202637148623,209528570136816040101415972101380191554643667968705494⟩
def resval7Tail88 : Box := ⟨-526592049720272759891120096945631534444609220845100280,201348654875247076437407942237349273554088430411199692⟩
def resval7Tail92 : Box := ⟨-534901034132091198923543063769589359522733130388851499,193039670463424705370869360351716239895805949236497056⟩
def resval7Tail96 : Box := ⟨-543341124248970286819980860553350025789634343747356783,184599580346545575902372889977521120262895527389243536⟩
def resval7Tail100 : Box := ⟨-551914388760056042876674305707429057685608222009374075,176026315835459818560036533853143162401076179199866198⟩
def resval7Tail104 : Box := ⟨-560622928995906124862860118025667438494855967897857415,167317775599609736474413689640467542565100288612070505⟩
def resval7Tail108 : Box := ⟨-569468879443528001399026895485508958543243365127717093,158471825151987859923207668692996911282971138618665659⟩
def resval7Tail112 : Box := ⟨-578454408269547514082060306851623224705684975558270974,149486296325968347241118308685939872154989176883308899⟩
def resval7Tail116 : Box := ⟨-587581717851632440982984934847297551008432429119876343,140358986743883420370356617062568420415819140232180890⟩
def resval7Tail120 : Box := ⟨-596853045318301281114398692774763172081798547803161011,131087659277214580568504094560047101396416187582748623⟩
def resval7Tail124 : Box := ⟨-606270663097249574353851988019741636691535134248166295,121670041498266295108524375665665141678490118881402890⟩
def resval7Tail128 : Box := ⟨-615836879472328645269215711582673625002944680963904274,112103825123187730379230771904417207149804880451074195⟩
def resval7Tail132 : Box := ⟨-625554039149426389557773578419716210446561303231676026,102386665446201068526894517026718887568454163396797006⟩
def resval7Tail136 : Box := ⟨-635424523947870544739984947527017474477068376229213460,92516180761002656307180760865231461638734086066471821⟩
def resval7Tail140 : Box := ⟨-645451796567598910212933186332452505912669759449214924,82489925196619222611620579276712849719952764271224301⟩
def resval7Tail144 : Box := ⟨-965726211432769990195631732855693415608363616361359437,68266554761567892585922685099783095736025432464083303⟩
def resval7Tail148 : Box := ⟨686891674030550329494807174190978160597340818082,218962258689315329601841029364701679992587163789⟩
def resval7Tail152 : Box := ⟨697623029479749780131319128248030682400756713491,208124974556700194693871844134399361314075571991⟩
def resval7Tail156 : Box := ⟨708630673435722781335861464785178130301561940586,197117328553295671933843068002276424456727147357⟩
def resval7Tail160 : Box := ⟨719812006731718580429835577143727687921610327862,185935995256591994607700756978019306991720267331⟩
def resval7Tail164 : Box := ⟨731169767918110936816655702242655654205352706158,174578234070198296620680214354173420705684030556⟩
def resval7Tail168 : Box := ⟨742706740812507167757252678591171823313762846914,163041261175802056092604863925761715513157054186⟩
def resval7Tail172 : Box := ⟨754425753158486614645540063677054835405089841333,151322248829822608995489780010230557689758889149⟩
def resval7Tail176 : Box := ⟨766329677317996899653794757432377923015581913488,139418324670312323975351889445989339205408073417⟩
def resval7Tail180 : Box := ⟨778421430975376412612013547991563470778116929895,127326571012932811015648801252428106117151360875⟩
def resval7Tail184 : Box := ⟨790703977852486706238716403466733109171299114299,115044024135822517388729436758513750635989699092⟩
def resval7Tail188 : Box := ⟨803180328435128822472159630179924878083247897043,102567673553180401155865077519322106725119098482⟩
def resval7Tail192 : Box := ⟨815853540710921588308652478512930725757063619625,89894461277387635324861982803736247587011348373⟩
def resval7Tail196 : Box := ⟨828726720918822737056921481208255759535254695064,77021281069486486665449312430483861625408986299⟩
def resval7Tail200 : Box := ⟨841803024310476568064292341295798019173596074096,63944977677832659271059759898687467952901848476⟩
def resval7Tail204 : Box := ⟨855085655923575200719704794556825357999394336351,50662346064734470514930393149604231210093398496⟩
def resval7Tail208 : Box := ⟨868577871367641791789081430765057315412753172877,37170130620880227353688565411200647974581613576⟩
def resval7Tail212 : Box := ⟨882282978269284985474469816808088358253510318459,23465024346219511364552625992963321522758701695⟩
def resval7Tail216 : Box := ⟨896233698131283377149461801930395985520424041150,9542955124045266309884462853050674256214663716⟩
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
def polyval7Tail5 : Box := ⟨22718981861259372558257667700442330686703645212646057100626,6930071569745206611080319194085426151356112554925784398215⟩
def polyval7Tail9 : Box := ⟨23077457507694104390867161038029168265636227179948968338511,6571593594819006902876259299542758029896631587150284751009⟩
def polyval7Tail13 : Box := ⟨23441591821282177776951154488396951262160350132314025452110,6207459280985451528240732547380098363345801570348105596028⟩
def polyval7Tail17 : Box := ⟨23811471733321660457956185874396899336039278182813889249240,5837579368945759433054940677465071902136384063652124885190⟩
def polyval7Tail21 : Box := ⟨24187187902146874701153599479365961898856029008112122322990,5461863200120544399812768658999762166985250807701477247267⟩
def polyval7Tail25 : Box := ⟨24568832416817220949034748973008103266414265383745143538341,5080218685450198141927862197440786254363308459288698025886⟩
def polyval7Tail29 : Box := ⟨24956498819446069232061971898209149848433532241052927915909,4692552282821349858544386449689640716558250644480900656500⟩
def polyval7Tail33 : Box := ⟨25350282128127983470075935523427360320976859866641687520002,4298768974139435620499773775190802595377432717854610222775⟩
def polyval7Tail37 : Box := ⟨25750278860227915346524301573047015355627046211323087284695,3898772242039503744046550142207136954970446743617752756746⟩
def polyval7Tail41 : Box := ⟨26156587056037874178659082396928923320852167379646977170270,3492464046229544911912642770146041135201566787498110432555⟩
def polyval7Tail45 : Box := ⟨26569306302806870379112124453968912313169881323379649879513,3079744799460548711473585167014262280949225320530570203086⟩
def polyval7Tail49 : Box := ⟨26988537759150022305771582780008442412182413406913068552446,2660513343117396784970788622877943867822787295382854207698⟩
def polyval7Tail53 : Box := ⟨27414384179842809241863947335460156112116713533961577817939,2234666922424609852731916438015166847575864409916671466107⟩
def polyval7Tail57 : Box := ⟨27846949941006547898251959990279447000844185957399145937286,1802101161260871456207402751838251642649457437104248031852⟩
def polyval7Tail61 : Box := ⟨28286341065691324815501517975303674837169181664545353502034,1362710036576152892907965072661190408255351333619097104683⟩
def polyval7Tail65 : Box := ⟨28732665249923136013236766778919810384899371273677758639707,916385852403246110045014388670146296587229624795264013785⟩
def polyval7Tail69 : Box := ⟨29186032379199749820635185014247019380299806925976244873086,463019202101388762652074539928434935246686202186983601532⟩
def polyval7Tail73 : Box := ⟨29843750000000000000000000000000000000000000000000000000000,2⟩
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
def pend : Box := ⟨1033535880159859612965153604586430941690817447261313918523952,3504143378727300488855005147585755506926599645941282431⟩
def zend : Box := ⟨1003885849865408715706992187500000000000000000000000000000000,1683242873646512539062500000000000000000000000000000002⟩
def betaquot : Box := ⟨428785529239319607936537752621266394797540805212438166386866,394842474957553946738272438137964361081182984759732683⟩
def crit : Box := ⟨294765540811290399372082981020942329771115944560866934710,8381549726555851349043475673088291723198402617725287102⟩
def subsonic : Box := ⟨218086515906350156410072127630150509919321317748129011065,3762059095166941527412201434141811547901928088621385870⟩
def pendTail4 : Box := ⟨29647267344510481099186533167882686846673320051198661563874,1744350914330177471417803432858665713438390409094958487⟩
def pendTail8 : Box := ⟨29647306860202315887797776935248227080017803263859493059662,1744240183656570014729637882174413848735619651092650520⟩
def pendTail12 : Box := ⟨29647306862098809415908643619190215819625536868148194814691,1744240167585621658134043869339633465930778324441199947⟩
def pendTail16 : Box := ⟨29647306862099845357909390506136046519619288436640474373504,1744240167571002912096115833039884148747733236331929287⟩
def pendTail20 : Box := ⟨29647306862099848120778210989741083786929463523022235102115,1744240167570943832847014755836660719417835968456208224⟩
def pendTail24 : Box := ⟨29647306862099848146842348685477854749007234642529664319250,1744240167570942991417934458890016353668252352368691356⟩
def pendTail28 : Box := ⟨29647306862099848147556417083871701576645465229867795296968,1744240167570942955154014184011018187393477416518295388⟩
def pendTail32 : Box := ⟨29647306862099848147604723720104863733258826368186506376275,1744240167570942950844948956001446652773985013136495633⟩
def pendTail36 : Box := ⟨29647306862099848147610906440118013520565467736197755233437,1744240167570942949507184366531966648649818166476186770⟩
def pendTail40 : Box := ⟨29647306862099848147610254935491590585735513338930784980498,1744240167570942948449582356022063434738865339340061721⟩
def pendTail44 : Box := ⟨29647306862099848147599965407487754484840147267283289398671,1744240167570942946326028633215661506977008777505552897⟩
def pendTail48 : Box := ⟨29647306862099848147508337729262805476944867136253839462247,1744240167570942935281030628391602772126969501717259740⟩
def pendTail52 : Box := ⟨29647306862099848145775675428573549863661561865228252095891,1744240167570942786686010151021476560170999873453187957⟩
def pendTail56 : Box := ⟨29647306862099848058889811958539039851830332995654206459659,1744240167570937629117805154131676276638315848153592001⟩
def pendTail60 : Box := ⟨29647306862099834182862983387707528185325431800439130195685,1744240167570345341231716661852762892183277443155015396⟩
def pendTail64 : Box := ⟨29647306862090687773819532172229552463190846820278102430506,1744240167286743317134765831568099877094072480888432671⟩
def pendTail68 : Box := ⟨29647306821978230665025799514701205787741929585523043817510,1744239292908521278876937256806306586259354981581341805⟩
def pendTail72 : Box := ⟨29643203126975521260505801364728725200856897785260643468664,1693102706381381867961892875877079816067076850323153746⟩
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
end SepticProfile.ExteriorCertificates.C61

end
end

end OAI
