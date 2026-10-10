import OAI.MathematicalPhysics.Transonic.Certificates.BarrierData03

namespace OAI

section
noncomputable section
namespace SepticProfile.ExteriorCertificates.C03
open SepticProfile.ExteriorJet SepticProfile.FixedInterval
def cell0 : Box := ⟨250000000000000000000000000000000000000000000000000000000000,250000000000000000000000000000000000000000000000000000000002⟩
def resval0 : Box := ⟨104607986316329150762048310586123803476217480009176643872,515863006252984186920257429961634813117336758471288358⟩
def polyval0 : Box := ⟨3710966702502013765562922772597106483302315500828005806399,18108080953619875439233913426691878545241470327123579490⟩
theorem cell0_lo : Holds Q cell0 (0/1:ℝ) := by norm_num [Holds,Q,cell0]
theorem cell0_hi : Holds Q cell0 (1/2:ℝ) := by norm_num [Holds,Q,cell0]
def resval0Tail4 : Box := ⟨48595640532034569791605120071959559949528334310190,1872958252428224557634912502197534396405050509783⟩
def resval0Tail8 : Box := ⟨5317223141820559459286576957770785275110098058,353532194519834608734316799208275593414553016⟩
def resval0Tail12 : Box := ⟨4376876132685775092276655385564678621837199,434745918047071439769828861111713912014437⟩
def resval0Tail16 : Box := ⟨15868556998719516915363138761443068358385,24486918453722741918525752375868653860711⟩
def resval0Tail20 : Box := ⟨195811242826583248700893284208893566926,356504451492106144490091746338377706797443⟩
def resval0Tail24 : Box := ⟨7058415169829483750743176912237865280,5703476492645915331429742512298895003021901⟩
def resval0Tail28 : Box := ⟨676431225332475366317489239028621263,91255594877911640486506846505495650411557411⟩
def resval0Tail32 : Box := ⟨160851574197468304539763984652561389,1460089514268387356683726509148047213070102910⟩
def resval0Tail36 : Box := ⟨-429129471084606681362876515542460310,23361432226768512868963957147255085190856439486⟩
def resval0Tail40 : Box := ⟨-134241705062132350176301470697955014560,373782915501799864752982590670402413160390934957⟩
def resval0Tail44 : Box := ⟨-34400394541268590713938678134380136999320,5980526615777076738205484534296869308256479568033⟩
def resval0Tail48 : Box := ⟨-8806619885577565617596521423600908449923022,95688417596219223979548480973637852196387819481180⟩
def resval0Tail52 : Box := ⟨-2254495696866109962105213562001102603068247521,1531012567949653733492624428109598387588251048680747⟩
def resval0Tail56 : Box := ⟨-577150917802412913019488339277787016925505339214,24495660008200802925644129521133066103798222466606831⟩
def resval0Tail60 : Box := ⟨-147750634633575677185045560535601120249308154344746,391792043909259783162254573630632307361433304795879987⟩
def resval0Tail64 : Box := ⟨-37824159122283061041692354374300998335216810384468530,6233212550695077855240368726555404739815867838308505588⟩
def resval0Tail68 : Box := ⟨-9682908439731694264509509314281258131579237586949688654,90653629951398918154326830208530882130458609536180967480⟩
def resval0Tail72 : Box := ⟨717708249342370609058579585562393807492408617613321988393,2945219015329463817046701965940313078976357546322938427⟩
def resval0Tail76 : Box := ⟨-22186001105556826342640380854043814391450569957291,642919178008992732709416275391133924035895073650⟩
def resval0Tail80 : Box := ⟨-1084346369013938511450162110146302027026284843,61577048853525250036112185947480136949959085⟩
def resval0Tail84 : Box := ⟨-554880496480815552940021749081282197638946,48875621535292208387778558806480552474285⟩
def resval0Tail88 : Box := ⟨-1389656862078823663185316612433976171238,320939715445704848348364232527517958283⟩
def resval0Tail92 : Box := ⟨-12534858573210355226295778537937321207,2336632553034551606485467799697583110124⟩
def resval0Tail96 : Box := ⟨-341881102522857185957591401646106732,37351336133913379775938726101796098594222⟩
def resval0Tail100 : Box := ⟨-25329820007794492261232955098235681,597620090252736928924649089430783394943351⟩
def resval0Tail104 : Box := ⟨-4783682443520927758260162759200587,9561921314444506901845021704461412239564530⟩
def resval0Tail108 : Box := ⟨-3928427870127248599600959585407098,152990740996891904055546531459855005006373441⟩
def resval0Tail112 : Box := ⟨-441493973064006259160592043202246113,2447851855537775201025971178039393362841614839⟩
def resval0Tail116 : Box := ⟨-112391548470672866487790306966644144351,39165629583239997418638759348155470048090425091⟩
def resval0Tail120 : Box := ⟨-28770522855076799121331294597674618249831,626650046359491551709749613189585276078350687914⟩
def resval0Tail124 : Box := ⟨-7365242408378558691226370953263596637499072,10026393836837435083943013759968507772072627262382⟩
def resval0Tail128 : Box := ⟨-1885501874255641456742212738414003261530971180,160420533731411756352961681675313640365745721042215⟩
def resval0Tail132 : Box := ⟨-482688477075306658387316097588830212241210729370,2566276019259570232179592402346752947912770081245696⟩
def resval0Tail136 : Box := ⟨-123568257929110918791443359920142294679720733176004,40944571070646997102409535262349747230158833474554180⟩
def resval0Tail140 : Box := ⟨-31633567196351981246562071973240917252869947887441942,625456707434096459708022682650002968204336226249343755⟩
def resval0Tail144 : Box := ⟨-8169665512959113163542974916062665044825600438210008026,2376784946254623015256892086793072629001449075900411267⟩
def resval0Tail148 : Box := ⟨46104579402047453489952219333238763197846859,1124021267728789219241977603912258469384534⟩
def resval0Tail152 : Box := ⟨743015685732121421099984202487097916801,37401237506133148135638160062633365704⟩
def resval0Tail156 : Box := ⟨213494686658312005432779129786665050,17073093617351136559622493547673899⟩
def resval0Tail160 : Box := ⟨338341301962674487592406811361769,40354232168870525658272530363914⟩
def resval0Tail164 : Box := ⟨2044693551531395965170218888111,23056737997798280502267514101011⟩
def resval0Tail168 : Box := ⟨38563760333767986347680994169,363721101003546520792479892098117⟩
def resval0Tail172 : Box := ⟨2008899309955934723363061018,5819405345601137244494819189765445⟩
def resval0Tail176 : Box := ⟨268078188544175604456378497,93110476247210565999479809320547212⟩
def resval0Tail180 : Box := ⟨93072745510257351965527886,1489767618268851176397877139872136607⟩
def resval0Tail184 : Box := ⟨1442894122905603660870060357,23836281890552659516262259487909257370⟩
def resval0Tail188 : Box := ⟨351842541338690972247122905867,381380509919039025648776040535399752516⟩
def resval0Tail192 : Box := ⟨90038790548591131700687486910595,6102088074293453189663168926079211196431⟩
def resval0Tail196 : Box := ⟨23049780941910548073317261269684577,97633387579528058570218281269679770156934⟩
def resval0Tail200 : Box := ⟨5900742271775644409798232334370720465,1562128669326659887012150179158093933905092⟩
def resval0Tail204 : Box := ⟨1510589984524168588901669894360578251712,24992642531126792226387316179564187438867506⟩
def resval0Tail208 : Box := ⟨386711041370403265292887336381454549887534,399519738901703157890258534985020623582698334⟩
def resval0Tail212 : Box := ⟨98998058270838441891669289917194171838318535,6299505157080080905087388384986604929303829638⟩
def resval0Tail216 : Box := ⟨25345254641156587885985618467961427196226053622,77031613747588087026613189956314939286286497093⟩
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
def polyval0Tail5 : Box := ⟨1849132132597751102733071663721177011955159968835876,55063648389582572689066034594901726776331424745668⟩
def polyval0Tail9 : Box := ⟨162172729865673156149259933631728943265242052132,9473694337112120799152653644910458854801053999⟩
def polyval0Tail13 : Box := ⟨115503703489873257090775473569869672765774445,10442155990660065327272787543155084973954324⟩
def polyval0Tail17 : Box := ⟨366951815771355877885934100859291490416761,410784137597127778462426739716745086452832⟩
def polyval0Tail21 : Box := ⟨3978701140556143601845729478760668490618,5816394348819029771051437646458496675967862⟩
def polyval0Tail25 : Box := ⟨125880144373373699578786874339058325464,93051015581414405166790120563700144530060755⟩
def polyval0Tail29 : Box := ⟨10550632957581646895496788455588727122,1488815764169254647055457122339444241727907763⟩
def polyval0Tail33 : Box := ⟨2231154617543007551521843646329192936,23821052171441264322968589912900915749746995449⟩
def polyval0Tail37 : Box := ⟨6660388494881310779022436175109123633,381136834725039699758305990883938398907680803399⟩
def polyval0Tail41 : Box := ⟨1419488133879497615942643105926151129312,6098189354270697373944965587221482257678727032790⟩
def polyval0Tail45 : Box := ⟨363043434056173353937677493274902886021296,97571029327979617715901616063913952842200715347375⟩
def polyval0Tail49 : Box := ⟨92938113577676697867490814866427637041354519,1561136382118203385580860472301473919530849443946241⟩
def polyval0Tail53 : Box := ⟨23792149948492395438057979613300666746163137443,24978159808750900384109131557041576470458156843818495⟩
def polyval0Tail57 : Box := ⟨6090790267957070144296679381584849868428377906549,399644846824152250930778169378698722682854387188199929⟩
def polyval0Tail61 : Box := ⟨1559242307032913839804914363464583010179055053424586,6392855759526702481107216732235805350620881244849155183⟩
def polyval0Tail65 : Box := ⟨399166036570030288036912676345979724236382460624233213,101911473996414272072156421681995590499857783619646506845⟩
def polyval0Tail69 : Box := ⟨102186577601524225442091049749162555056646396672218162183,1534783698259293744585210935018565228995839534339965233381⟩
def polyval0Tail73 : Box := ⟨26218750000000000000000000000000000000000000000000000000000,2⟩
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
def resval1 : Box := ⟨104405276297351837615294876330337092237152083269852718740,448535614225428150012296886450607837372295369641793629⟩
def polyval1 : Box := ⟨3693676642787227740479836344461741829475651731146308187015,12246296109913297276675195971056792042485979782908701027⟩
theorem cell1_lo : Holds Q cell1 (1/2:ℝ) := by norm_num [Holds,Q,cell1]
theorem cell1_hi : Holds Q cell1 (3/4:ℝ) := by norm_num [Holds,Q,cell1]
def resval1Tail4 : Box := ⟨47218854901173414316317999024393802904692426880869,3265490546245738446398359637809315420824766853346⟩
def resval1Tail8 : Box := ⟨5007013980178147656959631092252177268265199168,5963436020720089177262417227661762062252345766917⟩
def resval1Tail12 : Box := ⟨-313892542340925092414133040790035972891686113,18846504302903166931505160948435313604030861768832⟩
def resval1Tail16 : Box := ⟨-2083766026650891491014484594747962103625362766,59563180791096024367633939377242440520880790031491⟩
def resval1Tail20 : Box := ⟨-13656263119631628566982670236637195738833618960,188241994724024972597586093988622739777035388294217⟩
def resval1Tail24 : Box := ⟨-89497687106920971903629817508634041270662043568,594891325186318114084169144874957915839043138614230⟩
def resval1Tail28 : Box := ⟨-586532042262988418791493111688399197606030826735,1879846685928083490976347375414994812525013092054200⟩
def resval1Tail32 : Box := ⟨-3843896392178269327538057097631027013659742907151,5939253681390646438124827898284994226955290617830471⟩
def resval1Tail36 : Box := ⟨-25191359395780287635488869815942556787385839718091,18757931849399320241705963123916395191350406908306938⟩
def resval1Tail40 : Box := ⟨-165094092936186076199689859737668313230621247764343,59198850863255736621869463322532852188092921806927683⟩
def resval1Tail44 : Box := ⟨-1081960647466589391868269355652213582397335700306804,186537420942473314232524638743987983557731948494421709⟩
def resval1Tail48 : Box := ⟨-7090737299237039547304937446473140700239410985320937,585879160071437220912100286720298284798046412458111703⟩
def resval1Tail52 : Box := ⟨-46469855964279812736830444249353580851456751641682487,1827607844367727652497022495529777148107341540640355832⟩
def resval1Tail56 : Box := ⟨-304544848047499632356059541380371326752521859400021612,5618466155470938310804198043635233157452481786941819525⟩
def resval1Tail60 : Box := ⟨-1995865116162762783252998021195514583056188813897826692,16723774598659504617722768595083016520877416089286822032⟩
def resval1Tail64 : Box := ⟨-13080101623295880829685947881265984769521761375965766561,46083204140054046267822104372496672194671086219321245142⟩
def resval1Tail68 : Box := ⟨-85721719015017760244632789704261240699181744285525776194,101263510110653950626543253579605735271224833350671544890⟩
def resval1Tail72 : Box := ⟨720238243197041220752263659018169154290577272994084393293,2105489519165444344391811529414893711156188499066045556⟩
def resval1Tail76 : Box := ⟨-21702917901796326870135940419022429977685694079882,489936211013135979928099495334990431261351437162⟩
def resval1Tail80 : Box := ⟨-1037579112168106377580375330087490817568939685,58539959290246167736654795514521987376248039261⟩
def resval1Tail84 : Box := ⟨-3115607270084194497486820382084347019866717,184876247715253569656498636308732898568837708755⟩
def resval1Tail88 : Box := ⟨-17018895115628966873059198285396545536014335,584291401424512351999080002121226002564764654424⟩
def resval1Tail92 : Box := ⟨-111526730019433801848075813432748025605941808,1846591624747549523939710901140986276216044864131⟩
def resval1Tail96 : Box := ⟨-730901505128602999569913999549540384093553796,5835763009301240229876747559293598907066822049162⟩
def resval1Tail100 : Box := ⟨-4790036102096645261712606703444808715568172003,18441412941260271771001254038202814489932614846207⟩
def resval1Tail104 : Box := ⟨-31391980598565449275783702476849999970558358464,58267718663904652563636274121603038521649897860480⟩
def resval1Tail108 : Box := ⟨-205730484050734918413592139072721525368223177797,184048248836848311982214362509558294139817604015228⟩
def resval1Tail112 : Box := ⟨-1348275300274886915139794973253400795381631877322,580985288973183824074088743624520235187877563543835⟩
def resval1Tail116 : Box := ⟨-8836057007881491590282019688647610154961261905415,1831625578226753442780935930625898684471784816676831⟩
def resval1Tail120 : Box := ⟨-57907983206852143848289413663548757929719240980310,5758859654077919995276669930734475937470898200661033⟩
def resval1Tail124 : Box := ⟨-379505758744426583065778954730996686933575784535677,18004352452921026342854657113227941409914025623169322⟩
def resval1Tail128 : Box := ⟨-2487128940507501640400743140865530207532017823865687,55614941456854935631495851168071934885618668833630439⟩
def resval1Tail132 : Box := ⟨-16299648224515705588356649884649968294743933739937266,167331586611596623141200136293287788628620142802206705⟩
def resval1Tail136 : Box := ⟨-106821374609555175611637285069911274787301600458215516,473544009567585327039624885447849048005067824062390996⟩
def resval1Tail140 : Box := ⟨-700064605201342837772565629257061834432868377315548094,1134176641385812214964441344562840596967821737806073454⟩
def resval1Tail144 : Box := ⟨-4617576475669624245292492708361041469503365578648753330,1201824141384702850400706324102159468001177490063979463⟩
def resval1Tail148 : Box := ⟨45437451782906575669788899967874884927712861,893065871684294101594969204580778124772953⟩
def resval1Tail152 : Box := ⟨715266289951759200176138428629407255540,2356783628070879619856625488731338978399⟩
def resval1Tail156 : Box := ⟨291337622134166759540366775890769301,7362585734765805006602639307678813609966⟩
def resval1Tail160 : Box := ⟨591763731475124604695274785126709624,23269089738479607055199214783223554545824⟩
def resval1Tail164 : Box := ⟨3876144330320843781743733762100101449,73539807596557023244049983126437022940912⟩
def resval1Tail168 : Box := ⟨25402687494940150215347106588898330286,232408955796241484676420437411425747982445⟩
def resval1Tail172 : Box := ⟨166479052547937948881430958251173907506,734440876155199643809490034054332024081776⟩
def resval1Tail176 : Box := ⟨1091037118767231293404146051021609557017,2320630974402009613756612600726987444669255⟩
def resval1Tail180 : Box := ⟨7150220861551555519992621410115336884877,7330637864932507872796101740830248384183232⟩
def resval1Tail184 : Box := ⟨46859687438263871785206337192691052607426,23144174262725676818595934665798406568372271⟩
def resval1Tail188 : Box := ⟨307099647595405861212237947634340903780629,72988019997367171982970158151965765868074099⟩
def resval1Tail192 : Box := ⟨2012608250481251652401984919133897028844401,229636164948412821417212626945806131214943802⟩
def resval1Tail196 : Box := ⟨13189829430353932937494196845011877790275455,718934688334052027684292798857575709506990993⟩
def resval1Tail200 : Box := ⟨86440866154767660474482317395150687112295477,2227434152952490764205752755002368814532121860⟩
def resval1Tail204 : Box := ⟨566498860431900534446470110868166836641344882,6746488854277469452766001066225910660325235414⟩
def resval1Tail208 : Box := ⟨3712606931733094717792868956820593999670028596,19400045598710866530238146865021001403848121537⟩
def resval1Tail212 : Box := ⟨24330940804822778287383432427180410400317806739,48716454859017686016343145995312246259776653843⟩
def resval1Tail216 : Box := ⟨159456027312110198202643062761255514869442539339,71410381864072502951922963683128551737687628911⟩
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
def polyval1Tail5 : Box := ⟨1800459009121956345076146911373105387152266024678963,121098794532538586194036582698389637188067867594412⟩
def polyval1Tail9 : Box := ⟨156730655174173395667461881834486760810990852556,264383130615206113302228944790701974575657610528420⟩
def polyval1Tail13 : Box := ⟨14933033877311483451872124929659635609161559405,835556036118018031456860870466701334679077607145546⟩
def polyval1Tail17 : Box := ⟨97160514522821942500901558114604625820207685537,2640719385428473829645762099266208076896101259392518⟩
def polyval1Tail21 : Box := ⟨636748965752368026260568636994681630401357912859,8345647642075885869193307399290359903222089807318700⟩
def polyval1Tail25 : Box := ⟨4172997998980448224137861526094225859258500220659,26374207299602662314778278082199271497685530796927378⟩
def polyval1Tail29 : Box := ⟨27348159685417342397158749990199768780933842999554,83341359941376210678959278504022622595522045127651329⟩
def polyval1Tail33 : Box := ⟨179228899314295211599993807798327405539034725392318,263307058432436006559648327933960459902470108868002615⟩
def polyval1Tail37 : Box := ⟨1174594514546154295776794516091752031999674455324604,831572190138886892525894478015493011825764510680947596⟩
def polyval1Tail41 : Box := ⟨7697822610529672105210353843940846041574522265051928,2624193249874394522726519431822324356716172186002683148⟩
def polyval1Tail45 : Box := ⟨50448450260367255319194636266325356237606561259967360,8267627038087047481832704050603887365313399273327064814⟩
def polyval1Tail49 : Box := ⟨330618963626342846032420049132370665298716965409291095,25958607271150671633319329716748813936989177000576885196⟩
def polyval1Tail53 : Box := ⟨2166744440021600729731357291023580853136489614789494049,80920192795816864950318725422104185208435934748015365182⟩
def polyval1Tail57 : Box := ⟨14199976362125581820418526723309809477629853832024440234,248395775889413285449087218164333442759020928961312100218⟩
def polyval1Tail61 : Box := ⟨93060965086830389697380971670333887022263950407286374807,736871288942727387574352529971090565719689602290151376969⟩
def polyval1Tail65 : Box := ⟨609884340797104996916152814462122220843650120988061275358,2013111425027549636288367217943922215243614460519783461187⟩
def polyval1Tail69 : Box := ⟨3996938050358535955325641713228074556962287450351901088421,4293023901403261989103689622923383676695464958356123193870⟩
def polyval1Tail73 : Box := ⟨26218750000000000000000000000000000000000000000000000000000,2⟩
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
def resval2 : Box := ⟨104305431573149750559324981169499645267772577763137345248,434968952706447884046085089406593142073633870938285901⟩
def polyval2 : Box := ⟨3685131365951427822580730006916929658683313455431912363339,11063945016919320769262821105197559273726972965565674745⟩
theorem cell2_lo : Holds Q cell2 (3/4:ℝ) := by norm_num [Holds,Q,cell2]
theorem cell2_hi : Holds Q cell2 (7/8:ℝ) := by norm_num [Holds,Q,cell2]
def resval2Tail4 : Box := ⟨-149041776257488415384251530466005936594836774423172,33947601740920855120323104783983610398579587767443264⟩
def resval2Tail8 : Box := ⟨-448832119403252012876717987010604868586220588900356,57796097308638678440364203119902279514006547703158537⟩
def resval2Tail12 : Box := ⟨-1029900391585153496896448340922442953852492656388236,98333385884660922046947386561717894107392749831434037⟩
def resval2Tail16 : Box := ⟨-2363206901720232295660496959964354888152468005164898,167146172774513566910146517501588897917285274959479024⟩
def resval2Tail20 : Box := ⟨-5422608715102175909480949398827347744536709451081153,283752909466449253879428510900729176416300193677507363⟩
def resval2Tail24 : Box := ⟨-12442704553515168789929066677475106925614972760046289,480877962864908503071590693183087514824705240795657102⟩
def resval2Tail28 : Box := ⟨-28550999111346607509151792267948788561711406376808033,813032280249696032305777507745867533853639823975677597⟩
def resval2Tail32 : Box := ⟨-65513051985617145767045500020756428824374767438870963,1370190868157169465662540797332053174125944847377969147⟩
def resval2Tail36 : Box := ⟨-150326087144336867437528954267770811320456127692958170,2298921416772720175703780168377741843408740239846270238⟩
def resval2Tail40 : Box := ⟨-344937867970003184278485938938116279407217832131154729,3833370243668591421562538104283515845449919374843726324⟩
def resval2Tail44 : Box := ⟨-791493579191279320831704486002752966795115697420578868,6336515594183016183069925458119078354860609330400273004⟩
def resval2Tail48 : Box := ⟨-1816159210317554760611986108130774727398195668144932479,10343909750174371260757784031190738471604147497047269355⟩
def resval2Tail52 : Box := ⟨-4167354434626633076404090326741726070702978005767909197,16577186365946015329397569142719791101679973947845189191⟩
def resval2Tail56 : Box := ⟨-9562401184401488407807006486087259022302962892932800400,25826869585754928249852253945396683366580836287716714460⟩
def resval2Tail60 : Box := ⟨-21941862120405602579201913250514388820167253481337663051,38430671438343944365413051350209109413503262094754062671⟩
def resval2Tail64 : Box := ⟨-50347742581746471765709211727571888954238910523484811732,52645134324722878074925543517550781992767517456091677998⟩
def resval2Tail68 : Box := ⟨-115527778183480483304940914288654786422581022093588234027,60173493883002710396189244773515933494394180479372124288⟩
def resval2Tail72 : Box := ⟨721501777112259753241138460634727453354741632984265832778,1686026726265646850849433836556968617990122258952549558⟩
def resval2Tail76 : Box := ⟨-23546800860559666835757717456883896878147593860040,388622237352870444728316021893806276461687868753745⟩
def resval2Tail80 : Box := ⟨-4763894469376645911435979128335447174076815772667,661368440052778125023545660546831757055906008942337⟩
def resval2Tail84 : Box := ⟨-10928891349484990025710639640127360528040787485970,1125461698639705438640015965421389945921967514544996⟩
def resval2Tail88 : Box := ⟨-25077405922969665938274878448291154672915971555657,1913554770036059196469502816879615053271651093854918⟩
def resval2Tail92 : Box := ⟨-57542553639171285045700037252581845864697914523691,3249678351285028158407686516867880556301365828170012⟩
def resval2Tail96 : Box := ⟨-132037001340850991127102048764662910197770730736984,5509935854373216231675672660659661637039429410770338⟩
def resval2Tail100 : Box := ⟨-302971776894156121494173690150011743584029397880095,9321984831604310410302457968771490722135556336704185⟩
def resval2Tail104 : Box := ⟨-695198290344715324848218583753637769273293698840668,15724552758555625712063045456165511559056327156543698⟩
def resval2Tail108 : Box := ⟨-1595200278562769627891964100135569142550345941237682,26416170107233064138363253261348313731318555831037624⟩
def resval2Tail112 : Box := ⟨-3660342616010982468362463025201272137231103001820224,44125818608570331609705066301275512896699523041585440⟩
def resval2Tail116 : Box := ⟨-8399013118689672877739645058232621745350794233985298,73122068254023805865287851980555605905032207544484281⟩
def resval2Tail120 : Box := ⟨-19272354740605945248472127240258445883517562437796113,119799011066405470392644174345329896304109748367458984⟩
def resval2Tail124 : Box := ⟨-44222297548417465782485311133400344189416525081488372,193027312757921042818031066409138674961788390771325562⟩
def resval2Tail128 : Box := ⟨-101472374641402183208248637554679099012021980615086050,303264986380989559450665931521256087460879288422098523⟩
def resval2Tail132 : Box := ⟨-232838260022375657301922579551379210012128689777966486,457625809426905966764772516603293003549266845325718820⟩
def resval2Tail136 : Box := ⟨-534270095898269467295629477257770015560621832596414382,643631123790315209164001472831139723762817765019842560⟩
def resval2Tail140 : Box := ⟨-1225934876586817064808633683028708805638361331998236731,783512630208406410243513956657499182771840900509501032⟩
def resval2Tail144 : Box := ⟨-2835953935746068792238000227571143908623289680799986436,611254502635233362282003339396702367688285087740114897⟩
def resval2Tail148 : Box := ⟨45313286375605565929070641696261818341208457,36370675382007651508085023258635970317150903⟩
def resval2Tail152 : Box := ⟨457670586284584246903147496934416265575216,60656417387306176426497915207258794974402080⟩
def resval2Tail156 : Box := ⟨1048558659316978953849211566461648313912233,103208157796607283909431793910011185465834376⟩
def resval2Tail160 : Box := ⟨2406019659549597077435948603030611679579780,175451335517715309877301097425302313138118220⟩
def resval2Tail164 : Box := ⟨5520846762671718297497104390349544057770081,297895949074397143594366959483514014844587335⟩
def resval2Tail168 : Box := ⟨12668121334629048434469798893330726057193695,504947537036310783814700846377780287690168487⟩
def resval2Tail172 : Box := ⟨29068239900082185085108762189788846211796892,853961221444094997319574531953658050718563457⟩
def resval2Tail176 : Box := ⟨66699911420881131046233927078746485071975064,1439709365407835958593084200459048707348293981⟩
def resval2Tail180 : Box := ⟨153049451870693105732072280552079400729435382,2416818269033274073903662732377828881112246907⟩
def resval2Tail184 : Box := ⟨351186893939208829329333820905332506254632777,4032893982704960086768236203081991828442185058⟩
def resval2Tail188 : Box := ⟨805832578733237275944530414291690791950676862,6673215847228660216860310765928295063705044387⟩
def resval2Tail192 : Box := ⟨1849061443221926337360552502756168819863094052,10909864984408199497984738795599978899953482374⟩
def resval2Tail196 : Box := ⟨4242851816917900792714430418380377664015680717,17523313384070435494825163901020212521081885318⟩
def resval2Tail200 : Box := ⟨9735637291184886728988810830701942380363359250,27396479603129243064874819128970143621068782412⟩
def resval2Tail204 : Box := ⟨22339369262809184251208114798030645284375909063,41006382840110723458300021468909858904961494375⟩
def resval2Tail208 : Box := ⟨51259861489710347824290569273609907233623245555,56805194992409461759325795242737705079697971625⟩
def resval2Tail212 : Box := ⟨117620751478511128727453467466731656804583383441,66733464005172710461314091767159808011066561585⟩
def resval2Tail216 : Box := ⟨269892890232675186677195339338878934550412289855,44607753077554030290488310611075833948601647926⟩
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
def polyval2Tail5 : Box := ⟨21109760956557772374523842958686631495575900406113287,2965359073721538131821468803578524505410694679226868683⟩
def polyval2Tail9 : Box := ⟨44360473045972684512995369258213657527146042487122978,5047370732793159243073953461295989406779968323337207914⟩
def polyval2Tail13 : Box := ⟨101789085622972508117019232338561533059885549732721031,8584479298890918304645824420313634599885895734027397249⟩
def polyval2Tail17 : Box := ⟨233564984019439644327918056077797997237828121044645813,14584825396043832177909803850085644638392823880814049801⟩
def polyval2Tail21 : Box := ⟨535937634980469158347885794664144390394634328167304517,24743582147084423058783237363068146924239228091400199997⟩
def polyval2Tail25 : Box := ⟨1229761172440734262167362161343805810027095753678416906,41895983528657884736489501484193051237396677001687606435⟩
def polyval2Tail29 : Box := ⟨2821806946433106480876111690234692894650679021902588101,70748809586553125497963193279919142198165656974837217058⟩
def polyval2Tail33 : Box := ⟨6474911244054482190551187861411361404540077722561265522,119033312545662971433207808307513816988642879200179240164⟩
def polyval2Tail37 : Box := ⟨14857315335259778885748106604485108042921277464364919787,199254173478852128667949307522192633038035120859927826063⟩
def polyval2Tail41 : Box := ⟨34091559042455966843977425041171161960123640119182226899,331173188222268053704748488586574137239057114607569874563⟩
def polyval2Tail45 : Box := ⟨78226407107818152134019162107932315696384587194478915120,544899125918549856265379712724748593765598255536663537366⟩
def polyval2Tail49 : Box := ⟨179498120381568237057303019274841076334903344454647411798,883526529046171605682974110801036591536661787601866522407⟩
def polyval2Tail53 : Box := ⟨411875943325739854768261185968486667665235635243229480863,1401597177897093296554224674046583846228072988628485872395⟩
def polyval2Tail57 : Box := ⟨945089521438174000230703016902183406831349065348766208765,2148615561664168614451070917721418520402574571500471137512⟩
def polyval2Tail61 : Box := ⟨2168600079723128435631325521428445252638081039671902772624,3109124210317355372599606001807928881783833778811459663533⟩
def polyval2Tail65 : Box := ⟨4976064382368564170932591633375377796617940220089919343883,4027500254037895500466859316629504525810841249440393409155⟩
def polyval2Tail69 : Box := ⟨11418065058698200767083984821903735110228204748233879989671,3941618741213628625564476081734515665032626236965087236231⟩
def polyval2Tail73 : Box := ⟨26218750000000000000000000000000000000000000000000000000000,2⟩
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
def resval3 : Box := ⟨104120259179666731731680938717021980236373584884543203792,2016702302971862424935415459846372079312266332450930415⟩
def polyval3 : Box := ⟨3702755522896624557374508903243745357044674300829958765731,235831081738266642444746995053665901905128391197279522950⟩
theorem cell3_lo : Holds Q cell3 (7/8:ℝ) := by norm_num [Holds,Q,cell3]
theorem cell3_hi : Holds Q cell3 (15/16:ℝ) := by norm_num [Holds,Q,cell3]
def resval3Tail4 : Box := ⟨-201232116738264548033591833780771559952816800202896427,2070668875437130995294990088597798575530118753606491065⟩
def resval3Tail8 : Box := ⟨-298404249208647800014829462127064555107398000361093928,2642717108534226128570093333382931306414807720471408609⟩
def resval3Tail12 : Box := ⟨-442397772779719973761959324628280402179980508887535445,3364996392335643246077357227857664525390609781118936429⟩
def resval3Tail16 : Box := ⟨-655874662254902411653803560920749101908157748566712869,4272942799576986921632652500640369528137805877672877629⟩
def resval3Tail20 : Box := ⟨-972363784476905981043167600224232058238240108467760873,5408179053619202752871614519505340141743437165539669886⟩
def resval3Tail24 : Box := ⟨-1441573190389189485759671106486343110491829571210603210,6818283707141014780418490582387505933979902021804411628⟩
def resval3Tail28 : Box := ⟨-2137197308687119772196027975572028143049819217535737938,8555503563145758589571026846266396287276002836697705124⟩
def resval3Tail32 : Box := ⟨-3168491455523201249139060049957782924147267880595019455,10673619049887949690831398750748736793492118402812442028⟩
def resval3Tail36 : Box := ⟨-4697431567462856026235498594199061398960683586902820883,13221710241576653860252687073528941461534009674011220983⟩
def resval3Tail40 : Box := ⟨-6964154279959353807853207705671367955149041095208704194,16232860586158440165841535366045694306550631743101394400⟩
def resval3Tail44 : Box := ⟨-10324672991728406924991774259823303593702983794142050551,19704750539449780647269950401278100893995590289141457358⟩
def resval3Tail48 : Box := ⟨-15306793632197960949629973420272005129855344849442415336,23567444403146112148624155798866449487237621068840100515⟩
def resval3Tail52 : Box := ⟨-22693012310065743410321663490732583937834335103572794190,27631176606167524171529045685744758325657091690943288581⟩
def resval3Tail56 : Box := ⟨-33643414818211565569985361380620719142580130023116998338,31503173721329435825731707851394029919757206575743306601⟩
def resval3Tail60 : Box := ⟨-49877880695820039213209079909574012844198082451492685799,34456871433114264458748179853997035908751380747356140182⟩
def resval3Tail64 : Box := ⟨-73946208971358506880109466456319846004182329091429274478,35228355284218590190266915943490951912730099193147886712⟩
def resval3Tail68 : Box := ⟨-109628566943062090405119775650335215956479891552872839983,31702057634975612736694746178755982932438532704128099891⟩
def resval3Tail72 : Box := ⟨722131581600133837592650237434471929441580160442322801910,1495747139638335051886883484209292082208172806423149408⟩
def resval3Tail76 : Box := ⟨-2403011165393233118360946474251675571516318685386035,25447229909502351565411681730954934851518918279402818⟩
def resval3Tail80 : Box := ⟨-3530910036940662469294646104198244359958447019597473,32494304327246689848344009148900969964660913683848654⟩
def resval3Tail84 : Box := ⟨-5234731980294701059857365849803152637882936656704765,41401285427038345760479016284479316103617802464820550⟩
def resval3Tail88 : Box := ⟨-7760726388028549516609721222345036833916155992202400,52611382980335128934066812870328563605391713609562080⟩
def resval3Tail92 : Box := ⟨-11505627088882894816217005531781176009620599568297503,66648379025981307001363813307604552932708904291727906⟩
def resval3Tail96 : Box := ⟨-17057611374195630466742934007775778885891293351328112,84115740620742435990475835646915078858683246063004323⟩
def resval3Tail100 : Box := ⟨-25288678621804568685547655432953566192631059860270537,105684097602200588935680475055117706808715190248323438⟩
def resval3Tail104 : Box := ⟨-37491607260109273961229185638077455142894558321879187,132057664100214716331374238195634695688042000035609433⟩
def resval3Tail108 : Box := ⟨-55582999648479659499786125975396868018784343962924397,163905021050190820057792687468860160735725083860432164⟩
def resval3Tail112 : Box := ⟨-82404305275278435924623236430209271410685708170292485,201731337677967362558702355491593187105406371737961562⟩
def resval3Tail116 : Box := ⟨-122168101233216163348545963360778169682922766628354609,245656362896836511207720959121947912336860684778230057⟩
def resval3Tail120 : Box := ⟨-181119723163383254624186874166386591332836855544841581,295043122885547749431321148872607887959923034691740904⟩
def resval3Tail124 : Box := ⟨-268518162987225388355630677108215278857914981539288339,347892864739446064416272658007842065795449513295401303⟩
def resval3Tail128 : Box := ⟨-398090294059211070973304293551957681353253891578585839,399877372372297891278663693542500276977611826440206528⟩
def resval3Tail132 : Box := ⟨-590186825580546416874486828268569660836525030100741023,442812858118328551965001381654376602484019300036394122⟩
def resval3Tail136 : Box := ⟨-874978602313294873032889490136347313946423858090430626,462279022793867760725691792643851022438707706035915932⟩
def resval3Tail140 : Box := ⟨-1297195294982446500514082805474009756958657595904924262,433935906340297031252102320099703230284145675912968609⟩
def resval3Tail144 : Box := ⟨-1943747042582364915060349284533469258515479736950136758,315196592538016885424081623747822535783008501657101924⟩
def resval3Tail148 : Box := ⟨461039382153388870726412338123765137558143957,4069513389252509315635822828004875144701456495⟩
def resval3Tail152 : Box := ⟨616864678111784165143345534531667033920202484,5189125594367711893745802289094661677396206764⟩
def resval3Tail156 : Box := ⟨914528691047986921431827631668085236189993680,6601547001059660768975115995746958107275528252⟩
def resval3Tail160 : Box := ⟨1355830054168596352347111265039012970990497208,8374017581286485347911350923159463961189341446⟩
def resval3Tail164 : Box := ⟨2010079239905473415475283748532637074940521991,10585580901075545328774435115068967470079525437⟩
def resval3Tail168 : Box := ⟨2980033182091870030410677703299420247177752485,13325530926536908753048116094904384905069045120⟩
def resval3Tail172 : Box := ⟨4418033672536325276431530543886851971467451316,16690143106191489917473520913340257923120640221⟩
def resval3Tail176 : Box := ⟨6549934292329993046036646487135562732747706673,20775408391535806389829314794325445057030290807⟩
def resval3Tail180 : Box := ⟨9710573167544744999625427499167907202930707840,25663128721439532172047540742628498018846939192⟩
def resval3Tail184 : Box := ⟨14396362930336596816110937593271994320514120959,31396247973297449380815597679269291100599384859⟩
def resval3Tail188 : Box := ⟨21343257709510968544411278922967889524948925539,37937029661956900128392925266783103094054633999⟩
def resval3Tail192 : Box := ⟨31642342712455407896701490797522214951993558849,45098258041648656129886544885083248310131969207⟩
def resval3Tail196 : Box := ⟨46911200996570870408073068010318912522421513250,52432443665571627175251521013164782847609396822⟩
def resval3Tail200 : Box := ⟨69547972441194231277090442258828286839903204875,59056177614670869480374867795304159787201885235⟩
def resval3Tail204 : Box := ⟨103108007638403535324482839621631161655885482009,63374986496138207048468645388059707885366611959⟩
def resval3Tail208 : Box := ⟨152862274283417951074894624441569585846769925366,62656333195130651350560102084023613808244955866⟩
def resval3Tail212 : Box := ⟨226625219859912462817238701837822745797607254632,52371865774122001938641449787986672250359624106⟩
def resval3Tail216 : Box := ⟨335982660474377917802238098550720468116568819705,25190204485487852843286134237499286037590930847⟩
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
def polyval3Tail5 : Box := ⟨32450384272514563053410948082401451769942278593108652403,292948719345992020901539804300596217560364540160474627514⟩
def polyval3Tail9 : Box := ⟨48106541170562992071261720185097606849205182064805061380,373132745032393993697454273952507620270092064111090264569⟩
def polyval3Tail13 : Box := ⟨71320117970215714625846365647594220110059654344682888600,473990259326040790107047881884854034578676163314493295923⟩
def polyval3Tail17 : Box := ⟨105735293356713704047360089270412754158455149922025171999,600189859956482260959649675911412633640523432978885735730⟩
def polyval3Tail21 : Box := ⟨156757343922442570488596293948239937655557347236264099260,757089783930072775155780436865762623474886186920172975573⟩
def polyval3Tail25 : Box := ⟨232399836360398678119620097918666124667711823489733318396,950610245040933578026527735797937441478135396370235470686⟩
def polyval3Tail29 : Box := ⟨344543244921666783372697829628934428587761101898698678130,1186908581146831206394765799636590270083744751794793308562⟩
def polyval3Tail33 : Box := ⟨510800908814151191725351401510297639016567277224478096718,1471722091150788744212798528161147165135510846009404254347⟩
def polyval3Tail37 : Box := ⟨757285398251483356704757555990685232573337935887920686451,1809166499540167085597409078322316123484383311784448060562⟩
def polyval3Tail41 : Box := ⟨1122709776958447084312840945315255846946181059225387990595,2199660426965969772708073002231857644257686419439783011596⟩
def polyval3Tail45 : Box := ⟨1664467908913120258965253911100699632338334010039097798543,2636467472506940642599855351287610384283706452848520502963⟩
def polyval3Tail49 : Box := ⟨2467648787478362897736450913774993793924138611911244817682,3100076667469688682418784678000838694842755862721139379828⟩
def polyval3Tail53 : Box := ⟨3658400685129265248262181682064667246411907908043763513181,3549233002090004052813964596525470722269479898386235785754⟩
def polyval3Tail57 : Box := ⟨5423744108508647126865979037193720942693409995995809639884,3906813547305714029363079361175552705976129444462908862901⟩
def polyval3Tail61 : Box := ⟨8040945398396910776142058032959489448204089689631064790217,4037818582471239338121673352888834607679514842711770785137⟩
def polyval3Tail65 : Box := ⟨11921064417214025968091961268723229075907367896022833557704,3715357829705416568003029658651050650779435529404800060278⟩
def polyval3Tail69 : Box := ⟨17673515985572626952776554707796884474950662112457644858388,2568431064747095965489444623425013899490327906517231494283⟩
def polyval3Tail73 : Box := ⟨26218750000000000000000000000000000000000000000000000000000,2⟩
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
def resval4 : Box := ⟨100484919456501661408752424925427363213866560347738991543,9889973250645295424545557113873574633516978293493027430⟩
def polyval4 : Box := ⟨4505040456338059606786036845808613021765787069415732630650,1843922414967538979597903024770157614384314301140200665658⟩
theorem cell4_lo : Holds Q cell4 (15/16:ℝ) := by norm_num [Holds,Q,cell4]
theorem cell4_hi : Holds Q cell4 (31/32:ℝ) := by norm_num [Holds,Q,cell4]
def resval4Tail4 : Box := ⟨-4539589838124153217593074271742955235409520621418100536,10501014210475760616676742182162391274917656251803984595⟩
def resval4Tail8 : Box := ⟨-5500745849249048155149525818460967921530256769591078443,11576574279376162696342454906208700324049243309020151476⟩
def resval4Tail12 : Box := ⟨-6665337364140453692445816937928625731443415260655371854,12724441575481961600086666177119261810090574365919118904⟩
def resval4Tail16 : Box := ⟨-8076490598954527355743209367608642595553783782815220710,13938879751473142080904768890662843560362052448084713209⟩
def resval4Tail20 : Box := ⟨-9786406423461724040351767398801025094992451947003650866,15210089574539465605184686008735290039969006226047352298⟩
def resval4Tail24 : Box := ⟨-11858337419171924227121857510388638502037664775462438267,16522961747387467032262281233984594954697210438529699024⟩
def resval4Tail28 : Box := ⟨-14368927700551372356329840041687547067736396181822231951,17855514575124199995016387975526330705671285684132594322⟩
def resval4Tail32 : Box := ⟨-17411048106108808639738130934103145437265966031211455101,19176941537503831413028938633961506895117933477006843303⟩
def resval4Tail36 : Box := ⟨-21097231642525607657387356570291477442341741798620828588,20445178144085381866387026085278588477141732449962022263⟩
def resval4Tail40 : Box := ⟨-25563836264527875569214912106124443103950564210040429600,21603877176103582676811499312274761963211300112735969642⟩
def resval4Tail44 : Box := ⟨-30976088978532781536598371084574439285476296586078623214,22578656705348334281583153681011384093091040148512955684⟩
def resval4Tail48 : Box := ⟨-37534197859708474110994826047629096815627601006283723300,23272455167370850449804445142818798213008537437592059826⟩
def resval4Tail52 : Box := ⟨-45480758075949793624454471814063102445355251239876596832,23559791088089497060916194463234946316069279421696209032⟩
def resval4Tail56 : Box := ⟨-55109725879703085033321159935421853247769248421095094039,23279680403675050615066646197696696702113195600437329511⟩
def resval4Tail60 : Box := ⟨-66777292530266321902381163867461869242406454645197815076,22226909954569918547340385764997492919675896272248044476⟩
def resval4Tail64 : Box := ⟨-80915060389339372652601599016610541144651802969994498563,20141299588686027996554269397917352482377471744789618870⟩
def resval4Tail68 : Box := ⟨-98045984918006465406611466265969386678323894201014764941,16694502229331208215775488486658632332570804896004301785⟩
def resval4Tail72 : Box := ⟨722402205959260465334168113172901757562788142145345242272,1490422561529596664469468969840993337878911717107755200⟩
def resval4Tail76 : Box := ⟨-56485749242538396352643464158973996885386043121674978,133672468326372304221413133849002576325359402403782528⟩
def resval4Tail80 : Box := ⟨-68418830895380861354499914598436082559191275117098281,147464414783113135927776407144571643464884035772354523⟩
def resval4Tail84 : Box := ⟨-82904136168937512205777636647684984601403262160362497,162212097405495464921004287090747537575260208452603557⟩
def resval4Tail88 : Box := ⟨-100456201959234580129025635535275339248484846114746496,177851491895057962585307586686553754134812376209380645⟩
def resval4Tail92 : Box := ⟨-121724306873788461400782118973785420097007886337315466,194269339606321202184668470541188318159259593292771356⟩
def resval4Tail96 : Box := ⟨-147495192879351538730543785931519819461890180674226010,211287502751313556322510461641281601132203209054469803⟩
def resval4Tail100 : Box := ⟨-178722167176305339707468790365767943971392587405184203,228643690073957818806422166551063541207280697734890194⟩
def resval4Tail104 : Box := ⟨-216560366589865127438605647590628873370497447385787536,245967351926608176017921679892203991375328468818817658⟩
def resval4Tail108 : Box := ⟨-262409487969517391819638657274227562677963622162777719,262749620454795115033980577374660491438527141880010583⟩
def resval4Tail112 : Box := ⟨-317965565263532543693921359787601674807176049467897941,278305918844713951172574658848584080790151762595932667⟩
def resval4Tail116 : Box := ⟨-385283708587176640885253204265163645667258832549524250,291729556644787414725369333367439051586548385051530215⟩
def resval4Tail120 : Box := ⟨-466854126105313309215067180999409583171516409060162628,301834254130622789246619307176140024098384398298294732⟩
def resval4Tail124 : Box := ⟨-565694240903104415409600890634612519357701392366698110,307083083049763933715074367701241398729664682344834302⟩
def resval4Tail128 : Box := ⟨-685460310398437925431453504288613842375084274444072590,305500756259713754928430864021358128649736283564319224⟩
def resval4Tail132 : Box := ⟨-830582677280614323687727837958689926491194641394761008,294565523390665662722787512546390822638692549783002919⟩
def resval4Tail136 : Box := ⟨-1006429655132375781212230548274180105177464750842039137,271076107779289694589736430978487307496294430504965002⟩
def resval4Tail140 : Box := ⟨-1219506141521090205532191874187717087316510194745136736,230988115490955065223802369999429754759755628112536024⟩
def resval4Tail144 : Box := ⟨-1497294539267825940680338520228528094508832856291266933,166974288654487006850004453614389098082629332232419460⟩
def resval4Tail148 : Box := ⟨14249813035367369366444077214707253398926309102,30327729968491107127078588174953849373959968969⟩
def resval4Tail152 : Box := ⟨17212338914563397977535324382855300372989746843,33349823873413935886550370160192336862590067322⟩
def resval4Tail156 : Box := ⟨20856451855409552694569283715433382594792529874,36552388511321834121472816922796394665172725080⟩
def resval4Tail160 : Box := ⟨25272079736333747615154738091528993940161460756,39910555196903034501133441000444101641815118982⟩
def resval4Tail164 : Box := ⟨30622563158546271778692052479591852895280175269,43386524461284107108359085621652988026019498518⟩
def resval4Tail168 : Box := ⟨37105825249948559989160774569697540884117272271,46924914776592533814112051650555314615328107875⟩
def resval4Tail172 : Box := ⟨44961692473331232052948313817879751627285521376,50447742995997948270673976408979256269288378787⟩
def resval4Tail176 : Box := ⟨54480766199081176771844583154727032785536091679,53848166447482696259021716649835414675676788244⟩
def resval4Tail180 : Box := ⟨66015172524910830929882994871462869289723334058,56982700700282055563236975564460840658783813434⟩
def resval4Tail184 : Box := ⟨79991587995824478357778634598712438953930288288,59661563275213057493988765780361451798123552295⟩
def resval4Tail188 : Box := ⟨96927023066995668337959212107541522842260653321,61636715870374954737522803704814876169156331485⟩
def resval4Tail192 : Box := ⟨117447947165648428201195670658883738588297141569,62587083028567337831309509432141913573169774258⟩
def resval4Tail196 : Box := ⟨142313462819244526933297992052500144774910941469,62100309927590673441508083720466487518591709492⟩
def resval4Tail200 : Box := ⟨172443386098860617188713123534450254970420929044,59650281691893970032214632493411794442290121943⟩
def resval4Tail204 : Box := ⟨208952272119258201149807756824223257766027501146,54569455916550719682135429684032360033372461532⟩
def resval4Tail208 : Box := ⟨253190644254519351271359440966494201295008893289,46014852422740674721986024554345490387937148969⟩
def resval4Tail212 : Box := ⟨306794952217104370177048112639263448248805854130,32926291688430952221189491175040095178230932818⟩
def resval4Tail216 : Box := ⟨371748626494977866469039974926809407051637657989,13975092766300932470506025484612801326372254429⟩
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
def polyval4Tail5 : Box := ⟨1001234487799426505861792408935009287273122800753207879289,2024089105596033503551601716868319481695565445754200867599⟩
def polyval4Tail9 : Box := ⟨1213208915034657784249315732442268200656094554618406599905,2221775072841226190863095801833569566043472708116538114685⟩
def polyval4Tail13 : Box := ⟨1470063683251490287765795155755974440883905315695962367853,2430055285252671221066378230979227778340151387723840782080⟩
def polyval4Tail17 : Box := ⟨1781298510337085047210483219889178003115003467525332987576,2646939881121376094265540720201171765538188857069072732638⟩
def polyval4Tail21 : Box := ⟨2158426481165246914642825462087429694916959298059434557596,2869444568396102540306286063297825911058047127687928758969⟩
def polyval4Tail25 : Box := ⟨2615398175858676921675516141400343578110501303361218029672,3093302453217263487378589226631168571138138117128009247475⟩
def polyval4Tail29 : Box := ⟨3169117724404534776013321799289790452959751728324405243995,3312604370527722628265252694098000595528710916540667017156⟩
def polyval4Tail33 : Box := ⟨3840068118055331656385421590981881406483326158511849791808,3519351134366309800539219923273115232588795670751366842272⟩
def polyval4Tail37 : Box := ⟨4653068908658405014964458379495683103237021665839468048507,3702897444058290233259198755775110609350807213504534853758⟩
def polyval4Tail41 : Box := ⟨5638194324450665810154923921454611561955516113193168422069,3849262673566987753327602696221487055731264239517901175736⟩
def polyval4Tail45 : Box := ⟨6831885764922687010547218536382235220498966496829855818075,3940278278075099832396926111372802789762437007439890352542⟩
def polyval4Tail49 : Box := ⟨8278299827755724139582975271204525023309197024492977033355,3952534862035246868801747521711569012846321100662336119768⟩
def polyval4Tail53 : Box := ⟨10030941733551654907060144512826923445734374321571001211979,3856083808566236528294072642479655293309402977850443345810⟩
def polyval4Tail57 : Box := ⟨12154644571406717855027474779995969755410551281117493795866,3612838458055319435795482830520806972131141595032337802684⟩
def polyval4Tail61 : Box := ⟨14727967580858249943025770547856194726252716747124729276648,3174607764045858874473853692506347123346299914070061106850⟩
def polyval4Tail65 : Box := ⟨17846102186576891187924588560264119391313757072348802771917,2480680685561732879624888433121228662144079605158238297119⟩
def polyval4Tail69 : Box := ⟨21624393308309701277764162688297447423085668538705501279589,1454861733542293963883342382787777520437369484929899303945⟩
def polyval4Tail73 : Box := ⟨26218750000000000000000000000000000000000000000000000000000,2⟩
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
def resval5 : Box := ⟨86331421014323686884024033437674947836615012099473294446,16403497126933872137136716683088057504625403883050806214⟩
def polyval5 : Box := ⟨8428346983439327500790114621004671906180679765925295052398,3687579405533420817609830760763208806516320087921056444611⟩
theorem cell5_lo : Holds Q cell5 (31/32:ℝ) := by norm_num [Holds,Q,cell5]
theorem cell5_hi : Holds Q cell5 (63/64:ℝ) := by norm_num [Holds,Q,cell5]
def resval5Tail4 : Box := ⟨-19667634707885199060530832062889568861426871437263319715,16442380021469339062878439878234004489590174682438585547⟩
def resval5Tail8 : Box := ⟨-21624843634298576812227409261008126067286651638749344513,16833086483096629422405104398255362225625558878874691028⟩
def resval5Tail12 : Box := ⟨-23776767030060908156912199393019864232217900897103636337,17181691546124735397011174806485011229228201070425582862⟩
def resval5Tail16 : Box := ⟨-26142831820477181088051039352979877445576628059491618507,17478739169242120810039465274078523077907793913471106793⟩
def resval5Tail20 : Box := ⟨-28744347569607089180983207672054880230105049506959881409,17713490976038691974860291447053136225682087603014376227⟩
def resval5Tail24 : Box := ⟨-31604744385617800256018296961955248629821923363538539469,17873775377963480252799681693701891125314755882641046916⟩
def resval5Tail28 : Box := ⟨-34749783944875024608279180527409693064288731890384248209,17945821245404572777923682269158761738977675434356030052⟩
def resval5Tail32 : Box := ⟨-38207791510093848960359906562525927785926740826927078639,17914073485829260716973977094207685394717756824497676578⟩
def resval5Tail36 : Box := ⟨-42009911036989321004990665448281072710326137201506992323,17760988628123868220100830473344570318399258467882702496⟩
def resval5Tail40 : Box := ⟨-46190385667005076484511868563288029007100964789906245179,17466808316775600689595005347943649336150272912591673721⟩
def resval5Tail44 : Box := ⟨-50786866132329971140163661572264930485682064079859182223,17009308403986656417777782072783629272194429098452487320⟩
def resval5Tail48 : Box := ⟨-55840749850799931985932432335666788044199321551501643130,16363521090357346629159350015205812091569659851196720919⟩
def resval5Tail52 : Box := ⟨-61397553764685462304784094922370552959034263821421703783,15501427303211484328069510671747663815861640377914266561⟩
def resval5Tail56 : Box := ⟨-67507324281273785957699497726997996897541406285629758328,14391616213533359893100930030147736877133994957440943359⟩
def resval5Tail60 : Box := ⟨-74225088007304673994395994281307405285465373616487265251,12998908475166684742247478708482396661675058204559240899⟩
def resval5Tail64 : Box := ⟨-81611347335365712359781256547585703989406747672418065630,11283939420241198157590842423993349834090920565683388402⟩
def resval5Tail68 : Box := ⟨-89732602202463051199070504217327062772300261628959721339,9202695310407878381283726536279080888915263292777500315⟩
def resval5Tail72 : Box := ⟨722379085240794026278123542867262472262549237140392087030,1521816528130381859396025757794346310882960895001526847⟩
def resval5Tail76 : Box := ⟨-250166621986982305235923939594299322681499965938770032,212403935911293791973438259773195808814156782174711947⟩
def resval5Tail80 : Box := ⟨-275037720540034803596641491941169933158526718794142369,217586133286286190250268876289057104279279153304645645⟩
def resval5Tail84 : Box := ⟨-302407170715149028676048432856563655327157570392649244,222247006061255294776556304494892013429044191858878115⟩
def resval5Tail88 : Box := ⟨-332500200523611224465608637906720697589139293576360588,226266906756816043849704397954390295988142078189414412⟩
def resval5Tail92 : Box := ⟨-365587836713560905056700369718058270929365518607354386,229510218346619851392377822739492966957370192248008448⟩
def resval5Tail96 : Box := ⟨-401968077440033834128762137970162833646980000745164553,231823157802949714748389633048459366114416884236963709⟩
def resval5Tail100 : Box := ⟨-441968575140080823721600896543729173599246560542625466,233031664661080842281784408750713140752339990141663819⟩
def resval5Tail104 : Box := ⟨-485949587478109633693365912298423551432813860132699325,232939059754362174059863506019877668521669215765990750⟩
def resval5Tail108 : Box := ⟨-534307221945132030107401313093104730595160413530687720,231323449937251334679403859118806070784830991523457773⟩
def resval5Tail112 : Box := ⟨-587477003333364627382560011460352223277542296967578668,227934852151827794906883195263921570558584873741929775⟩
def resval5Tail116 : Box := ⟨-645937796216034319426567750686807021082446651329694349,222492007452993875991619267501983707984563743142180765⟩
def resval5Tail120 : Box := ⟨-710216117759534067925193837195785029387335388208074456,214678852588762899535196229619740020383368181515232531⟩
def resval5Tail124 : Box := ⟨-780890879710536605581307616591377524044840044815173205,204140613406660438191222735768361503933643725516915770⟩
def resval5Tail128 : Box := ⟨-858598602265964737363261157656903414335365755217321632,190479480694421464833517879948047504511298386204567542⟩
def resval5Tail132 : Box := ⟨-944039146783653483762071624424338542885278948077674334,173249825028843939796357711599529002475394457700192211⟩
def resval5Tail136 : Box := ⟨-1037982018968078031419666301834749293941187578810807928,151952902762781829656726104856535494899342210542141594⟩
def resval5Tail140 : Box := ⟨-1141273329014059303121437123853155787362533140331052988,126030996143471352974569710904195960560582104692521093⟩
def resval5Tail144 : Box := ⟨-1273980955470141531067152802715748627270134930637065602,92814799305383692733535527018258919099891250843539050⟩
def resval5Tail148 : Box := ⟨77851108198558137172785457662814305948950710473,58694230148866254534048830026198834930834528529⟩
def resval5Tail152 : Box := ⟨85548901067167756327449656508847162274671758133,59826149769258934169530026648328225973463209609⟩
def resval5Tail156 : Box := ⟨94062010706950595477033417248810323428855988414,60765301886447633577956289796597863257608904868⟩
def resval5Tail160 : Box := ⟨103422274504073302232963033017728091365878795634,61471885144747125714630526644653244077227345098⟩
def resval5Tail164 : Box := ⟨113713993388269622682588092930882871772722056486,61901558098637464083383769223814848900247211322⟩
def resval5Tail168 : Box := ⟨125029857971245632608703802554960888120050744998,62004188533088462842622509430636551187840431895⟩
def resval5Tail172 : Box := ⟨137471782658566374480313561397481493812708200342,61723187579553179996282439283574622892853345823⟩
def resval5Tail176 : Box := ⟨151151823524188803233937735043339797567261126283,60994771760247132286432855442839447496240000620⟩
def resval5Tail180 : Box := ⟨166193187524391519953551260463383438118018464834,59747145391532231040574061800759804165054688126⟩
def resval5Tail184 : Box := ⟨182731342140225735808038983112703587159959945207,57899595017706833818578751825263068426398580460⟩
def resval5Tail188 : Box := ⟨200915235442292782426413265125820280419886155480,55361486691473741470947314946352336096508486948⟩
def resval5Tail192 : Box := ⟨220908637566153624519490013479791125839546459052,52031155975529228945147087510720508127517348041⟩
def resval5Tail196 : Box := ⟨242891615680139994582063087169171334933962043468,47794679502347807940122698292324560497901223280⟩
def resval5Tail200 : Box := ⟨267062155729613330910959888345819603771175550218,42524515786703968521368268558772015152871040533⟩
def resval5Tail204 : Box := ⟨293637945563634769933473022766651494003720825628,36078001727182683235610651101118388394234345742⟩
def resval5Tail208 : Box := ⟨322858335503477206621959980365928107660933967207,28295689847231014575729541485570606009889591388⟩
def resval5Tail212 : Box := ⟨354986494022025853858809007414366215817805425799,18999509798478195769503059144966973958161731897⟩
def resval5Tail216 : Box := ⟨390312285505764177063803392499822259084741302934,7990667691737502325563989953306173344135038470⟩
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
def polyval5Tail5 : Box := ⟨5223407445827091544626626777052117724893700443486167385918,3757037063891329144437276566190203509719920507642772104252⟩
def polyval5Tail9 : Box := ⟨5743195291024636392920091789841657317521841776914294666531,3821154389612163858602746152224560101335269861742894314426⟩
def polyval5Tail13 : Box := ⟨6314710002907395281392941003853402290226765887524850531103,3871512161232730228372130391456265338515416740583747857564⟩
def polyval5Tail17 : Box := ⟨6943097074229989010301613194072477528665759260464212040728,3905431622804465766687244243817673025878314493923661966652⟩
def polyval5Tail21 : Box := ⟨7634015965893397983592939569220550036114127186319544318698,3919882328677737044035902739300361243629013009846338878111⟩
def polyval5Tail25 : Box := ⟨8393689321127422911628225879139652658542358577104485888220,3911441589185346837942071863009704625981887316395888089637⟩
def polyval5Tail29 : Box := ⟨9228959008518841152978531041326874937752697323390372537629,3876249541835213912929264119351644835290450744726950492104⟩
def polyval5Tail33 : Box := ⟨10147347742134530086869728381185012652263986250043281771773,3809959368213604356965815410431570905482765577888289815963⟩
def polyval5Tail37 : Box := ⟨11157126833563455476590043072534029712551857249773379145614,3707682148611164695531639820943964362429783232352969995063⟩
def polyval5Tail41 : Box := ⟨12267390686074643561652850794760409188932358453844884969522,3563925794216506295547741656099798832289503928194304811599⟩
def polyval5Tail45 : Box := ⟨13488138701810072758313294153021740574902505351123236535067,3372527439254096958264493542490593837399603044897594594816⟩
def polyval5Tail49 : Box := ⟨14830365339695656576099290140136339509581646219580765194779,3126578612144257532480964386485001699408928677006973683128⟩
def polyval5Tail53 : Box := ⟨16306159135161542550697528338193340331136665895808189620223,2818342435045597327589497217293461039064275276569031683128⟩
def polyval5Tail57 : Box := ⟨17928811573475960062222257665827942896368460917597759546781,2439162024357764700313272060276264152872670990499400593377⟩
def polyval5Tail61 : Box := ⟨19712936797241743717609132641408618877164657810936851004087,1979359180203612152855720167497254642042512273186815107936⟩
def polyval5Tail65 : Box := ⟨21674603226183481817937278710165718590672443144626775389966,1428122359791643833056801236181726708361855071759233506136⟩
def polyval5Tail69 : Box := ⟨23831478297645819395554251395159995775315541571027833003441,773382823820796165180662473013698137296176770804717144113⟩
def polyval5Tail73 : Box := ⟨26218750000000000000000000000000000000000000000000000000000,2⟩
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
def resval6 : Box := ⟨66073070291029812702613071058550093821002980015247472558,15300237356927444412346465741173914202437725220618061923⟩
def polyval6 : Box := ⟨14890985548402098375387925474285424612091364784559171710706,3690493059459791250509969638702640743820727457736299643748⟩
theorem cell6_lo : Holds Q cell6 (63/64:ℝ) := by norm_num [Holds,Q,cell6]
theorem cell6_hi : Holds Q cell6 (127/128:ℝ) := by norm_num [Holds,Q,cell6]
def resval6Tail4 : Box := ⟨-39981247453063492666305662837569857306200669434575368372,14766053715528554522328098563171374624412063071984466593⟩
def resval6Tail8 : Box := ⟨-41911636250489297156515256529497358626255006147854829908,14580509014120719556176528064738246123556449506448138845⟩
def resval6Tail12 : Box := ⟨-43935178260330254871176522019122839460240417189386001073,14357372827722557827356188871972103818502840775202046952⟩
def resval6Tail16 : Box := ⟨-46056419200824125367498700183490674194444739295022273728,14093916676076449989193823958414187633709288286987162942⟩
def resval6Tail20 : Box := ⟨-48280076093764636301970452734694862456849267883709490217,13787252210987830434444416100850955689575575544732286589⟩
def resval6Tail24 : Box := ⟨-50611093699138316921845040618926974778054395183141982833,13434321621133206223947063973010632700173648209955238545⟩
def resval6Tail28 : Box := ⟨-53054655515627352320551259723224465566033426188850662900,13031888493582018094759286001171224540047292303571557634⟩
def resval6Tail32 : Box := ⟨-55616195307192331468025106373413539274779957751330583940,12576528203787798801026974864839727067832849305615179823⟩
def resval6Tail36 : Box := ⟨-58301409186167755835710766533434768990615459823076485433,12064617810144162331822792275378786915464044753804328808⟩
def resval6Tail40 : Box := ⟨-61116268279743284170275763416649471126089648108826530743,11492325428182838634309696465823058059784573241804787874⟩
def resval6Tail44 : Box := ⟨-64067032007997260569891601546476166510782056589339283307,10855599058255915059764509465961550158410834862410866655⟩
def resval6Tail48 : Box := ⟨-67160262003008973636713026325564728077792691398019632381,10150154839248551133567003947919391217909973838901795565⟩
def resval6Tail52 : Box := ⟨-70402836700001665172647426466410501102008263260759977404,9371464699508919845320001829030387078735954599085356855⟩
def resval6Tail56 : Box := ⟨-73801966632962702703037316384534453813684882550956270052,8514743374755891607061897838213979111120595793512570881⟩
def resval6Tail60 : Box := ⟨-77365210468752957580894950135707687840096039808387403080,7574934761228587159398212562631536088835448458434940238⟩
def resval6Tail64 : Box := ⟨-81100491814017614967403392260478265904575467868876135251,6546697570561061117988408304735622507919603150058609869⟩
def resval6Tail68 : Box := ⟨-85016093947111157362195420813735199586550234802887062315,5424387438507908648066556926064660976454172676678660187⟩
def resval6Tail72 : Box := ⟨722196158110281127437457032627421220321474169528494217447,1482082710641733295009950810610049327805685883387588600⟩
def resval6Tail76 : Box := ⟨-512966936146369262940674808634484609485080633322234794,191653277442204408202905518287852758835710863246543838⟩
def resval6Tail80 : Box := ⟨-537711285090489273124957865828044875147360942460155945,189342945737745069850165635704283176083868741966653663⟩
def resval6Tail84 : Box := ⟨-563672603365000309297013173185926162587166829925109952,186552859533992034904558103791249476586986634274880713⟩
def resval6Tail88 : Box := ⟨-590887364989115809447897444912309170266342533937543944,183247798671494589458945730311233090463004989974452216⟩
def resval6Tail92 : Box := ⟨-619416086607272514453714170387074278259597916313708773,179390780465073789639981825502802467470003443373277959⟩
def resval6Tail96 : Box := ⟨-649322207718786166083127919000838755749489010394717146,174942650454850638687826411198349534806776312882650626⟩
def resval6Tail100 : Box := ⟨-680672230755474694593747493823511173814298242729642142,169861965213665114793787706437145212176744983686143722⟩
def resval6Tail104 : Box := ⟨-713535868963056240081592117762799460288880982942349955,164104869131446374160479590017975559256758322291369176⟩
def resval6Tail108 : Box := ⟨-747986201422936143958812284387378206949225346396785824,157624964845810404414080342551641627273170169339240778⟩
def resval6Tail112 : Box := ⟨-784099835558625289554996148295420234438060910633890095,150373176999195566192289816943442537434280690624167795⟩
def resval6Tail116 : Box := ⟨-821957077488155243648770247115358798123012756478804172,142297608987021340054191228299710367590875765450613829⟩
def resval6Tail120 : Box := ⟨-861642110601303939961949617103125032160762049071689067,133343392344732372699121389122124564046590813751755128⟩
def resval6Tail124 : Box := ⟨-903243182758735217858792585833450704712832047493947601,123452528404150513307676336106695776953383266008882073⟩
def resval6Tail128 : Box := ⟨-946852802529328154155086848684161168623096273150819739,112563721831262175933068487887314835856591475395257789⟩
def resval6Tail132 : Box := ⟨-992567944902074413258115659127483501318649016526451206,100612205638374489130304380661781108474057116748746692⟩
def resval6Tail136 : Box := ⟨-1040490266933641062824638769565743745866907921951588561,87529557242800575379325574194632279020795083008029997⟩
def resval6Tail140 : Box := ⟨-1090726363199365257265951386871213022877902442083003322,73243501025455313745173607955170792317640016970460779⟩
def resval6Tail144 : Box := ⟨-1162302270886834406793484542580191505508909671107634311,55722950937877991005368046284768346446965250522683112⟩
def resval6Tail148 : Box := ⟨179386523924980410007413896272962947026875751981,58055312420587267521049173933732720736061176293⟩
def resval6Tail152 : Box := ⟨188000531584486185699399020066772579052866891331,56961658519972719336582919417702755063429771879⟩
def resval6Tail156 : Box := ⟨197077412763268321927191710877382403677109209940,55691726592484829021957098535284304254753926329⟩
def resval6Tail160 : Box := ⟨206592536928998014773602565301329383870490397042,54232360039131625899448445287891254590068539117⟩
def resval6Tail164 : Box := ⟨216567062233909181653026234356074270824044588843,52570329505760811458538990651777481677367022052⟩
def resval6Tail168 : Box := ⟨227023169093204238904530742381734300437973510244,50691636795451170343510426213565331262183393952⟩
def resval6Tail172 : Box := ⟨237984108818241883030739399382866586231359546919,48581473582791317571227061379345613710442272021⟩
def resval6Tail176 : Box := ⟨249474255320437077968665044187817992076718358711,46224178020447780291025086652065814754206359285⟩
def resval6Tail180 : Box := ⟨261519159311682687401969088768849338191109324020,43603189114268667753508160710102430106516408596⟩
def resval6Tail184 : Box := ⟨274145605121630097752960396394024466472123338936,40700998754830821751303295844693952970582758224⟩
def resval6Tail188 : Box := ⟨287381670258173502263601925074567914443087285974,37499101287795628783402458797806370182641020027⟩
def resval6Tail192 : Box := ⟨301256787843582872587291020261167536049249829491,33977940499616204323771083668238225272632297532⟩
def resval6Tail196 : Box := ⟨315801812065125244063855929944804437199844572563,30116853889030500816479417483060311421539253115⟩
def resval6Tail200 : Box := ⟨331049086785717277809759222290504890034472927263,25894014088367122389145412162192396403292769683⟩
def resval6Tail204 : Box := ⟨347032517467179055135365236369602372636265088886,21286367291968633263494195917448918137323701742⟩
def resval6Tail208 : Box := ⟨363787646566029852052723412617756286857958016705,16269568541984707295225937246131472254906264076⟩
def resval6Tail212 : Box := ⟨381351732580881766122780809359957242647384816468,10817913712552338504322925260639509506484206093⟩
def resval6Tail216 : Box := ⟨399764334733222565237187265531624073183631879665,4904202243315605757672823647269658829147017519⟩
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
def polyval6Tail5 : Box := ⟨11755246028416640065896182105506269483118132226031145887422,3617645333004209075726029293765165365751988923732040003644⟩
def polyval6Tail9 : Box := ⟨12322800986730510932823082838424099413764665913439265136578,3540022902801551185300940456141953398350626007068513297988⟩
def polyval6Tail13 : Box := ⟨12917759991855664842078373099351485002333091602540146314983,3450612417528832858333424092868288207544028245677314043955⟩
def polyval6Tail17 : Box := ⟨13541444302222589303268369700158716786953407711484533071446,3348588468780824233449400702236962434187057399418690923973⟩
def polyval6Tail21 : Box := ⟨14195240808453543920494779489076660754667008513897831961918,3233077650504235662276745973022780660253951762882556898661⟩
def polyval6Tail25 : Box := ⟨14880603361999676638458864604216426146609440048361334856902,3103155960736281032655206301015327574208586639510434902641⟩
def polyval6Tail29 : Box := ⟨15599056007932515972520225167470519278717168455464335112268,2957846090207871878156122239534536993551369075370689926109⟩
def polyval6Tail33 : Box := ⟨16352196373972595203977139380998842963975874512313488957952,2796114571482059634409778086444006944789670371083701685600⟩
def polyval6Tail37 : Box := ⟨17141699223144380517644922077744455804476962800831152112043,2616868781617675675796485310151117232500156387989441564215⟩
def polyval6Tail41 : Box := ⟨17969320177957465623660056807406355925482129981862450206954,2418953791004719247117177762706342927200667538173422773106⟩
def polyval6Tail45 : Box := ⟨18836899624395517998022278220329490652604322185964489087044,2201149050654043920662490523195879373803179507065893964144⟩
def polyval6Tail49 : Box := ⟨19746366804394301801495516074222988792024907877439917022827,1962164909842029425656504643885967216414910611493219027402⟩
def polyval6Tail53 : Box := ⟨20699744105909246898490157001575046240667100381284711844194,1700638955610330069381411446610135975290666941032382797789⟩
def polyval6Tail57 : Box := ⟨21699151560112414542409353315441779886386468704176227450443,1415132165200549715052981367269272391800517539301917369228⟩
def polyval6Tail61 : Box := ⟨22746811555719308163781485811745635276305662056044600582244,1104124862062847614934059092034543175585383438358663876499⟩
def polyval6Tail65 : Box := ⟨23845053780931565481345336193520674004210677863601204216220,766012465614552902222903502467309010261672059165802304359⟩
def polyval6Tail69 : Box := ⟨24996320426741703870984889752109221959935936214884150995747,399101021350972266017014214993399107378869389254163924928⟩
def polyval6Tail73 : Box := ⟨26218750000000000000000000000000000000000000000000000000000,2⟩
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
def resval7 : Box := ⟨41569322916790619278173936201600152259272988698683288085,25101112402138560318121066465530862716242441959250426116⟩
def polyval7 : Box := ⟨23445196876422294434325278192451238638327089955592921815256,6442724235962459041522705989673858053164110974242621433887⟩
theorem cell7_lo : Holds Q cell7 (127/128:ℝ) := by norm_num [Holds,Q,cell7]
theorem cell7_hi : Holds Q cell7 (1/1:ℝ) := by norm_num [Holds,Q,cell7]
def resval7Tail4 : Box := ⟨-63627839834898058061564415382221978209671843781714912565,23728993511151839141136061193069151861965801695811164228⟩
def resval7Tail8 : Box := ⟨-64631856705809565541909878163632981571085091023594700277,22725021671590996979736944784810261972972220573981719746⟩
def resval7Tail12 : Box := ⟨-65651669087593019179687115253530150098696534780322777023,21705209294465965426813024560780914765513857658150598698⟩
def resval7Tail16 : Box := ⟨-66687572868044560672616063609395118441961032311958637865,20669305514018021929158317387969194988134192974252971146⟩
def resval7Tail20 : Box := ⟨-67739821954822833494736301443217702942531947754011050120,19617056427239761147750809889069474603089372218161786536⟩
def resval7Tail24 : Box := ⟨-68808674257057990732689350158226167611276611875923506691,18548204125004604042488216150895027330329566895267994128⟩
def resval7Tail28 : Box := ⟨-69894391753369909900531185236329118304371562234493740673,17462486628692684878606221351627775935382150656654050010⟩
def resval7Tail32 : Box := ⟨-70997240556083607464695290442187073118054322699371873900,16359637825978987314693679420081815628604776125223491624⟩
def resval7Tail36 : Box := ⟨-72117490976454109293197807036337196765704564382854201465,15239387405608485486196135769519161399708378001327044715⟩
def resval7Tail40 : Box := ⟨-73255417590920478007145785296858627936433851054420838278,14101460791142116772186550744520480526335926836269926338⟩
def resval7Tail44 : Box := ⟨-74411299308405248465282060846718613652763859594350435424,12945579073657346313765609796058144810979368891969628216⟩
def resval7Tail48 : Box := ⟨-75585419438675766781197137385012878578251689485322840909,11771458943386827995241468073331511495663834510736366772⟩
def resval7Tail52 : Box := ⟨-76778065761784188388506943688335782252523965070585020535,10578812620278406327012074371243876141053292103183791229⟩
def resval7Tail56 : Box := ⟨-77989530598603151834502493312945558284803756222076749764,9367347783459438602863403085829517262329632907064573090⟩
def resval7Tail60 : Box := ⟨-79220110882473496625577234677162309770510434147623961982,8136767499587975350024767536966860243985307070915369293⟩
def resval7Tail64 : Box := ⟨-80470108230647956162957876572208536539068901365258517845,6886770149863719855893508056928764977656834606591516581⟩
def resval7Tail68 : Box := ⟨-81739806299239723249928430900704588451035732324796074498,5617046565830795596628971620329129984721176276430177384⟩
def resval7Tail72 : Box := ⟨721931534114919703202684129202732085537914306883953664734,1606626982009246306152443175276270399542823423815770588⟩
def resval7Tail76 : Box := ⟨-819281874004496360313243438697901413101079721137244783,307607316027951973246059547032486565078367707234879598⟩
def resval7Tail80 : Box := ⟨-832187564827852910122541735197874346974129277305342308,294680078039125293675571872761105485579338384274347880⟩
def resval7Tail84 : Box := ⟨-845318475132502300945756147673660335136895722398261564,281549166713874056637465297129279299574578519885071903⟩
def resval7Tail88 : Box := ⟨-858656576298997395207439600036284323320502811717721761,268211065546871606141344442098505558716600688418558117⟩
def resval7Tail92 : Box := ⟨-872205136539066331796849789338773256723980671309132382,254662505306801437115428381151618109978276728089663094⟩
def resval7Tail96 : Box := ⟨-885967476641360273998850317851891218317270654424732422,240900165204507484179493244327379471041799141765242379⟩
def resval7Tail100 : Box := ⟨-899946969793042080313525869700065137894639282913412650,226920672052825677585814422339573693834091668257968941⟩
def resval7Tail104 : Box := ⟨-914147042406081504034214235623148659385164533781406207,212720599439786253846123713271395067215280767684051421⟩
def resval7Tail108 : Box := ⟨-928571174957077008965014631071109928179311450704359138,198296466888790748912353992677587467881722235214049108⟩
def resval7Tail112 : Box := ⟨-943222902840330085035690911221424635841787939646164461,183644739005537672840919563243350237669141287770437148⟩
def resval7Tail116 : Box := ⟨-958105817234380051698811518896153217669996150797786958,168761824611487706178556211724774055349205794246948118⟩
def resval7Tail120 : Box := ⟨-973223565982211730642205976040784379270133240639750263,153644075863656027248181474380269872266871509104235529⟩
def resval7Tail124 : Box := ⟨-988579854485351729260201158924772587217657948599550452,138287787360516028924666335020076719547885015539467946⟩
def resval7Tail128 : Box := ⟨-1004178446612072500303886506871947323731987065363332368,122689195233795274918366810391992865603613473562865799⟩
def resval7Tail132 : Box := ⟨-1020023165619930782660878083149805409291030369510669949,106844476225940289108909710115265381939058959490983967⟩
def resval7Tail136 : Box := ⟨-1036117895096496258882304979739101909532817373728165518,90749746752390760692896657474246075584581748667873532⟩
def resval7Tail140 : Box := ⟨-1052466609093264447539099355769485686172084641969436239,74401057885849554632740628257951248659786749214565109⟩
def resval7Tail144 : Box := ⟨-1087841663460781120285091979562477496286499005358366150,55855746808654954113844490112869670754149182308204498⟩
def resval7Tail148 : Box := ⟨311272211616568128360071296435742954930527036821,99857587567879625087455539712068283889388524307⟩
def resval7Tail152 : Box := ⟨316138199807998562139533744966320317724098367632,94946139073004245641510047443635551375458262410⟩
def resval7Tail156 : Box := ⟨321126476798906750520604075933053360284444657731,89957861375281521023329432430144571000279519635⟩
def resval7Tail160 : Box := ⟨326193463456341676802165929949498131157747766496,84890874717649105087029171114531319354518070188⟩
def resval7Tail164 : Box := ⟨331340401023167209402545882130585298965359955039,79743937150823268404180764431631098947004307927⟩
def resval7Tail168 : Box := ⟨336568551027655342850632217618098445059513424949,74515787146335133175610766080164600672796719037⟩
def resval7Tail172 : Box := ⟨341879194903657559083511461304498241051374309895,69205143270332916910468004111873451276011582292⟩
def resval7Tail176 : Box := ⟨347273634304498940869026920384869787778344005953,63810703869491535123375140977653376156980650162⟩
def resval7Tail180 : Box := ⟨352753191422016677807160342274849780071821224134,58331146751973798185056523287519417482904488393⟩
def resval7Tail184 : Box := ⟨358319209310632896920166624530692164552648762617,52765128863357579072006910549108650351200315557⟩
def resval7Tail188 : Box := ⟨363973052216540971322860238112865634654181695828,47111285957449504669309738534043241579229079313⟩
def resval7Tail192 : Box := ⟨369716105912085989954018279408640118944157233675,41368232261904486038282643573080807448877885612⟩
def resval7Tail196 : Box := ⟨375549778035421345915702928153237246757286372656,35534560138569130078844751781580881989747916753⟩
def resval7Tail200 : Box := ⟨381475498435524694271954623033845615320382836563,29608839738465781804964949787767016416659035069⟩
def resval7Tail204 : Box := ⟨387494719522657854409600902118193552909150385172,23589618651332630525618757847176362059840993819⟩
def resval7Tail208 : Box := ⟨393608916624361076267966185010393778981116240978,17475421549633092602787157029524340777078555007⟩
def resval7Tail212 : Box := ⟨399819588358386418664816309188664133973452685135,11264749825124971471833774437958993679086862937⟩
def resval7Tail216 : Box := ⟨406128755066603113742782200948606400159250725622,4956015987510520179817421101188732980689908875⟩
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
def polyval7Tail5 : Box := ⟨20080314931923728764064676760687802657651140875035756308499,6124567998830945217728512001564791963318169516168942111474⟩
def polyval7Tail9 : Box := ⟨20397156185137764352613093757544304479111331327959521087617,5807724970858344917579596097288097186461538188772177965196⟩
def polyval7Tail13 : Box := ⟨20718998591985622799632325939829309822294319169116842094358,5485882563859384153576481204272219941021432137080338772013⟩
def polyval7Tail17 : Box := ⟨21045919282149427005189116169770691847270418103878065842735,5158961873695475417888164452037875288131652483706229405152⟩
def polyval7Tail21 : Box := ⟨21377998384636337461850752036233022107432400614666373507990,4826882771208564639288424413477644101948851013663317578937⟩
def polyval7Tail25 : Box := ⟨21715317292941663844411573231175365561915309418534916057069,4489563862903238253362021122132776156339367493992922766008⟩
def polyval7Tail29 : Box := ⟨22057958684851539009042591031327905422433411017022942719216,4146922470993363088629880990834501027886441360125113410844⟩
def polyval7Tail33 : Box := ⟨22406006542707371008566930059081307986500531477542278336008,3798874613137531089097815289797392208634573103606078633788⟩
def polyval7Tail37 : Box := ⟨22759546173990144158006265666198270210631702983073762156566,3445334981854757939657168776488851443273267677260991440442⟩
def polyval7Tail41 : Box := ⟨23118664232229515719627604930679169665443395168617388713987,3086216923615386378035501106504241471838969713241535985707⟩
def polyval7Tail45 : Box := ⟨23483448738242832798428186509692182116088505512496854694497,2721432417602069299235462353720769531121003221755299409064⟩
def polyval7Tail49 : Box := ⟨23853989101709275186520266019103728849366243602326743537280,2350892054135626911151804725135582445236221046036482773649⟩
def polyval7Tail53 : Box := ⟨24230376143084412037925241563059609876783076526878524787259,1974505012760490059943711641629835573484840176885806081902⟩
def polyval7Tail57 : Box := ⟨24612702115860543705428828353913641403043240981538392674759,1592179039984358404336258434141877945917671104573476242465⟩
def polyval7Tail61 : Box := ⟨25001060729178287717912365993316331834595342460074589130183,1203820426666616793739235286833083767401118910642499633849⟩
def polyval7Tail65 : Box := ⟨25395547170797689962536453196185466341386841865503328262260,809333985049498797493864294650296461818772314195297022050⟩
def polyval7Tail69 : Box := ⟨25796258153025883790411597015375077677720399365170184128373,408623022364047115907140285377881371649737484075057703863⟩
def polyval7Tail73 : Box := ⟨26218750000000000000000000000000000000000000000000000000000,2⟩
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
def pend : Box := ⟨1029879979889812027080938550647245080084982996883079902721165,7941222572726394909433534880016606508204046755640528046⟩
def zend : Box := ⟨1003671392120013684951113281250000000000000000000000000000000,6157630011479516738281250000000000000000000000000000002⟩
def betaquot : Box := ⟨428739732872888254614837167122943250721972334816049884072445,394750055234599760471308305370310291254794991458800990⟩
def crit : Box := ⟨108862273215266581161251903114739619928763611131376440353,21321732881910165340566094190011492842423136748897293056⟩
def subsonic : Box := ⟨692659005592528541637544779284357048508499780752389748570,12670806002374081538629564271674278605670407984189914083⟩
def pendTail4 : Box := ⟨26203319684134423153895344287707156504110750538653113184433,1530134352927522763737094605960605527755273771206946744⟩
def pendTail8 : Box := ⟨26203351287562402452401474254519168609417052296596245104124,1529867092635589692038846104471001007345584345026862000⟩
def pendTail12 : Box := ⟨26203351288777817454662254710708238051839746834703854261715,1529867066570244412228277928342158428231898914686706168⟩
def pendTail16 : Box := ⟨26203351288778350269745395631112823778018802642035375205851,1529867066550741344080101231606748236670632327654744603⟩
def pendTail20 : Box := ⟨26203351288778351413345865856579630915516976115353822628869,1529867066550676176973275664724257269569753723851120161⟩
def pendTail24 : Box := ⟨26203351288778351422067930169651742947909152118701770860611,1529867066550675416832144489901197869992460205022035427⟩
def pendTail28 : Box := ⟨26203351288778351422262820423528625253543862545568131746701,1529867066550675390175735149473030469702834182214632248⟩
def pendTail32 : Box := ⟨26203351288778351422273803287336284160218783116025332711156,1529867066550675387607659078464239856412658819518144245⟩
def pendTail36 : Box := ⟨26203351288778351422275074406036324762118775563243270042947,1529867066550675386961938233835784761665536334096388226⟩
def pendTail40 : Box := ⟨26203351288778351422275140014277748783119829265910411813919,1529867066550675386547900961667858715229205564010516073⟩
def pendTail44 : Box := ⟨26203351288778351422274264624551276412634759437004912809644,1529867066550675385870915680454185353990403867806634298⟩
def pendTail48 : Box := ⟨26203351288778351422267113609069482668393595912059628631741,1529867066550675382983717725823275932513314210263865544⟩
def pendTail52 : Box := ⟨26203351288778351422150568238859037895872269717506201713303,1529867066550675349248341412400498827444775886872748336⟩
def pendTail56 : Box := ⟨26203351288778351417124545019254317030183749556182707887828,1529867066550674172270085570373896986403336505257022898⟩
def pendTail60 : Box := ⟨26203351288778350714977183362980231221483026503784604488981,1529867066550532431618263230896899700699569336932097898⟩
def pendTail64 : Box := ⟨26203351288777929963411000098898757656135839492024289445382,1529867066475482609453614082568959140380868537274121268⟩
def pendTail68 : Box := ⟨26203351286966686157364796430147660810415129757956521542615,1529866811630767671477017100139668286018163378175846190⟩
def pendTail72 : Box := ⟨26203109951659285510765631921945869816521702211655723116176,1503612156763008001529790990504880391176452449876620864⟩
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
end SepticProfile.ExteriorCertificates.C03

end
end

end OAI
