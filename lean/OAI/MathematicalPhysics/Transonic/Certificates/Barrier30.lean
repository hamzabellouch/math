import OAI.MathematicalPhysics.Transonic.Certificates.BarrierData30

namespace OAI

section
noncomputable section
namespace SepticProfile.ExteriorCertificates.C30
open SepticProfile.ExteriorJet SepticProfile.FixedInterval
def cell0 : Box := ⟨250000000000000000000000000000000000000000000000000000000000,250000000000000000000000000000000000000000000000000000000002⟩
def resval0 : Box := ⟨119589597266231037762065277217239621789900761102415897345,307174501259800824095204646866727751753455518218388959⟩
def polyval0 : Box := ⟨3845590449290827143811817697472716309326885247373586777175,14813644396476537248953646521944047658517173923487348609⟩
theorem cell0_lo : Holds Q cell0 (0/1:ℝ) := by norm_num [Holds,Q,cell0]
theorem cell0_hi : Holds Q cell0 (1/2:ℝ) := by norm_num [Holds,Q,cell0]
def resval0Tail4 : Box := ⟨64018265433013229217636305216321011201337396337463,1849838504970303965246709675806077930270277693131⟩
def resval0Tail8 : Box := ⟨8067173987380609926583083633776208314761157212,425488698275500046509551447037420782684249435⟩
def resval0Tail12 : Box := ⟨7641511109062335695095943653421076433139030,612991151292038292518190970246618214446579⟩
def resval0Tail16 : Box := ⟨31850321682057822661491002497304509143602,28645301757413656447925861279527244893054⟩
def resval0Tail20 : Box := ⟨451332589911995217373815931459210342264,400245085798524906425251373780428330655644⟩
def resval0Tail24 : Box := ⟨18659316032978768037127451204531525372,6402781514434063792215334622319811563195213⟩
def resval0Tail28 : Box := ⟨2047846402656510905903345703931391850,102444439579294430068340926784711367232581791⟩
def resval0Tail32 : Box := ⟨561540242614320993514256139728388746,1639111023482230196044094610273275405575599324⟩
def resval0Tail36 : Box := ⟨-195534978849712795950141586477461774,26225776371908993284226223045372041864162276665⟩
def resval0Tail40 : Box := ⟨-146251732052679730253606920372652976236,419612421811489976804703579363242895900573978778⟩
def resval0Tail44 : Box := ⟨-37595203046043246553517461847774090848907,6713798713733594005312362592817592464945205822641⟩
def resval0Tail48 : Box := ⟨-9624974690619969416497461265735182444226060,107420770396291189052239892055203244214031439304787⟩
def resval0Tail52 : Box := ⟨-2463999232200829772126085386343546726825057862,1718730016340701664048319641207989563169320091603940⟩
def resval0Tail56 : Box := ⟨-630783922490625257964580736735300499102282010836,27499088901477199678127640101926374367067603786914501⟩
def resval0Tail60 : Box := ⟨-161480680014966843671356394756669915588931217339822,439834034273295485186481908988257311231694525586790085⟩
def resval0Tail64 : Box := ⟨-41339025064507771388831022079605964719326806310281093,6998589192862268899674522511860384927641360663090852750⟩
def resval0Tail68 : Box := ⟨-10582111324456444705648916468760772433478832848466884642,102056347133412141333149439646427391771858329796518847001⟩
def resval0Tail72 : Box := ⟨842726085104786170770024556992005641042325541487302020928,2542555336085636689758775585761992108105314655844119199⟩
def resval0Tail76 : Box := ⟨-30033235581330862086091852124085071913858012700555,642997602052220000510012603857130599558913247394⟩
def resval0Tail80 : Box := ⟨-1691108129077034452297310763972455696067261942,76617960848835743814888291655153481317430870⟩
def resval0Tail84 : Box := ⟨-996246132446561861733240337759398172518013,71160849227714552459729088874606816343713⟩
def resval0Tail88 : Box := ⟨-2869800302840529291104969860612986317831,470735214736887349886511301167248378282⟩
def resval0Tail92 : Box := ⟨-29743725920305584474760040491461000872,2785424515314205840589694046753506260139⟩
def resval0Tail96 : Box := ⟨-931046047220651356285790211131359359,44498148589439761919751559764904283512723⟩
def resval0Tail100 : Box := ⟨-79059353991841981201522713987339994,711967422740739882343863615388861968350021⟩
def resval0Tail104 : Box := ⟨-17068563508555893370275017590472851,11391478418400630582717411490104947951965438⟩
def resval0Tail108 : Box := ⟨-11001924414099573189715745194681125,182263654589531525992334362374696516529653394⟩
def resval0Tail112 : Box := ⟨-516687296497221220102908976918147116,2916218472962517017785866481992293521835095685⟩
def resval0Tail116 : Box := ⟨-129344163784607980629039824688821138806,46659495446182763175161129780442656954271368626⟩
def resval0Tail120 : Box := ⟨-33103091684376681294805113018748287346354,746551896105013524602102747953077769565330765984⟩
def resval0Tail124 : Box := ⟨-8474323769125823378362544775049011409166010,11944822393005735456170943557219466838690258675737⟩
def resval0Tail128 : Box := ⟨-2169425699540735972934357186290436603673413249,191115124451728495640684037166069853213830323529049⟩
def resval0Tail132 : Box := ⟨-555372967351065957864548594805890282698372971170,3057321329119595327731773531447726619859158430557651⟩
def resval0Tail136 : Box := ⟨-142175553711604226215311542125696500139607394501964,48783851734332558657865702289055814914623487725067048⟩
def resval0Tail140 : Box := ⟨-36397881512964897831372999577173109452005540797439524,746419077715414618732449020132504882509903699602672990⟩
def resval0Tail144 : Box := ⟨-9815297805275340297510214680948103526262054150142737165,2963743367440818641975846764011186025706449794228197347⟩
def resval0Tail148 : Box := ⟨72252379192345387387930174859816521410535258,1267555763674259135134399494719633941604576⟩
def resval0Tail152 : Box := ⟨1342228538497610736856951925020648732691,54173496054580606036306636504271848977⟩
def resval0Tail156 : Box := ⟨444266336489286725770265813135416540,28888920450183807446584292544692249⟩
def resval0Tail160 : Box := ⟨810386217567718848317101416227550,78683924269510730421824736452593⟩
def resval0Tail164 : Box := ⟨5631789209262231322852560268797,34010234411637462367979059259734⟩
def resval0Tail168 : Box := ⟨122017507846971689584981212343,532303721058085325327090559889537⟩
def resval0Tail172 : Box := ⟨7292892175663516719695197511,8516508110260348566538371976361783⟩
def resval0Tail176 : Box := ⟨1114982328052627166506602145,136264101115940057941260282932180034⟩
def resval0Tail180 : Box := ⟨424976583815901898128775119,2180225611813841128038762458745798145⟩
def resval0Tail184 : Box := ⟨2345692511653001995896054815,34883609784935238984460459412772500177⟩
def resval0Tail188 : Box := ⟨505339616364493802068376236633,558137756086315896649750156552471759557⟩
def resval0Tail192 : Box := ⟨129163950995632133402207361538925,8930203976293799375795706857196466329014⟩
def resval0Tail196 : Box := ⟨33064928678023922090258998310041233,142883232622371556708736953237048011181346⟩
def resval0Tail200 : Box := ⟨8464608890515504445607522236336042372,2286123786388472387144416920795080414662108⟩
def resval0Tail204 : Box := ⟨2166939574609930426917485553555693648896,36575949076520933075123764893192373602532264⟩
def resval0Tail208 : Box := ⟨554736598887294947365306375021412331912537,584695119736526427584880976163700835175471768⟩
def resval0Tail212 : Box := ⟨142012970048215995263445966109932091521769741,9221984972490208544693378915666806563075586504⟩
def resval0Tail216 : Box := ⟨36378906169742309655248770161208121512976478005,113457425495604564437546195221845002043889876336⟩
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
def polyval0Tail5 : Box := ⟨2208482741056096384663635061157480483098392469422152,54075235719206526630391545742215588983986341288643⟩
def polyval0Tail9 : Box := ⟨223062243710625053386849484862220164238784847117,10800386640142221282633032368479903029046843504⟩
def polyval0Tail13 : Box := ⟨182821021397536695387544509204512306603384547,13734522522263426739235313393577517420530070⟩
def polyval0Tail17 : Box := ⟨667737205141497944880192082146481593686136,456707642282994873236934950326745336663117⟩
def polyval0Tail21 : Box := ⟨8314295087648416854667212369907324091955,6156503643567496991092378972671392450621968⟩
def polyval0Tail25 : Box := ⟨301699872682441950036551919860868854578,98484155233207226796366988331196627218953062⟩
def polyval0Tail29 : Box := ⟨28958718630432027784661697694937978122,1575745493430810954583445462674065332489724242⟩
def polyval0Tail33 : Box := ⟨6955677931447262499437571380320250020,25211927764223308480010800572378298830282544615⟩
def polyval0Tail37 : Box := ⟨9843857310144411032769712886808692526,403390844182031969994296643542837657986794054133⟩
def polyval0Tail41 : Box := ⟨1498544549810255727024467063005515792627,6454253505517863744461403701123111038341523777852⟩
def polyval0Tail45 : Box := ⟨382222502760842694893121526767069247520815,103268055729973726798972081702559303899937582717801⟩
def polyval0Tail49 : Box := ⟨97844335210663042938560740055097633629368770,1652288799950643989973152290123947287758753731230769⟩
def polyval0Tail53 : Box := ⟨25048113038283334374081535548248376230935359992,26436597316606655427506388923044213592474737866695330⟩
def polyval0Tail57 : Box := ⟨6412316266522120595273908780127627784599860843201,422979545519345194272887776287595644530690365406311529⟩
def polyval0Tail61 : Box := ⟨1641552959048821111885777999962362131907444665909985,6766133772440864999721241012565035588875609951750205637⟩
def polyval0Tail65 : Box := ⟨420237604477829578913242491590586151921752289894187456,107864167636526967255080370973361027419952597474395522537⟩
def polyval0Tail69 : Box := ⟨107581395112331364416523037197412377678928946316853444474,1624969406726673953482969510892396454409947457464651263473⟩
def polyval0Tail73 : Box := ⟨27906250000000000000000000000000000000000000000000000000000,2⟩
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
def resval1 : Box := ⟨119349641418865123942889077531905577839461615606491560554,225236426609407442821194853525947985627809070092091805⟩
def polyval1 : Box := ⟨3827030543000528576607058943230203387856158673494863510583,8486447861437336623526955341716434701371533814913612378⟩
theorem cell1_lo : Holds Q cell1 (1/2:ℝ) := by norm_num [Holds,Q,cell1]
theorem cell1_hi : Holds Q cell1 (3/4:ℝ) := by norm_num [Holds,Q,cell1]
def resval1Tail4 : Box := ⟨62142979183341142603498934150838161234958902298489,3209367226028945512183074295067482941177076650830⟩
def resval1Tail8 : Box := ⟨7605667452892690961707055736534013418473164619,6485293779623639788427966699519991466955084310371⟩
def resval1Tail12 : Box := ⟨-330910163960633440588831552211999331908097705,20495803853372980175220897755035318116618867887310⟩
def resval1Tail16 : Box := ⟨-2215049517525412745503251069617189293249109409,64775713766302625372741938825580277797448698957889⟩
def resval1Tail20 : Box := ⟨-14516736740553871461213746582205881138122732347,204715727507346557873059784000609372494608924172193⟩
def resval1Tail24 : Box := ⟨-95136888486879492012778741238046672264565525623,646953536279157359203196057891019630805137223888599⟩
def resval1Tail28 : Box := ⟨-623489112490239807787011979831184695321062121324,2044369848306281192735106265685607881278068517477868⟩
def resval1Tail32 : Box := ⟨-4086098247626669175720730426958140938109377694645,6459102721248741634774120156356172694739844800721545⟩
def resval1Tail36 : Box := ⟨-26778653475648794267199793236817739004435501231316,20400089714315343309087045276413501180249474158339439⟩
def resval1Tail40 : Box := ⟨-175496583418013387302761177804979178639292341271947,64383494801205369357609479748915724332950491590198374⟩
def resval1Tail44 : Box := ⟨-1150134409088293773330173487545427667913896089570134,202888159349721409097811043879303292707136540798112892⟩
def resval1Tail48 : Box := ⟨-7537520863401036665949090199442362900769089606023291,637324247065676530166981258489345914200890944060807286⟩
def resval1Tail52 : Box := ⟨-49397896730384702054987677539226122214473003627483054,1988683740181267458956508903668455395131583636571744980⟩
def resval1Tail56 : Box := ⟨-323734056012216321880767612610139606523559181216368415,6117610376696182154895022181774924458150874044712697376⟩
def resval1Tail60 : Box := ⟨-2121623509471142853454203803894389325010900634419465667,18236205808708536824867703951591531518654826528318116843⟩
def resval1Tail64 : Box := ⟨-13904271814694149496235445232779508141116508939214892822,50436522064566556426812258824927600279700123300353274829⟩
def resval1Tail68 : Box := ⟨-91122724518394376843638212165392733034751756347434592329,112225685990769801413033058746092730960630278040205084250⟩
def resval1Tail72 : Box := ⟨845804548805405368090728595632016549891876118652159383828,1515906938978691940864633458144935861094490594112869266⟩
def resval1Tail76 : Box := ⟨-29356797437498380550542000302449738041131686649268,418901782494826257086610635931888762433708420053⟩
def resval1Tail80 : Box := ⟨-1615577573954878933499486114579395961218059202,67612108714831659386493879818161915330852700956⟩
def resval1Tail84 : Box := ⟨-3854088456135212782518217976537136133136800,213538598696422187136227475451725381972791681038⟩
def resval1Tail88 : Box := ⟨-19168152721542593499695497413517954653929886,674877515644648657360307408024383931650223208815⟩
def resval1Tail92 : Box := ⟨-125603315481072772392455371484098970763731145,2132881191618401802819556243874814004719103760866⟩
def resval1Tail96 : Box := ⟨-823153716475208654397513673988851357067590366,6740531654881373605714397524429320747515720421555⟩
def resval1Tail100 : Box := ⟨-5394620191109158417540104779960179862576265998,21300615639078638087490069740776834840480944440270⟩
def resval1Tail104 : Box := ⟨-35354182884034969034268527115792798212088362513,67302159722955956759639755093856365679434685859436⟩
def resval1Tail108 : Box := ⟨-231697172948728568885955061246154525804534741789,212588099862792441752802988286126995612510920687249⟩
def resval1Tail112 : Box := ⟨-1518450592636750294838487710623997894922439409880,671097204236372364952777552156214857074795668070303⟩
def resval1Tail116 : Box := ⟨-9951317803904176119105490032460167729891019884569,2115846307334692526248303596043191829765054497967523⟩
def resval1Tail120 : Box := ⟨-65216956359666434271638042253855627304120110411274,6653353315683305928909749096757276638621446274702634⟩
def resval1Tail124 : Box := ⟨-427405845198712602561122995790922506011044218145908,20806594026937103759436159997242870972814546820622517⟩
def resval1Tail128 : Box := ⟨-2801046947094492696970627329887610532164080433696219,64308878574717646310056232153903231396051912211200603⟩
def resval1Tail132 : Box := ⟨-18356941272526474519253680677327357238149930090125499,193743564080400858760182938883521672524137628904654978⟩
def resval1Tail136 : Box := ⟨-120304050372873161194468108468407342947211367129477588,550038287573130592770376033476881173914315300531570095⟩
def resval1Tail140 : Box := ⟨-788425071843599848678790319601167158178743346400682907,1330188115978251404072762704868069149931633723158657908⟩
def resval1Tail144 : Box := ⟨-5375637913234564098604949017609075727897442043887732577,1491969692093212435269856170576694834406263350739331949⟩
def resval1Tail148 : Box := ⟨71170373229581508445385314856158511094091469,885911122213434639742072422780833815306886⟩
def resval1Tail152 : Box := ⟨1290418170748878683341702217634042566697,3468872684696427366194445450162286966340⟩
def resval1Tail156 : Box := ⟨550451567369676891551894083777431766,10854176001732399874331666182315665566476⟩
def resval1Tail160 : Box := ⟨871233629250770372845017888019889428,34304108733282117121711168712238427674275⟩
def resval1Tail164 : Box := ⟨5704847809190982587255823577132822744,108414970240492991364035943555847840085586⟩
def resval1Tail168 : Box := ⟨37387257705473519915042634058115593836,342625487079673054609661685703937172464422⟩
def resval1Tail172 : Box := ⟨245021131409503516136592319557473005151,1082738878008617584737372558426985309943068⟩
def resval1Tail176 : Box := ⟨1605770486765922617243187378139169076534,3421158157659473773174350432601243327771713⟩
def resval1Tail180 : Box := ⟨10523577462063516539654887284974829342731,10807100689271728436796011495059376015122095⟩
def resval1Tail184 : Box := ⟨68967317255377593126390713652589609084104,34120067402298334413036931404237631642555130⟩
def resval1Tail188 : Box := ⟨451984210364841322010675234925349179410526,107602248977360470233532006290753773451551088⟩
def resval1Tail192 : Box := ⟨2962123721047023215326530514355854188409710,338542613267319393946486928469514003422406490⟩
def resval1Tail196 : Box := ⟨19412574018253790546336032065482153626770458,1059911039179546264401803597126005289303983543⟩
def resval1Tail200 : Box := ⟨127222245086029189974693945308370901114777488,3283973371934179370366214701768806210003405290⟩
def resval1Tail204 : Box := ⟨833763705395953347258909682436266571588625221,9947298985433473318963377538942301207083011700⟩
def resval1Tail208 : Box := ⟨5464153819756275024747938137905737900062208241,28609328264900452944396073555897051008787226781⟩
def resval1Tail212 : Box := ⟨35809878685122345958744311253700616226789302487,71879151286434845093210548628705266819559090400⟩
def resval1Tail216 : Box := ⟨234694046253021595161336443769397756937459134160,105664969983444058086367436895360999752730308662⟩
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
def polyval1Tail5 : Box := ⟨2148372202279111979600729676409264123844381375334499,120596378082445479233744953457085074119631901577352⟩
def polyval1Tail9 : Box := ⟨214516810701827604219962513907332489290453510194,280334029016869224828123518651877514175092553711405⟩
def polyval1Tail13 : Box := ⟨15878203901473003341951636011382082521826667658,885968767435404431899731501161585356879691211600475⟩
def polyval1Tail17 : Box := ⟨102946756674299002928466013793936434911369767062,2800045524411108077478138790574028923395354177357482⟩
def polyval1Tail21 : Box := ⟨674667906265286888549840055911449745414109183147,8849177288462368533811557300727608601865271494679130⟩
def polyval1Tail25 : Box := ⟨4421503542697058168199665902573668490770411912164,27965480975821817375852153196129669850893894216296584⟩
def polyval1Tail29 : Box := ⟨28976765615749674007832994455163107621922526313653,88369727366695997690681724362210240642011456074814975⟩
def polyval1Tail33 : Box := ⟨189902131139225111397367051807087781575763713467701,279193656608018818705118077138850770453978030712202530⟩
def polyval1Tail37 : Box := ⟨1244542606633992355988534478306411563438361213770819,881745470198606229719942097471343045893188995686692388⟩
def polyval1Tail41 : Box := ⟨8156234426836516121104871641281202737830358447386615,2782528250488490598851747398379035789233279742428981581⟩
def polyval1Tail45 : Box := ⟨53452697939715778274875286352422460615619838450906936,8766488390187737816806756878545054279638279369481394313⟩
def polyval1Tail49 : Box := ⟨350307601217721343838668883042512868485765634330190602,27525061763728304873972653435333305747261423050239909698⟩
def polyval1Tail53 : Box := ⟨2295775895340460161710695160520474570485314846829694786,85804156912390192044219070548024397236044569353410760844⟩
def polyval1Tail57 : Box := ⟨15045596907703366266216552628573502502399426840430772036,263393696904383739713552930231423438064380480861279567670⟩
def polyval1Tail61 : Box := ⟨98602823894354647888717800693829620318175142100948337108,781402845437698409400564668184438951406982016769224776016⟩
def polyval1Tail65 : Box := ⟨646203466705132651423714749858676986818495866168753248366,2135049019110655171050166379453869958051526819011956489134⟩
def polyval1Tail69 : Box := ⟨4234959310860898425351754038426974898943287782916918716605,4555172225550054285688125723828804540174647747841853095172⟩
def polyval1Tail73 : Box := ⟨27906250000000000000000000000000000000000000000000000000000,2⟩
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
def resval2 : Box := ⟨119231531846927355795223607271640543674715669705409440462,205005780662661141935635248541930728594229352620727353⟩
def polyval2 : Box := ⟨3817860970518881536438647870418572810070287303694270581985,7178198130494432541348103580891734629637575840925288081⟩
theorem cell2_lo : Holds Q cell2 (3/4:ℝ) := by norm_num [Holds,Q,cell2]
theorem cell2_hi : Holds Q cell2 (7/8:ℝ) := by norm_num [Holds,Q,cell2]
def resval2Tail4 : Box := ⟨-134589981566699840737498493915035418408331921744974,34991159711879716687779081694198170640556207002663767⟩
def resval2Tail8 : Box := ⟨-449372955949791751012738048360148156272734492254924,59576793401207663438441841203264716271911859169165139⟩
def resval2Tail12 : Box := ⟨-1031147205215135260468352171684135524209939785451488,101370855004402141338835755628557122724496456710049864⟩
def resval2Tail16 : Box := ⟨-2366067843851071448095008555579270517968140072266534,172327227065622533034876297103779701091311285136856079⟩
def resval2Tail20 : Box := ⟨-5429173425874908804760973646404319917435693396382263,292589875282709285464565763036081238717427248484828730⟩
def resval2Tail24 : Box := ⟨-12457767922627433442497075174496931421520412823359019,495949572148327280613480390586053006142469553255584418⟩
def resval2Tail28 : Box := ⟨-28585563480876454113947612939683162121874021846582145,838734913374863054879010286955542754655762213778630871⟩
def resval2Tail32 : Box := ⟨-65592363302500591266647990453015333209319270497512884,1414018079513454857945360376373783696461119554103677931⟩
def resval2Tail36 : Box := ⟨-150508074696007799747415200299981765893042674140904803,2373642018504389335102433254168546624480025419224793060⟩
def resval2Tail40 : Box := ⟨-345355456156211868278034879129930589100621970925786180,3960733165979909191374289002955624084937794050836483613⟩
def resval2Tail44 : Box := ⟨-792451776011116591955286762500829607084813433569528043,6553545306983282349255518007248135855995731804720057095⟩
def resval2Tail48 : Box := ⟨-1818357886371784484436554831096919376252270111142512479,10713588824142608698332645557213372498425544703186789211⟩
def resval2Tail52 : Box := ⟨-4172399511265756040532555532062319248610221367489559855,17206548313085328336884829344044498327187975542548752899⟩
def resval2Tail56 : Box := ⟨-9573977604786658891522727731659571497711182749052146431,26897563539962183377089883361208425770072375213707065897⟩
def resval2Tail60 : Box := ⟨-21968425345998036245350512843349335117653763743028200737,40250413691432368407478114104814289832456509974507014991⟩
def resval2Tail64 : Box := ⟨-50408694481495424999121417963998240637690963058146312484,55733898048839543821737777350921396922854444354695881234⟩
def resval2Tail68 : Box := ⟨-115667421180863806793245857380500441764925662794184431075,65406920633174514815088080571124266556667825875107822464⟩
def resval2Tail72 : Box := ⟨847341939570196361367186181650199517687558349171360728486,1003039485967048137252092920703060735350480654903206782⟩
def resval2Tail76 : Box := ⟨-31236635612840957470888574614560444229504535376316,425316000650862035031036180073092024143659545829939⟩
def resval2Tail80 : Box := ⟨-5058822248279700151930729366759421901073863021792,724190749987125592422195103198435353471583057363413⟩
def resval2Tail84 : Box := ⟨-11604336669938798940212329220671273100897124693223,1232460532887913309138859015806477504772219226368175⟩
def resval2Tail88 : Box := ⟨-26627280175833193346439635350539616345829103631892,2095692462432986797030604279824424724034011107911895⟩
def resval2Tail92 : Box := ⟨-61098891265721057369574078213528725987445406248163,3559484892872317853651947581447783395507675640088199⟩
def resval2Tail96 : Box := ⟨-140197364867780629580772709411775360232983169267646,6036358728355586790044933564601260289108137981378951⟩
def resval2Tail100 : Box := ⟨-321696526871426910643118342814194766022005045540134,10215235483891967480954177479408820081341011274822590⟩
def resval2Tail104 : Box := ⟨-738164055356809298896853869659067499305733776670702,17237376767669789283148661175444270835008455031974042⟩
def resval2Tail108 : Box := ⟨-1693789416752349482569814507061137240114660413157138,28971689638273451330005381192464684488569226972817263⟩
def resval2Tail112 : Box := ⟨-3886565008798080441694651687365199019565479915033157,48427388431179295700024860999007053328747462662284536⟩
def resval2Tail116 : Box := ⟨-8918102461979307446200535815274872348701928626711087,80327192535999589966688335301497999939222305894783663⟩
def resval2Tail120 : Box := ⟨-20463455864580228147027107666658630989537997304624902,131785077376453326223518059486702856863350415120315593⟩
def resval2Tail124 : Box := ⟨-46955395243203316275137936977443516178080797845610093,212773880956410779847813359564754413507278784293691367⟩
def resval2Tail128 : Box := ⟨-107743733855907633712880317894892454220389930231495392,335342944742018119316078764452448507676598801879229092⟩
def resval2Tail132 : Box := ⟨-247228505373828278086202199819861817863308421490617943,508657806803260172912465991971276970140383509349722381⟩
def resval2Tail136 : Box := ⟨-567289917345876497775326110743419912448959066528012337,722218760189737025740609621034668468813852922945692870⟩
def resval2Tail140 : Box := ⟨-1301702395252556515057595243370299371091173709539453561,898142797992892284955077873303383817076856107738603005⟩
def resval2Tail144 : Box := ⟨-3148582918869853964891252382422762694945450533612928443,752074264479847788524048089843889364220614413542947325⟩
def resval2Tail148 : Box := ⟨70940870912348066352154618736255267927251312,53279411768784457822219196239183778338832666⟩
def resval2Tail152 : Box := ⟨676605713079710060191187316530142640896436,89612282604559814887111494952452225121187981⟩
def resval2Tail156 : Box := ⟨1549632931634327967899589623680170573992622,152477052558530465355902934893976812978764179⟩
def resval2Tail160 : Box := ⟨3555782964511921522030823388455191069495103,259206941772696472317924021155635552340880724⟩
def resval2Tail164 : Box := ⟨8159090799186384247541879663074047588170593,440102517081135887627551752343288122689872046⟩
def resval2Tail168 : Box := ⟨18721829579327339899784795661106398942098508,745992683489302520223144687144868791615030490⟩
def resval2Tail172 : Box := ⟨42959063874191736325832714113325915358862434,1261610134596906764467521548972863068555079029⟩
def resval2Tail176 : Box := ⟨98573761775113941445371916136128508513481492,2126963696341345632366702500722188730619562532⟩
def resval2Tail180 : Box := ⟨226187110104473485536623573104860645656885366,3570481539810153091450756826191813454701162247⟩
def resval2Tail184 : Box := ⟨519008383733299756167069825678133014646059232,5957940716662498019155550931972585998571131369⟩
def resval2Tail188 : Box := ⟨1190915354376441049624299994451676363709203431,9858473864791067358385728484622534222524959266⟩
def resval2Tail192 : Box := ⟨2732671428325844356568372042064312793627156940,16117098768138176652208698406686596540252107618⟩
def resval2Tail196 : Box := ⟨6270381104539845822148139621301938009672965078,25886494665854419112157832103458809783659360299⟩
def resval2Tail200 : Box := ⟨14388000982708006276651956662169784945385771664,40470209411100786493495423176539333891846626758⟩
def resval2Tail204 : Box := ⟨33014671489190001597527235568501499714245529304,60571013547478507484464490672744051477139021140⟩
def resval2Tail208 : Box := ⟨75755383590114913628240988904836219723527569520,83897663436258416919517208827766372696988763121⟩
def resval2Tail212 : Box := ⟨173828116095048714119882787595626036276355324403,98532933877413534272316674336707459220276993384⟩
def resval2Tail216 : Box := ⟨398873714404573092757390238329629033083541404120,65769565511255361162646425162443479089800596777⟩
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
def polyval2Tail5 : Box := ⟨22624549242836181884874174532879222037458630961547213,3145937167243112916679625071971999154698925482553388791⟩
def polyval2Tail9 : Box := ⟨47050444377244342952235694651403152214716014436089286,5354758866373952027492721147442876195681583729346609665⟩
def polyval2Tail13 : Box := ⟨107961358365726916429994744534249381051634893331887306,9107286491118979508140086537207430462898241196910008402⟩
def polyval2Tail17 : Box := ⟨247727865660110684828873243259105998310476771284021920,15473078128015377458201996552583046471432825583315400918⟩
def polyval2Tail21 : Box := ⟨568435748183303069435338241823831480912131786272212872,26250565230614041468592086511374282529388315727937315293⟩
def polyval2Tail25 : Box := ⟨1304331262663789881329250992513581813899245800832837016,44447700394626462069843662202331273445834145515949069892⟩
def polyval2Tail29 : Box := ⟨2992915291128956215894346353122823651558731420680975375,75058030843090481946031741154884256141725348038181192801⟩
def polyval2Tail33 : Box := ⟨6867536028830477688344718462862807303620575279771331291,126283932261782941148697117792311820084099462082349709730⟩
def polyval2Tail37 : Box := ⟨15758231195876691485982319938881132412607492628875325517,211392295300729957218915632454372187303311006089973617902⟩
def polyval2Tail41 : Box := ⟨36158798349251596692944842160588256897830895852963703563,351349971550832048909113608036039910094233942947855131411⟩
def polyval2Tail45 : Box := ⟨82969889311177922375250662769994683900435237414205410442,578102964295961857880213544585722641969436668012076785005⟩
def polyval2Tail49 : Box := ⟨190382502919973261532608889892946303511895750237744669031,937378600109949495677336075447421976949744099123582746459⟩
def polyval2Tail53 : Box := ⟨436851220593234400631606643888172098349427696124320771258,1487059432472389763073583417469663889672708874463481955371⟩
def polyval2Tail57 : Box := ⟨1002397730919723151090743361446916339722125627578292202807,2279708905880275521422581087974081902015415136191732315979⟩
def polyval2Tail61 : Box := ⟨2300099355539220934405486820115743990587914381739028569115,3299029667506529920706389073722393868764014769899585727865⟩
def polyval2Tail65 : Box := ⟨5277802295624655036148914776085624260831572251051409927308,4274064625845389795389857887420396611933324736229391336865⟩
def polyval2Tail69 : Box := ⟨12110432315765617434870761575194495683467769507418137320945,4184631148050237681721896894043208415144057894657945337081⟩
def polyval2Tail73 : Box := ⟨27906250000000000000000000000000000000000000000000000000000,2⟩
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
def resval3 : Box := ⟨119047451190242742032699769175077771631793698131144586501,1715494712594809039474256624846854312614649253527464387⟩
def polyval3 : Box := ⟨3836510128106022213607488852761424469421806431535258543920,245660460940539941954321008282374581164081074520712054473⟩
theorem cell3_lo : Holds Q cell3 (7/8:ℝ) := by norm_num [Holds,Q,cell3]
theorem cell3_hi : Holds Q cell3 (15/16:ℝ) := by norm_num [Holds,Q,cell3]
def resval3Tail4 : Box := ⟨-186188273824605037427415023443388370465719777178802679,1986106005749548656228628807741202293898916940861518849⟩
def resval3Tail8 : Box := ⟨-276122677348096545279474265248278167582433746906902187,2536073330075296285298817741184419950502268617571968985⟩
def resval3Tail12 : Box := ⟨-409364340700655294490823551192396496066933772805099961,3231131027535230875413115918295273426403332961801938201⟩
def resval3Tail16 : Box := ⟨-606901108500804129529520934643393358704965094908119663,4105859473289504909395670749807054493037401624503095693⟩
def resval3Tail20 : Box := ⟨-899758281004815759890611861385824045124153579963037441,5201090657033927347057338110795201687313710808688841007⟩
def resval3Tail24 : Box := ⟨-1333932255020149080425225933964572783303188080120944795,6563850184551348996812213420161227460585115897494867792⟩
def resval3Tail28 : Box := ⟨-1977614764485413656163011384976128180590225651639652677,8246366864349306319872998886214211910077297756524485659⟩
def resval3Tail32 : Box := ⟨-2931903132255860275079659739515866532395601917800444607,10303432374456479644282182925061627529436527016157670889⟩
def resval3Tail36 : Box := ⟨-4346678701687619127385850266041590215137146258378724374,12786969649283243271911212260988042186070420755591249331⟩
def resval3Tail40 : Box := ⟨-6444147328007958525833762332853319790198440564212580465,15736016194544662475519066856575250855925536843290402374⟩
def resval3Tail44 : Box := ⟨-9553739219084455992151314056081255627380197831863708173,19159331331315713289586180611734600410000327089725550068⟩
def resval3Tail48 : Box := ⟨-14163849524291904516670189811267939629778659528657261504,23006319198493784241737223095656315462645232771352577885⟩
def resval3Tail52 : Box := ⟨-20998546092407272131019745195715753760641964658925331869,27119659881251648965506025149696750251837271995337800980⟩
def resval3Tail56 : Box := ⟨-31131292184283232256481511160923038161807177584938527788,31159567009587575129170025441490396003207944595308086307⟩
def resval3Tail60 : Box := ⟨-46153545526348540994178974337362952215881859092616042379,34484355671263345087940325863850329266559574049913655734⟩
def resval3Tail64 : Box := ⟨-68424714003433998892093858215667297261709178177398502982,35964135226239874867349845872220219451459515923221398317⟩
def resval3Tail68 : Box := ⟨-101442505404085274072506782781399230165963235746297153341,33692634770790751562207510603978142490357076669856018980⟩
def resval3Tail72 : Box := ⟨848108609983252279289434045731894882071403312721911292146,766393058712894572189424776989717709472953177429071876⟩
def resval3Tail76 : Box := ⟨-2366860525168907355279315533137089414793972700441654,25927371500015804787204632155150438702179169698736813⟩
def resval3Tail80 : Box := ⟨-3466172229761632847063355035066534238703515661735741,33124284286553600454512255810808358974478858908693589⟩
def resval3Tail84 : Box := ⟨-5138754432501002866031950418433433193422331806154294,42228989864727103241217506016380586848548114160723660⟩
def resval3Tail88 : Box := ⟨-7618435341663678237300218025667134688895297010143345,53700922489535875451549335416727123977002645181226679⟩
def resval3Tail92 : Box := ⟨-11294674191470975685594423133243105050503425374277392,68085581311251624315761977451100041360792249151614180⟩
def resval3Tail96 : Box := ⟨-16744864184101997437195149363588565092193735217664819,86015914573950875887470840897663762144329541810082471⟩
def resval3Tail100 : Box := ⟨-24825016799134905851306434279823726325437134063783169,108202744123092315076274371882495263984633292084059981⟩
def resval3Tail104 : Box := ⟨-36804207684314555296916944154984443443707061357933830,135405320015420420450156771504934939900514369240193614⟩
def resval3Tail108 : Box := ⟨-54563898757053871271366720471071966295433981461243056,168367925585263785419635306980416451710819548208800875⟩
def resval3Tail112 : Box := ⟨-80893442214730100371807220781864003802662512392112917,207700336355109503554911900432735523238682405921504564⟩
def resval3Tail116 : Box := ⟨-119928178565171169216913171581497202994956430903338322,253667512740567266009750761386544573865656472789918097⟩
def resval3Tail120 : Box := ⟨-177798936726920310345550962113614233133018978395087925,305834983775062387854916856673286689782289468145167592⟩
def resval3Tail124 : Box := ⟨-263594947237897233729342811915874847452395836794266523,362487672298259570935095435261347664073268541434038258⟩
def resval3Tail128 : Box := ⟨-390791404540664113381327060908278209478623526535262362,419696507635564634750946875689188978772822281795757149⟩
def resval3Tail132 : Box := ⟨-579365892492032961199280955070820227777200208142183413,469841728493311058268231379953418947627646674791636239⟩
def resval3Tail136 : Box := ⟨-858936080725178346178272607021062294709590529313112791,499303339533592244927714595985207424665001789723004432⟩
def resval3Tail140 : Box := ⟨-1273411820487211494244025320427454180971244079430922718,484881390498644186897411594615625283384465713151315350⟩
def resval3Tail144 : Box := ⟨-2033247659001040716944899421534169504563665793211385574,381123352891123190827529141827923368721328218605490841⟩
def resval3Tail148 : Box := ⟨686191913779831829496851355665444237514456944,6016329029983383432133441982834100737276323229⟩
def resval3Tail152 : Box := ⟨912957247557185707215393731249363184438387201,7672049048052386207394448371966122745669707570⟩
def resval3Tail156 : Box := ⟨1353498459284160047658383936199364537732125593,9760119114209198810180921764314157870300163762⟩
def resval3Tail160 : Box := ⟨2006622544679728424125867262291082950554716398,12380380739664581552046114966015784117547067375⟩
def resval3Tail164 : Box := ⟨2974908475428237627037197792402606617747910608,15649617889860494879488059111062152390685288898⟩
def resval3Tail168 : Box := ⟨4410436063644626210784650853300986174646619426,19699726106736846649012839098476024961748482125⟩
def resval3Tail172 : Box := ⟨6538670494290426967639554382610837753373839550,24672857169869972025044442043995119471387274614⟩
def resval3Tail176 : Box := ⟨9693874078649191400318412476050305148316808237,30710642997862727770836187397340248226264429282⟩
def resval3Tail180 : Box := ⟨14371605777468438316795789908157062512976659288,37933587923791514962355301025001727640137802175⟩
def resval3Tail184 : Box := ⟨21306554113166825033254119065214199409344174091,46404520936823738879686503938963819044687542793⟩
def resval3Tail188 : Box := ⟨31587927974550449858206321542594912729744644518,56066650089176594025293507863527778124504942114⟩
def resval3Tail192 : Box := ⟨46830528692050560543429086329485667112253086386,66641677292826783614967484357910829337720091335⟩
def resval3Tail196 : Box := ⟨69428372109240328231100152379182286396931242959,77465741301622321209767344273007891828295482984⟩
def resval3Tail200 : Box := ⟨102930694749072556952965216989639071426501455118,87229356934765361867546654942424659263287045253⟩
def resval3Tail204 : Box := ⟨152599399923373583096506343759447970927650666406,93570064711727797459917683058154030149085060583⟩
def resval3Tail208 : Box := ⟨226235496746116874832771983352536284801832481222,92440296524570784744709151799620014773229137626⟩
def resval3Tail212 : Box := ⟨335404333418587349324100886261249024382897647690,77133677347015900510931305573191988209592888034⟩
def resval3Tail216 : Box := ⟨497259407028575397071636178510527335577359965458,36793723975933867210330723389642838086616955101⟩
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
def polyval3Tail5 : Box := ⟨34430603626922396496157518466000436051590142199147817494,310858738006521418948078338902249709983386151502520176629⟩
def polyval3Tail9 : Box := ⟨51041801899703550915549662681049230254435675444531057533,395945732764884755346731989757986791072474869687703432261⟩
def polyval3Tail13 : Box := ⟨75671774378643399008939245153559728625272021285935126911,502970695908360389985445971318802630830949304847497940875⟩
def polyval3Tail17 : Box := ⟨112186820359505733408707230328077011545009152391632839249,636888003002833200907590815695240584267861262565135311142⟩
def polyval3Tail21 : Box := ⟨166322023842416939722229526333311729569819807893578228591,803384003295839000684539832120040894161805825959855572108⟩
def polyval3Tail25 : Box := ⟨246579905967481351939837195872064595651345812236006412543,1008741658368967850385478474833115164211507000429391339262⟩
def polyval3Tail29 : Box := ⟨365565838018775742402019758889961334381686179327485282306,1259495970185738527398870157078282824910425894743926159862⟩
def polyval3Tail33 : Box := ⟨541967851768074913430437474430471465854358355595091764434,1561736852676192685274061465769788251980313605817888370312⟩
def polyval3Tail37 : Box := ⟨803491797652645724149280835732733131720047502169639832170,1919834454405813956808255590825960986175487416047247185699⟩
def polyval3Tail41 : Box := ⟨1191212849228836407093109954584155687671651522166343587059,2334237210127276455152740033677851881062763226369997585974⟩
def polyval3Tail45 : Box := ⟨1766026804895050714508277096470589440701455626232603120346,2797803221573338669005264080863506553898715899067253566664⟩
def polyval3Tail49 : Box := ⟨2618214433824226436261061928258558370193101869485843931609,3289838200538882040596879342744026655506362060312651712645⟩
def polyval3Tail53 : Box := ⟨3881621050419383612448316863467647978402834234370410854393,3766579195420037171998630945362928294508365499328755010937⟩
def polyval3Tail57 : Box := ⟨5754678373326239027832604127475563308724378554714800193864,4146209553811188831130610367827892759391456193456224767946⟩
def polyval3Tail61 : Box := ⟨8531570380073762285067723075894460607974340636451643958172,4285507964476944661833445106909124496819580548818504640327⟩
def polyval3Tail65 : Box := ⟨12648438093024446433682611792015437031086946424664477184192,3943760354176609218924836224519343357328251984418636654185⟩
def polyval3Tail69 : Box := ⟨18751880453566022919818942385342351478018371501083630547358,2727355628747341249040414094217559940262423078643700969655⟩
def polyval3Tail73 : Box := ⟨27906250000000000000000000000000000000000000000000000000000,2⟩
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
def resval4 : Box := ⟨115949649597531964761258419166250412639285651113418463702,8596603801566722850741151837257979809025443731814210424⟩
def polyval4 : Box := ⟨4687855763245782568766527195003146190518374996188213360878,1952242874976781794126526942776232376294000448231911084601⟩
theorem cell4_lo : Holds Q cell4 (15/16:ℝ) := by norm_num [Holds,Q,cell4]
theorem cell4_hi : Holds Q cell4 (31/32:ℝ) := by norm_num [Holds,Q,cell4]
def resval4Tail4 : Box := ⟨-3870493743627351245388310742542018936652385864957410623,9342740768992464512462086320360684625158974746974976300⟩
def resval4Tail8 : Box := ⟨-4690009529707779303211015393798323668815943914897074770,10312511864050026692811563757450767887659193226919706367⟩
def resval4Tail12 : Box := ⟨-5682955845363256184764980198147274283849098680755702564,11351073570903275853862584513916315381975722966218178297⟩
def resval4Tail16 : Box := ⟨-6886123980207006532741304996692171942202408807261363821,12454502198513227390368674041572003683137976656122212005⟩
def resval4Tail20 : Box := ⟨-8344021097650414589307085643694111480556692699956127697,13615540662155561212418518661761436479777691428613442920⟩
def resval4Tail24 : Box := ⟨-10110577195263047140498988152735080616733070346663278880,14822553109137514652392912596090587408585013443561384085⟩
def resval4Tail28 : Box := ⟨-12251140070841656993669027802482204418686537186597352821,16058212983465850355877254780147098445296585548204496342⟩
def resval4Tail32 : Box := ⟨-14844892644279663561069010650552391124026438483484717500,17297861216513484431868830166139981744595357793651490881⟩
def resval4Tail36 : Box := ⟨-17987782063212417358718460887405294593544163561016317483,18507457646913325261055439718483785919524028406880930570⟩
def resval4Tail40 : Box := ⟨-21796068944850686925289317808478374566737818920437533826,19641031537200950983452297437751846286819557282279977724⟩
def resval4Tail44 : Box := ⟨-26410628046259671931896385660746635855750261551441394265,20637516040412724549330762646403578747857170263289085338⟩
def resval4Tail48 : Box := ⟨-32002159451907363946652222787267378735143296954239569141,21416825859554524630748702519129053864830595523920834650⟩
def resval4Tail52 : Box := ⟨-38777503048828269263169125474811254569907251401472914739,21875006143655129550613223774353688380399138096299091504⟩
def resval4Tail56 : Box := ⟨-46987289872160893755589716705583854292945971263406628964,21878242670160771873181649611051456940995206797721586738⟩
def resval4Tail60 : Box := ⟨-56935213356830360026349725295939269141572780022047175849,21255477110511592048991523716948084856985703073010348053⟩
def resval4Tail64 : Box := ⟨-68989263442305673377453961145635345637346893646959462467,19789314885898964748252550987203233556580171846535549751⟩
def resval4Tail68 : Box := ⟨-83595128448262770028607575618682875134355308303734191583,17204841777132534810088964983297207332230362196859006542⟩
def resval4Tail72 : Box := ⟨848452044643821199043947274442344913689580129713826688661,730735452355404655052303895909902844924202821295178224⟩
def resval4Tail76 : Box := ⟨-51108067573458352990834337158313839000074805157709427,126332676961300948077231670000563734217642975316423742⟩
def resval4Tail80 : Box := ⟨-61893532138508225596414204600030692355418408856283453,139541819900924924829899050535866333957904648489294452⟩
def resval4Tail84 : Box := ⟨-74997331806804057797365226078418568105488951429202150,153714602252728887832352236323973984121892346357387401⟩
def resval4Tail88 : Box := ⟨-90875406927734657269610165673435590944582888687282128,168806663071188053821895975674077677453624321227834211⟩
def resval4Tail92 : Box := ⟨-110115111903600540908906665291558465430482220148694525,184730794395430886203548305006689120653171031161746034⟩
def resval4Tail96 : Box := ⟨-133428154871262573377406026122668032505154467953777733,201343161691558577805713894137495095813672769707186154⟩
def resval4Tail100 : Box := ⟨-161676923399353233586967640262551440742852769047568062,218426147387533854727880666397363491233461986959914103⟩
def resval4Tail104 : Box := ⟨-195906385613297412514264749071299661151542011800811662,235666862372867401780538523129069561798803586924970670⟩
def resval4Tail108 : Box := ⟨-237382745274453401702137234376460722664553076575639639,252630313530209141223711734965736132445345253249307659⟩
def resval4Tail112 : Box := ⟨-287640280727077828085040145393992174699688817508789406,268725988311912980580873784527979804791242668872829793⟩
def resval4Tail116 : Box := ⟨-348538100362326981131811997571752044235626780455828470,283166340493732411341294920046606337732887669705643480⟩
def resval4Tail120 : Box := ⟨-422328914076684690141598327972452571953310873128174761,294915323764234285844639261379003830282296377821382233⟩
def resval4Tail124 : Box := ⟨-511742364693483021314109333882611623005916477095734990,302624708646786943805638383673973135685632679535832118⟩
def resval4Tail128 : Box := ⟨-620086001913017837569416585086748874378243212870306888,304555417496878702424990065117189899884304634178487057⟩
def resval4Tail132 : Box := ⟨-751367633982768236217078920887445276326958149901952450,298480502658609901862411456798253843702293732168288505⟩
def resval4Tail136 : Box := ⟨-910443583110545430700713335552520224542762137622933552,281565650850695512215477272091112437341520378682903824⟩
def resval4Tail140 : Box := ⟨-1103198633673393324110272274063587476527772679634017593,250222179568314941633456415225114431371803555440647926⟩
def resval4Tail144 : Box := ⟨-1475127884237883372177875662021003332043397852377146596,195396998227398166008092064239916293900595545400845247⟩
def resval4Tail148 : Box := ⟨21106447187144299426893456130607631327387808540,44836974019938595758669189845161227245609417514⟩
def resval4Tail152 : Box := ⟨25489868006454317529313748484445428709736110916,49302724564909630933661355356297013857812723286⟩
def resval4Tail156 : Box := ⟨30886459003339803467931085003347853475264770065,54033879814304966198273934834319382759485944894⟩
def resval4Tail160 : Box := ⟨37425591855888414066001613845890183671609195603,58993903960263216085899545135002801012977230610⟩
def resval4Tail164 : Box := ⟨45349158530281346723171114003412002983066584728,64126607851767649197361221668109120723183809756⟩
def resval4Tail168 : Box := ⟨54950264709870106025021268634754041820699996817,69349736275297965985977058019701026218297827416⟩
def resval4Tail172 : Box := ⟨66584071006930391530626510354512988563577993986,74547530584179714441029163364076765566629017286⟩
def resval4Tail176 : Box := ⟨80680930933889005051689979910604948998880513422,79561456916522485833681112441253000859853219973⟩
def resval4Tail180 : Box := ⟨97762310383236204847937299338797762985093282330,84178676429876956050356917014325136042502297485⟩
def resval4Tail184 : Box := ⟨118460077503316453493340171548326868775315608696,88117739556119061023338305899013671202428867923⟩
def resval4Tail188 : Box := ⟨143539876534035083648176375260917355931149007302,91010871203065268233313728578753858730293624444⟩
def resval4Tail192 : Box := ⟨173929450238872304684708347200181979329736604710,92382073656283017799367560967923869107965381181⟩
def resval4Tail196 : Box := ⟨210752958626262734960337060797324347561705821115,91620103253095057066661794662351505416652398850⟩
def resval4Tail200 : Box := ⟨255372563465944263785891790431269640827929249613,87945169139171891632741494230012770281830371393⟩
def resval4Tail204 : Box := ⟨309438816879513290345651475558400139269117385454,80367949598068027953558695721167752060228182847⟩
def resval4Tail208 : Box := ⟨374951717961572086095098325562105442864025074060,67639213880845978752653156765082707279974292371⟩
def resval4Tail212 : Box := ⟨454334696162141211952156831075387325482665595340,48187963393578605444920427756863001345672901943⟩
def resval4Tail216 : Box := ⟨550531259730226762083497228508890721656003251578,20045225243441329542381287556166672318047774862⟩
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
def polyval4Tail5 : Box := ⟨1062487672953385334879034786551049163655671245476942819121,2148069260862810697786277471815851147123646396839561282588⟩
def polyval4Tail9 : Box := ⟨1287429920345359244262196301106725115310934534360051638145,2357869686929362764652034147418977214671652577567783265783⟩
def polyval4Tail13 : Box := ⟨1559998403497880982116881680518074313962064213245852515331,2578915254970681860749031476743002972999513467267166552556⟩
def polyval4Tail17 : Box := ⟨1890273777890156873543694363309306075448560167263117780938,2809094756601383608119307840274632562659485167821407412810⟩
def polyval4Tail21 : Box := ⟨2290473469311049927904634173178715251195883301493945390136,3045241755814313716367599269041178622643808876895153512425⟩
def polyval4Tail25 : Box := ⟨2775401518542705764048391121011565849930337536068112790722,3282828806377954731654746048563731311846787181448500082146⟩
def polyval4Tail29 : Box := ⟨3362996206826221666442504705622560589124922011390805428381,3515585786635764037951870167083541145227401157775463544463⟩
def polyval4Tail33 : Box := ⟨4074993622207866994969832890352884898864538090758741273346,3735024766520050531487744360162578671226766217726009906505⟩
def polyval4Tail37 : Box := ⟨4937731712967365541308471383085274465604822154574713099133,3929849903453663161037783495895466191438064786341511074049⟩
def polyval4Tail41 : Box := ⟨5983124571378762231741093247993120353303070762030054038598,4085226079034489435076637281806127935686008366914893206088⟩
def polyval4Tail45 : Box := ⟨7249842988152825947853371281508513658525418724522518120377,4181874159164588360851822816055627346156548336212190830169⟩
def polyval4Tail49 : Box := ⟨8784744948199636406232557327768144441146761695839249894583,4194953661215314662795837188915123895242158480582956535471⟩
def polyval4Tail53 : Box := ⟨10644608984088009614670521294330077147353303538915611927693,4092684969233995768510686039369188424140214732095197521438⟩
def polyval4Tail57 : Box := ⟨12898234506779696642217326856753153309545301535295668552024,3834652719822162116899592944600525579225935158630174058756⟩
def polyval4Tail61 : Box := ⟨15628986808305594495375121075176503405462544896618115284349,3369719183784774474288633894499523998637651125363930824165⟩
def polyval4Tail65 : Box := ⟨18937880880215021526109308729593526944034556894156709040194,2633460902355471139812001193846178197337780899021389509492⟩
def polyval4Tail69 : Box := ⟨22947318308399528482849973648698042041030173475128171570646,1545022899233067136475579297962848053431507587052360748860⟩
def polyval4Tail73 : Box := ⟨27906250000000000000000000000000000000000000000000000000000,2⟩
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
def resval5 : Box := ⟨104875948004539640513446247059308384920305387495462601614,13495218442075240161003414088473793755616734191728697055⟩
def polyval5 : Box := ⟨8851524583917971320560539059526692741453311800722164021654,3909036738935595360675488959432754486639432108137539516831⟩
theorem cell5_lo : Holds Q cell5 (31/32:ℝ) := by norm_num [Holds,Q,cell5]
theorem cell5_hi : Holds Q cell5 (63/64:ℝ) := by norm_num [Holds,Q,cell5]
def resval5Tail4 : Box := ⟨-15671753446773943553291636519509525569281237441009416481,13722743358282548218582779964911303481569936514517658515⟩
def resval5Tail8 : Box := ⟨-17231341653313013913001693056846001434155809327356773058,14074444502361949675925022268329612447545186019175937389⟩
def resval5Tail12 : Box := ⟨-18946060518031803371122421183765943166989646533779539830,14395222844775645831718276368695473820644479609567480231⟩
def resval5Tail16 : Box := ⟨-20831413840131022243026984533096775976770039824868312641,14677714424398757150719084542573394602954089609225479922⟩
def resval5Tail20 : Box := ⟨-22904381740237983989449570452874688599344666214881627291,14913544354146536510832845754104892768838875097255357539⟩
def resval5Tail24 : Box := ⟨-25183634050411957751997208687619626392970687605251837916,15093207538767720466714954939512214920738366664020664080⟩
def resval5Tail28 : Box := ⟨-27689698468083551725218646937927000782721303266301238443,15205936907351626745784935286328107912779171941403358506⟩
def resval5Tail32 : Box := ⟨-30445145435269159541789076982486219909960727977450526634,15239557278774065933250473043715990551596180088322138586⟩
def resval5Tail36 : Box := ⟨-33474791415409849648661350012036821548552870841662729256,15180323348683670746201875918509175931402063884895117311⟩
def resval5Tail40 : Box := ⟨-36805922398619354797282972100499455591306841295086030398,15012740131046403650427952650919984145931839375962834225⟩
def resval5Tail44 : Box := ⟨-40468539648303105127231540795876914610064846570433212244,14719364015732426812629823589759434702124709742674082231⟩
def resval5Tail48 : Box := ⟨-44495629902423341663433535675583221922502471306341767184,14280582414658859633808496394453938724988365939724605675⟩
def resval5Tail52 : Box := ⟨-48923462462931948125620721130505030869446540126789503193,13674369760835290014483537419908587655531287223992761223⟩
def resval5Tail56 : Box := ⟨-53791915849056314860469775891482942787953444253985363635,12876017395360582983162566101652550150763673112214641020⟩
def resval5Tail60 : Box := ⟨-59144836956377995600994190372721253150147383534079251336,11857834624859267922288995865864204169436238195518100750⟩
def resval5Tail64 : Box := ⟨-65030435944833727451960026988999815380100291284897888629,10588817953302473427481327686615973142893617789187491786⟩
def resval5Tail68 : Box := ⟨-71501514512670474700028489108996680097074695613209255303,9034280775468033231552884406660191115613723951824447565⟩
def resval5Tail72 : Box := ⟨848493845222759936965650338691658487985129384382491239914,733912004822568174031719411238439421549987741105773451⟩
def resval5Tail76 : Box := ⟨-211500489356666883637184233063507928241848882212175206,188349813378695667854724888421072941882768816335944423⟩
def resval5Tail80 : Box := ⟨-232515631042647294385691115584354556000424736156156673,193302097877343658130025350016620196803559614637191659⟩
def resval5Tail84 : Box := ⟨-255653638267201352808829210829027147736301926963576692,197850689486680933317190099631726571462822256864478478⟩
def resval5Tail88 : Box := ⟨-281094147957067210083863168977282612217124756735197522,201896958517885500128283866448874163871875159511830040⟩
def resval5Tail92 : Box := ⟨-309066284178580126491047739877703221955150968146884164,205328826645933380009216254571641271834803542041744259⟩
def resval5Tail96 : Box := ⟨-339821973207870404468671364951416393579384464611505015,208019025296905985823704561642284331045761756363988864⟩
def resval5Tail100 : Box := ⟨-373638210915837848109427107174171487924713926934958316,209823321526876287980414278280797186095887510916030318⟩
def resval5Tail104 : Box := ⟨-410819557483385284062565629848597585772532532694501576,210578550306154897403982274860312234772469065379731240⟩
def resval5Tail108 : Box := ⟨-451700880370772955747600118120030449913123721565910939,210100432815770079876761382726007169832412284612191060⟩
def resval5Tail112 : Box := ⟨-496650370244320818989951381502986100690049490972753548,208181158280016973883063490267132907565914182398264643⟩
def resval5Tail116 : Box := ⟨-546072857022886258519901808043034407947658357609768951,204586704545442159746740186402229168483841272671816216⟩
def resval5Tail120 : Box := ⟨-600413455909524583518216122995557482988917226001673222,199053870067930996668426606749187869874100074841410522⟩
def resval5Tail124 : Box := ⟨-660161576245694984186524932174573479384308080424859946,191286987161919840615088997188447208784988849027237605⟩
def resval5Tail128 : Box := ⟨-725855329293074195247457305204281611180902940208338696,180954283273049239308190179527767195942028119527913670⟩
def resval5Tail132 : Box := ⟨-798086374640947384214912560638411605807807899359299782,167683853629069994262755310963420530048896968546011493⟩
def resval5Tail136 : Box := ⟨-877505248921338201911241309059396312132868080315150631,151059204870200584943448728505682274820342510011512082⟩
def resval5Tail140 : Box := ⟨-964827522891069871824624686427854806421099773736099757,130614313204521263631122498695570275531817296057414352⟩
def resval5Tail144 : Box := ⟨-1195954862400994413326144955580397952389803122673265326,102471097458009794137982817471036342112995806170990981⟩
def resval5Tail148 : Box := ⟨115326997345647147677760483414404325778445627682,86694465723421956963572612650981355615203548777⟩
def resval5Tail152 : Box := ⟨126726193263164167008122783870808861101681841736,88355395902403503103222633887854860860751413933⟩
def resval5Tail156 : Box := ⟨139336921667340173826140517299240381642665318822,89729236619942949841307869882568466261555807738⟩
def resval5Tail160 : Box := ⟨153202565551319927846781560648636810089292881709,90757437642314239783385413668047449884864273040⟩
def resval5Tail164 : Box := ⟨168448002228790361647357840353910272741747436783,91374241280876071128537168279960211014009646272⟩
def resval5Tail168 : Box := ⟨185210537126192561559305478734717622522608268121,91505307023124620928582803804525735780004491722⟩
def resval5Tail172 : Box := ⟨203641139156887264386634412688559813653976757969,91066724838677164518054620617129596186561476810⟩
def resval5Tail176 : Box := ⟨223905800396548048301944778495902594424333652658,89963921692664733064397390746067917251114290824⟩
def resval5Tail180 : Box := ⟨246187031062496690879287058300111838187410920743,88090450063159247895241959111520762898535166535⟩
def resval5Tail184 : Box := ⟨270685503260866411375228255010060618986400053626,85326646123687567175289345342839782103004496675⟩
def resval5Tail188 : Box := ⟨297621858305720983931473647938326315920217246539,81538143985208902951599692281731189881377476846⟩
def resval5Tail192 : Box := ⟨327238693887441304497570084331036524252435191760,76574230996675754709012967081113681970943041925⟩
def resval5Tail196 : Box := ⟨359802748987472770058525578841189338466983107791,70266027566510120647543093883331003107634669604⟩
def resval5Tail200 : Box := ⟨395607306217495722240548131440930758957838791409,62424473274747458697021431496636722727945398850⟩
def resval5Tail204 : Box := ⟨434974833219277321823804013020670377070793430347,52838099181541536231133126858427950986128240519⟩
def resval5Tail208 : Box := ⟨478259886914573452481659745804984676355349937631,41270564184918391092276289806406436579558997849⟩
def resval5Tail212 : Box := ⟨525852306905002664501814904091051228102163432046,27457931013162995622192992229997546018481650390⟩
def resval5Tail216 : Box := ⟨578187567897539194550072688382890794494075852109,11105388493483987495561450156348331229637887023⟩
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
def polyval5Tail5 : Box := ⟨5543354517183300365677911900931410819186737387779988835239,3987379652442397623640757580538452105719340012505056812266⟩
def polyval5Tail9 : Box := ⟨6094980444747627363944378174838624036500162539293225330952,4055438292365233016604535725575077472047372329204401967921⟩
def polyval5Tail13 : Box := ⟨6701501869844445306673398593675280808354496958691306269852,4108895466856497556498826983180136230470987056446625774242⟩
def polyval5Tail17 : Box := ⟨7368379229456399061534122874055356821493215301973081670890,4144908409842253217661433879704495994180454612931495633004⟩
def polyval5Tail21 : Box := ⟨8101618640650473334358259904252670391587922568341624781777,4160261116091358777759345469078912620802753242474635978312⟩
def polyval5Tail25 : Box := ⟨8907823899201986332285677533498771810936368917097256982343,4151321314506418930021175934112592897563260370456029663638⟩
def polyval5Tail29 : Box := ⟨9794255955353531339393888985161885836167054164232259038131,4113992787581341418657342263388682748251876527918844402557⟩
def polyval5Tail33 : Box := ⟨10768898308325543224508676675618637977279754971622518314899,4043662539247610431749114859384499418750305706956022998656⟩
def polyval5Tail37 : Box := ⟨11840528908341230763696377620142293941776048441734666785285,3935142272008791983911325130573159273758869159878935591965⟩
def polyval5Tail41 : Box := ⟨13018799213739050941047561603776987037792242424962133500816,3782603578898300680754003337280230957845475937944725631294⟩
def polyval5Tail45 : Box := ⟨14314321115187132843495342492235932123392416969739533288332,3579506194807480729597243405694091715719887480245445391693⟩
def polyval5Tail49 : Box := ⟨15738762509867772027671799518559971283649889826530849166727,3318518584554958451585674877374295540858081881092760079286⟩
def polyval5Tail53 : Box := ⟨17304952386404597286265507854506435434657320565226429185571,2991430071080477715363506740513385078127060695408733708785⟩
def polyval5Tail57 : Box := ⟨19026996366961894595303610447866494802096532500769037764310,2589053625660947646095945270596262441841343669739380384099⟩
def polyval5Tail61 : Box := ⟨20920403747126332622166686048911252567768137114477385252609,2101118352308316574715772262173397709751015590733241666268⟩
def polyval5Tail65 : Box := ⟨23002227177755482256071055637191050508813297274981222887698,1516150599686520470811844778935984669552646331743643765714⟩
def polyval5Tail69 : Box := ⟨25291216427820861303112604880223295340865751043248149863440,821342518302686252332397421439560816881211181457055452320⟩
def polyval5Tail73 : Box := ⟨27906250000000000000000000000000000000000000000000000000000,2⟩
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
def resval6 : Box := ⟨90104091074168467601147137495522831644635373341704292076,11973000611228532529704911116193890697818547827691770742⟩
def polyval6 : Box := ⟨15710416227460447358397851777627558469022737571220938877017,3912233844260982606513641247258529673767574461989016984921⟩
theorem cell6_lo : Holds Q cell6 (63/64:ℝ) := by norm_num [Holds,Q,cell6]
theorem cell6_hi : Holds Q cell6 (127/128:ℝ) := by norm_num [Holds,Q,cell6]
def resval6Tail4 : Box := ⟨-30418985383311758853107026718691036068863008748673941633,11727448436775800652217378396232120822781367701369684095⟩
def resval6Tail8 : Box := ⟨-31887712341388727477513286668512043145585252342791469233,11601991034853803284505098956710884143259856161603345141⟩
def resval6Tail12 : Box := ⟨-33427287778008118649233478938872543296483839062903920023,11448433336828666875024173138083235183078568237755115945⟩
def resval6Tail16 : Box := ⟨-35041195679881257709340658661568268999670812721433998122,11264715579662127647637078313952314986464636525493771644⟩
def resval6Tail20 : Box := ⟨-36733024911560903985694309620471978537039040090850513902,11048656681684254402112355001358553353627472565592270556⟩
def resval6Tail24 : Box := ⟨-38506537604481803564340042499871803682743612235513036828,10797947153017278259919666784116365719311956272031190552⟩
def resval6Tail28 : Box := ⟨-40365677530104728711904766104923580216589274126763562313,10510142159466794893646510461468609732058976836067510768⟩
def resval6Tail32 : Box := ⟨-42314578869712663047536369702907324438766529005279729959,10182654228177331095842947362360229004385624593985842893⟩
def resval6Tail36 : Box := ⟨-44357575407616052489627145676084931232887568135937921605,9812745576894995791924207678458504108729979606101512692⟩
def resval6Tail40 : Box := ⟨-46499210168216554118951559489785437328127028688768566509,9397520047892691746498417072628314116417324280981241982⟩
def resval6Tail44 : Box := ⟨-48744245518359307049305641918624254954496068368531561020,8933914626674255104323034417700328975514527959936525957⟩
def resval6Tail48 : Box := ⟨-51097673757438390607791812036361985584928407646443218823,8418690524588508376894441505587933672312287855218398804⟩
def resval6Tail52 : Box := ⟨-53564728218804754472072055951779106333847513974681970910,7848423803450446026793087152073518056913609345474851110⟩
def resval6Tail56 : Box := ⟨-56150894907162868660740157898515210043989036225023995557,7219495519182257781234581164075765357804100027558586617⟩
def resval6Tail60 : Box := ⟨-58861924697826938632231746500719687397569221665793859573,6528081360348796821543660887194852347670224617616128592⟩
def resval6Tail64 : Box := ⟨-61703846113510038293947965220510552619338224815631536818,5770140755853388951962443482556612674638503693424436124⟩
def resval6Tail68 : Box := ⟨-64682775103452921806869166965886560800585297209407209660,4941400282553364765354527900542176373396859001765941166⟩
def resval6Tail72 : Box := ⟨848387244775395448009963257164809278222853031596429262568,681876904244007220236128123001270106433138076895223249⟩
def resval6Tail76 : Box := ⟨-414010924726714432996612465387718682632865442381609292,161861305812026372383586688846288261430763318108641120⟩
def resval6Tail80 : Box := ⟨-433969725710048111183515243603364428655742772898937546,160225759385234282149858394296240247091761683232802456⟩
def resval6Tail84 : Box := ⟨-454922281595440932267757836231170922082529470820931863,158210224080695907280858373091658165446059143832054270⟩
def resval6Tail88 : Box := ⟨-476886452599897789627040900225351737745511380686169477,155786598502309176547159191741544637214420825726057252⟩
def resval6Tail92 : Box := ⟨-499911079044469804185687457680706317919879581876725071,152925275064902655410551267591520370052703836034697337⟩
def resval6Tail96 : Box := ⟨-524047360936629249703246302326328478819502773987222986,149594901056870219030856788699873728374998832245443491⟩
def resval6Tail100 : Box := ⟨-549348970280005223255489812603076747673308280987678615,145762284305079613220568304926743189711202760707642917⟩
def resval6Tail104 : Box := ⟨-575872170424297802968218353297330191876737591108600590,141392293982944546738836576973580412126711046559578087⟩
def resval6Tail108 : Box := ⟨-603675941178444507802747107997867895153044633327402082,136447756298582781197109674054077260589319195759553066⟩
def resval6Tail112 : Box := ⟨-632822109964396720954231054414661260705972457646719309,130889344805305299726622391571167113338239891065830275⟩
def resval6Tail116 : Box := ⟨-663375489303151312757223335317521219073726513250329435,124675465063916878773033743344173192358442448614346720⟩
def resval6Tail120 : Box := ⟨-695404020938766006853892255719404542085443683219071136,117762133372900714756227224561136883880957761570248206⟩
def resval6Tail124 : Box := ⟨-728978926920847981420261295478872647384447343214048112,110102849268493636332066910672892419822410428940783662⟩
def resval6Tail128 : Box := ⟨-764174867981478948827225819881428030142416190580230156,101648461481901768508664239592018561636888725458086765⟩
def resval6Tail132 : Box := ⟨-801070109558794087531292658408220680375949963761778140,92347027025423601695798059791755847837013816530713245⟩
def resval6Tail136 : Box := ⟨-839746695869873756665407004466020568646451383174945638,82143663061442854746972845244230148463420868129965618⟩
def resval6Tail140 : Box := ⟨-880290927210815025894563281937290843927014108140749854,70980380467736325197182348246072057790210996949595166⟩
def resval6Tail144 : Box := ⟨-1056339979781026861545022113626763086353205728784386732,55992437691713983375864984037387862094091418114094567⟩
def resval6Tail148 : Box := ⟨265771190862296662578748088381227039876847929314,85557854954848558664838470940878200402050070102⟩
def resval6Tail152 : Box := ⟨278529377888503192896379970405542569213532149511,83923619481631039369737355118868848376739610430⟩
def resval6Tail156 : Box := ⟨291977095312450295515977695652944981623314821978,82027285157256504489243423473322526893384132817⟩
def resval6Tail160 : Box := ⟨306074085304707937770236916514451839530429534201,79849822377385931096672289474625320620291123265⟩
def resval6Tail164 : Box := ⟨320851694188510608474206907031322132920325428762,77371616281085349744479536166697505606832647040⟩
def resval6Tail168 : Box := ⟨336342783026375608705748583462574136934441377863,74571912447730136685403546554782124024078322603⟩
def resval6Tail172 : Box := ⟨352581799451126389472257554311909625189576097667,71428755725725060375520107301514507620266222718⟩
def resval6Tail176 : Box := ⟨369604854266921363304430924558573635221950636079,67918925927771479062429691252162325649765152142⟩
def resval6Tail180 : Box := ⟨387449801749078230028743117356295977800268754461,64017870219632983670719756544943218980121681039⟩
def resval6Tail184 : Box := ⟨406156323820866876949786239980487944931848967203,59699632036318789164704053584275193666087279723⟩
def resval6Tail188 : Box := ⟨425766018294454664366631719481463627410203828166,54936776351388165661695328678055184379636611430⟩
def resval6Tail192 : Box := ⟨446322491372226043960884804060577897990600159020,49700311116452470017686972299878386057401708244⟩
def resval6Tail196 : Box := ⟨467871454614172283062156228625103850156068432856,43959604678901341096354077011757275542636479695⟩
def resval6Tail200 : Box := ⟨490460826586978297214300406168501597211203178820,37682298976385724477100867137917758369845997509⟩
def resval6Tail204 : Box := ⟨514140839420844420459888153056715777450691358971,30834218296630933754244910952337074449351749220⟩
def resval6Tail208 : Box := ⟨538964150511044747773927484558212330791174954742,23379273380702374227987641192593102836731646138⟩
def resval6Tail212 : Box := ⟨564985959754374791890683433121493400320620055950,15279360630493531049418121439990832601942842894⟩
def resval6Tail216 : Box := ⟨592270896212701372866891703900825403499152073755,6494017911014657476453098679880184023478998940⟩
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
def polyval6Tail5 : Box := ⟨12475710520696916657823716417229753617488968070458419305890,3839543676560942442139223153780242968005667456949618695658⟩
def polyval6Tail9 : Box := ⟨13078049979516831140576958857884925306623636545628901557093,3757169530748123733227628529845236329166030726101564770384⟩
def polyval6Tail13 : Box := ⟨13709473274640892452715937433786500903094174043028611971985,3662285023632677794235327625954960948666933464153780853601⟩
def polyval6Tail17 : Box := ⟨14371382412926345646059750042914706117188509856415166851185,3554014175653799492660609570626386933122492633046042638530⟩
def polyval6Tail21 : Box := ⟨15065249285733853102060792198573276777048846604964724030443,3431430056726080568833126434240342151130292905211652445969⟩
def polyval6Tail25 : Box := ⟨15792616849243643784101464772964882498656130838869089002502,3293552040082092719917728881252762364364867100377549307723⟩
def polyval6Tail29 : Box := ⟨16555102555335195132020354825345048074464594145810476259335,3139342924705147543856947110144686010949115087763064630554⟩
def polyval6Tail33 : Box := ⟨17354401948325113541162743693524481566788652521490447042731,2967705909748227606735637702201934568685985660052988606088⟩
def polyval6Tail37 : Box := ⟨18192292435359820033678434597376645808892075987171335784085,2777481413501055068795385525835139267322014815009158086356⟩
def polyval6Tail41 : Box := ⟨19070637238847132029878169669072686581725238519714671385722,2567443729101172116397180579491639037660639167482630816222⟩
def polyval6Tail45 : Box := ⟨19991389539715787965584427038675092572631261458182137701610,2336297508798597567860066746442643882856302448967276121687⟩
def polyval6Tail49 : Box := ⟨20956596820716307320138685936953589281884327208085825591768,2082674068178356488237310142726293931104735050157956060191⟩
def polyval6Tail53 : Box := ⟨21968405419421411816611751055719147705140098393341865965625,1805127501320032231577605219728634914183665681323334417469⟩
def polyval6Tail57 : Box := ⟨23029065301050543894794402086902091644582866962995232043421,1502130597427493233620668137964170175570998337869908940347⟩
def polyval6Tail61 : Box := ⟨24140935061731863599924666597907430690590926060414907642912,1172070548994081954967862055104364644862582309343099993292⟩
def polyval6Tail65 : Box := ⟨25306487173348641106891673818552037081273457789942185028744,813244441076808148749105678223185301987726328038126332372⟩
def polyval6Tail69 : Box := ⟨26528313660653093134501631877579074601852902889681910852452,423854504698432371828706880740322265223939046346546422904⟩
def polyval6Tail73 : Box := ⟨27906250000000000000000000000000000000000000000000000000000,2⟩
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
def resval7 : Box := ⟨73220302844814129152631368870870103927567202056205433011,19220865129076756123321695103087273506116973538108333658⟩
def polyval7 : Box := ⟨24789368666063179267516354472407507113939019628192602200600,6833423028559604269792218375832677120540821473649759587064⟩
theorem cell7_lo : Holds Q cell7 (127/128:ℝ) := by norm_num [Holds,Q,cell7]
theorem cell7_hi : Holds Q cell7 (1/1:ℝ) := by norm_num [Holds,Q,cell7]
def resval7Tail4 : Box := ⟨-46621107143528556548366646123618259062082184090098583016,18350380287457282625473816474610723007265001500586981102⟩
def resval7Tail8 : Box := ⟨-47356793073522555758007039707500880188837199270624427875,17614754264200924144823748918294427726927051026705545230⟩
def resval7Tail12 : Box := ⟨-48104025887897396606686179255127654152292550412496993355,16867521457004305261306583176661097421584938465256089363⟩
def resval7Tail16 : Box := ⟨-48863049123178445657305283609428176687545587700932717172,16108498221729694030879434611180045886533860528507833338⟩
def resval7Tail20 : Box := ⟨-49634048825308932845144190709471914451071392159302111398,15337498519599231941858409409702552840413652131922436522⟩
def resval7Tail24 : Box := ⟨-50417213968429103024375167676837316058610290534666303966,14554333376479062086875611278689192412375437786431920725⟩
def resval7Tail28 : Box := ⟨-51212736508455520901853115812738091802617539026591936596,13758810836452644220910072854348783289990200254175549756⟩
def resval7Tail32 : Box := ⟨-52020811430136473934470950179660061249916091542370040452,12950735914771691189209761551043980473239404019057903922⟩
def resval7Tail36 : Box := ⟨-52841636794843291571894720991661631202118799548834539552,12129910550064873551861394831789485731931449804401280684⟩
def resval7Tail40 : Box := ⟨-53675413789115728859090331257061785911946585119429523056,11296133555792436264475493726827816036242932269555462963⟩
def resval7Tail44 : Box := ⟨-54522346773973337071264756212557465124299558324252472055,10449200570934828051139492144798064542099007845351960854⟩
def resval7Tail48 : Box := ⟨-55382643335004908004874031050649093864051956531862463631,9588904009903257104885160008674079778995771269377919772⟩
def resval7Tail52 : Box := ⟨-56256514333248268737111229725906280359354956503617803853,8715033011659896032039825845514422624181315032407176925⟩
def resval7Tail56 : Box := ⟨-57144173956872874213177122615857732213340979817777930495,7827373388035263680074879300728431842179411292838631728⟩
def resval7Tail60 : Box := ⟨-58045839773670604951695010945087046065138752939112565866,6925707571229755458489736615160589926121097739965542959⟩
def resval7Tail64 : Box := ⟨-58961732772992866611740202692363474847271014688191382044,6009814560074547632892237957684731271939435934781774253⟩
def resval7Tail68 : Box := ⟨-59891875295878301215863252584538434371051062758462499652,5079464760867348652069783121051225091199102698831408088⟩
def resval7Tail72 : Box := ⟨848219422819130282234137941038633383038660039662882478014,779849143613446760682487843731420266391829800791086091⟩
def resval7Tail76 : Box := ⟨-636640528159767042877425789356347643938318871283296880,252945900723343737545291586038652699196702463445714420⟩
def resval7Tail80 : Box := ⟨-646656768739811749771210932679685022010364749465699541,242900788462963635281485261844993207138519228022985160⟩
def resval7Tail84 : Box := ⟨-656860227350831744081273477346872124389020471748169797,232697328288152709747797895033795949072714813454013311⟩
def resval7Tail88 : Box := ⟨-667224685743695662491102566411167161614864816971967409,222332869894402976197554863026565380869523190737340881⟩
def resval7Tail92 : Box := ⟨-677752682731062116114912489418170429206659657917692262,211804872907034082080637171082250766778303980362435853⟩
def resval7Tail96 : Box := ⟨-688446798752894562220622589961451427162755499141202507,201110756885201612057026600650901483255631359444290493⟩
def resval7Tail100 : Box := ⟨-699309654966248772750516021601407289844059402223947330,190247900671847400838119234706049510715769407996279056⟩
def resval7Tail104 : Box := ⟨-710343913886864845569349185069956380257340091904144900,179213641751231327969072984989715508381664941192583426⟩
def resval7Tail108 : Box := ⟨-721552280041754799165239038437907146254061453290003110,168005275596341374365709635224023028388436038658173467⟩
def resval7Tail112 : Box := ⟨-732937500632089512638625732082470594898381608143152651,156620055006006660892044895203176841525523082952874731⟩
def resval7Tail116 : Box := ⟨-744502366206545238784877357109116121607867206931700716,145055189431550934755886515006461297858109636808653002⟩
def resval7Tail120 : Box := ⟨-756249711345274709742161758288118428925853536526964061,133307844292821463907992060780880128084305814627914657⟩
def resval7Tail124 : Box := ⟨-768182415354670480093228946525280227292180256717904240,121375140283425696014601422528431189061961204970090098⟩
def resval7Tail128 : Box := ⟨-780303402973090946990758242235937467723680747695555146,109254152665005381584309676571420341042097034697955574⟩
def resval7Tail132 : Box := ⟨-792615645087755405778814521971901735531559082382118449,96941910550373168818404870034822809005132162960315116⟩
def resval7Tail136 : Box := ⟨-805122159496226582653700941249533146731029517073766530,84435396173784974379054421761401345438372370067052396⟩
def resval7Tail140 : Box := ⟨-817826304358965579105463542824141094331515942123255353,71731533521249136749340936445025782240510655465368804⟩
def resval7Tail144 : Box := ⟨-963252820198369406158597871930027121861363322588537579,56050003292460191176996296431036222787238442429900210⟩
def resval7Tail148 : Box := ⟨461206103107147035286629451619343463745067642927,147170755177419514856723459638896988500274068293⟩
def resval7Tail152 : Box := ⟨468412126803269453687919320108660298927608919709,139894092159537978047483200472294673895573372891⟩
def resval7Tail156 : Box := ⟨475803101272261001668375934269340005812390944135,132503116432717361104614620765271306894219767443⟩
def resval7Tail160 : Box := ⟨483310697624042988041083700475222230683921330437,124995520080534300444733581303294032843570530749⟩
def resval7Tail164 : Box := ⟨490936754748828683818482320621235223251858686420,117369462955747902643011284196577655550636855596⟩
def resval7Tail168 : Box := ⟨498683141813664811344483742505002786178502779077,109623075890911770473682697601408860541515659568⟩
def resval7Tail172 : Box := ⟨506551757479186913204597981390454121961266175780,101754460225389668519609734083753011711787895593⟩
def resval7Tail176 : Box := ⟨514544530364595214330582682426338074486682407572,93761687339981367388618471664182876483540733617⟩
def resval7Tail180 : Box := ⟨522663419520363791544594549450440016914206263352,85642798184212790174007225876163549124861147003⟩
def resval7Tail184 : Box := ⟨530910414908409193626358460004515007054220288883,77395802796167388092142428208925595744023658002⟩
def resval7Tail188 : Box := ⟨539287537889835544460402193346952252115579442370,69018679814741037258245586940097907088930642390⟩
def resval7Tail192 : Box := ⟨547796841720375672925830937128219383156997007632,60509375984200908794305921732692018851725037717⟩
def resval7Tail196 : Box := ⟨556440412053649703454561882048084033631208276109,51865805650926878288785780233908321710314225199⟩
def resval7Tail200 : Box := ⟨565220367452364458163897606151468916061200753409,43085850252212124470215183607449336132327924440⟩
def resval7Tail204 : Box := ⟨574138859907579074462431529703303603451757278204,34167357796997612887034625381242993814816574384⟩
def resval7Tail208 : Box := ⟨583198075366214328689394658631644492856011973011,25108142338410341103730215022838345562967235450⟩
def resval7Tail212 : Box := ⟨592400234407694790133460246649254915834292124630,15905983431639416733292272645894226513742566878⟩
def resval7Tail216 : Box := ⟨601754306013865086529272415616206073670203106019,6558389445533568989722247716098683610423404014⟩
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
def polyval7Tail5 : Box := ⟨21311488087946061885011231877039264950113006714980165331605,6500377753994119789745486603839380293655083269713447770574⟩
def polyval7Tail9 : Box := ⟨21647755418940001493497814591414078663160426550757604664588,6164108321049280850300666221655808508578622374480022758843⟩
def polyval7Tail13 : Box := ⟨21989330766145277739599468825299090483227109873256848135086,5822532973639603840959156074828332315542177001167669870549⟩
def polyval7Tail17 : Box := ⟨22336295758608186100549689263814688844654020464235875403315,5475567981176534455895047390876928381170823130662777570763⟩
def polyval7Tail21 : Box := ⟨22688735438194529310190164048383069337777985020148847325397,5123128301590190684254985140519236348315929763152892951092⟩
def polyval7Tail25 : Box := ⟨23046736188832641075079071349789439813664881880294256383789,4765127550952078912763836799497131327255244316287669380818⟩
def polyval7Tail29 : Box := ⟨23410385757484721907629269408895532838320723597964351042280,4401477982299998079994331465023109680545243993156077654486⟩
def polyval7Tail33 : Box := ⟨23779773275653703193824666914894317547839841932451675173662,4032090464131016793781109566437905260236600941807451350984⟩
def polyval7Tail37 : Box := ⟨24154989281229621585820355332588048006743379888724074967535,3656874458555098401782610280357643300606938533448054483674⟩
def polyval7Tail41 : Box := ⟨24536125740680703234699362344308188985329438693542058878620,3275737999104016752903714451423326263475204172379639146814⟩
def polyval7Tail45 : Box := ⟨24923276071594596446454623845172254431419002226783380422674,2888587668190123541153919191662452891448820096956148885678⟩
def polyval7Tail49 : Box := ⟨25316535165575277673644460070257988530086369165890830785427,2495328574209442314024502599958772636904073276029734433088⟩
def polyval7Tail53 : Box := ⟨25715999411501242938055895824313441940131765277598472069936,2095864328283477051030076579616632890742593848730229659117⟩
def polyval7Tail57 : Box := ⟨26121766719150685421674623865255230374048240068156608517467,1690097020634034659145985305414264089826986839947834797268⟩
def polyval7Tail61 : Box := ⟨26533936543199470577972221120468145326112815312896910169684,1277927196585269575541057255996850963022664892998052800679⟩
def polyval7Tail65 : Box := ⟨26952609907618778133015071622145772953036451988411887056773,859253832186127949977640051069359677133932431253627310969⟩
def polyval7Tail69 : Box := ⟨27377889608197859141883948341299842190153208836650837976793,433974303462135044519326160510348503335874002069632923031⟩
def polyval7Tail73 : Box := ⟨27906250000000000000000000000000000000000000000000000000000,2⟩
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
def pend : Box := ⟨1031618988636475245359743635774677927682539426293940390656831,3803058147538177564937073562256551940414807901971130905⟩
def zend : Box := ⟨1003805028336134497442558593750000000000000000000000000000000,2096111398076979003906250000000000000000000000000000002⟩
def betaquot : Box := ⟨428761050537347859221210506543022973920542586476685894426269,394793074092309403870833978150766225383956547303667920⟩
def crit : Box := ⟨166519868069241691968744990521020552157245079192213904995,9359499342491393376139779548599108503300864692873801273⟩
def subsonic : Box := ⟨404435009344741088599518122630392747353664636025333930336,4583857972012728273753436576976726936546816678611754087⟩
def pendTail4 : Box := ⟨27810212844235381049370901616779967074323022447429847911699,1614632275847828109988835913766799202444187030757439970⟩
def pendTail8 : Box := ⟨27810249227075841403115496824357879204680272513608271675533,1614511114324074881994536942335111108390203563439600655⟩
def pendTail12 : Box := ⟨27810249228685142904906594045065103835440491954170691247754,1614511098777373165920053106276958049872668913495636481⟩
def pendTail16 : Box := ⟨27810249228685953741175189161605180923767198027987905141382,1614511098764280913019171816398132104090339396515331509⟩
def pendTail20 : Box := ⟨27810249228685955738511966431869461788463925527925834103234,1614511098764231847638147570080947957718879222660024885⟩
def pendTail24 : Box := ⟨27810249228685955755951259240238255613526608388067670720620,1614511098764231200581313701332099100246644073441927502⟩
def pendTail28 : Box := ⟨27810249228685955756395115618395017117916764005547276864011,1614511098764231174780602903848082286218377778911727672⟩
def pendTail32 : Box := ⟨27810249228685955756423251608421328272880059382879318659755,1614511098764231171944146537953040640331775831349063274⟩
def pendTail36 : Box := ⟨27810249228685955756426741051244137589966122007806838629581,1614511098764231171128727872371888610478056438786785845⟩
def pendTail40 : Box := ⟨27810249228685955756426622649406259410282605849886549525402,1614511098764231170530708492835592389767315501418231860⟩
def pendTail44 : Box := ⟨27810249228685955756422361080875749776227991434851484548247,1614511098764231169413559183565542933842207491255863751⟩
def pendTail48 : Box := ⟨27810249228685955756385601440641039025489770916697420556200,1614511098764231163984814098923134251539568001829786989⟩
def pendTail52 : Box := ⟨27810249228685955755723134485317626226161354185500669073310,1614511098764231092024558952861193407368970138792516613⟩
def pendTail56 : Box := ⟨27810249228685955724007703532803113707332607808963892356314,1614511098764228465254884951913020260425655665048952365⟩
def pendTail60 : Box := ⟨27810249228685950836065979358119300971427883801625599180240,1614511098763933332285039466548808984599682951394504832⟩
def pendTail64 : Box := ⟨27810249228682780077652563243773019377670086160545249494004,1614511098621691857835159654139018450625814823885151383⟩
def pendTail68 : Box := ⟨27810249214416611076782889787117860744784060564974239837552,1614510629093435466817297084084822062501091804780324018⟩
def pendTail72 : Box := ⟨27808519801144520695650027767835336794460806105472312129601,1577691892334233594596807605881214955003608103743293848⟩
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
end SepticProfile.ExteriorCertificates.C30

end
end

end OAI
