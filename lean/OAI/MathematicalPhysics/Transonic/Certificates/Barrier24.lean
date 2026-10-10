import OAI.MathematicalPhysics.Transonic.Certificates.BarrierData24

namespace OAI

section
noncomputable section
namespace SepticProfile.ExteriorCertificates.C24
open SepticProfile.ExteriorJet SepticProfile.FixedInterval
def cell0 : Box := ⟨250000000000000000000000000000000000000000000000000000000000,250000000000000000000000000000000000000000000000000000000002⟩
def resval0 : Box := ⟨116764189684591591344200246776868314139178491866916220969,312112093411682481679887176693278315786977623835270851⟩
def polyval0 : Box := ⟨3825742123206089523977803623327454319536434704478992341107,14874232862779865062676911650265155686318366755896430004⟩
theorem cell0_lo : Holds Q cell0 (0/1:ℝ) := by norm_num [Holds,Q,cell0]
theorem cell0_hi : Holds Q cell0 (1/2:ℝ) := by norm_num [Holds,Q,cell0]
def resval0Tail4 : Box := ⟨61234539024349753212276363691725581458739975074811,1791649568718558327760915525629672862698919948455⟩
def resval0Tail8 : Box := ⟨7560473714693201893218187870345717220096347928,402344489414258814688637445102671817115139218⟩
def resval0Tail12 : Box := ⟨7018082885313025087478012520556996015217278,567383038778237455447139575131001079812100⟩
def resval0Tail16 : Box := ⟨28671813535129654197112024427356520563633,27682578431446518591605641829776621039726⟩
def resval0Tail20 : Box := ⟨398330872791719695801986619046187029729,390291137152453107273717231320127220901740⟩
def resval0Tail24 : Box := ⟨16149865993163373347403439343695502125,6243646561766241004923078460508774895787073⟩
def resval0Tail28 : Box := ⟨1738747918503632582307135911155730864,99898288777269974234010494532491011604593078⟩
def resval0Tail32 : Box := ⟨467570785080656860596333810753162251,1598372612098664272692447534653174809172041853⟩
def resval0Tail36 : Box := ⟨-252990964488763814341077680927501127,25573961790336057472385301122939123660577170778⟩
def resval0Tail40 : Box := ⟨-143471369848349408627790159615254349028,409183388509267166014869481338348526535179646242⟩
def resval0Tail44 : Box := ⟨-36853081837035081892822769475052095244640,6546934181594670147490791593856429328514812205143⟩
def resval0Tail48 : Box := ⟨-9434865459622728876717212285099245113211875,104750938060302535137031816883525903697208860552245⟩
def resval0Tail52 : Box := ⟨-2415330005457570168026624677366209902585587832,1676012744592433068884642268432492190048729043933508⟩
def resval0Tail56 : Box := ⟨-618324573237310523066115131102185659180120660833,26815624234155616331790119279341830172314386440454200⟩
def resval0Tail60 : Box := ⟨-158291087776791988675113851841467242049642457761978,428901589841995127713105350843450887152415362304199358⟩
def resval0Tail64 : Box := ⟨-40522496949447674706631512726294979060413297871155577,6824435581976909652699164844587629575365826562000049652⟩
def resval0Tail68 : Box := ⟨-10373253645665477536750121120433447560022485064822033090,99465781634217075687058605266229489933884895889498156087⟩
def resval0Tail72 : Box := ⟨815973235352475223372562537091802451097966317940456314373,2495834833459098260200289274164840066334943311107478739⟩
def resval0Tail76 : Box := ⟨-28485452287427988510317024509924700623958758179527,618085162313556458490913835619821110271820181614⟩
def resval0Tail80 : Box := ⟨-1571424593294867172996967652268550013238274833,71811916574695207136084185797181436011888546⟩
def resval0Tail84 : Box := ⟨-907109603617785123026003766631628661830977,65281198783417987042260111612912366999050⟩
def resval0Tail88 : Box := ⟨-2560941377220225557089864786988474732693,434025404988234438358138903939510456042⟩
def resval0Tail92 : Box := ⟨-26019241637633192412670579240389270946,2681026157770046841601516212764469761512⟩
def resval0Tail96 : Box := ⟨-798606095300416458355127785491657006,42836031909949833935097325188649502401555⟩
def resval0Tail100 : Box := ⟨-66512884225347037191335663594267237,685373964391057627945842760973651262207755⟩
def resval0Tail104 : Box := ⟨-14090493306666006456782332129528529,10965983138587299792183395965808414586424450⟩
def resval0Tail108 : Box := ⟨-9228287945521086905959185433068890,175455730130528024803579383214934828060221731⟩
def resval0Tail112 : Box := ⟨-498859959049953499718584354736670416,2807291681637891013801060130427837296892283714⟩
def resval0Tail116 : Box := ⟨-125377953889847460181151684995395621288,44916666788697000754588447961103349572867574424⟩
def resval0Tail120 : Box := ⟨-32089703893969808638662766007524793054867,718666638535233529567008576462025677608239424202⟩
def resval0Tail124 : Box := ⟨-8214912060627568268621800810397125647512552,11498658515086692558673970779757668996845382913992⟩
def resval0Tail128 : Box := ⟨-2103016585477519210951462514228533382973692711,183976564663506296095493582542467709996941513062965⟩
def resval0Tail132 : Box := ⟨-538372236295280624837000994451833342030002370481,2943120310680043917966021192367135815010045732538592⟩
def resval0Tail136 : Box := ⟨-137823346305712837198390826342958499856033991294024,46960715619845951031918045966916031359135673019709944⟩
def resval0Tail140 : Box := ⟨-35283455784658504308247303211614116176278416089183001,718293543236765931012755405839033943896260564891732856⟩
def resval0Tail144 : Box := ⟨-9425036487074963728012046009542205442124462102432205822,2831370288416557627724504343678783014735361633967987737⟩
def resval0Tail148 : Box := ⟨66255135853201247800242358617762909951630431,1184761820224178605242906686779836935827896⟩
def resval0Tail152 : Box := ⟨1205704718683660360929493068438328947048,49138145776710143151568335408764971879⟩
def resval0Tail156 : Box := ⟨390994774962056359530773520113012220,25635117400837565665296406937449317⟩
def resval0Tail160 : Box := ⟨698888641593247746982427771560387,68462991354407120210177292598731⟩
def resval0Tail164 : Box := ⟨4760331909711092886263931085462,31352992766576727007099207466342⟩
def resval0Tail168 : Box := ⟨101108287093577300974478274460,491560164796889303289038592208714⟩
def resval0Tail172 : Box := ⟨5925867647797302694941127363,7864669893502845428369305398975390⟩
def resval0Tail176 : Box := ⟨888672877663579074810417896,125834694919437098147292204087373570⟩
def resval0Tail180 : Box := ⟨333483746041267330786284351,2013355113880873466452915012326987596⟩
def resval0Tail184 : Box := ⟨2116074141022889895978630364,32213681818652894146926768990616060963⟩
def resval0Tail188 : Box := ⟨468648545525670153954604128879,515418908659902738749561955770921614074⟩
def resval0Tail192 : Box := ⟨119820909190398215446425512557849,8246702426229197191316007851889477402547⟩
def resval0Tail196 : Box := ⟨30673379275751106675906677413669505,131947210063403630802072470006632480074305⟩
def resval0Tail200 : Box := ⟨7852375699799843390535187842449382694,2111147999413196403333987892643357118250908⟩
def resval0Tail204 : Box := ⟨2010207960017494302718565276041694310776,33776483420757369897549954089838490663364916⟩
def resval0Tail208 : Box := ⟨514613284387998936012036530887931669203207,539941284828803963761506857592287304999507191⟩
def resval0Tail212 : Box := ⟨131741275932847113378178458133959576365018506,8515553258524486316118950754815029011299527194⟩
def resval0Tail216 : Box := ⟨33741984693339529134917999549185106134024693519,104623179985159695924103978600046037242817669940⟩
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
def polyval0Tail5 : Box := ⟨2152339490876496651603549781060382613452157099134316,53065296896676382747148822473901816600126370860877⟩
def polyval0Tail9 : Box := ⟨212999907849806990611726127292442866882942039547,10379051320396722160688249399853894176624856996⟩
def polyval0Tail13 : Box := ⟨171076655351926469389020349782458512854265730,12931012157618576831196609977595558828286341⟩
def polyval0Tail17 : Box := ⟨612451547175927341025173935630228443315016,446405769197931773637432170661241152622550⟩
def polyval0Tail21 : Box := ⟨7476478443779518725848969942319560951961,6081135961268826391177437182333316993713817⟩
def polyval0Tail25 : Box := ⟨266055663581557901618961164041690211229,97280191425686845097023099455679958764049649⟩
def polyval0Tail29 : Box := ⟨25052060180232495726625192024514497826,1556482185991312314412636632367252874104747386⟩
def polyval0Tail33 : Box := ⟨5908421472667076604393463614712132335,24903714862467648465691799970174246344728128408⟩
def polyval0Tail37 : Box := ⟨9111453032043673255402198048329830953,398459437760487743530432410855408172705992721699⟩
def polyval0Tail41 : Box := ⟨1480990669285185781402644974565267735791,6375351002787580690050754202155172816622252832302⟩
def polyval0Tail45 : Box := ⟨377982917048359204769121514178465504394121,102005615690259234160562341240712273837671411838164⟩
def polyval0Tail49 : Box := ⟨96759901075945912585524374081627523760088287,1632089760331840264803661228499767100027630413989148⟩
def polyval0Tail53 : Box := ⟨24770505501826343901544099248751656389967257474,26113412942962319220460713326617848170132890157154829⟩
def polyval0Tail57 : Box := ⟨6341248881678080361646401632699659197211752569596,417808662166675075080353818166942169969719920870951933⟩
def polyval0Tail61 : Box := ⟨1623359709280674471973426124204090873484656324397756,6683416694962240627975857954887367178719325432874565880⟩
def polyval0Tail65 : Box := ⟨415580121124185902854714346353511155173355421837457732,106545060779629688985674201462154505093476052228262673850⟩
def polyval0Tail69 : Box := ⟨106388944301413982662668534344399482046120130917513854225,1604981551013609641067768000554331784389905453046506656557⟩
def polyval0Tail73 : Box := ⟨27531250000000000000000000000000000000000000000000000000000,2⟩
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
def resval1 : Box := ⟨116531083609798479984922856359156787258063427353656482759,232624080092390217321982978231519159212679858272038158⟩
def polyval1 : Box := ⟨3807372204291108023541902447132715997079677171784957398484,8613947591122354815594294156976919064591103696096981802⟩
theorem cell1_lo : Holds Q cell1 (1/2:ℝ) := by norm_num [Holds,Q,cell1]
theorem cell1_hi : Holds Q cell1 (3/4:ℝ) := by norm_num [Holds,Q,cell1]
def resval1Tail4 : Box := ⟨59449430652301235704709804912384489524872181046753,3144065130479397438200627478098106260717272823180⟩
def resval1Tail8 : Box := ⟨7127317330987937351395919291430605654217888323,6354078916848808573454649406517673009314068473317⟩
def resval1Tail12 : Box := ⟨-326005538608338015813367056364628620000967299,20081139013660979922035793162324407456645932983941⟩
def resval1Tail16 : Box := ⟨-2179136490272669300059160631158386550257676051,63465186751177826538947539055296666756843565305302⟩
def resval1Tail20 : Box := ⟨-14281358422982152802267220132306590366417173074,200573936832528373624102477007584881538208461883023⟩
def resval1Tail24 : Box := ⟨-93594312842880429623401511437198971666898210407,633864231081791728977487944407280496827391057609306⟩
def resval1Tail28 : Box := ⟨-613379688736008455793613697036771757866527763116,2003006414151134805330818457636403733692150981974350⟩
def resval1Tail32 : Box := ⟨-4019845128109347003113802647202541404725139887400,6328408145279387211519612504597434924983941422467347⟩
def resval1Tail36 : Box := ⟨-26344457031579635004689276561632829349452537851136,19987255117589644820593356287557070195671568686968552⟩
def resval1Tail40 : Box := ⟨-172651033602161489030227188562752015426750680365709,63080206881250103697346364115994442010213848952357364⟩
def resval1Tail44 : Box := ⟨-1131485813815126553965334967314513604810025269643371,198778781176335241935655448782920343731012364961857697⟩
def resval1Tail48 : Box := ⟨-7415305429418809319932531403553565874261028168904307,624399859378957654027063396167801605287208013589720903⟩
def resval1Tail52 : Box := ⟨-48596945662238855467139540982769288518492587267696615,1948250982621024722481247033537026727812862902402293041⟩
def resval1Tail56 : Box := ⟨-318484943092023739613212550864990607115210915803098328,5992540608025426019278183396239779870392000247568105106⟩
def resval1Tail60 : Box := ⟨-2087222923040020171152919648839219475462570934003722883,17858734374311424883409586032466720890736772120462147766⟩
def resval1Tail64 : Box := ⟨-13678824135827750201112650005696318673659375184172594750,49360250767878157402286476729198836508320799675166496711⟩
def resval1Tail68 : Box := ⟨-89645310221413424949678723351596854166420479612474225355,109589093993580921058593020924604505198668006645327415806⟩
def resval1Tail72 : Box := ⟨818938578275847985996850503411562733237828566980018009090,1507138515056769907077726796556388873671265449781756056⟩
def resval1Tail76 : Box := ⟨-27847007671668383730618736736855916099025312713349,407381611820382416393949030875401065436798957721⟩
def resval1Tail80 : Box := ⟨-1501587798957432175516492884923829778192709334,65382360796355349006974116756755286495308243294⟩
def resval1Tail84 : Box := ⟨-3687946774984650633624165818348628209938097,206499492568918523416969578584458154292931062261⟩
def resval1Tail88 : Box := ⟨-18622402461432552374598400288663475345187304,652630742362826262254630934803556931822588384322⟩
def resval1Tail92 : Box := ⟨-122028519092946618724633143339767195724470038,2062572252808606043519051123433571468806475353809⟩
def resval1Tail96 : Box := ⟨-799725952296082277304346405694639768618741805,6518332817431145644604157512495167807936971367543⟩
def resval1Tail100 : Box := ⟨-5241083996518328835668917128264879566655296058,20598437077805815466846794524991824249176504358375⟩
def resval1Tail104 : Box := ⟨-34347968079230387929417418827641023711266251305,65083449679098349093286987756190891143669617240500⟩
def resval1Tail108 : Box := ⟨-225102843603975595702214269854872659759359992421,205579294658586861107565650732563507371295997840547⟩
def resval1Tail112 : Box := ⟨-1475233995842984129159802573937736058836675822802,648968293912315696694632270822319087867461668490429⟩
def resval1Tail116 : Box := ⟨-9668093515156556052647638543562310055469527493740,2046054661355073342143102961960760428855367184827377⟩
def resval1Tail120 : Box := ⟨-63360817660930023302160674672674113048762316999770,6433738259459796618975974642089118668653395397514701⟩
def resval1Tail124 : Box := ⟨-415241454622672999977654070811899189445689876353034,20118800073067526622957265402288804559316611116611483⟩
def resval1Tail128 : Box := ⟨-2721326397015306150854063980095811933918334568687057,62176385097906935825706224170486240571525499607369591⟩
def resval1Tail132 : Box := ⟨-17834484675514892155375595790172259418598199049882060,187274331901058377333660182916818223975734708482887959⟩
def resval1Tail136 : Box := ⟨-116880078805364738586884328378232924284558251017838642,531365069910388884357550431675103436194897954180575968⟩
def resval1Tail140 : Box := ⟨-765985607837763506079019799618073802942443386201049095,1282789446845979944760599918574388234433457124582544033⟩
def resval1Tail144 : Box := ⟨-5184134782484376661512269458411901555515998211128188221,1425606942540603291449237461405064799077157180192992844⟩
def resval1Tail148 : Box := ⟨65267873605435231946246587811473098901383825,836964664413792618752379080872785355308564⟩
def resval1Tail152 : Box := ⟨1159385779957625384669494611536763986247,3198036394162188849037743914142015569212⟩
def resval1Tail156 : Box := ⟨490187352508757352526187717385410308,10007424799914268049549269419186086412659⟩
def resval1Tail160 : Box := ⟨803672721633218115132320325320691986,31627990175936950807583940188251631313429⟩
def resval1Tail164 : Box := ⟨5262748830498094614775613237064544106,99957342950338178268091880289665728587389⟩
def resval1Tail168 : Box := ⟨34489922914008736273443452167146439961,315896708322819448457771854662095511805484⟩
def resval1Tail172 : Box := ⟨226033158237818280239969901585881459827,998272568704546784924807641587381588683977⟩
def resval1Tail176 : Box := ⟨1481330905795316393977446403871435201684,3154267336709903664070273299405213196141359⟩
def resval1Tail180 : Box := ⟨9708050224215686930798342779845496762152,9964016133845151807788823823964368556263184⟩
def resval1Tail184 : Box := ⟨63622677949418459039376008280238384659107,31458271039603149750626895114883488369069772⟩
def resval1Tail188 : Box := ⟨416957582209307827511025997253874843013799,99207792932524734537585414131030544230533872⟩
def resval1Tail192 : Box := ⟨2732573210766919081219741920422560475926496,312130835823454252086405579447852732926592623⟩
def resval1Tail196 : Box := ⟨17908191794082094661383129445666039737378632,977215668857283596630309145523974883470344644⟩
def resval1Tail200 : Box := ⟨117363125741697237094650510212036819375887058,3027719693107064157245934928918151614842913282⟩
def resval1Tail204 : Box := ⟨769150980860894823169402187970681814972707768,9170863854019228953836969347624271382809460101⟩
def resval1Tail208 : Box := ⟨5040707868221172137084406329295568843225965981,26374647659342757113930082871148360790795219848⟩
def resval1Tail212 : Box := ⟨33034783230984533120144593985552519078019442011,66253254110310033889698269664720001841530954600⟩
def resval1Tail216 : Box := ⟨216503918909849670579499123754101237278277430808,97301122541884746843805644504489070044822355972⟩
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
def polyval1Tail5 : Box := ⟨2094039818967707254523186770296182199375762982448543,119162165740052776591013938296493780504012981536167⟩
def polyval1Tail9 : Box := ⟨204966404758915908886683131277219891381257937888,276795972980385451911517514460493295101494423925053⟩
def polyval1Tail13 : Box := ⟨15671603760977759530397388914811341041154686232,874787431456406202670591400659104775674963266954776⟩
def polyval1Tail17 : Box := ⟨101663898250534636484038106196877092459496787242,2764707644480541013109017886256454114084649778078240⟩
def polyval1Tail21 : Box := ⟨666260891336709435787876686009288811334758491588,8737496489778712298131376879446197877535041282762144⟩
def polyval1Tail25 : Box := ⟨4366407334451287360492468645027844233140295563571,27612543026861464194053350319773815034255543598972914⟩
def polyval1Tail29 : Box := ⟨28615687105586167154441811416770591111630934298472,87254456104920309552593169122830449844484159678674141⟩
def polyval1Tail33 : Box := ⟨187535767015037872157477669123245613555064053239880,275670073847288965533193546050029559268387474089352160⟩
def polyval1Tail37 : Box := ⟨1229034402709723829853187635112764663957745381320242,870617237958547360332824600116314004045674619160025311⟩
def polyval1Tail41 : Box := ⟨8054599861598432530453817217976495641032697576612066,2747410162169041235199275638441354046089250787747474099⟩
def polyval1Tail45 : Box := ⟨52786625652971475957713923801424382744194569483774382,8655842745703124261372186269000506403159001343538237613⟩
def polyval1Tail49 : Box := ⟨345942429879313879048922060121909462879191680936747933,27177626941320198605535465373482461974069761740110135404⟩
def polyval1Tail53 : Box := ⟨2267168308457072650200486086959767832466278855102355786,84720902790642622236445509815489222965793112238700025840⟩
def polyval1Tail57 : Box := ⟨14858114226304368708910180485963580985333700322473718314,260067147518998451509457012905920850288499736862974849783⟩
def polyval1Tail61 : Box := ⟨97374137393531084152623807262754522545900792150657574770,771525455283000171765825083789371849999567725722243726144⟩
def polyval1Tail65 : Box := ⟨638151146845820466806649460050883388677809110865189799521,2108000652249900873353664553025125703061828143100993417176⟩
def polyval1Tail69 : Box := ⟨4182187562806463519527012840160759011083951624103709305369,4497008415875080135089933845493597495504088398805909574398⟩
def polyval1Tail73 : Box := ⟨27531250000000000000000000000000000000000000000000000000000,2⟩
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
def resval2 : Box := ⟨116416334434744698954001428211100656919066641474545233491,213367514754818689713284676457489553542381694528449831⟩
def polyval2 : Box := ⟨3798295977469721788204107349901272635685074020044671939802,7315507780671564860792428715738587768652053859044854648⟩
theorem cell2_lo : Holds Q cell2 (3/4:ℝ) := by norm_num [Holds,Q,cell2]
theorem cell2_hi : Holds Q cell2 (7/8:ℝ) := by norm_num [Holds,Q,cell2]
def resval2Tail4 : Box := ⟨-135950425971614439735980940380360220502213578147130,34574306513203877176182716877817588752805718624236168⟩
def resval2Tail8 : Box := ⟨-446412226249745006203830165783141088597455002377812,58866426590948093663457831502097523301469333945857369⟩
def resval2Tail12 : Box := ⟨-1024352452028248886942962720418179107222746744090451,100160743679435728359952671735691833978468046625382706⟩
def resval2Tail16 : Box := ⟨-2350476618714460196543569669709892974310868422251964,170266830244803628183582829317642922682122953350688293⟩
def resval2Tail20 : Box := ⟨-5393397839210214454320279592803018176734004155804146,289084106914253387272514841659017493725968929905697581⟩
def resval2Tail24 : Box := ⟨-12375677349900280461479468809826998491574157648201210,489989945086662882481611445988582278709599742029880489⟩
def resval2Tail28 : Box := ⟨-28397198655616595526133481708235286199187645333571210,828616374647241697107217664860301650498974682075119130⟩
def resval2Tail32 : Box := ⟨-65160141840078753593211461481496546975458436560809433,1396867178546638268742112303729391026909722267071713540⟩
def resval2Tail36 : Box := ⟨-149516300396743853917036796932103471246587420874836115,2344637762203836289420145299965620428743133227780046056⟩
def resval2Tail40 : Box := ⟨-343079733300689934354264970115051410581049188053438667,3911836984905047786184288780954201517625256367609877916⟩
def resval2Tail44 : Box := ⟨-787229907972200396521111636087159855008034247091538725,6471470166068075197540042186056267907044870150247912180⟩
def resval2Tail48 : Box := ⟨-1806375800877634709782012393274455638537833112614203185,10576646066373081162216500740367677668752729561632378492⟩
def resval2Tail52 : Box := ⟨-4144905447509424071680756663235922625338804698602585027,16979983169008248367603134636071145251904120745332098762⟩
def resval2Tail56 : Box := ⟨-9510889794054024489849903102897871417981101491735134534,26527237558405922141691165353442093331840081181670175184⟩
def resval2Tail60 : Box := ⟨-21823664211440026414419065230821504561661399589771692933,39655790030817460494840591959118411927649235699898942260⟩
def resval2Tail64 : Box := ⟨-50076525943481356013206308475075981367782859514499203472,54804708772221054165108426253561737500619176871284184710⟩
def resval2Tail68 : Box := ⟨-114905290641522713367985482803794267722141284441519086065,64017289770197354907869254737623093178029219266977392173⟩
def resval2Tail72 : Box := ⟨820419484948352175287391006515484025506763062991096243714,1013232862539153326529476438482251268223473708988168103⟩
def resval2Tail76 : Box := ⟨-29702735492090580964293979022031446709110007231685,414781698179268027694017600248635068706085000110469⟩
def resval2Tail80 : Box := ⟨-4961755585856972658085377661966356155943550406052,706229252730721315968221660867392661975429758478293⟩
def resval2Tail84 : Box := ⟨-11381863153563425972164858543546833274374629366734,1201876082536613324491498294022702595270599929925868⟩
def resval2Tail88 : Box := ⟨-26116793178694336670187081431873604515219837880692,2043647697520188044091298938159612947031350712153674⟩
def resval2Tail92 : Box := ⟨-59927529064571491237526176491472966880064423121925,3470999315539099508131267125597991639974887463591620⟩
def resval2Tail96 : Box := ⟨-137509560056522711062567297766632417140681799132006,5886095752520131478891612925053286227986413856351223⟩
def resval2Tail100 : Box := ⟨-315529096595505469666183071834806914639435904745030,9960475634897194639278565500961112773516699944361102⟩
def resval2Tail104 : Box := ⟨-724012285090964721035147101214333911202199009144578,16806398118988210393087807734086128186628268643988788⟩
def resval2Tail108 : Box := ⟨-1661316799682135199240492671659905689722856806332867,28244789412357973602505846750882334344298486844933327⟩
def resval2Tail112 : Box := ⟨-3812053421937901763122053694083621508671268578746340,47206443472904366309221346851117058802249325040194931⟩
def resval2Tail116 : Box := ⟨-8747128358955300236470028744694747183474076720687216,78288174965190443217332005017361059247926793642177862⟩
def resval2Tail120 : Box := ⟨-20071139110412610161714248905120337482864218838317499,128407245902374130932618639996828768255488806450322673⟩
def resval2Tail124 : Box := ⟨-46055186188858964437696974485808849075812483063641310,207242383578893845258253660214516843502697625921319493⟩
def resval2Tail128 : Box := ⟨-105678116385037817922356868282510614964309234518164425,326436354988854643602025839368091759818022682064320607⟩
def resval2Tail132 : Box := ⟨-242488744631164313576050943701701483873703761323312635,494679466425697831554468471806514113626514097637643116⟩
def resval2Tail136 : Box := ⟨-556414074051216161649745838936770275555216334096994804,701162349335278826696973817380405823529140166376283787⟩
def resval2Tail140 : Box := ⟨-1276746614260154298958933693217224762522496620222289821,868623473625941757697462011385277453322308676718909875⟩
def resval2Tail144 : Box := ⟨-3056818020018456278466800019038501853784401844225692911,718916246630081134289310923287381314404560410083132157⟩
def resval2Tail148 : Box := ⟨65061111138452064383557163910289586116990235,49122679422019321715364013578242119232400486⟩
def resval2Tail152 : Box := ⟨623581981346310971238695990161697908182348,82583088980412806834697488782311049307050175⟩
def resval2Tail156 : Box := ⟨1428259537582000429780019902087787940959383,140516694923753811812769776695769164470594957⟩
def resval2Tail160 : Box := ⟨3277279985687343734633919990759076368458053,238874545086587392836382765746577979025196329⟩
def resval2Tail164 : Box := ⟨7520038552631706501296454852762194829701106,405580284435076058765918651040977465420997561⟩
def resval2Tail168 : Box := ⟨17255461874059334362423653943328032226021130,687475451477725038230186435177358377400621584⟩
def resval2Tail172 : Box := ⟨39594340162401430427187038575780899063408007,1162645485364007753949048124035302815992695306⟩
def resval2Tail176 : Box := ⟨90853075063308002495298837181393194399459615,1960114990474456262716718740685852437083079002⟩
def resval2Tail180 : Box := ⟨208471241460346388942391110672473092200287594,3290389731651974488982518224138854834715230853⟩
def resval2Tail184 : Box := ⟨478357595334381181892848973133028677725646881,5490544756130869261815573315416298703041996888⟩
def resval2Tail188 : Box := ⟨1097638155801057565733327667597947581333440987,9085045739076770763018171305389741573275226561⟩
def resval2Tail192 : Box := ⟨2518637799046885916353322574816157669485890479,14852571377720954498727114798596973503457731471⟩
def resval2Tail196 : Box := ⟨5779260067866556352266448035258776894588835082,23855255878839430478166302228668920214129541387⟩
def resval2Tail200 : Box := ⟨13261075865960668732829335796353748991553512829,37294100026462373193864498101838951172990339812⟩
def resval2Tail204 : Box := ⟨30428831901950247902756756230370662862638342308,55816066246889807260500414837331551373189481963⟩
def resval2Tail208 : Box := ⟨69821922465159127518974983829404411391031719748,77308066213615417168484369785603190347371975929⟩
def resval2Tail212 : Box := ⟨160213210811908205497169378980898220966052857572,90784054443039426442200721446094535713144148529⟩
def resval2Tail216 : Box := ⟨367630436209422540760976286858559460814712344296,60564844288702158564527490767866275525634004261⟩
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
def polyval2Tail5 : Box := ⟨22311032267116749999705973503045210266393073051404183,3105873118429088029007873755139721184833794505906214491⟩
def polyval2Tail9 : Box := ⟨46453747933718472851307438849874085385590381058179286,5286563341942878659863626836728485418676631205471436349⟩
def polyval2Tail13 : Box := ⟨106592201448093252093768744267931947820656893739659309,8991299171922372713618347052245912263459293190131415576⟩
def polyval2Tail17 : Box := ⟨244586201605301754578146986304873136756394963695904470,15276014824922509562510602103592940018134809881773269919⟩
def polyval2Tail21 : Box := ⟨561226893609133333860083235383130475080018327084129929,25916233249937610380681335261794758764934524708073635678⟩
def polyval2Tail25 : Box := ⟨1287789842777485370055901363348184415876445627511990892,43881588228012783987521590686027061001631901494746015360⟩
def polyval2Tail29 : Box := ⟨2954959389946614887536371706989004079311127789134751219,74102005448852611448599720156569353518942654245980913049⟩
def polyval2Tail33 : Box := ⟨6780442511800754600140398035038732505253104607880744489,124675337571381932197001971212898586634529665465869300518⟩
def polyval2Tail37 : Box := ⟨15558386626986949100494650160784160491850481164400502719,208699370649446322497680252455584256027221811097290613277⟩
def polyval2Tail41 : Box := ⟨35700235495473432169156644504296090788925752367025628915,346873597825755505965767759484233954044334948652673106093⟩
def polyval2Tail45 : Box := ⟨81917672120421093473885156374772829015808581555659283151,570736397552112738515310319544175967015679996345987780289⟩
def polyval2Tail49 : Box := ⟨187968087955040677264822588577309264825534723971263538056,925430941357203627579913304916559701963488224591270800079⟩
def polyval2Tail53 : Box := ⟨431311109982897862930422888981306811133072153921141714611,1468098479381097420436842700860040861189132651186966001743⟩
def polyval2Tail57 : Box := ⟨989685406807856757130288464413718474729916345463591597762,2250623496996776671469331241918379064757202744595595352005⟩
def polyval2Tail61 : Box := ⟨2270929688055748889227539297027276922164691945555611334499,3256894247797570057094282328702872732201536530285426572254⟩
def polyval2Tail65 : Box := ⟨5210869648715576270121449251571817216887452472938364224907,4219353941994969349221925902056083102052816226574114435093⟩
def polyval2Tail69 : Box := ⟨11956848778558157797360308323986294457402986857440603086406,4130696486343617998321992707822097833391735391849815296740⟩
def polyval2Tail73 : Box := ⟨27531250000000000000000000000000000000000000000000000000000,2⟩
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
def resval3 : Box := ⟨116233022564364283965027142785136159988645062443469265685,1724801495359014612991430819895693281459530750341104770⟩
def polyval3 : Box := ⟨3816695315715948905531908620584007167966155483655410040854,242745589988998442210436753110991826426061053489941546874⟩
theorem cell3_lo : Holds Q cell3 (7/8:ℝ) := by norm_num [Holds,Q,cell3]
theorem cell3_hi : Holds Q cell3 (15/16:ℝ) := by norm_num [Holds,Q,cell3]
def resval3Tail4 : Box := ⟨-187517559735782285039021612055831692858488370927866319,1986009437457260209761002851211823937572628932106248941⟩
def resval3Tail8 : Box := ⟨-278089504720408197742603743048084675108202074700991315,2535698894301357209879555987748635921414025125241283093⟩
def resval3Tail12 : Box := ⟨-412280250354907056757102751712934597636243726330071899,3230276529156402495928463714836958345466284133364793377⟩
def resval3Tail16 : Box := ⟨-611224076148807416773651238827790566499860330398907083,4104205081430361597167106773700211782520085856520825412⟩
def resval3Tail20 : Box := ⟨-906167275625723055080079955467748867302530749322320668,5198136235902374295244299808832568953502293363060377188⟩
def resval3Tail24 : Box := ⟨-1343433878764619022052716783480514953435407536403238585,6558820638400919886703036272483540952888312426824545615⟩
def resval3Tail28 : Box := ⟨-1991701350466772284006590809576976758940304290162699828,8238069553967020478715580840635447061312139187670936147⟩
def resval3Tail32 : Box := ⟨-2952787131659193751251032276857157436685986486175981527,10290042813881014496759920418372045135949547237234340554⟩
def resval3Tail36 : Box := ⟨-4377640173236197136795989466752317182521159441964976665,12765710015621542868127353580317069278718719732581778638⟩
def resval3Tail40 : Box := ⟨-6490049106778378959579965376450933226103073170790029159,15702673816223711884017484172911737283646868190535864976⟩
def resval3Tail44 : Box := ⟨-9621790677523142139335496578908148580405961150157999668,19107538497427278117075322007704846060545388022764736651⟩
def resval3Tail48 : Box := ⟨-14264738882388338278152919359001602250909824583735397787,22926477252121305996646191842459748325003328384880149599⟩
def resval3Tail52 : Box := ⟨-21148119118623622042417003403497614736064003219119942011,26997333535030186023164566149743230835668912514467940338⟩
def resval3Tail56 : Box := ⟨-31353040945437342083010414098373455918949156875027806360,30973090118461025814510353786281530275430995033582320644⟩
def resval3Tail60 : Box := ⟨-46482298071627369700797354577415411473439167448269717129,34201263911648292964466431607616061886659204152094942588⟩
def resval3Tail64 : Box := ⟨-68912104490631544155186997860544057327367418169581588554,35535854376769027549061195786343547161582195418455467750⟩
def resval3Tail68 : Box := ⟨-102165140313131472532070591272841326019716175227221588149,33046575177657161914312644312308758876538224974095556788⟩
def resval3Tail72 : Box := ⟨821157940866813891722661518834355847171409746701059012930,785813648113619023870799822621218269551343645477460559⟩
def resval3Tail76 : Box := ⟨-2352033992682671501389893809976237858088612678317945,25588110499773156567329488784175741388600638604838430⟩
def resval3Tail80 : Box := ⟨-3446389397141643358405493562656884345284293658645852,32687598911831933272326384072997874148186267226921129⟩
def resval3Tail84 : Box := ⟨-5109425653514236746048385654034023513956702152715300,41667403221807898129328643637133063964257397171725173⟩
def resval3Tail88 : Box := ⟨-7574954103411318136807440433788296566987818983793146,52979441098951322584149261795463912550877873386961536⟩
def resval3Tail92 : Box := ⟨-11230211293582535087672472849277854899273870524671172,67159770809763495842926220455526324110304687698060081⟩
def resval3Tail96 : Box := ⟨-16649295028962432836140154723528949751810432862425724,84829536914245153869036728494462086898687569467114371⟩
def resval3Tail100 : Box := ⟨-24683331213887141539722582643062827763443050294467067,106684900494360806351382258964462848278598314774130965⟩
def resval3Tail104 : Box := ⟨-36594152410333266809658490711958809351965446178460869,133467051209059079066996723034508268508861752523226458⟩
def resval3Tail108 : Box := ⟨-54252482334203259484208937824133376021774024560672735,165898254266300380592530546404258684774354984438374217⟩
def resval3Tail112 : Box := ⟨-80431753314551807578442658876530139713405830817240162,204561800736818198465400139514630430102516641348579223⟩
def resval3Tail116 : Box := ⟨-119243703936002064510559595294088698047129662634931752,249691358944207016307053136740648667624415839723183512⟩
def resval3Tail120 : Box := ⟨-176784172200861186521684632427911389217999545495514337,300816386434543896432010802882331606135145541701859668⟩
def resval3Tail124 : Box := ⟨-262090513034692323211781616743226483436794652584957111,356181688658737950596953510173120125374995185678768309⟩
def resval3Tail128 : Box := ⟨-388561012943746022947486866464250983532782872202013134,411816014417847109869142845387761730380601694714170036⟩
def resval3Tail132 : Box := ⟨-576059236298614996797064297851835734179024590621160731,460059457334384920304175329614546521857013427875556770⟩
def resval3Tail136 : Box := ⟨-854033813689002593606796102478331029676497849346299750,487261489168633776295772376676573477117568746944070048⟩
def resval3Tail140 : Box := ⟨-1266143899848562458918512951666272565977260699640870411,470214418635585647734006009194263249893153453756511070⟩
def resval3Tail144 : Box := ⟨-1991441742614722990390463644053070820581925042380759444,364617649955636326857130126200413192030330344143220760⟩
def resval3Tail148 : Box := ⟨631947988756500421226156866212575145763277724,5543404063901398121292564651666744830919080488⟩
def resval3Tail152 : Box := ⟨841187499968184280651118566018357938445058111,7068941117626360315735778871517080486840899966⟩
def resval3Tail156 : Box := ⟨1247096758296782351309026068597628215292042859,8992865997564730481427042964613929138004282588⟩
def resval3Tail160 : Box := ⟨1848877221442545767885860424898291759677853661,11407146465367452727464202079539415236772602419⟩
def resval3Tail164 : Box := ⟨2741043915149293555186051165772905840400165237,14419386076727047601458498627760632138846298188⟩
def resval3Tail168 : Box := ⟨4063721299415057882986270112698741483516499027,18151112082266080510157553295304177125468798605⟩
def resval3Tail172 : Box := ⟨6024650210108066883999071216732593637599793668,22733301799805119890482178644384400365246762715⟩
def resval3Tail176 : Box := ⟨8931815811133448143961001358924616228149355932,28296453678677329301371658406660141071703616131⟩
def resval3Tail180 : Box := ⟨13241820006440250085170500031214826353146113440,34951599633742250865385625374709110433637022360⟩
def resval3Tail184 : Box := ⟨19631595723726625871761731440911633123069228871,42756630440006715012932064496118525408456579250⟩
def resval3Tail188 : Box := ⟨29104726576286328135740761448359703346663868530,51659219890211019582216539860135354889005242583⟩
def resval3Tail192 : Box := ⟨43149070559588074346893500433172677837311008630,61402949107145163778427719307540374029943344648⟩
def resval3Tail196 : Box := ⟨63970444294545767043613158149997334953451651505,71376146537632593344133719097047650958811803345⟩
def resval3Tail200 : Box := ⟨94839070463645457398115948326080508717368694647,80372271299863501799564453342381420996575299549⟩
def resval3Tail204 : Box := ⟨140603201769151949271536371754839382813810419608,86214585762963152658497625958942015806184365756⟩
def resval3Tail208 : Box := ⟨208450591629518464319432184691093395700302785177,85173715011596975599627710197385755247622863285⟩
def resval3Tail212 : Box := ⟨309037408955162772547876223803681014801443530703,71070493562797676650729093788146422975246235275⟩
def resval3Tail216 : Box := ⟨458166952240426547692881404995487406287165588029,33901983876099955889736396459136340685806480484⟩
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
def polyval3Tail5 : Box := ⟨33991287425117661708146097560719731170524366742995934934,306884865200114497446213172104735166622071322232358420129⟩
def polyval3Tail9 : Box := ⟨50390574461455282531797725295989355208166044996934710643,390883986160820308986694551110291545545088344865501744631⟩
def polyval3Tail13 : Box := ⟨74706300327032735223049979241955377764484854657082761578,496540506429276432689555384178663319946763151333930317347⟩
def polyval3Tail17 : Box := ⟨110755461509019216704719927453442008643531654745690189393,628745392368935848206082230284452946856397579369804945417⟩
def polyval3Tail21 : Box := ⟨164199969753578555138109052159302462109682948766487802317,793112187475964728461483681614238502131672162008290678933⟩
def polyval3Tail25 : Box := ⟨243433865018752632709533421575446761621414663041195978158,995843360387575233648286137432074121869249109779971608786⟩
def polyval3Tail29 : Box := ⟨360901690340760688316121176405142912739045935319051945697,1243390107076110482773072917270096955104432171442533752055⟩
def polyval3Tail33 : Box := ⟨535053042356225431611059267736754279188716449372313430960,1541764088221790747498149668452832276956268452791928355466⟩
def polyval3Tail37 : Box := ⟨793240280654678180488721594378544203443744483602339886385,1895278978003314280032909649500415571213020212422927177095⟩
def polyval3Tail41 : Box := ⟨1176014512658702591733450783908643894299063301891045687479,2304376561621004941949716816816481019734029896764030263769⟩
def polyval3Tail45 : Box := ⟨1743494585073841554958666038936685166808831779733226316588,2762004860733465367068712893509765247463637486404967076827⟩
def polyval3Tail49 : Box := ⟨2584809401126834288452534018658361454886917227031014772665,3247732064165564061064821900417650161227675305206541276051⟩
def polyval3Tail53 : Box := ⟨3832096581975157528279833905721923740142200362931314240322,3718351565568597894744718964119732488246472779407858482705⟩
def polyval3Tail57 : Box := ⟨5681256113964863806899907204953297886234423860979919723488,4093087980799137360225541815210870031989316562880294068664⟩
def polyval3Tail61 : Box := ⟨8422718567241073102703517290607515403110489068214968687065,4230543943266667891377328951640645334515967508571200572816⟩
def polyval3Tail65 : Box := ⟨12487060368334027232913700814468876592609786479664203796486,3893072212198277992806662520941324502608485211074609899377⟩
def polyval3Tail69 : Box := ⟨18512630648002893102785435288967189309108480557650994352884,2692078009700287094147917314066659332941600138555091868331⟩
def polyval3Tail73 : Box := ⟨27531250000000000000000000000000000000000000000000000000000,2⟩
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
def resval4 : Box := ⟨113064801421806851842142797578906130769192669936665459597,8718060590665333845485797837962268984266842209230681903⟩
def polyval4 : Box := ⟨4657144143958368967982494996797341203933721582390751732774,1927461232773627663929253556233172848617000859007359194352⟩
theorem cell4_lo : Holds Q cell4 (15/16:ℝ) := by norm_num [Holds,Q,cell4]
theorem cell4_hi : Holds Q cell4 (31/32:ℝ) := by norm_num [Holds,Q,cell4]
def resval4Tail4 : Box := ⟨-3957912690641905321475860508403833242009127964993290188,9464311482835846023203616737533387790521521912717996934⟩
def resval4Tail8 : Box := ⟨-4795933222344800070847678821539103473241002845147549185,10443874371569087074068413707354488312789256416821243680⟩
def resval4Tail12 : Box := ⟨-5811305193244572870056682428581611795478028901209074178,11492141609456501725309935173371013907372701207509032421⟩
def resval4Tail16 : Box := ⟨-7041646835976834538045438565639765494672614723069388062,12604878835443001013656331220832507923235522455387125392⟩
def resval4Tail20 : Box := ⟨-8532470505973622051960850074066319405601058096262677840,13774412935155220044273522399780190747590263926785973039⟩
def resval4Tail24 : Box := ⟨-10338924207807149642992955446856530580360734179025787246,14988558990912876251616385698126527374775149337185874218⟩
def resval4Tail28 : Box := ⟨-12527831616873936086133315194474933479749356242857821134,16229274093316790365344057144980475218042915876825710862⟩
def resval4Tail32 : Box := ⟨-15180163996388754608968331098441330407758025153516722267,17470973202623451047920736151094934501504585318761171093⟩
def resval4Tail36 : Box := ⟨-18394035456772712906949487894235691803911562323272634476,18678428341658966025064911880326983728915738069079504183⟩
def resval4Tail40 : Box := ⟨-22288332356982466239869822097363722639608153240692682611,19804154765567314618055500150395934024271600766863428171⟩
def resval4Tail44 : Box := ⟨-27007111105268646686683559404289931625400723634226160276,20785166251732178429407036255845540586814054053231501841⟩
def resval4Tail48 : Box := ⟨-32724927041202540414047155158717938032632427704706052382,21538955449714826042884816211092748961996262634010567733⟩
def resval4Tail52 : Box := ⟨-39653291523028172640556593695428580649485840916336286158,21958523310414887346156469888580372216911866757111124488⟩
def resval4Tail56 : Box := ⟨-48048496078556178347102506823627523939718290862901940665,21906242742534376891320504933521193898491420777630061171⟩
def resval4Tail60 : Box := ⟨-58221093047725339351637274415761924469119459551249533395,21206294325229140191124679224192074600569876474510833712⟩
def resval4Tail64 : Box := ⟨-70547383412514872716867292611833714931503274190599105737,19635354320128329839014737756152912398491538148194728849⟩
def resval4Tail68 : Box := ⟨-85483180011091573000959596088121832455565670892234244881,16911142336072963803454883113000494194469408869100070648⟩
def resval4Tail72 : Box := ⟨821486857584614671639727685307934116587082896479825623074,755150947976652593552187015843714460006740065334001679⟩
def resval4Tail76 : Box := ⟨-51593443032059407083821279128536185491650652324698040,126308271583477520003793243206851387801268691123426078⟩
def resval4Tail80 : Box := ⟨-62483460235272881842718060514005047868287211989574355,139476955699764655943421771699672262957677650684944964⟩
def resval4Tail84 : Box := ⟨-75712156781259071281185624859213862036209598895263431,153595940780995099957005293451228567032419314942672690⟩
def resval4Tail88 : Box := ⟨-91741571214897439619602860007990002960879968767191252,168617389446080083468888963226119878288119615575522087⟩
def resval4Tail92 : Box := ⟨-111164656336273163271253829091147938939457898823659268,184449799137985528039194065485014987739972150978250795⟩
def resval4Tail96 : Box := ⟨-134699903813673951012043130058700021820547981158547357,200944032018187218617003753092925970738366985492856703⟩
def resval4Tail100 : Box := ⟨-163217920923780044858501561854505171688736293196721583,217875931472461791732545386080204104414703401298381981⟩
def resval4Tail104 : Box := ⟨-197773635737199159545585305410353575819459794632521456,234924556691821599050014381027892739705877061717708344⟩
def resval4Tail108 : Box := ⟨-239645320632261307537595304140295499195761130865196449,251645012586423347124177004462321507773539222298267379⟩
def resval4Tail112 : Box := ⟨-290381877679853793279777063934571127257927278021726193,267434622914193857445652095772159566297774855634861292⟩
def resval4Tail116 : Box := ⟨-351860135062975657340256469238776959465338880488445677,281490914806928881282499140060047986432914248501459951⟩
def resval4Tail120 : Box := ⟨-426354274019231927283362420757659943368195451189452970,292759541983203341179961039360856624855871878728180771⟩
def resval4Tail124 : Box := ⟨-516619954522361063339869809703051520337257896282655685,299869858625980518264459981727945679067858169269639962⟩
def resval4Tail128 : Box := ⟨-625996251649273609176776813891095885137812933326612846,301055350113800027828294920574230858092294912058774127⟩
def resval4Tail132 : Box := ⟨-758529173425477194918360788871887256337427299703101436,294055511027111337892419256719280339980802562025517514⟩
def resval4Tail136 : Box := ⟨-919121329301092331080037414684686696929077285456159682,275995011428012211648753956706373059189152980245132410⟩
def resval4Tail140 : Box := ⟨-1113713506128127008820836467667498495154481975230128075,243235069097023511529548690966663070275993180289864005⟩
def resval4Tail144 : Box := ⟨-1458323937265258993188084279468947724187569385163540861,187229944672740467488716558256257819577289403897850571⟩
def resval4Tail148 : Box := ⟨19444324472110490799934480544475152525801993976,41309801139961148829759424655044196197480025779⟩
def resval4Tail152 : Box := ⟨23482904362257604724909005327049346769605695345,45424328956996609582379486668094186004464925469⟩
def resval4Tail156 : Box := ⟨28454590802683574944287108784911999608250111933,49783445901912366843071977841621804442498995311⟩
def resval4Tail160 : Box := ⟨34478860192196293767143987810894866169763933838,54353475591381961525176375765727122307303004195⟩
def resval4Tail164 : Box := ⟨41778558982315970410658040774453973290850380129,59082661635949030759679659457093151315457364842⟩
def resval4Tail168 : Box := ⟨50623714963580410280291603690516567748435656108,63895235088468040918058310571083541267982152045⟩
def resval4Tail172 : Box := ⟨61341524914696093604997823407934397599204394345,68684562818854910303425327819466406289923907708⟩
def resval4Tail176 : Box := ⟨74328458145896514101384547895502179771544278572,73304605933096792461070039673616343631315423401⟩
def resval4Tail180 : Box := ⟨90064922546825817999677751965332274496068912191,77559298017400101520823649259376796108519007139⟩
def resval4Tail184 : Box := ⟨109133035659687762047544245703783142057488294087,81189365999130778935302883467501091436944542603⟩
def resval4Tail188 : Box := ⟨132238158158705135818776347776877869453958503640,83856010400317680586807268152554722941658141597⟩
def resval4Tail192 : Box := ⟨160234986294495101016906625629479103428831683942,85120732623586792882923290134990077759443755162⟩
def resval4Tail196 : Box := ⟨194159168505530572030551062412957796224686137720,84420439668237690947117161234400295455500533493⟩
def resval4Tail200 : Box := ⟨235265615746828496127862789879960477687263252206,81036765271488608424572567203285878410344255215⟩
def resval4Tail204 : Box := ⟨285074922697548248595847314452853807825289695647,74058313556595344833070681926525751547955955214⟩
def resval4Tail208 : Box := ⟨345429617043889208614409703876089328655773521033,62334247923400539942656488317244215090741915426⟩
def resval4Tail212 : Box := ⟨418562317690970401677978610105395290194492451910,44417303302468963321718777561237433084411833487⟩
def resval4Tail216 : Box := ⟨507183133330406459366171834001900936726095987990,18493634735405548656006623598640806389561172336⟩
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
def polyval4Tail5 : Box := ⟨1048896799817169976804287416614468492787644457671502042995,2120558934861797424602028249402916538277871136724633721691⟩
def polyval4Tail9 : Box := ⟨1270961716818334225448531364547512589263218033058259123096,2327671191996770182005415386462961710179770284400861121116⟩
def polyval4Tail13 : Box := ⟨1540043630974319654426925449389379704047032694081301024065,2545884139794338093714978229051309216203935653767647493139⟩
def polyval4Tail17 : Box := ⟨1866094276705759110238048592491235841673204893222816838699,2773113492431441792173899884896934679720182734461859659204⟩
def polyval4Tail21 : Box := ⟨2261174800191355693141988070937207116995868304058250122945,3006233223806808969360703941223274618835299788627361820312⟩
def polyval4Tail25 : Box := ⟨2739899875823159871546737666821521374445199470918177631934,3240773694319695031401827113446309208350110052144842474385⟩
def polyval4Tail29 : Box := ⟨3319978326708961266008929102078259132303700676079073248271,3470544866035019891437615666620194144161505026260222741486⟩
def polyval4Tail33 : Box := ⟨4022868202987078379364368803267532236390326875598863233823,3687167245426885987589590367903380433879235316799517900900⟩
def polyval4Tail37 : Box := ⟨4874570550177924127504295274562462299813490692790226164646,3879489325402729804610152701883521189655400843723973009576⟩
def polyval4Tail41 : Box := ⟨5906591230361078934732319686177274527072448476989495697301,4032865574732535371299220726242894942165354539342227790460⟩
def polyval4Tail45 : Box := ⟨7157106375515476400539739374721820257713134767903862309890,4128263268334356699698310120254745361187210687185465441529⟩
def polyval4Tail49 : Box := ⟨8672374585046893064532672672974615937074890584817368053948,4141159443599431808381304309633954464423644625403863509692⟩
def polyval4Tail53 : Box := ⟨10508448106997768867202110566745488010742842218218099144079,4040180735900063180974924685838162591697188973701504138268⟩
def polyval4Tail57 : Box := ⟨12733246302329535699450906773561117324364186269597852989636,3785428462586949365471001705870150876346001994521679381913⟩
def polyval4Tail61 : Box := ⟨15429068093110715115958790199301617184087416793419206688580,3326418690944095348665531148814452212783208832337918597254⟩
def polyval4Tail65 : Box := ⟨18695636334192836200565082632128162802675549560771521869804,2599551658382835869753981065724882568720940648506967047395⟩
def polyval4Tail69 : Box := ⟨22653786865691189923052608219767017043109714705123675500374,1525006219027566484248407465973467222870968120721345162303⟩
def polyval4Tail73 : Box := ⟨27531250000000000000000000000000000000000000000000000000000,2⟩
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
def resval5 : Box := ⟨101545321424870738396300377662696530642913465100746732390,13833645928146900049745919377441701758942109398680646749⟩
def polyval5 : Box := ⟨8767473346762942547693961910406923575163433086783683161966,3859150525137532822438072412433431882085751553257212053989⟩
theorem cell5_lo : Holds Q cell5 (31/32:ℝ) := by norm_num [Holds,Q,cell5]
theorem cell5_hi : Holds Q cell5 (63/64:ℝ) := by norm_num [Holds,Q,cell5]
def resval5Tail4 : Box := ⟨-16241670539148036240203421018439693255072311180100782827,14054989199626023976571825320538907240433661958466608434⟩
def resval5Tail8 : Box := ⟨-17857969248550266796276459177935836099217381009528093954,14408635536892382050952730559322335171347418251917336698⟩
def resval5Tail12 : Box := ⟨-19635044844779432902152287188066473161812865071132561746,14729529420659855298419503134850758457035956064595291868⟩
def resval5Tail16 : Box := ⟨-21588960118744871474216773580816925256544395734309612764,15009993258935409022045143340424078076739261909911804421⟩
def resval5Tail20 : Box := ⟨-23737312682152345737781045132129621547494191741893732438,15241298779608527368636511295171600084286478645832697524⟩
def resval5Tail24 : Box := ⟨-26099451306181214499637173845716922857668836757962027646,15413543226975943274516523745782412845577657403092003648⟩
def resval5Tail28 : Box := ⟨-28696650189719756537035016255299694919122500130486035431,15515512596031874416178060217810797866443660344139177670⟩
def resval5Tail32 : Box := ⟨-31552300561817228732346875985431501957389938680234186399,15534529963803753562210036395574717378197458852010337839⟩
def resval5Tail36 : Box := ⟨-34692121350801260476255636489216258637398106208551895647,15456287350504910096327459011117352699846273819694627330⟩
def resval5Tail40 : Box := ⟨-38144390817422017828043636201067442980634703430085080352,15264659381971804439832964968548419277600410285294845735⟩
def resval5Tail44 : Box := ⟨-41940201238187590041310233521571001759781590999543370269,14941496847021484318696388314558013388126631789432174434⟩
def resval5Tail48 : Box := ⟨-46113738932652647809629902078443619816880589409308295330,14466398047457887951922984750821984132788664757429583628⟩
def resval5Tail52 : Box := ⟨-50702592156678417390182983598662329248138703076314440373,13816455622650316944965608714848989258280390295668834512⟩
def resval5Tail56 : Box := ⟨-55748089634652117857918529097114258830207426726351501902,12965976292897514493939238077825352729508017041679657332⟩
def resval5Tail60 : Box := ⟨-61295672779593072094712937798499471156518332691533508803,11886170703968337124226772393423782383072438371832150407⟩
def resval5Tail64 : Box := ⟨-67395304944885230844102968158967329881881874535538081802,10544810266517776097413375543755314206382314981184268550⟩
def resval5Tail68 : Box := ⟨-74101768172552796601745674570113049261133879415842545073,8905843592725821986197765617187560461035199529339940830⟩
def resval5Tail72 : Box := ⟨821517555293973343453555118799739566571947634811341456966,762693237997786986456315127164161967707185106105810014⟩
def resval5Tail76 : Box := ⟨-216394281877903305584854471554331125354847789581945277,190389711143282860248078815344247932615611682101206230⟩
def resval5Tail80 : Box := ⟨-237898035820650454284584292298586293582634249920861826,195305778867621382496658983655915594121263250876022340⟩
def resval5Tail84 : Box := ⟨-261571655025941774712158410733370535156499228018118319,199799000725722902956693696101126110972425836907252646⟩
def resval5Tail88 : Box := ⟨-287601076196760888409024381429384872620704656031736177,203767825661990001348703835614331723075898779294476769⟩
def resval5Tail92 : Box := ⟨-316220727439227625585080212636061506358484365617779703,207096901682499292956696506683418945929280725038141035⟩
def resval5Tail96 : Box := ⟨-347688366763215972400334296798560279792628817813498493,209655290748733841420895078147140545369765904751829226⟩
def resval5Tail100 : Box := ⟨-382287402098602489553346231255148534174510610442380674,211294650717246200580043458276650819952069457560365820⟩
def resval5Tail104 : Box := ⟨-420329443759692661700342867659594183425648576007040660,211847219015953243660284828017621299769099186336953152⟩
def resval5Tail108 : Box := ⟨-462157110910400323837756543671160930326251665945410264,211123577180312964517336318962712262198894360116212028⟩
def resval5Tail112 : Box := ⟨-508147117305347629351025956644061635865386592619023801,208910173239999650616981645066302380277014740560192843⟩
def resval5Tail116 : Box := ⟨-558713664098084790787123840031088647617705784579727985,204966576578829797597263256027126833546602794265461843⟩
def resval5Tail120 : Box := ⟨-614312170273178499340147353300105455741263054138157658,199022437282098395217958720047610014508002809496927990⟩
def resval5Tail124 : Box := ⟨-675443374299669772508125276909962231588219550910943675,190774119111893452273539836393516465086511858766543277⟩
def resval5Tail128 : Box := ⟨-742657843946744081255255808050095615265379885364281176,179880972085643411584614324810702707597118767095424474⟩
def resval5Tail132 : Box := ⟨-816560934878524894970016329842510504286627423259995538,165961207146711123622210401287758209508241137761435186⟩
def resval5Tail136 : Box := ⟨-897818242711395794265517124757205264301401197700964831,148587331574545521241952381658680583488186542961662745⟩
def resval5Tail140 : Box := ⟨-987161813127907721131692110263921989048160354692445498,127281089904254359126039344085033081822881150781483393⟩
def resval5Tail144 : Box := ⟨-1191657526856820462734656299671136344846713141710183692,98476491081028110753014612199889755543152742045738998⟩
def resval5Tail148 : Box := ⟨106239740521583916053473634706226129108574744019,79877076557500140204237542359049381505993059553⟩
def resval5Tail152 : Box := ⟨116741044956611986344906294635908020219973400767,81407990646680944602575794359768191744184449719⟩
def resval5Tail156 : Box := ⟨128358135138052935812518871508520981976669626101,82674517802843864489349471926527817007404727851⟩
def resval5Tail160 : Box := ⟨141131262103549954892482514509479342615623310701,83622700115776039515656675896275449042244715609⟩
def resval5Tail164 : Box := ⟨155175463725554861048873833805624670717435778562,84191965103187961855377900064543514160355051631⟩
def resval5Tail168 : Box := ⟨170617226711780462414009062911231068416965320091,84313833983694203074727888715049991505732859970⟩
def resval5Tail172 : Box := ⟨187595624668496564142060887759666164444951115475,83911012743802538490745895870601368713835381261⟩
def resval5Tail176 : Box := ⟨206263570642914197622317721339599481931295409700,82896384828303124721526386888113778127175865600⟩
def resval5Tail180 : Box := ⟨226789194308480556267548488923380789058854034111,81171895133116791678396104152844986785470283066⟩
def resval5Tail184 : Box := ⟨249357356196125011102919950286567595207366051827,78627313933953904950682902268374561640447466287⟩
def resval5Tail188 : Box := ⟨274171312609121250461514774944998309663009194292,75138868217269551348925144723365604092672177065⟩
def resval5Tail192 : Box := ⟨301454546216337459721218150539455086033541315083,70567726594686257178969394615975990942580824836⟩
def resval5Tail196 : Box := ⟨331452778810800622202489820241726149844862910359,64758322566360920939864141681441615678486382384⟩
def resval5Tail200 : Box := ⟨364436184361141874366405372031108751729475365581,57536499339562817674366378440294379298686563689⟩
def resval5Tail204 : Box := ⟨400701822287393618176758383239291360860316063835,48707457691551491898819037110124658584123064971⟩
def resval5Tail208 : Box := ⟨440576312876057758721666210906872468865404545944,38053486474792434210346739567084636964754878121⟩
def resval5Tail212 : Box := ⟨484418779028701754022041342096334184650798813271,25331453274807287207055170163961411060961786340⟩
def resval5Tail216 : Box := ⟨532628780735162581660532295463566947530817736413,10269825604848696219739903073607155962196480536⟩
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
def polyval5Tail5 : Box := ⟨5472361942825512011436142817669198815538093182276525459797,3936266272856951177226471101215995869154784708019188132128⟩
def polyval5Tail9 : Box := ⟨6016923341749695754589116060784182483686502041988705731397,4003450187607533237059218333606703940958941017844760088726⟩
def polyval5Tail13 : Box := ⟨6615677177477669823703964759633661714232620460629235517498,4056219432907145761646202547809282952386346358987338493941⟩
def polyval5Tail17 : Box := ⟨7274013982248842421054897432441143931103596890269987800634,4091767635701672077380235066302141740112120058755943716447⟩
def polyval5Tail21 : Box := ⟨7997862954087808143642274187908941379524935095999650344769,4106919963433872405604196870609086111190544783097539684059⟩
def polyval5Tail25 : Box := ⟨8793743315378453878912336463200263988864840746805744319889,4098090647796559323819718164738357825511130044020024335115⟩
def polyval5Tail29 : Box := ⟨9668823026936082757677625848383901012517257121771207207538,4061235914765305463990043476600330315649843929348134557383⟩
def polyval5Tail33 : Box := ⟨10630983345024563846787397789072882466951221053211729171872,3991801828991647943142603057144080809039211624760320802233⟩
def polyval5Tail37 : Box := ⟨11688889802547503625883398071153712519962813223610976251552,3884666520360143558754383310556629119851011732220737148325⟩
def polyval5Tail41 : Box := ⟨12852070253693292943260693930460111148362026519132087834929,3734076205857222345163985453223374456700403987996816011473⟩
def polyval5Tail45 : Box := ⟨14131000684929821799903572829809330468048212855369827067596,3533574359692853131194633854351485442556012850692954803291⟩
def polyval5Tail49 : Box := ⟨15537199565190959279592868654391357007765609192319250751471,3275923318300230460390642223109728355992170287449705837827⟩
def polyval5Tail53 : Box := ⟨17083331585003671067031343845637485272573880663443543298002,2953017533798471868640327282123160658807151732778589194821⟩
def polyval5Tail57 : Box := ⟨18783321718864540563665106962647054650445346248168408416073,2555787609061378532292693709049484924357201772209235458440⟩
def polyval5Tail61 : Box := ⟨20652480638149061770738821881767180976644782824956917447520,2074094158946431506812305496821705123190317814619022195269⟩
def polyval5Tail65 : Box := ⟨22707642604079886157064822056928143557085135106188422744243,1496610444681545270371761437436321640802490049065254401635⟩
def polyval5Tail69 : Box := ⟨24967317220564514962833452930296444552898952762762137380214,810692615183343372010273927015434116312126676041348571405⟩
def polyval5Tail73 : Box := ⟨27531250000000000000000000000000000000000000000000000000000,2⟩
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
def resval6 : Box := ⟨85947482694122589274480328063943772122896027636562277714,12367095287042433394125976720941117875707197687088246687⟩
def polyval6 : Box := ⟨15538435547273632706858537534747065277025124255556683866669,3862283709805041182218983736145287323283536401854633536149⟩
theorem cell6_lo : Holds Q cell6 (63/64:ℝ) := by norm_num [Holds,Q,cell6]
theorem cell6_hi : Holds Q cell6 (127/128:ℝ) := by norm_num [Holds,Q,cell6]
def resval6Tail4 : Box := ⟨-31828425419742021961135211943446751016401817284833312834,12101977614452415276111607070636570005420513436174439788⟩
def resval6Tail8 : Box := ⟨-33365199025829594618260671052647904086299057460612579041,11965325995012822838507713486722723737518909294527664600⟩
def resval6Tail12 : Box := ⟨-34976109218496652043060886344507086365476625273141056234,11799100563727356916833943284467286712685448890492346068⟩
def resval6Tail16 : Box := ⟨-36664796000964767035746554444181161186077496349345506205,11601140668430437947157581305130562293862410720409072492⟩
def resval6Tail20 : Box := ⟨-38435014523605466214277977071979697054299265545724146969,11369158529170313118065441678043126553626635559095356105⟩
def resval6Tail24 : Box := ⟨-40290701232618096388471129566902612863920020865670187437,11100731828364230239007764001805326666992472565102096424⟩
def resval6Tail28 : Box := ⟨-42235982630345913316155061998336877178112631723606229401,10793296447589298345106790128004026845324826893245910904⟩
def resval6Tail32 : Box := ⟨-44275184451411569377900622241823778547450842698539841999,10444138829350528200576197103594232220176548419319291480⟩
def resval6Tail36 : Box := ⟨-46412841281880742448005502501728135929011892127757075857,10050387944827755041334538531116075474570479158930580517⟩
def resval6Tail40 : Box := ⟨-48653706642850025606855166046313443608020890158258611364,9609006847773150069429325227256033739219194494531529477⟩
def resval6Tail44 : Box := ⟨-51002763560882038005832322898700031131254460130440595992,9116783793748203585772926063639039439010097567911635736⟩
def resval6Tail48 : Box := ⟨-53465235648793300946828184042220034972350116928652693371,8570322902857826898033874860749904050910793353589794014⟩
def resval6Tail52 : Box := ⟨-56046598721435297498085694755473012435084877872635838107,7966034343057351370933739247092325400552110191309810593⟩
def resval6Tail56 : Box := ⟨-58752592972298784099410860539831120731863974610792796868,7300124009973229112961470549020252942710036407831008234⟩
def resval6Tail60 : Box := ⟨-61589235738013080130510124666442143261790616772124773262,6568582677987262296099376868186848553093813914900706185⟩
def resval6Tail64 : Box := ⟨-64562834870617666031752940786821093908608912602149063426,5767174595729437472261819156338380273643212505770427170⟩
def resval6Tail68 : Box := ⟨-67679851235152152607889911735998230257973755910928348164,4891420985129036318256336434314939425197994521916304529⟩
def resval6Tail72 : Box := ⟨821398837785890558390764264654514173383073030067692545617,712831298610369719817473793582118392435318812680355979⟩
def resval6Tail76 : Box := ⟨-427682544109145471133632653011938622372218319879467518,164825147792460682601650072826019020096574303180461056⟩
def resval6Tail80 : Box := ⟨-448302972831346939569464242477428112217393159024082110,163059664611168372751457821178050587762065803820847139⟩
def resval6Tail84 : Box := ⟨-469947554487981109346445871994841830965703727007686711,160899221142522703955800188015979211295657263010305797⟩
def resval6Tail88 : Box := ⟨-492637162949784862429225651347697937503168390968425843,158314712250622646564926634382757620506215045570395196⟩
def resval6Tail92 : Box := ⟨-516422251806459057620003875114518683126193837275415923,155275472896914300999147444382994455137055477549531129⟩
def resval6Tail96 : Box := ⟨-541355712110657795041224110525320844085199732652187317,151749032741312792373186875303626338503898024048071648⟩
def resval6Tail100 : Box := ⟨-567492988556718004908546179743636944613707927754290712,147701018611403428624330929529778778905500453549310191⟩
def resval6Tail104 : Box := ⟨-594892202772593657113574315680059193346420963638163675,143095051950988927323366006738000646187222616051627820⟩
def resval6Tail108 : Box := ⟨-623614282565287642389056657507799932443904880556617709,137892640976962243916485557359155412595295894421355871⟩
def resval6Tail112 : Box := ⟨-653723097406403892015167314733646858124228683707253452,132053067278153202113981442218370499413749244624818129⟩
def resval6Tail116 : Box := ⟨-685285600459097807459056570112089840832559863824070680,125533266576607070745724328622267487989759265709623013⟩
def resval6Tail120 : Box := ⟨-718371977462251216127745909813054871131016593006642926,118287703357899936952669353533098923539936809197375297⟩
def resval6Tail124 : Box := ⟨-753055802802946541730398275867988438568993053232022651,110268239062562151363204099391279278799350836653417297⟩
def resval6Tail128 : Box := ⟨-789414203124299656643277800133981625911851000709155645,101423993515434106510594532358117833911524363108610646⟩
def resval6Tail132 : Box := ⟨-827528028832491962916931925115715403747122724573679812,91701199253781679353901423075464172002505343536104638⟩
def resval6Tail136 : Box := ⟨-867482033908795152438731927876927133070719758941011555,81043048396934268815896559088916405802539511585825525⟩
def resval6Tail140 : Box := ⟨-909365277549115923392850732669520934298000902466406797,69389522910300002902179976331829277208462281474949869⟩
def resval6Tail144 : Box := ⟨-1058297363507504962157107897363591864048882965337138251,54084837728778671280320850526249511025630071251741021⟩
def resval6Tail148 : Box := ⟨244822617493973489356703165718663024456959754022,78840996432709233186239532447180898884433984235⟩
def resval6Tail152 : Box := ⟨256575478598979116413797848336215771626136293234,77336403769127544891558131622131553365070590609⟩
def resval6Tail156 : Box := ⟨268963236646139145300369056981112920300015554540,75590423036858298900219191720913923344041917701⟩
def resval6Tail160 : Box := ⟨281949091071580672628517430807919701420294440431,73585500753354223961579015917765936984843591183⟩
def resval6Tail164 : Box := ⟨295561917485328034827754599111649888443007536383,71303569012624110080451225305555248664103511025⟩
def resval6Tail168 : Box := ⟨309831986815754827023745603728295438869968833299,68725510198914124103911182530999032875008513168⟩
def resval6Tail172 : Box := ⟨324791031506836116221550722542635154621561053538,65831100637532364403450584487556117646856986110⟩
def resval6Tail176 : Box := ⟨340472316081441234542999848044765883764307666801,62598951359604421775133462462115079400733891794⟩
def resval6Tail180 : Box := ⟨356910711111864381610752951618039344597528476440,59006445820978389770590977125762544039966390767⟩
def resval6Tail184 : Box := ⟨374142770761738125630795872824778944678418552665,55029674422290134678555230187022951777954446162⟩
def resval6Tail188 : Box := ⟨392206814071759680355708021308442586655101691914,50643365669631302105670344388362469922886720516⟩
def resval6Tail192 : Box := ⟨411143010169985541306696429642228077703717109870,45820813807315803338673935097585361234370421756⟩
def resval6Tail196 : Box := ⟨430993467596177155617933714427183496407152663429,40533802745903887303301635819757087649814929823⟩
def resval6Tail200 : Box := ⟨451802327938828741984657890398595457374614743287,34752526099897356204381414573580119340531036155⟩
def resval6Tail204 : Box := ⟨473615863993098591868531340657557489619411790057,28445503140345072018658746132286763661210898310⟩
def resval6Tail208 : Box := ⟨496482582657953568308741425674818745241046198638,21579490457971481428146349166368002361096626478⟩
def resval6Tail212 : Box := ⟨520453332898875167304868528797762141431140718023,14119389117418977634667052586974176786610653424⟩
def resval6Tail216 : Box := ⟨545586065663875520597876435368261246349440323225,6027961796191442503591299578862204733683731311⟩
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
def polyval6Tail5 : Box := ⟨12315844950947587648649283930060037573410363597810073461628,3790302251603184137190018146398227527924047853540182123077⟩
def polyval6Tail9 : Box := ⟨12910465971421587692395014745536878990908831138921736502528,3708982353938139763885486909642629779119632056342282891545⟩
def polyval6Tail13 : Box := ⟨13533798117889777921332777899821021249376857336358793486869,3615312363436165657194325209733194854563638480916388752645⟩
def polyval6Tail17 : Box := ⟨14187225457546375893585765751156035636280217784333467176148,3508427523631385810082330412685864692890099916194561992306⟩
def polyval6Tail21 : Box := ⟨14872201020731482752578747554157171484736736394295176111144,3387412780885179191195986178204114556802120127138266981871⟩
def polyval6Tail25 : Box := ⟨15590247991963551522184142607498091465052378510236555966617,3251300072910336018210381659815591859661541618652519328552⟩
def polyval6Tail29 : Box := ⟨16342963096861701436804380646695219753023400766846465614029,3099065488075935561629939978713505492482723386022007555520⟩
def polyval6Tail33 : Box := ⟨17132020152794491278228543643092760685673824340735395611542,2929626278595072957434329016775506870278667287070859250717⟩
def polyval6Tail37 : Box := ⟨17959173790958252459591936796323798971436195701149225847564,2741837720252660354256017999505473151355974543342482868917⟩
def polyval6Tail41 : Box := ⟨18826263358161645651459258892360709740572774855828902785035,2534489810969178355641862581765312723515698340496903902539⟩
def polyval6Tail45 : Box := ⟨19735217006992863625308184721289302487474005373331114699018,2306303800114894039409673822323016410933389825655089440712⟩
def polyval6Tail49 : Box := ⟨20688055983464811145806508634482794634852146634518077206448,2055928540088987411505665928683228858324384583159106191794⟩
def polyval6Tail53 : Box := ⟨21686899121672725783091605682641926237109580907468150212773,1781936651258328585813793151741350156860053494248356334426⟩
def polyval6Tail57 : Box := ⟨22733967555459038468089494835847772412849726524882945730925,1482820490910365906346919146929676155884071106342836057511⟩
def polyval6Tail61 : Box := ⟨23831589657562848854755619010088943002314325785422502173243,1156987916412715699014153397814299047255699398488489306714⟩
def polyval6Tail65 : Box := ⟨24982206217253258150157475537171765317079648354940352303518,802757832286724385604634755314274162359316088364158003078⟩
def polyval6Tail69 : Box := ⟨26188376004346994741544119937083456226709664432501929887600,418355505152229229466133535796088758081557802514753592743⟩
def polyval6Tail73 : Box := ⟨27531250000000000000000000000000000000000000000000000000000,2⟩
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
def resval7 : Box := ⟨67893029682354278091910044964058860705068776242041884701,19952120666672055004660151106927176128140154206168482214⟩
def polyval7 : Box := ⟨24500947032912288150856520766196837441093472505449505050392,6745978481682187636810225551903506186063099192264597826668⟩
theorem cell7_lo : Holds Q cell7 (127/128:ℝ) := by norm_num [Holds,Q,cell7]
theorem cell7_hi : Holds Q cell7 (1/1:ℝ) := by norm_num [Holds,Q,cell7]
def resval7Tail4 : Box := ⟨-49176123122141265735624773453324462381666761160390873003,19032195505885628410948016020919863981633438320472426271⟩
def resval7Tail8 : Box := ⟨-49952121456605735079752888661472056055178291203949615193,18256254458738708913504841203182146050994918039988025270⟩
def resval7Tail12 : Box := ⟨-50740305407343093966969432060283543426907272077117714415,17468070514726246267110542122459147294371278693809403404⟩
def resval7Tail16 : Box := ⟨-51540925938754290838837844967042668991355027296028972281,16667449983320958454514856236013005145837628985129170533⟩
def resval7Tail20 : Box := ⟨-52354179291940122060896567082293082465968244959318956057,15854196630135149805801030936474962555852565458495353126⟩
def resval7Tail24 : Box := ⟨-53180264797525634360070002925372647400303060663708860062,15028111124549637792429130060377947769072034257892916115⟩
def resval7Tail28 : Box := ⟨-54019384931325508015443966561873072681418525984458478512,14188990990749764147003508799252936076735142577309465329⟩
def resval7Tail32 : Box := ⟨-54871745363977392626973131597255367984676718781717465375,13336630558097879536252385610079133955336117954965083651⟩
def resval7Tail36 : Box := ⟨-55737555011352364624016755102693343679588193446767708289,12470820910722907539272051548344614888814061795972091337⟩
def resval7Tail40 : Box := ⟨-56617026085760778381492155229434110589771735653043267490,11591349836314493781642585565059502464681184601887478000⟩
def resval7Tail44 : Box := ⟨-57510374147966083355052150747497459725607397578362183868,10698001774109188807156790092590745583764930698827971805⟩
def resval7Tail48 : Box := ⟨-58417818160019356206053124225040126083157782884816259367,9790557762055915946244707960187963376418697705195871175⟩
def resval7Tail52 : Box := ⟨-59339580538927497616252946605780183925120798252550535005,8868795383147774273006321159152316758735943289666293099⟩
def resval7Tail56 : Box := ⟨-60275887211168230317237829160768560837346738081342586042,7932488710907021068626275065340831653770838803033290325⟩
def resval7Tail60 : Box := ⟨-61226967668059829089766084257829773983157959159182172790,6981408254009564155082038408151314325934449915082765941⟩
def resval7Tail64 : Box := ⟨-62193055013550979718660068500408011955764731260570519973,6015320899682527544565221684835119659748588789280896572⟩
def resval7Tail68 : Box := ⟨-63174235610403766714270023351203926353311487277461981609,5033985377210597806552514386314625356681379882340168946⟩
def resval7Tail72 : Box := ⟨821215733481793937830511163281294932576832876931097108226,813968505818748161831238195554558544389327241986328527⟩
def resval7Tail76 : Box := ⟨-663024086754213546732845781940249079701661891106674083,258877373153758043416704530491044371638036476739084374⟩
def resval7Tail80 : Box := ⟨-673458125466615614082467290365679795444949376419949762,248415933626149082536081751262794095973892564687227935⟩
def resval7Tail84 : Box := ⟨-684084477118997696653239509906308319419404235272486748,237789580519041894820584241710881661238314405050523256⟩
def resval7Tail88 : Box := ⟨-694878501182495613872808000324428563180481540775568901,226995556454736026866890644828672532775153255073412859⟩
def resval7Tail92 : Box := ⟨-705842841866145734959075662263903063683848280439119635,216031215771083722327138145616061274348355122164058887⟩
def resval7Tail96 : Box := ⟨-716980186559020600788314004380276945906265722071146027,204893871078208835492994634056087360335008029165021094⟩
def resval7Tail100 : Box := ⟨-728293265054734604758677589900681922175026255914227904,193580792582494830927866876480518265177563878837353119⟩
def resval7Tail104 : Box := ⟨-739784850219739464292856464986639436596590081997185585,182089207417489971350946332970519841376218972845639583⟩
def resval7Tail108 : Box := ⟨-751457758672959319377413119808107161074151517182882254,170416298964270116260041826083035982284094365604990252⟩
def resval7Tail112 : Box := ⟨-763314851476151709022122730725675628934864973399496373,158559206161077726614938378056341447425019138548391476⟩
def resval7Tail116 : Box := ⟨-775359034835161625318163351848455569823481174549225208,146515022802067810326518816382824093697467078316161071⟩
def resval7Tail120 : Box := ⟨-787593260812240507155177588286432561719254711751321186,134280796824988928572432374456927842955482589501994653⟩
def resval7Tail124 : Box := ⟨-800020528049604766164182219169644875830246916186431734,121853529587624671408164700746845092446105397746079831⟩
def resval7Tail128 : Box := ⟨-812643882504411303818172548160236092842769046010363259,109230175132818246416825068308254431345305918390231565⟩
def resval7Tail132 : Box := ⟨-825466418195354773721513902236443073991399525354278967,96407639441898366353062552726359692839755043009201768⟩
def resval7Tail136 : Box := ⟨-838491277985315143780092423742802268901127651283562990,83382779675049772632906306235417295032768788129090607⟩
def resval7Tail140 : Box := ⟨-851721865972706296163982395322710685927783692863382943,70152394704504835793741998741533530682098030468604703⟩
def resval7Tail144 : Box := ⟨-969380545278645318114519186011026408361337307021270466,54144606555899798636665435418105602538053300565699801⟩
def resval7Tail148 : Box := ⟨424844854412704555646896549191858910148866744990,135614654793588756862429773210493295444525222339⟩
def resval7Tail152 : Box := ⟨431483046095589972157472765058854830168278563217,128911650940028288904895790255354485178498395355⟩
def resval7Tail156 : Box := ⟨438291324550275026965917181506908498039528594662,122103371354326690572112001722426196165055698124⟩
def resval7Tail160 : Box := ⟨445207030522809624716258970921924183588248398618,115187665381438556663813226068736350814679198013⟩
def resval7Tail164 : Box := ⟨452231857955378079213019171210287321312451518764,108162837948869495321756924890643493522926833444⟩
def resval7Tail168 : Box := ⟨459367528652033549048731530268787141424844557563,101027167252214021547653259757706698563309138861⟩
def resval7Tail172 : Box := ⟨466615791585161075153247158770054284734561990514,93778904319086495364860363819194443541126521571⟩
def resval7Tail176 : Box := ⟨473978423323811089523427845930263070550568026801,86416272580436480990573809472438419546621539458⟩
def resval7Tail180 : Box := ⟨481457228469140768490635241962836336857474115590,78937467435106802022879407810175413162188426578⟩
def resval7Tail184 : Box := ⟨489054040096726703821492640074550142914039588832,71340655807520866691937129858801955660907310850⟩
def resval7Tail188 : Box := ⟨496770720205856735269543726611464944591492898495,63623975698390835243988958713105723475363082006⟩
def resval7Tail192 : Box := ⟨504609160175911063845624751449862303418028610072,55785535728336506668989091734517608066205892707⟩
def resval7Tail196 : Box := ⟨512571281229944506022138924901643945477142924397,47823414674303064509210562446502932322611662758⟩
def resval7Tail200 : Box := ⟨520659034905583514757425267575722279349104359021,39735660998664056406474005295374804514115437824⟩
def resval7Tail204 : Box := ⟨528874403533353461557677178105594883656282793976,31520292370894183045375100569009954412998859430⟩
def resval7Tail208 : Box := ⟨537219400722588485228168749969860523506562040786,23175295181692432017544178186553693977055040032⟩
def resval7Tail212 : Box := ⟨545696071951889594419704503777259123613014040763,14698624044553821251230964606042238951734391167⟩
def resval7Tail216 : Box := ⟨554311107078050268805250979509799922880390112933,6088017646163811476966759703872064279484721217⟩
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
def polyval7Tail5 : Box := ⟨21038297065388022539493896484293961176656540284200506044237,6416980957872349564104168115183732842465266452021098887256⟩
def polyval7Tail9 : Box := ⟨21370253826594377628057516007843465049946623927731716561788,6085022146990117314929135241709617438915451426291561451238⟩
def polyval7Tail13 : Box := ⟨21707450534962533976823810041974871625520500170177875330208,5747825438426569254158488862168324942089035146888408236567⟩
def polyval7Tail17 : Box := ⟨22049967798964412472003776133180101145245536267257551798544,5405308174424539820551135202236459665410255188837193698909⟩
def polyval7Tail21 : Box := ⟨22397889570324429875854917829395530909525701151409293020512,5057386403064521899892501618163445143104376948438203361347⟩
def polyval7Tail25 : Box := ⟨22751301125619278635375395130581163885929114767215073097386,4703974847769673134411295224276933392654379326439391512705⟩
def polyval7Tail29 : Box := ⟨23110289086986840919645111235490355690416108672341417408910,4344986886402110849946901463287558831629290828283306027770⟩
def polyval7Tail33 : Box := ⟨23474941443357365064463370523138974463117645011129517204874,3980334530031586705113029224945687031419680351670139928026⟩
def polyval7Tail37 : Box := ⟨23845347572019792320753231281108308761550063229174811300034,3609928401369159448820704623165987073860348975248688780362⟩
def polyval7Tail41 : Box := ⟨24221598260528374588095610986423813594791672708567855236965,3233677712860577181478337669066472947056002569884075374463⟩
def polyval7Tail45 : Box := ⟨24603785728954952034313623185523664614466155629758531590982,2851490244433999735264592084975258874531792149187899719868⟩
def polyval7Tail49 : Box := ⟨24992003652492344690390565841953078056249777224249849370262,2463272320896607079234875111944448575960606393415321378784⟩
def polyval7Tail53 : Box := ⟨25386347184414398174613848713487964842762027041323216902795,2068928788974553596108468703113584336452121117998738071490⟩
def polyval7Tail57 : Box := ⟨25786912979398311185983244215739774378768793839787046172092,1668362993990640654720738341169964289815291105915671528347⟩
def polyval7Tail61 : Box := ⟨26193799217214976962679078155029772460453657972374433307129,1261476756173990070710532486781496294409309042153117137447⟩
def polyval7Tail65 : Box := ⟨26607105626809060416885963971669655854827745338630424217087,848170346595106336426569066202779831895139233924307316426⟩
def polyval7Tail69 : Box := ⟨27026933646170544559139207364354164967365593143611123773778,428342457525707849738531963129578110372371300850625393248⟩
def polyval7Tail73 : Box := ⟨27531250000000000000000000000000000000000000000000000000000,2⟩
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
def pend : Box := ⟨1031242951779152789687124364393156552427818072318601681983013,3973735441686100542381924943791199338499379112420894114⟩
def zend : Box := ⟨1003785322519709633324453125000000000000000000000000000000000,2282793687388928906250000000000000000000000000000000002⟩
def betaquot : Box := ⟨428756313077821290729011615698528288879011096281781272871258,394783513726486191959422719967700462594820447949625486⟩
def crit : Box := ⟨144887488081129481601634758598559927205179439692001515165,9871101222729093517896360216375205945091976853593239751⟩
def subsonic : Box := ⟨448591236415566395991043040368935804381059284796703018684,4955519240911734329799293451468952609874902721910700626⟩
def pendTail4 : Box := ⟨27453649131928652645185721113164163254460621876129206248296,1591319858975920212344850030828255565252260662204103405⟩
def pendTail8 : Box := ⟨27453684779123861446437720211265424689068213843111175492646,1591192734909172889524984649193816945705829265113452632⟩
def pendTail12 : Box := ⟨27453684780669047838989751487733183974155756833085133123501,1591192719152086724959276677336976028935605704026792997⟩
def pendTail16 : Box := ⟨27453684780669810900500276205520084955082721262556024488306,1591192719139058663001317571403533568826280626621829208⟩
def pendTail20 : Box := ⟨27453684780669812743310795917250597498812870308068633743748,1591192719139010703704826726753711424303055852201633140⟩
def pendTail24 : Box := ⟨27453684780669812759092543280417248708344970048005587023289,1591192719139010082873989092395085193360517927562416866⟩
def pendTail28 : Box := ⟨27453684780669812759486845596747990878025679401769477240731,1591192719139010058585915866769875001837853947617756926⟩
def pendTail32 : Box := ⟨27453684780669812759511430742104646208157747470715366494772,1591192719139010055966707343408501848406977367052969595⟩
def pendTail36 : Box := ⟨27453684780669812759514452978594730386921718739617600901310,1591192719139010055228114564840015196907884251231004280⟩
def pendTail40 : Box := ⟨27453684780669812759514395786979488139757666702541962265728,1591192719139010054696659506119929212182196937637886476⟩
def pendTail44 : Box := ⟨27453684780669812759510985925819475216447556301375026988033,1591192719139010053722132053649616097296280631591490715⟩
def pendTail48 : Box := ⟨27453684780669812759481807296305250541359095236602437050040,1591192719139010049070117586662208199789212891621479580⟩
def pendTail52 : Box := ⟨27453684780669812758962829218033498184223039136895212308687,1591192719139009988428985632431564374815287089758174673⟩
def pendTail56 : Box := ⟨27453684780669812734439542306258344766311851091587954063170,1591192719139007713530657621856009809319994163608411782⟩
def pendTail60 : Box := ⟨27453684780669808997073621729744728168299678669762483648647,1591192719138752635922583591664943901196840979576520664⟩
def pendTail64 : Box := ⟨27453684780667402419658145156491314741118121825258641635261,1591192719015947941178413088995340327974400811751923277⟩
def pendTail68 : Box := ⟨27453684769829977244813684125955404856750980331584581310660,1591192308590095557510251752118756272813612042398732531⟩
def pendTail72 : Box := ⟨27452330279075186629869214911148874784634859735621262830749,1556935432315559913255638429763720929511305564725515395⟩
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
end SepticProfile.ExteriorCertificates.C24

end
end

end OAI
