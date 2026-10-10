import OAI.MathematicalPhysics.Transonic.Certificates.BarrierData01

namespace OAI

section
noncomputable section
namespace SepticProfile.ExteriorCertificates.C01
open SepticProfile.ExteriorJet SepticProfile.FixedInterval
def cell0 : Box := ⟨250000000000000000000000000000000000000000000000000000000000,250000000000000000000000000000000000000000000000000000000002⟩
def resval0 : Box := ⟨102582547731688995563114183812481135403149662023304065962,685127153823815540558229528600806027690585834042186584⟩
def polyval0 : Box := ⟨3683726382804299364674087011997467260102011189213813661294,20955809774943767350699113179183862293692891239038417485⟩
theorem cell0_lo : Holds Q cell0 (0/1:ℝ) := by norm_num [Holds,Q,cell0]
theorem cell0_hi : Holds Q cell0 (1/2:ℝ) := by norm_num [Holds,Q,cell0]
def resval0Tail4 : Box := ⟨46274628301322654355730638336008800599507735844651,2129807843822679603599924368261908971510299024894⟩
def resval0Tail8 : Box := ⟨4916767296214842074024307193438826143883669768,380622983713984158265647641726553636084089239⟩
def resval0Tail12 : Box := ⟨3930399635434527722280870097305659711854792,450882056423029501469704145993573618150181⟩
def resval0Tail16 : Box := ⟨13839559375833057002035211179384463293109,24300246384886628306483723492628667040266⟩
def resval0Tail20 : Box := ⟨165872563816831114269777320420875752255,353475625827663971726796242697122186221038⟩
def resval0Tail24 : Box := ⟨5808207664997541525753946754340042678,5655035033799782370917695182200116713837807⟩
def resval0Tail28 : Box := ⟨540765641936706676409183154312220544,90480533461125329095253606663292316444466079⟩
def resval0Tail32 : Box := ⟨124501084076881468608190585370892755,1447688531971935196224197443516723679652301467⟩
def resval0Tail36 : Box := ⟨-449723562153779024803436335389170961,23163016510167289220820510209948342045975325108⟩
def resval0Tail40 : Box := ⟨-133540251863876382160163189921104645311,370608264036901091491216453901688577289405078997⟩
def resval0Tail44 : Box := ⟨-34211643842760249795206985746499569112854,5929732192515824486842418143559467579536814947270⟩
def resval0Tail48 : Box := ⟨-8758265730458386722528022565548034396791952,94875706869372506296316065002935023789027863509565⟩
def resval0Tail52 : Box := ⟨-2242116727279310402910456714429535187219843213,1518009207925418547224884267225063120705649410838910⟩
def resval0Tail56 : Box := ⟨-573981895437711340504798407550126776506283369946,24287609218773522913009121522585610218357024422610083⟩
def resval0Tail60 : Box := ⟨-146939365060568920057504779330191642969540297679535,388463991844207639401644948771681356501438231502411832⟩
def resval0Tail64 : Box := ⟨-37616475360012359542698597041401410721393060105451682,6180158421998998212757380649364537358455110863195117509⟩
def resval0Tail68 : Box := ⟨-9629770728330505289324033416004937503295816322785861919,89854595329245163923061258268115386326364711821815361182⟩
def resval0Tail72 : Box := ⟨705634776211687774636548259560034187850310070652034453652,3485607835335301167815629414999317503181153540368826743⟩
def resval0Tail76 : Box := ⟨-21180236658695623081603158150326694710032286510668,737643822830447530859076358578491623783145277480⟩
def resval0Tail80 : Box := ⟨-1005214199020639352433016115865995015077464489,66266401615036858042167511796135980504325377⟩
def resval0Tail84 : Box := ⟨-499520354102162087459349405764420604308390,50722627140574425001999171921395560996115⟩
def resval0Tail88 : Box := ⟨-1214945087834574721280225949128946474123,319496650378219657786039247456417780877⟩
def resval0Tail92 : Box := ⟨-10643904031850465849552615047014455391,2306246923808323903243929955872823958803⟩
def resval0Tail96 : Box := ⟨-281988680451026524174595221129616774,36866252862992613495249300603375560157372⟩
def resval0Tail100 : Box := ⟨-20296140475581943053445678374650521,589858840381969798685849294842861952155122⟩
def resval0Tail104 : Box := ⟨-3725566848594983332849691711672312,9437741328940719105585190853129984400083105⟩
def resval0Tail108 : Box := ⟨-3373342183173131020791738289625969,151003861233112850534112321730098792339576117⟩
def resval0Tail112 : Box := ⟨-436709625456024901173190282492681246,2416061779319331793495828294097983219426514395⟩
def resval0Tail116 : Box := ⟨-111333626521749342826118450887664364919,38656988364732699373665013401631429949094381074⟩
def resval0Tail120 : Box := ⟨-28500182556279157160281257558286548060391,618511787116800513263057287718130301449020066989⟩
def resval0Tail124 : Box := ⟨-7296038762986636586319932641794243554111975,9896181753832539745570630423896380582684505990354⟩
def resval0Tail128 : Box := ⟨-1867785799108065845821604466846507574214451687,158337157012141750591954584499827376943214600000409⟩
def resval0Tail132 : Box := ⟨-478153162590064788823029003337312572137549676219,2532946243606354496056201410809676912021888633090063⟩
def resval0Tail136 : Box := ⟨-122407214474149367385929059888157065136732682556742,40412383136336882420038496593686607664118764931486715⟩
def resval0Tail140 : Box := ⟨-31336303959213516763711852488029802218420557449889613,617220366508761271194253087347498692548784499450698628⟩
def resval0Tail144 : Box := ⟨-8066400264572827763950703892430452042633966272747312633,2329543119054330566409637734071158346204480290714709303⟩
def resval0Tail148 : Box := ⟨43712860184518508194717503356480538330596421,1281688338081978673299187235210308234106491⟩
def resval0Tail152 : Box := ⟨684046128529241837417132869158352402582,39705019497088343948528426856932001401⟩
def resval0Tail156 : Box := ⟨190860807177768712234939745882983066,17520808377429393995543432333109902⟩
def resval0Tail160 : Box := ⟨293735051517881457092491989484619,40046597982515886963644427670960⟩
def resval0Tail164 : Box := ⟨1723985086116501478199027213981,22297568558942073012648250751083⟩
def resval0Tail168 : Box := ⟨31581108086223255378875803274,351776570386626144425631705160992⟩
def resval0Tail172 : Box := ⟨1598059388441385551378830291,5628302195824493066650349305828664⟩
def resval0Tail176 : Box := ⟨207177648429930353769237499,90052826793569534678233064635513237⟩
def resval0Tail180 : Box := ⟨71051485964218204027678780,1440845227232810702613358144502417124⟩
def resval0Tail184 : Box := ⟨1380186350923108842432737313,23053523634100016137940142511515501453⟩
def resval0Tail188 : Box := ⟨340527346611750095230324642815,368856377826312972161665848349773938603⟩
def resval0Tail192 : Box := ⟨87151654215281078409652981102481,5901701963516256978502695910338030826599⟩
def resval0Tail196 : Box := ⟨22310720292489167468819546643268735,94427210499959964902596105954687472711379⟩
def resval0Tail200 : Box := ⟨5711543284190975068741915018111165127,1510830013427557953290782560104558459073260⟩
def resval0Tail204 : Box := ⟨1462155056093360886369835781687484963173,24171909444480411679277100743035845953272160⟩
def resval0Tail208 : Box := ⟨374311697538202238371981662787180138663016,386399633897644968038445167450566465927060824⟩
def resval0Tail212 : Box := ⟨95823813707848180022515689956692573961976122,6092559324315451856388031052038271099717423973⟩
def resval0Tail216 : Box := ⟨24531928591183379412983995358042182111607013199,74482640794552626198863090626348235717460644205⟩
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
def polyval0Tail5 : Box := ⟨1782351387806974643811932156492517252253169593733632,60665708466793130717746310800368206249939645406704⟩
def polyval0Tail9 : Box := ⟨151793518050406904572776211137019690092383967807,10100877195985711612943948820568209501871262630⟩
def polyval0Tail13 : Box := ⟨104990028988185396642772861934289612635211961,10805589222339063485517699757175464041459438⟩
def polyval0Tail17 : Box := ⟨323945737936227940869837583798254702787319,409349881825077801347229036107855037950324⟩
def polyval0Tail21 : Box := ⟨3411577023730520867410868884063777119803,5791143661109214336801870489956795841473425⟩
def polyval0Tail25 : Box := ⟨104849765751798206546405944276930361147,92647329672025128662785201396161231838455178⟩
def polyval0Tail29 : Box := ⟨8537673094199308807400405980183666335,1482356818844813023640485755767707287903052762⟩
def polyval0Tail33 : Box := ⟨1758838335848985403290497232505342968,23717709051289639299474852201917089730545202367⟩
def polyval0Tail37 : Box := ⟨6374218688672550089439234708772955984,379483344804009045416831192663979281839353562409⟩
def polyval0Tail41 : Box := ⟨1413558635466317492381365479119260528362,6071733515538483934451429618999780158562265670758⟩
def polyval0Tail45 : Box := ⟨361614282397846653137431976885899562188954,97147735909601761656273676492164978726147387992909⟩
def polyval0Tail49 : Box := ⟨92572529502890142111330547011244380270955647,1554363687766881574103771972918272064937866713656179⟩
def polyval0Tail53 : Box := ⟨23698562534708726698756915427676263843052985461,24869796786867784826420181100220056765994224327417387⟩
def polyval0Tail57 : Box := ⟨6066831926988341327798176184982334136329245688871,397911060934958720689428948735554150774831059009943840⟩
def polyval0Tail61 : Box := ⟨1553108972137914216969579756476373038160141208381739,6365120935299470025962490938371416346548786614030498069⟩
def polyval0Tail65 : Box := ⟨397595900640159626963262335010298382567381583790397071,101469188809648342709306121755457014603219936152421167708⟩
def polyval0Tail69 : Box := ⟨101784595660892299417879822485496764446984762707609809830,1528083979464680442859249188877162498704528654988300277498⟩
def polyval0Tail73 : Box := ⟨26093750000000000000000000000000000000000000000000000000000,2⟩
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
def resval1 : Box := ⟨102385191290699564932418082607960682273421866808472157754,620875454990912722299270891590627766152964689311026347⟩
def polyval1 : Box := ⟨3666687901604004473083752404172622789350867160567159461081,15200025473485672202163028386570106797368309436289359900⟩
theorem cell1_lo : Holds Q cell1 (1/2:ℝ) := by norm_num [Holds,Q,cell1]
theorem cell1_hi : Holds Q cell1 (3/4:ℝ) := by norm_num [Holds,Q,cell1]
def resval1Tail4 : Box := ⟨44972665369187600390934591493747303070523801138008,3554394783332028341196751090313893484157016559026⟩
def resval1Tail8 : Box := ⟨4627826509312862624292697769208424125977131490,5952336081189189545884213979232478587372389813762⟩
def resval1Tail12 : Box := ⟨-314632300805663275436566047970542824900964196,18811297250201356443323888834114227376136616709888⟩
def resval1Tail16 : Box := ⟨-2085908609328929000754759405545243780912576858,59451907887668462803593695787229712845524758854364⟩
def resval1Tail20 : Box := ⟨-13670292775021803626014918497484709325238108399,187890310135318133972983955798128747144863573962519⟩
def resval1Tail24 : Box := ⟨-89589631685190118971559181219762581856821746703,593779780610574968117185076764419016682631375709144⟩
def resval1Tail28 : Box := ⟨-587134610244255052297648206556891430242986581658,1876333344180120826749178861811272218984243022065179⟩
def resval1Tail32 : Box := ⟨-3847845381699592580490424491310977367943491678936,5928147741906368740706884465792110530136836474526681⟩
def resval1Tail36 : Box := ⟨-25217239493507059528772926241794020420195571184235,18722818196873721391245030792924372709948605485388991⟩
def resval1Tail40 : Box := ⟨-165263700744648157074255861625036572502067080355302,59087786567280172627002599390331817663487441695387569⟩
def resval1Tail44 : Box := ⟨-1083072189200126406361844272828466027584205666737239,186185827423322763760248759470332647104523038743945624⟩
def resval1Tail48 : Box := ⟨-7098021899141947979756783100321956402959847057866011,584764179345374838335251943852773010718128184133833671⟩
def resval1Tail52 : Box := ⟨-46517596318216637064636938533018299567095934831126968,1824059237244700556799543171500349738200062597688978573⟩
def resval1Tail56 : Box := ⟨-304857719231061565501442793957590857241102042955828338,5607088816473956745842835890382776916996274600493776358⟩
def resval1Tail60 : Box := ⟨-1997915548751831618744617353175827414878571807564148209,16686754983845741355831828210478383244072227623061386396⟩
def resval1Tail64 : Box := ⟨-13093539339048456223014112967626609848589250950604021994,45959246540383001311159713556511970949037143684871473709⟩
def resval1Tail68 : Box := ⟨-85809797861737036957435781253329202174333902812095794851,100826145376459524567225125064994118694339083078771867101⟩
def resval1Tail72 : Box := ⟨708103962832573754966186546052334607514872704089053172258,2668869380906166005404027187213362553354747191223693556⟩
def resval1Tail76 : Box := ⟨-20722277632259774729726383975134258720082132107895,595815522026553308723994063280798444562891177933⟩
def resval1Tail80 : Box := ⟨-962181550520386878391737980202437911090568995,58169033927194977250115279611269122403376125486⟩
def resval1Tail84 : Box := ⟨-3055258970858095009183672469819999954312837,183683463967731259525525062857100753941300511562⟩
def resval1Tail88 : Box := ⟨-16961166516030191757299746336162361347425810,580521624805010359737790482740965290621071106211⟩
def resval1Tail92 : Box := ⟨-111149438939185518750765954813134470834087112,1834677464284338036792585162826395955125325726740⟩
def resval1Tail96 : Box := ⟨-728428901223965976181393360377362294097736699,5798109658883711293101331782949413434964746362365⟩
def resval1Tail100 : Box := ⟨-4773831645480673977223803025799147191279785047,18322418149501132537924582954804059065813114913058⟩
def resval1Tail104 : Box := ⟨-31285783071713675675617491728276555522465968023,57891691342527399378038912985156947189289509804256⟩
def resval1Tail108 : Box := ⟨-205034507938764305512981024214609391395958020857,182860177148275705780885916541761263012688609678577⟩
def resval1Tail112 : Box := ⟨-1343714151227478557952475479681696971399769761213,577232757256067632251157781360215854684634996310797⟩
def resval1Tail116 : Box := ⟨-8806165061484398004336900016534503416406380466701,1819781201361571750578417049441682440267688477452315⟩
def resval1Tail120 : Box := ⟨-57712083346944150518164354085109655690029263268828,5721527000656788857727747445469988421941277290800259⟩
def resval1Tail124 : Box := ⟨-378221909422533433495642366915277798897166152842390,17887027541255931480495614392486847584258464439990720⟩
def resval1Tail128 : Box := ⟨-2478715105591533224607501228898399809657173992153850,55248493034824365317692962039310587678659550555106715⟩
def resval1Tail132 : Box := ⟨-16244507316008355468456267394950411523009706506808977,166201977670987224147311931318049646805910536361046799⟩
def resval1Tail136 : Box := ⟨-106460003149557207976851020744195206408046336200673644,470160986441036158435116387441666223246038871625994723⟩
def resval1Tail140 : Box := ⟨-697696303967802595579236144578469994419474395409598590,1124710792272884978717190474747771331836526593662746125⟩
def resval1Tail144 : Box := ⟨-4590778889704873823130092054071033323745673711406579510,1181805097490665684956081748089079616290801693113318918⟩
def resval1Tail148 : Box := ⟨43084818031999463603077896889403482182345301,1066836864241116253552395579054908977107539⟩
def resval1Tail152 : Box := ⟨658673798006103483455682129906806524955,2282375790693103291506287997784156005307⟩
def resval1Tail156 : Box := ⟨267025475225381911150815888711723783,7116780123913588850853486221905167482770⟩
def resval1Tail160 : Box := ⟨571629083082810575480403104407794935,22492226340182387621486302328089590979409⟩
def resval1Tail164 : Box := ⟨3744457636999685040794142048830421188,71084603787813236171709681563319778982176⟩
def resval1Tail168 : Box := ⟨24539667454205556413427889379315003883,224649746140138155080513288903805284880611⟩
def resval1Tail172 : Box := ⟨160823164448428234586978612269006861110,709920870252045444267116123757516109843942⟩
def resval1Tail176 : Box := ⟨1053970690520507384445948699892499249182,2243154838131973909708720196429109140462887⟩
def resval1Tail180 : Box := ⟨6907302317394134621312262758683379635342,7085900784825303664609684801650952551181316⟩
def resval1Tail184 : Box := ⟨45267696467273896968440071958557045118981,22371508480181252295201166322403007905381908⟩
def resval1Tail188 : Box := ⟨296666375567926027347516742671852432552546,70551416355568156625381584911493204335751930⟩
def resval1Tail192 : Box := ⟨1944232758921959862644468529987456538617123,221970695378989609842789424881574766441137010⟩
def resval1Tail196 : Box := ⟨12741723808870957518918615254925502738348933,694940024380084127229728932940039956972164430⟩
def resval1Tail200 : Box := ⟨83504161153816788664947639584054324173921032,2153119635591522776332678847383948853384148071⟩
def resval1Tail204 : Box := ⟨547252870537663351628555178423775888968761004,6521582832756254598149906027494549006535606982⟩
def resval1Tail208 : Box := ⟨3586476412359710255189332820936310566853585208,18754535193114823370930740614803976678425074583⟩
def resval1Tail212 : Box := ⟨23504331826352832269604788869971781771470912741,47104297451772646447431569517387431408956152768⟩
def resval1Tail216 : Box := ⟨154038445223400104509774989905448261830198376327,69119998303606267546015437883264143314322131692⟩
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
def polyval1Tail5 : Box := ⟨1735761402148605899897589610592829623961434683066266,127284653740169985288803223282815908345350368410234⟩
def polyval1Tail9 : Box := ⟨146882634376803592993987053837784294921500595384,263199988343272051320227146783190958284133178062695⟩
def polyval1Tail13 : Box := ⟨14857719365615584683277206976665873670232905374,831813897168012684452638852596219519946605648434687⟩
def polyval1Tail17 : Box := ⟨96730759632478354672516018505347977337580399185,2628892596641260927387977500531803672308116265198311⟩
def polyval1Tail21 : Box := ⟨633932778586852152076473034677368674610774989619,8308270607172830438905806812723829496750797056708250⟩
def polyval1Tail25 : Box := ⟨4154541838029805708210583235053898590333821471155,26256086967134107643889743249364542076692433025847740⟩
def polyval1Tail29 : Box := ⟨27227205389127584614865566665973188182269103778231,82968103983460776377948438145714253033748962108128777⟩
def polyval1Tail33 : Box := ⟨178436213238141230092348727598758030800348279706607,262127795692262765018037348302491428035792508123638324⟩
def polyval1Tail37 : Box := ⟨1169399567077473842438600624351072645924501693098651,827847827195987113826639333650056796269969724889139695⟩
def polyval1Tail41 : Box := ⟨7663777002798928965657854916564981090273111345318752,2612440050791578037207036182937122666310610005601760581⟩
def polyval1Tail45 : Box := ⟨50225328965543057991564966241444866632652634190593226,8230596645298166857626184397547737290144355297085692763⟩
def polyval1Tail49 : Box := ⟨329156715908582985586706885303684686682241124653945509,25842330017566845881419071592578577742658992513713923494⟩
def polyval1Tail53 : Box := ⟨2157161453378489625668801364364644565054245822726878272,80557660815383359704449907661884516878286942949809819439⟩
def polyval1Tail57 : Box := ⟨14137173300861282415337354527010625200006364547890163371,247282511894237902491167163148038822782127029713906585135⟩
def polyval1Tail61 : Box := ⟨92649378944527211430108540509949383547863822910428692134,733565922412824874028480261753358353476883365790121281028⟩
def polyval1Tail65 : Box := ⟨607186969853429955825072912700840736803799407351100794008,2004061389993618687259453938900901738110125580342620475501⟩
def polyval1Tail69 : Box := ⟨3979260547197556713002055390510177506755717595473496047393,4273573789593898270208551024411432783185883541618639342313⟩
def polyval1Tail73 : Box := ⟨26093750000000000000000000000000000000000000000000000000000,2⟩
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
def resval2 : Box := ⟨102287969352116527208109156830296400011937884221126220834,609016999783864798528629096198753349918732960773591226⟩
def polyval2 : Box := ⟨3658266411879193638213173557033891822752598478547953331317,14062715789196134600526325274815926991329971992186033200⟩
theorem cell2_lo : Holds Q cell2 (3/4:ℝ) := by norm_num [Holds,Q,cell2]
theorem cell2_hi : Holds Q cell2 (7/8:ℝ) := by norm_num [Holds,Q,cell2]
def resval2Tail4 : Box := ⟨-153552125808742074443047828642130679532544012653259,34237512093624887118094685574179646469634507420980733⟩
def resval2Tail8 : Box := ⟨-454108970793079575812152079513054795494631463414632,58288784816865679727447050138613960508667889299563237⟩
def resval2Tail12 : Box := ⟨-1042007794565873558559416156549781113958926241611595,99170782989750245540590436600150964737977547112841041⟩
def resval2Tail16 : Box := ⟨-2390988517759212693162272452458695817497464106827451,168567608344330589544544477815265163906177758680571656⟩
def resval2Tail20 : Box := ⟨-5486356342587798186252358490062079945681096110823793,286161462377596817090555881932177667746418960064611333⟩
def resval2Tail24 : Box := ⟨-12588979701965718291081908979040015426584195551224026,484949323287570580288280383160072527481821299194839838⟩
def resval2Tail28 : Box := ⟨-28886641705403368473413895254867168480493891554872262,819891737738636903460028368263606979480486495125331471⟩
def resval2Tail32 : Box := ⟨-66283216652264107727132052861558629271002265244781750,1381695226580884144994450749435439422064218933427343752⟩
def resval2Tail36 : Box := ⟨-152093305084653218326826706949255614699302564970106284,2318093993325582201593548896535012208198529595876822744⟩
def resval2Tail40 : Box := ⟨-348992921887463090146559097354555179376481386672938612,3865037554700760266742200424436867465318728964675361532⟩
def resval2Tail44 : Box := ⟨-800798295886585941462310684040834901467395369675315592,6388151655011107881628734082638842155280268621323672771⟩
def resval2Tail48 : Box := ⟨-1837509790246255250998438136484895845376785217726156858,10426521446270593517876956831356582946175293528072740199⟩
def resval2Tail52 : Box := ⟨-4216345422554482795424712305670893177840168717888972653,16705550431161890564039620478576584266121701636394404650⟩
def resval2Tail56 : Box := ⟨-9674815784199800737786664767743418396271972851341288769,26017014876700764451029372630147751331983662239081883423⟩
def resval2Tail60 : Box := ⟨-22199808383225303983221835058527866906943922421490742303,38688878991637927697051611940258364928310821332920387187⟩
def resval2Tail64 : Box := ⟨-50939625439386641657538674714900564896379816874302592341,52933787090637352237547579847411083361375713107121381738⟩
def resval2Tail68 : Box := ⟨-116885921679318298087790566876898005992923653574722516802,60317515270318919088004440858856739968002058989899540559⟩
def resval2Tail72 : Box := ⟨709337138190311857413216052273967169593448966930040550304,2260904231170828871948438743693981540134587695333152242⟩
def resval2Tail76 : Box := ⟨-22593150046264385526393822780665532067133112840532,390251049078917473163397310218800851883542906001611⟩
def resval2Tail80 : Box := ⟨-4798230293865136613908747654156294767215099769146,663933419169291776225677494679227121305256251085658⟩
def resval2Tail84 : Box := ⟨-11007847240610961129941988274321864594229261265134,1129817170144977018144677288350772349828638497472614⟩
def resval2Tail88 : Box := ⟨-25258578029848431496761543904272778702175547951117,1920938535369584182266555930129027562209426899521346⟩
def resval2Tail92 : Box := ⟨-57958270708122622715777127901849019519033777314994,3262168083510717069471575690907870037739954800591687⟩
def resval2Tail96 : Box := ⟨-132990904699658360764616550348032379366721335328113,5530998077757787424571970859197242020597993339186896⟩
def resval2Tail100 : Box := ⟨-305160601183319765045168230663367941767644405318074,9357354547565408637114913862143726118910790541903279⟩
def resval2Tail104 : Box := ⟨-700220761148070556656779223078961141345809192936245,15783603499274583113523139017549673802551035523839994⟩
def resval2Tail108 : Box := ⟨-1606724827653091693366918570396392706221017552802769,26513951628278265832824772784889556270017909206291480⟩
def resval2Tail112 : Box := ⟨-3686786817866076719095796747529188822919641486907577,44285845736692374102382755622243593217644339022350762⟩
def resval2Tail116 : Box := ⟨-8459691918898890230413524696328328518718066643825269,73379501310368671019739092258658333630346113946589010⟩
def resval2Tail120 : Box := ⟨-19411588165573952960373116272219301418318530607019327,120202462424630099887541116038073670910501805200050353⟩
def resval2Tail124 : Box := ⟨-44541782221177640474222997332243688908651747744474953,193633624366692330710345900354614879708749450115550155⟩
def resval2Tail128 : Box := ⟨-102205463381782791863380901217684413203369142723317238,304111265224595977630622534194038400496575612878218236⟩
def resval2Tail132 : Box := ⟨-234520403633927573566708404545782176376486854950059093,458637997187285357571582564270528848911503717843299304⟩
def resval2Tail136 : Box := ⟨-538129938469620880429954620273754767782217015720553424,644367691587921264876295361091258994800476369202672658⟩
def resval2Tail140 : Box := ⟨-1234791648199196713790197226429566237379486122452104061,782497119268026605913915328830320283819899851842604986⟩
def resval2Tail144 : Box := ⟨-2847550350971641041051949542045295921663677011142170202,604939510598945728869660145953261133690716772476431909⟩
def resval2Tail148 : Box := ⟨42972701564150178342258271535835201322068255,35358701600201328351822018363862929474728373⟩
def resval2Tail152 : Box := ⟨441949446187515508850063827461741149227220,58622004206647821389922046112760085022311538⟩
def resval2Tail156 : Box := ⟨1012612257989785522023081698275518905589922,99746752156548259413177458016066109811970314⟩
def resval2Tail160 : Box := ⟨2323537183192344473183388269013021273069218,169567489845340993471174408335738340993458354⟩
def resval2Tail164 : Box := ⟨5331582676400836958738222210399486457601212,287906920742067131043317216228830604975802653⟩
def resval2Tail168 : Box := ⟨12233836430114822902695075447517444282528089,488018104428709939565311277984483475869685417⟩
def resval2Tail172 : Box := ⟨28071730831693686087634940735927176519542544,825335995014931098987194468681484446675283880⟩
def resval2Tail176 : Box := ⟨64413324175829884573566703824787982643651297,1391462579642485448123330652666727509071785165⟩
def resval2Tail180 : Box := ⟨147802654430418658538768267315988907602138716,2335857363078877302308623366975664601191484265⟩
def resval2Tail184 : Box := ⟨339147605502325450925246862159926321710464743,3897866735071633839128418397766358140606936860⟩
def resval2Tail188 : Box := ⟨778207257245908783001090174098105966674430215,6449952150913581950833632830546416059322482954⟩
def resval2Tail192 : Box := ⟨1785672448824196561960105344539698144262102188,10545248390751511078918603387492453867012758303⟩
def resval2Tail196 : Box := ⟨4097399587064267565851886531208134342037461120,16938606976410159131021382720548262406013433775⟩
def resval2Tail200 : Box := ⟨9401882964106433300254102737769759986538899792,26484615529850772803769152920255894150640588608⟩
def resval2Tail204 : Box := ⟨21573537408903030391554671363977823201347934886,39647244694907352179912056810643009109874795991⟩
def resval2Tail208 : Box := ⟨49502585610796705622278168151306693305263735496,54937365866592974882928620675820604529768075126⟩
def resval2Tail212 : Box := ⟨113588510585218450178337857798094284104378558160,64581435797646785631341459940281874610599674479⟩
def resval2Tail216 : Box := ⟨260640272148522239159711664614894978860245924736,43310056679692063054465023849670893156623847142⟩
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
def polyval2Tail5 : Box := ⟨20959035437367910429200625591470906852714969462920852,2951965455369997426092444578794335767164136019224048580⟩
def polyval2Tail9 : Box := ⟨44160801881167030735453171571506148180901202123368714,5024559820715468259628614307660685274648460061953458627⟩
def polyval2Tail13 : Box := ⟨101330942657066826940315160893462644229202634158159678,8545682417001763257376684283010745402641099493509742710⟩
def polyval2Tail17 : Box := ⟨232513730323897962320665178686572392043489366641763023,14518909310392008318109780209377918030556053619464957692⟩
def polyval2Tail21 : Box := ⟨533525430849360357519586731229747687821594192994503841,24631751026781262923885225070780575074903199609863526394⟩
def polyval2Tail25 : Box := ⟨1224226134804225879373359381016955197637220503825047260,41706624498454841282389452458554410493815974779799609170⟩
def polyval2Tail29 : Box := ⟨2809106262754446338835028552084754165585066967344410569,70429029594733741379280547287825745327515977800856312060⟩
def polyval2Tail33 : Box := ⟨6445768286680277121484023601485324963953266962178219174,118495258149084661180509659138346854145438754552358718397⟩
def polyval2Tail37 : Box := ⟨14790443977307469674270666608385197899104166034918309080,198353431191744253474075349814858471620745141184000235787⟩
def polyval2Tail41 : Box := ⟨33938116189798057930495999675772311599003057667370182346,329675924914923249030444900228196156426566088169425458436⟩
def polyval2Tail45 : Box := ⟨77874317517405046200799761523163399314978686272786992709,542435183675822139684453028091282229882392065871375702453⟩
def polyval2Tail49 : Box := ⟨178690216477737372922888441568759799918922105346923484977,879530406965602299460115797765472593198558022057308156606⟩
def polyval2Tail53 : Box := ⟨410022129025069026907385448803277629182818299222100433041,1395255535957821143156130223458875233279421247681634242230⟩
def polyval2Tail57 : Box := ⟨940835763726302443171490782597277816125932365656337341382,2138888232845925025954271043412587923377130541898753820101⟩
def polyval2Tail61 : Box := ⟨2158839417792339969252216641126897597361582003077504950541,3095033755868571014364578409800644593883173478187582152912⟩
def polyval2Tail65 : Box := ⟨4953667591628384933371664542642400550943182920013573953602,4009208093218983587883786717853973683110042586986190621971⟩
def polyval2Tail69 : Box := ⟨11366673427805461349766180857317873581226582669250469601291,3923596807624956491201176563548983447110861691759723459772⟩
def polyval2Tail73 : Box := ⟨26093750000000000000000000000000000000000000000000000000000,2⟩
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
def resval3 : Box := ⟨102100740436200336810915876318835288381435081646806558297,2226813857734150394907151362177751622557488472647812162⟩
def polyval3 : Box := ⟨3675852936577879434077465309708622277448646203592035179155,237830075710049057162729592935002000618818450071567878054⟩
theorem cell3_lo : Holds Q cell3 (7/8:ℝ) := by norm_num [Holds,Q,cell3]
theorem cell3_hi : Holds Q cell3 (15/16:ℝ) := by norm_num [Holds,Q,cell3]
def resval3Tail4 : Box := ⟨-206210651261373092812839729690106034169608964954174471,2115908165300321749103942188854064505663149840928323106⟩
def resval3Tail8 : Box := ⟨-305781899531049069333119815157581574755772557184569294,2700345099833030073598340845406102548285533117420251100⟩
def resval3Tail12 : Box := ⟨-453335471773930982475628915996865581722995364288809514,3438210983758584728252515637669450533682578378296122628⟩
def resval3Tail16 : Box := ⟨-672090294599253021941098266948743138067246612515136170,4365665527820285320694117437404886164167076673732861938⟩
def resval3Tail20 : Box := ⟨-996404191190939034734582095207041082558598066073451828,5525163523931777906170365974866138083724373604243701331⟩
def resval3Tail24 : Box := ⟨-1477214178215207572905401026594818382344090810702628843,6965204819874321013450616259379554294104005923781426321⟩
def resval3Tail28 : Box := ⟨-2190036681511576728920153595388639441287078229070763162,8738997816439936271465713384257112948496065641649096697⟩
def resval3Tail32 : Box := ⟨-3246828210220100752685283318664748430834435978078022273,10901225219068795168425923435905405185954656704254479335⟩
def resval3Tail36 : Box := ⟨-4813569341407096142702509271431233656809752802479324429,13501627291518870930607641843837406815159769179955457645⟩
def resval3Tail40 : Box := ⟨-7136333770785992052573816480932455420861315673248149576,16573389222506574428685806277095451593966134917655473092⟩
def resval3Tail44 : Box := ⟨-10579936856830160010581307765249437957215307475501586751,20113206967138662446775414231749614926690435611052018288⟩
def resval3Tail48 : Box := ⟨-15685233831514690571797890042816685183097274392448878299,24048215524487694582925767956309362127077650712964619754⟩
def resval3Tail52 : Box := ⟨-23254066983439889035454564207821740784254839639575815835,28182403870781786245171702194570814013368737463203458496⟩
def resval3Tail56 : Box := ⟨-34475203690227029055613187006596525027113991310988608134,32111276386854878050021597475121605850348230394627129219⟩
def resval3Tail60 : Box := ⟨-51111045234755403747236006861478492698072196657417663855,35087701596486045386327404246220987093727783144929214576⟩
def resval3Tail64 : Box := ⟨-75774431049938027826643891656659942209426150773356507825,35813145686375053965370899872339888409128480560669191133⟩
def resval3Tail68 : Box := ⟨-112338998209159604836626759536372131338510776383733872889,32115372733349463884132850049729616532190785467234851839⟩
def resval3Tail72 : Box := ⟨709951742063465258719718050565004207687516197607880304906,2076712787719470400303802538080524478365905150885564593⟩
def resval3Tail76 : Box := ⟨-2449941989215194293963429488664639711911891422458341,25883243250418858219745048047629590279235701346757884⟩
def resval3Tail80 : Box := ⟨-3601914398065671478248145325463902400774710738691053,33049582392534709742900136854479467183545717668434372⟩
def resval3Tail84 : Box := ⟨-5339999257817366617546280667063917667353544074662428,42106764802643227516239841837996998823554380046741142⟩
def resval3Tail88 : Box := ⟨-7916789877429433661357674648862383813660896981725184,53504862062039133848763483896232609019675957726609790⟩
def resval3Tail92 : Box := ⟨-11736998254603699368058001044712639471014576327189397,67775680886234594831204443946792254224716196680653369⟩
def resval3Tail96 : Box := ⟨-17400629568473237157770073732394716615218103668300261,85531576657185583929203162897111041683205426766575282⟩
def resval3Tail100 : Box := ⟨-25797218574217875079963564760542986691782612493956116,107452461765629561609496573912440641355936048387280245⟩
def resval3Tail104 : Box := ⟨-38245540688466228508603624804184678214290850980641377,134251270190590395881439691511058424846384547449971135⟩
def resval3Tail108 : Box := ⟨-56700739978804978534222792851256067615550936495343410,166602983433932896741515202069745923772158463943363019⟩
def resval3Tail112 : Box := ⟨-84061405755301512653585948342265767454359159719288742,205013810394371364264967934371132139517544623203088661⟩
def resval3Tail116 : Box := ⟨-124624827474894757434584697224590747836249875339928619,249594103203326707488004711188108778774425091691383136⟩
def resval3Tail120 : Box := ⟨-184761930681462170172439730783626757146462110690874695,299678797040570855514859154864970103500726553563471049⟩
def resval3Tail124 : Box := ⟨-273917899994832148402147935795053907882351635478506842,353209162365486989955299906625310633661450295653817941⟩
def resval3Tail128 : Box := ⟨-406095647847151451584068653828765700039148461784669972,405744335537458435747851803114439695935911481268627107⟩
def resval3Tail132 : Box := ⟨-602055123829109927000751403037024954523179549956178322,448902805081386696460381496058410870338795595769484591⟩
def resval3Tail136 : Box := ⟨-892573890046515431325820603262615224146961590541885478,467931370776556838384623737560977276752057037598795207⟩
def resval3Tail140 : Box := ⟨-1323281090754360127898945030375810458570864854296946709,437945052998591881571391022750853345886792577902906485⟩
def resval3Tail144 : Box := ⟨-1974580540976450956960019806822499892582310491925492011,315756820301573063216590737946826178389987225043994930⟩
def resval3Tail148 : Box := ⟨444405988142592528026934257604501654367474185,3933274576720027271966966920944893742145984902⟩
def resval3Tail152 : Box := ⟨595651009488825169185697523850806283909671629,5015200404252801544396270445360859403570022732⟩
def resval3Tail156 : Box := ⟨883078551442071328437185994398814749931014076,6380382484956753568954489272325704829149792196⟩
def resval3Tail160 : Box := ⟨1309203802981114697185301165014454765138957612,8093624492714446923632767296694544392302885857⟩
def resval3Tail164 : Box := ⟨1940953718415253029375910699187942659222199583,10231367371692133157647797011927495256111922036⟩
def resval3Tail168 : Box := ⟨2877551477052247791318615584703436210845211689,12879984028355703969834690413540891262436098474⟩
def resval3Tail172 : Box := ⟨4266099920118789780082349504027972870538156784,16132632857805467499184791814202015734562789402⟩
def resval3Tail176 : Box := ⟨6324685648050039674851848712785809404778890502,20082254625215029460212710916193824183129898670⟩
def resval3Tail180 : Box := ⟨9376631887594489887289503283667812661151517143,24808162932132909042574563887688991611386758729⟩
def resval3Tail184 : Box := ⟨13901279913027891075866785466792973574024119181,30352245288071463319480581548248384302752549273⟩
def resval3Tail188 : Box := ⟨20609274794718271680949755165952297765183351418,36678607231538464904767982194042851407478916055⟩
def resval3Tail192 : Box := ⟨30554179918796781542603432823219033966092748702,43607175863381223176068753774879293461457107628⟩
def resval3Tail196 : Box := ⟨45297950549402930383289459534534430065138727625,50706762784736678847259209057163866231715345946⟩
def resval3Tail200 : Box := ⟨67156255852045689314001611902818821046782252557,57125519813458971087058656665077546645150310590⟩
def resval3Tail204 : Box := ⟨99562179863893793549729626324108409185656066814,61325335198121291463045269656358305266155128462⟩
def resval3Tail208 : Box := ⟨147605424594983422883300614983711903854551169010,60669621076213172507890313634063491813481510262⟩
def resval3Tail212 : Box := ⟨218831702965866883182761570143277198063571697098,50788314681232210361004472648470648501128118591⟩
def resval3Tail216 : Box := ⟨324428196319428620885117206553691683355684180096,24605485056519812394030473034378466429263238651⟩
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
def polyval3Tail5 : Box := ⟨32303392272691147373699779929007355806210068505682524358,291619815891206711156829222927070758308316960965686036209⟩
def polyval3Tail9 : Box := ⟨47888712632014524164444647257557228744305165214446761655,371440042394178680233239543062470677746730662750257151206⟩
def polyval3Tail13 : Box := ⟨70997177345891295200229540049523380300379668490290855008,471839944233665523082742298385382812627776113310101749666⟩
def polyval3Tail17 : Box := ⟨105256519307811023762398860806613367141076159386975781515,597466909824661851093026836961195297610481266060756540044⟩
def polyval3Tail21 : Box := ⟨156047539789287376004778083355827918025035622039207326720,753654833576159003487151601716721045217420285588497660976⟩
def polyval3Tail25 : Box := ⟨231347519701634564929747477306053013957263542161865078236,946297018389780619788606564071041056757466848457117720993⟩
def polyval3Tail29 : Box := ⟨342983137987110024833775715411246263642225059803889645083,1181522786918746479654162350238374623465647490357303197084⟩
def polyval3Tail33 : Box := ⟨508487979880658297613412541345213613811862743037000708322,1465043285198456998735282492955661824293686311632888191311⟩
def polyval3Tail37 : Box := ⟨753856376731937030794549960151643494515408969385023851004,1800955376121888155603891277618284503307433501177410997863⟩
def polyval3Tail41 : Box := ⟨1117626097814118580878430627462999967981258199967126560533,2189675493001254997704780398947345658467787373119491589894⟩
def polyval3Tail45 : Box := ⟨1656931125170246627668110588428219228087580673051119634482,2624497359880149872993978150176990396002412750240440082660⟩
def polyval3Tail49 : Box := ⟨2456475165466789759459299420575765225557174941986688074803,3085997865570499822122275162265048257052863486691486348420⟩
def polyval3Tail53 : Box := ⟨3641835286264588669780371168749490326751758482470012027955,3533108171751407577606308841034454653369073384390690553731⟩
def polyval3Tail57 : Box := ⟨5399185157144299559464277914080383539850509676563910449942,3889053745858887214266616569932205467745966983390643961499⟩
def polyval3Tail61 : Box := ⟨8004535644726413599433770024142753916837009636802533285790,4019445091021081133505003985198379887622145129554485128852⟩
def polyval3Tail65 : Box := ⟨11867085314331910468237055688403585663910384330176298749269,3698417925135088847706697879161513203901633195807029389804⟩
def polyval3Tail69 : Box := ⟨17593489520382262685740515757640506840898068145782770604610,2556650151718720981566095522527480087517812983531246044761⟩
def polyval3Tail73 : Box := ⟨26093750000000000000000000000000000000000000000000000000000,2⟩
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
def resval4 : Box := ⟨98330374935353058496853825787839408913117777692666872671,10405972258449937896316676148966942697813690637951736099⟩
def polyval4 : Box := ⟨4474516498171206875851395807809278510771467061795331188834,1838636147478048965426992848923243457694188441431755683515⟩
theorem cell4_lo : Holds Q cell4 (15/16:ℝ) := by norm_num [Holds,Q,cell4]
theorem cell4_hi : Holds Q cell4 (31/32:ℝ) := by norm_num [Holds,Q,cell4]
def resval4Tail4 : Box := ⟨-4708055333427727651962379755201977123802306918673804036,10877525849175467478524960023419752769623380285263276950⟩
def resval4Tail8 : Box := ⟨-5704875403233135802522927121939735560780553635283278997,11991214967207164404679833653735745445690341039788855647⟩
def resval4Tail12 : Box := ⟨-6912684247085295092477060118219937008087831624101448071,13179653296675132696251928583087487230884102726051860608⟩
def resval4Tail16 : Box := ⟨-8376204576753769357436545178793881882191797926643723579,14436858615409131051981026069703131480995270006345722971⟩
def resval4Tail20 : Box := ⟨-10149574406089652506419366015996104409380605667148715552,15752630903573491296034444313185436163864390646370728155⟩
def resval4Tail24 : Box := ⟨-12298393583967764589702054972636138711923616266977043338,17111257993836465947178468481819654848017479155863920814⟩
def resval4Tail28 : Box := ⟨-14902150444399969899086639851420539929286912555519516674,18489894579857896292013402922353698980518377171011266755⟩
def resval4Tail32 : Box := ⟨-18057162209951297678187080644761391148824679839093747764,19856536561767175750557953971082715536162617336573279655⟩
def resval4Tail36 : Box := ⟨-21880137923250040978229613152759005388324701416674769370,21167496730703112219172422890347900564414545976524434062⟩
def resval4Tail40 : Box := ⟨-26512495705255994164641371935550995912192910232128827434,22364266766743648038478099602076721464707889694391404965⟩
def resval4Tail44 : Box := ⟨-32125594042727498415825014604853458742563678795624996321,23369624892022763703344752693458236800211630877181895080⟩
def resval4Tail48 : Box := ⟨-38927070618762158979245350954433233971009831830100971270,24082817288199015536496155672879842885051963810742381108⟩
def resval4Tail52 : Box := ⟨-47168523170114866504624211898062512703713418388740372850,24373603345611056875650840523067201164968002146847097409⟩
def resval4Tail56 : Box := ⟨-57154816498761023407041317431528499084727602839455793164,24074908492174562170912246850448534723523642918898414806⟩
def resval4Tail60 : Box := ⟨-69255359919276031025391632513857013609661007964090218526,22973771970626351038458541534834287111438076584586420651⟩
def resval4Tail64 : Box := ⟨-83917772312371830347775808397670506718094951028899690651,20800208328662477475108407645910878943381994016544449895⟩
def resval4Tail68 : Box := ⟨-101684425689512340882253733486249018694916554059859213466,17213515298660842564200722570440888399592877663728281244⟩
def resval4Tail72 : Box := ⟨710213306029624894715296262901507307946494679766637954870,2077628478320637806121773831807916402741917830396167875⟩
def resval4Tail76 : Box := ⟨-58315984804083222367545119404833185726741562940055231,137820723772671887703652231711965803679018755820750258⟩
def resval4Tail80 : Box := ⟨-70637718179053003410325844969904770947797346016282755,152034528499355537339409554914442998885489827132518690⟩
def resval4Tail84 : Box := ⟨-85592795705930538041841404344357800183882897643978513,167231745074976055971970794817318490874512180239717387⟩
def resval4Tail88 : Box := ⟨-103714091588575729936662820157855295562374694789603271,183345699876253045927983106765912263804343234881779942⟩
def resval4Tail92 : Box := ⟨-125671941258411169138672314640350916328826876459588600,200258934049267953538973589003708184120124858473210766⟩
def resval4Tail96 : Box := ⟨-152278601468244208459343029627028823548256741447669541,217786934135845935371052448898870342386540726725612148⟩
def resval4Tail100 : Box := ⟨-184518296072492109552429967547353929689481398405690730,235658222990522620376013602723835412450816215594873649⟩
def resval4Tail104 : Box := ⟨-223583624076006056984355187584027897121242734332028581,253489462137539421062813438577757795534030357548733236⟩
def resval4Tail108 : Box := ⟨-270919675820772030771307655549954736307871162434024313,270754404627268309606246030109332866041667588340038617⟩
def resval4Tail112 : Box := ⟨-328277489239914689689565190267630711076581499690103906,286745277518918458609949491037874523290657923304190655⟩
def resval4Tail116 : Box := ⟨-397778823613222524403900657634145076222871124920031957,300524856191470847280188049047316244603581689132081572⟩
def resval4Tail120 : Box := ⟨-481994646911295222022972516968005209537887329792957755,310867106481303491934046734537822267194030633293564883⟩
def resval4Tail124 : Box := ⟨-584040240103474594541329247627677839074527639212976363,316183800200316644892945328590103270647644769702367718⟩
def resval4Tail128 : Box := ⟨-707690436493374135340270275367126726091385291124582456,314433936732127192355232347169100180301422300490731141⟩
def resval4Tail132 : Box := ⟨-857519258973410025163824001443520539873283459016494791,303012106073302541963820633933438653457810262996115491⟩
def resval4Tail136 : Box := ⟨-1039069120611003652917717725115250041277041377934403055,278611080095661031903813824047860131611560088314141262⟩
def resval4Tail140 : Box := ⟨-1259055866213033438395685690128101527572554077326772712,237052882267976445462025348524281692086598447242846699⟩
def resval4Tail144 : Box := ⟨-1537756605284913943117525653099393890638661029933855253,170977927671976461913253712579322526762284186310667872⟩
def resval4Tail148 : Box := ⟨13758336687406318474716739999058150956580160926,29319060807388230178333253973165430148656142756⟩
def resval4Tail152 : Box := ⟨16619620528563236208966656693295515984180576674,32241677399233766173827556866289617938660655481⟩
def resval4Tail156 : Box := ⟨20138246043860185964863302592069138645117110854,35339413527829243595049468326601640820505635223⟩
def resval4Tail160 : Box := ⟨24401818837593028718116071849899043530122310647,38588131973330659756784740070995152001887000134⟩
def resval4Tail164 : Box := ⟨29568054799355484266350400994545748784615592063,41951434916108303448806203508423878433807978646⟩
def resval4Tail168 : Box := ⟨35828061442322181571550936599275347875720303967,45375961474192066644461144389447223507557121791⟩
def resval4Tail172 : Box := ⟨43413406645295925427465818125734054050806162221,48786542823862701510015136432062566376668398535⟩
def resval4Tail176 : Box := ⟨52604684726912949874148718509106488231226815465,52080161870589950870017747370039445615261726454⟩
def resval4Tail180 : Box := ⟨63741896088169694656605381629362100895354981388,55118441365795295474143958712671766988354504745⟩
def resval4Tail184 : Box := ⟨77237024383046000016005734416576307368115423886,57718322821975643770430471677062619158013370280⟩
def resval4Tail188 : Box := ⟨93589276467325421417504250721215127080288568884,59640523559802034433511248992138652584434036127⟩
def resval4Tail192 : Box := ⟨113403548876231897897339523286232889907123604745,60575267840708159931848380750195709353757551635⟩
def resval4Tail196 : Box := ⟨137412803936077253605967095999265731992344827493,60124676768511096934334690649080434229888850292⟩
def resval4Tail200 : Box := ⟨166505183238867055996479105693391242667871599724,57781066199201417051504938738283244679166546769⟩
def resval4Tail204 : Box := ⟨201756861451612242056369321951842516948217547786,52900237077573441629450756024124267087605112814⟩
def resval4Tail208 : Box := ⟨244471855776461172331901673129472099390334212345,44668642108634368881002340434749699153848751332⟩
def resval4Tail212 : Box := ⟨296230263685795100277006484836161017995420427975,32063068805052899699529419246247124117621598532⟩
def resval4Tail216 : Box := ⟨358947019651479624269810767447250550434472742372,13801118327554288444726149566735427571020166708⟩
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
def polyval4Tail5 : Box := ⟨996689186731046905518500944929853997911328267183285964355,2014890700220938375714753814199743577947537577957059997579⟩
def polyval4Tail9 : Box := ⟨1207701380962873542539377708154954481802748883375876902668,2211677912901176355667573945443973249955692721207939356354⟩
def polyval4Tail13 : Box := ⟨1463390120512188435647736902997250522793301267260207546965,2419011105114960265661512061558944369261981167472397021869⟩
def polyval4Tail17 : Box := ⟨1773212052926035359998364444539944476559982002425161356741,2634909416497086830605950022732749386059118201608374017026⟩
def polyval4Tail21 : Box := ⟨2148627997804071469075519547982414138598691937595076085964,2856402075060345762632619442346825430293736001427663601572⟩
def polyval4Tail25 : Box := ⟨2603525204630504761039069124702721420736571212862064319255,3079241525832450775414984358717029913185354311405753948313⟩
def polyval4Tail29 : Box := ⟨3154731064695180203478812134880567918183552996441366934910,3297545393730696484217457186528465043918187818514312067869⟩
def polyval4Tail33 : Box := ⟨3822635583804624972408682954201967735783422212900390283886,3503350765905205203267279130666942080256258577676816864672⟩
def polyval4Tail37 : Box := ⟨4631945641927875306460769888573235249289473176533633997108,3686060621744888914697444179631785310147484881030867609561⟩
def polyval4Tail41 : Box := ⟨5612598941074263415097555899306235476253247916173371636381,3831757750259157715515296507319033275523518998947047009659⟩
def polyval4Tail45 : Box := ⟨6800871449829171760386535310009456467391423293834537651214,3922356026288462159636339196600647600273109094154480330236⟩
def polyval4Tail49 : Box := ⟨8240719310731444751187956750091034668850740991562960662295,3934552257535572571997458776638605291158386227981961439444⟩
def polyval4Tail53 : Box := ⟨9985404849839931470061150880216743637606939688067348527782,3838533707017092849664363253642739049438266449944917913110⟩
def polyval4Tail57 : Box := ⟨12099466837241023917913676089269367635162663892501181707806,3596386528513421448729009458664830780699619696611883720614⟩
def polyval4Tail61 : Box := ⟨14661107881654103224179219908904219678477510298191943504333,3160138347559238543970356243665996113947660496753456416955⟩
def polyval4Tail65 : Box := ⟨17765087272765773444322684237224109395278975246672018578793,2469353618177516603673393393041972937949906860834399185873⟩
def polyval4Tail69 : Box := ⟨21526226296967239367212866124059013063418690153371787990061,1448182625265269242591201084877548413335327563591565203818⟩
def polyval4Tail73 : Box := ⟨26093750000000000000000000000000000000000000000000000000000,2⟩
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
def resval5 : Box := ⟨83482564732975134715997949216436213626676826202402298437,17371447499586381495480885894670077512781261419084343519⟩
def polyval5 : Box := ⟨8379997484487888635845806271888652468703734617403499797163,3673898675932179916772807638077798965344107049630881395164⟩
theorem cell5_lo : Holds Q cell5 (31/32:ℝ) := by norm_num [Holds,Q,cell5]
theorem cell5_hi : Holds Q cell5 (63/64:ℝ) := by norm_num [Holds,Q,cell5]
def resval5Tail4 : Box := ⟨-20584259030421545336759634429414256487133553486967498011,17257886242485234935548706379880509463618167183095776239⟩
def resval5Tail8 : Box := ⟨-22632680337649968541606374114136547717275047871187526897,17670000504149979693023538939124025910452106408629586150⟩
def resval5Tail12 : Box := ⟨-24884895203898356834515522897939379857880293153158999527,18038259492758592885756394293478931655695580752401689775⟩
def resval5Tail16 : Box := ⟨-27361231632677217527337580570139415114738136413027156830,18352779704447363164039697755023702549722069964131500955⟩
def resval5Tail20 : Box := ⟨-30083992330401122127465456796319969074923728570447421043,18602336698750164447542583634911529223779609177494395735⟩
def resval5Tail24 : Box := ⟨-33077699377200037542225821875545440693644755411448795655,18774206964035837627631188164035199744489773004163588899⟩
def resval5Tail28 : Box := ⟨-36369315085310394703669610446866422526598500411705669095,18853993897596627330123496168338553060267930395854803022⟩
def resval5Tail32 : Box := ⟨-39988484830547864387185907885083441293062248493803933571,18825434853565580480771349534307481802659019869044126400⟩
def resval5Tail36 : Box := ⟨-43967804048331565902283505991601736184552750810044838950,18670187269429141627793855771417405898045063618178895492⟩
def resval5Tail40 : Box := ⟨-48343111798917242602173573650907287470812446332876585563,18367591677349601868781967991146327321610129528364966953⟩
def resval5Tail44 : Box := ⟨-53153813545784649007704351583806780964647440192106828424,17894409180931917060343500152591352983483530816670046916⟩
def resval5Tail48 : Box := ⟨-58443236054227677732270243280423191812856966131959831542,17224530729568257499813285934512633158491410970730290578⟩
def resval5Tail52 : Box := ⟨-64259017606480885316954696893690327083826046405897821769,16328655248760088401434393330519675378147153593682674360⟩
def resval5Tail56 : Box := ⟨-70653537047788439273461795434799015866367105491066438634,15173933383307943130687586385085136614980876938858344234⟩
def resval5Tail60 : Box := ⟨-77684385527545174867862463236828906359333498198746747408,13723573278174256055889271329912853972249355938035424172⟩
def resval5Tail64 : Box := ⟨-85414885183311621692716993624298787347840803159048676577,11936404455880186397072706195654253381940124401355478194⟩
def resval5Tail68 : Box := ⟨-93914645180260563175560904736337429522895807406732037315,9766392748181662951761087088819162443478867461901462683⟩
def resval5Tail72 : Box := ⟨710178376571247854160777492529406198032535503498295633212,2115804740296368183875730711477790218612103804751225186⟩
def resval5Tail76 : Box := ⟨-260643927647387333925181659067893635214479006436038565,221876937798405372105146365575553280272240835309835855⟩
def resval5Tail80 : Box := ⟨-286558693687757602912566871607660647350581995328891769,227313528970721728187608404126260497412491392687303361⟩
def resval5Tail84 : Box := ⟨-315074614733733488817102697641938755256336794772739914,232209496479532417032231023541206736517646113486990382⟩
def resval5Tail88 : Box := ⟨-346428202516299533076614577858748676155554543063570241,236440233911948167292072952395263375275777925655076470⟩
def resval5Tail92 : Box := ⟨-380901836856209158391438094489093578363777918275469488,239864611911039205065886755404880244079445065325598160⟩
def resval5Tail96 : Box := ⟨-418805998664638912969934972036828416056840478286400018,242322585131198540043712237020926099554900243767546141⟩
def resval5Tail100 : Box := ⟨-460482065314110413307521954251227455132704171993778558,243632993062334805212391578733064818695343342576825652⟩
def resval5Tail104 : Box := ⟨-506305385195171889263447006139060684401587767962041272,243591121451053588155859897252227205481697047150264063⟩
def resval5Tail108 : Box := ⟨-556688658227698135418439245142728713746057358738014630,241965999118889621595632087111976934795073093106881574⟩
def resval5Tail112 : Box := ⟨-612085652772373712123407496955429496369944667149146205,238497402420214504299208819756499729689713305727659711⟩
def resval5Tail116 : Box := ⟨-672995292418088147421762639388082888579042867004839096,232892536727554637193439643278317179475819646071949641⟩
def resval5Tail120 : Box := ⟨-739966149452197210132106364233075818123090397784789781,224822361187011790412352612386502879644035522082297388⟩
def resval5Tail124 : Box := ⟨-813601385483324245491875853042083384774435201647356063,213917519522046330478841487934013455646371840083848979⟩
def resval5Tail128 : Box := ⟨-894564183713578712471750206904322101157931240665265892,199763835847860147538900133102989675752779220496761329⟩
def resval5Tail132 : Box := ⟨-983583721785028331715750410065093513544571541958153823,181897330255569923045174382936580234967551319938584862⟩
def resval5Tail136 : Box := ⟨-1081461738996162851741333978272307426759078703810870452,159798704295691589560305137305859657202470568162561920⟩
def resval5Tail140 : Box := ⟨-1189079775261690887793062257841556350952836045638798111,132887237431373503920039016835640072143730634467509392⟩
def resval5Tail144 : Box := ⟨-1319259814174822290537842146924729899102781325486360019,98541594374526993420846531409907720234127865080855305⟩
def resval5Tail148 : Box := ⟨75167806137623237044749489486349840102644155933,56781775326352097658747321138622907247611244518⟩
def resval5Tail152 : Box := ⟨82601127408373769547202131275851794954661955769,57881616565330505301731145495503295539389617611⟩
def resval5Tail156 : Box := ⟨90820899353012470715678598017523425877911184666,58796009422713335475888505329895453565989474096⟩
def resval5Tail160 : Box := ⟨99858634883523583003149568177561554880997970486,59486341326322513480742375839350576881333930063⟩
def resval5Tail164 : Box := ⟨109795730188271995394961469245024188894246770247,59909830841647696640194343286162939937441764728⟩
def resval5Tail168 : Box := ⟨120721682022161443071840261733836529828796308321,60018107392675876069004113329394496885714548985⟩
def resval5Tail172 : Box := ⟨132734893108043403551823634996072089152829857526,59756568453198277146700578001438187690677223177⟩
def resval5Tail176 : Box := ⟨145943558383898166476564789468367014273926016900,59063667163644857673577632353397385932261368360⟩
def resval5Tail180 : Box := ⟨160466639442101564930752965083237992735308420369,57870123060633481861871336679861870021895948791⟩
def resval5Tail184 : Box := ⟨176434935936729576163312480589095067880958160033,56098047878128244586020293266766217217533449654⟩
def resval5Tail188 : Box := ⟨193992263608347815633265916490521729223544038700,53659977553575562962068899947439439730644749972⟩
def resval5Tail192 : Box := ⟨213296749535965394109075997178278383521852612459,50457800663053031578920426167821410641811667700⟩
def resval5Tail196 : Box := ⟨234522256281619083134724395958606322130117543678,46381572507887544588498020348126109408026836470⟩
def resval5Tail200 : Box := ⟨257859947753903239239713170827031918017218691341,41308202972082258182287107668135713248356985437⟩
def resval5Tail204 : Box := ⟨283520010893128472972885200485083543747410128982,35100005055010774046672435096135614293031489647⟩
def resval5Tail208 : Box := ⟨311733548684175827380133490493704267401431733051,27603089645939331147762559091153732273327479035⟩
def resval5Tail212 : Box := ⟨342754661553127894687245128279334893272032267677,18645590631907973861316045138088650621618551325⟩
def resval5Tail216 : Box := ⟨376863035200343514582890431472337884973630108946,8035642144404725375874449304118092382953576169⟩
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
def polyval5Tail5 : Box := ⟨5199666849262040183646723889745494821322438406339084093796,3739949052597437106800887715618338315359054208657532183038⟩
def polyval5Tail9 : Box := ⟨5717092298175931185809298258177073265579641148617950764218,3803774163985505531651183599632614980331362833914433632732⟩
def polyval5Tail13 : Box := ⟨6286009458760798212140373088953762507146867650421490379041,3853902215015093471948495637585427171139316550219107937228⟩
def polyval5Tail17 : Box := ⟨6911540492217317115607910063084353807828336284086670992033,3887666613790121405554507571292170091012366598541287865573⟩
def polyval5Tail21 : Box := ⟨7599319137037598305249611779400918432513260435996842804831,3902050684561127722543929416206270772541159082221746499672⟩
def polyval5Tail25 : Box := ⟨8355539754353517320193800765750750549885511262012587339597,3893647290091224963021455698751246121855545109514674306867⟩
def polyval5Tail29 : Box := ⟨9187013116256315011195549913918948555110386038909017643156,3858614107035296092794748965116899314037790387129794595861⟩
def polyval5Tail33 : Box := ⟨10101227745854443245193437139168181310685782795727394838116,3792624069092828602907185821726236305758985754363297421348⟩
def polyval5Tail37 : Box := ⟨11106417361380514128484088597626860770759740247650423353231,3690810472254217044041652580853937851559066734046581837595⟩
def polyval5Tail41 : Box := ⟨12211635031771115927937312185732577964410861195458856367997,3547706184531136707830039307051402965172595071289992501126⟩
def polyval5Tail45 : Box := ⟨13426834711589085150187327777655587207995741266394459823663,3357176345354788052878323435720457736237047960387347832276⟩
def polyval5Tail49 : Box := ⟨14762960889618614505126413849718796835257457527862709546106,3112343876814544353357954710009333951965256055351782056375⟩
def polyval5Tail53 : Box := ⟨16232047158537987894548431603591858210530810833657575853258,2805507059508933933851748214993620814080850359815149300957⟩
def polyval5Tail57 : Box := ⟨17847324593420898616658938673574079310975749955916114525405,2428048349347404165170669710762449484244230900200165677545⟩
def polyval5Tail61 : Box := ⟨19623340915158851595997826267424189067573309831953335175533,1970333527466853861631434280247327346142454834813445456220⟩
def polyval5Tail65 : Box := ⟨21576091512031473012606245454759713711925977969977040061614,1421600182731929543425312946362667088125427007649993038149⟩
def polyval5Tail69 : Box := ⟨23723163513829323073101520585101625233734704228798502569635,769834421153193854001702545503211287460460009665278341864⟩
def polyval5Tail73 : Box := ⟨26093750000000000000000000000000000000000000000000000000000,2⟩
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
def resval6 : Box := ⟨62046696790060296064501521518525961808624303700763981286,16435975320640590762951093850077157504867676315159380659⟩
def polyval6 : Box := ⟨14813239237988232091673342501003661645793868660588594285388,3676792787056662073928245843284457242328403431107112287825⟩
theorem cell6_lo : Holds Q cell6 (63/64:ℝ) := by norm_num [Holds,Q,cell6]
theorem cell6_hi : Holds Q cell6 (127/128:ℝ) := by norm_num [Holds,Q,cell6]
def resval6Tail4 : Box := ⟨-42089700716682873042131197883796164425578038463928660993,15724067481979960568256697876173012505558536780748539914⟩
def resval6Tail8 : Box := ⟨-44121885779163049148598868191222118078852301778233065289,15534452296897600099673027077152340957475139491031193650⟩
def resval6Tail12 : Box := ⟨-46252141178091550804860039673659341067179697546646768809,15305445610250829111608909614555071935593755970021551269⟩
def resval6Tail16 : Box := ⟨-48485247753216797678847496794819147343653585376803522425,15034180578151799413298265369230108768117702913376675315⟩
def resval6Tail20 : Box := ⟨-50826171282296531813942857161979152585123629959200888864,14717622521975035704320761725091283030655306388346462099⟩
def resval6Tail24 : Box := ⟨-53280117291881894501404156425435651136439885281018456001,14352558554089551065841244136300629360124642517396970588⟩
def resval6Tail28 : Box := ⟨-55852542637329752367395802371394298640174091342789102018,13935587963498310643239896557087933489220373164950274699⟩
def resval6Tail32 : Box := ⟨-58549167637250045048316537328039646112105318812176294017,13463112105313766104347142810096994865496187667839833311⟩
def resval6Tail36 : Box := ⟨-61375988793814689461907981085681451402804926099767263348,12931323768871079090445533849581869278057059813982610446⟩
def resval6Tail40 : Box := ⟨-64339292127217617510557755616566425312303489352481933075,12336195998248256937520394807755966227115121239211202687⟩
def resval6Tail44 : Box := ⟨-67445667153937881536587663141297422760877060289849868605,11673470337662482507993525580991890285482794351071282938⟩
def resval6Tail48 : Box := ⟨-70702021539889380252093369991727653515354350098876494717,10938644472847894976041966980614062543243621371183665050⟩
def resval6Tail52 : Box := ⟨-74115596461041507408520544388733338495864535899551861715,10126959238089086145404329532662085229657729602253095650⟩
def resval6Tail56 : Box := ⟨-77693982705668230936357644135892619584117431885234167144,9233384957083349184744485661842263035408081682126999860⟩
def resval6Tail60 : Box := ⟨-81445137554031682068870032726119532244603098044620154814,8252607084229661582048966880295950982753237192321381191⟩
def resval6Tail64 : Box := ⟨-85377402472190322852162065671673447294076620587104950358,7179011111084044734515065340993013406890860367537562106⟩
def resval6Tail68 : Box := ⟨-89499507559330442143694512748243896725905052074521581435,6006663972239129798623992838021581932346083509657971642⟩
def resval6Tail72 : Box := ⟨709979594878066426845878878305232935319376585600456432512,2078989065953121559339959441649036153191953289728976118⟩
def resval6Tail76 : Box := ⟨-537589711862948257864657168201502289917435563582846649,203068414349906780586758399428065561924998324661894768⟩
def resval6Tail80 : Box := ⟨-563523880631107078984229755814527388073660686172349125,200717658877940085328551106558985838420527311775732805⟩
def resval6Tail84 : Box := ⟨-590731460783434527837292181061820013472681801911211632,197866471146246082741588805964923337224085146746995108⟩
def resval6Tail88 : Box := ⟨-619252655166761316698926688364242534321804317947148946,194477908893083426946450416846695051885341962452648223⟩
def resval6Tail92 : Box := ⟨-649150885620347788438141050797121270017385425202964937,190513288067325206946800551678842544549209142139308420⟩
def resval6Tail96 : Box := ⟨-680492637029069653321774489918121013965206667293380507,185931650952760037894908431003734414451148179583830181⟩
def resval6Tail100 : Box := ⟨-713347604244972316773692370253401524301914800134477393,180689643417868344281343713509084963356100271373444852⟩
def resval6Tail104 : Box := ⟨-747788847067721739498583754653640449026326167944779617,174741385862810037633590022684385590060847520648077707⟩
def resval6Tail108 : Box := ⟨-783892952708144876980007198724389393455177401671008338,168038337510105338353950131050981636944098245021598170⟩
def resval6Tail112 : Box := ⟨-821740206095697739724435934514398891335592432862571179,160529153704046649686323122339810371339292519668377834⟩
def resval6Tail116 : Box := ⟨-861414768408573906296294513237877346336011916027963044,152159535867301812607697707844558519709326830034265192⟩
def resval6Tail120 : Box := ⟨-903004864223452020208594567216781447847481885363043076,142872073745750460518001369119921864949800983062148450⟩
def resval6Tail124 : Box := ⟨-946602977701048355144386970970463723102943419094441746,132606079554321290975706461150109074996288499919425615⟩
def resval6Tail128 : Box := ⟨-992306058243733523361394443161971105550733957535007387,121297413617427214210142767178759889956942150899403554⟩
def resval6Tail132 : Box := ⟨-1040215736082538062585904993522494693566291546142223222,108878301077483002619334064293108718840959986458618519⟩
def resval6Tail136 : Box := ⟨-1090438548275239658274000898673216750910554697111597572,95277139223290930436914943324978999588695283402023352⟩
def resval6Tail140 : Box := ⟨-1143086193644966994394102450693162721435448420630625258,80418291107995656376907537788034776306920716801970160⟩
def resval6Tail144 : Box := ⟨-1209990155214287940156108405999556305283863968376146242,62311687341485012661599231199451662454334541530339172⟩
def resval6Tail148 : Box := ⟨173202735358644898017171272979505250431618975548,56246259898792791900136614243817432766995415524⟩
def resval6Tail152 : Box := ⟨181520610822339700187374922643598742176747249316,55196200214091805119992806733120451820476173399⟩
def resval6Tail156 : Box := ⟨190284634030638961214199525841011133716062516454,53976345910099537510198801025158126677464463736⟩
def resval6Tail160 : Box := ⟨199471795026149081332056541391085236191031083503,52573787313372631750340347600747281717591380103⟩
def resval6Tail164 : Box := ⟨209102522721739480293092148513397687334386674369,50975757453538030957189897549371398258389988682⟩
def resval6Tail168 : Box := ⟨219198233027700972503395784385370668544249562217,49168747226742855310190278862254377652000495851⟩
def resval6Tail172 : Box := ⟨229781375839283310916143412277936830987605956106,47138465534441642880025564818247864997991359551⟩
def resval6Tail176 : Box := ⟨240875484958500951592807155584650721829477736936,44869797392341418404305918866289275079811413243⟩
def resval6Tail180 : Box := ⟨252505230426398102813196657552286689424573037870,42346759885011477883304149669228603591479993529⟩
def resval6Tail184 : Box := ⟨264696473381975978123099201515291133991940549833,39552455857934110192048535683962228719275106362⟩
def resval6Tail188 : Box := ⟨277476323569772157036122709029860602004386836731,36469025233423054491884633835099751704402154016⟩
def resval6Tail192 : Box := ⟨290873199623972022297559746748146654563996209697,33077593831214936035936683873361647994845689592⟩
def resval6Tail196 : Box := ⟨304916892263106435905860648266485537057181354437,29358219568641528972665812038978091591439091922⟩
def resval6Tail200 : Box := ⟨319638630535862105305563080531582583546730819617,25289835909104025059472680821467914314976973485⟩
def resval6Tail204 : Box := ⟨335071151265315876679227878472985947433378753366,20850192421080428477724226025144364976697842206⟩
def resval6Tail208 : Box := ⟨351248771846019358905936906586244775394300929460,16015792303088149908962181562314108322497376527⟩
def resval6Tail212 : Box := ⟨368207466562722806966428215980961691222661198444,10761826721184303106012642563617209651677873579⟩
def resval6Tail216 : Box := ⟨385985242516883673830892882641616999029649029442,5062046774497999637970242476385894676020971929⟩
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
def polyval6Tail5 : Box := ⟨11701787474889683877274993252958201604894548012231551451703,3601186379587566911105473612853204940141135756052135792938⟩
def polyval6Tail9 : Box := ⟨12266761458593660372757180404795903469265528526127631442910,3523916708670074282171083716873881062099367586328800544125⟩
def polyval6Tail13 : Box := ⟨12859014810853719403209755708410217461968413203324286089663,3434912590634776696995230709638384533051705532754295202319⟩
def polyval6Tail17 : Box := ⟨13479862836313387382227722113650427634456289914514201811914,3333352362878179091150937628200120669757299851400687408270⟩
def polyval6Tail21 : Box := ⟨14130686118539469187113155450048644755014819590159820201055,3218366591030353929818314431722755155852308406115095318599⟩
def polyval6Tail25 : Box := ⟨14812931897405982434284181196723922352357442588722470370252,3089035474896762912007064896582410759972024882445134578944⟩
def polyval6Tail29 : Box := ⟨15528117287192767446038104822888254691192789719565857365356,2944386149390457103490441732670593883784316823375442312828⟩
def polyval6Tail33 : Box := ⟨16277832650202074797829679910751714382571408339309775729797,2783389846634925061418747069445010378226789495415325833715⟩
def polyval6Tail37 : Box := ⟨17063745133257336621677005950605994000783886711233613840553,2604958912258244900100156442201950823375561129882756282324⟩
def polyval6Tail41 : Box := ⟨17887602374948166524298955601724161765122305904530127004464,2407943668558529740504410118367849801297881668184081094832⟩
def polyval6Tail45 : Box := ⟨18751236391865412163359256168269346390232251469336628256343,2191129116858313000350721036132683727963122529633049792016⟩
def polyval6Tail49 : Box := ⟨19656567652468106095480488586964417206896772941557796362039,1953231470985392769177073950148073968168041720953920584741⟩
def polyval6Tail53 : Box := ⟨20605609347641398758199830443713512716683433434464850635989,1692894513418880636748423843089755216872183213457165531780⟩
def polyval6Tail57 : Box := ⟨21600471867441940445852542773977386695168349144014759991189,1408685765220870181304902189729809427228334886358632017311⟩
def polyval6Tail61 : Box := ⟨22643367493985681372870337205361838393533433711140657512302,1099092460435299475827785995670099584732017324077994087316⟩
def polyval6Tail65 : Box := ⟨23736615320915447112543772630887357132474788337801498330589,762517315174778220944316543691239255307008208265304051925⟩
def polyval6Tail69 : Box := ⟨24882646424611064305800071465518224103767197441207597476871,397274078149439938334716986882932553553728199525512562000⟩
def polyval6Tail73 : Box := ⟨26093750000000000000000000000000000000000000000000000000000,2⟩
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
def resval7 : Box := ⟨35950992003288057247971340412946813304710271873677084038,26985846145531956607752679090456897383761460497377217665⟩
def polyval7 : Box := ⟨23328519068215925706200244450716510373229833794833676730304,6416492450835011198198160995532517735421874522315148295959⟩
theorem cell7_lo : Holds Q cell7 (127/128:ℝ) := by norm_num [Holds,Q,cell7]
theorem cell7_hi : Holds Q cell7 (1/1:ℝ) := by norm_num [Holds,Q,cell7]
def resval7Tail4 : Box := ⟨-67288105293255894036447969302211208762245016705647723033,25381507147849757358197419915428077383589058264069509827⟩
def resval7Tail8 : Box := ⟨-68349874506119403781756966829091760173264472080541992291,24319780462108241244324944393620323514470982342212427313⟩
def resval7Tail12 : Box := ⟨-69428352702872002204002952893289076702636091668482605542,23241302269605867780528836400241746271589112889788987722⟩
def resval7Tail16 : Box := ⟨-70523847974125963286121649287192587434536902525748815347,22145806998355069510128835614042887418620400415184795062⟩
def resval7Tail20 : Box := ⟨-71636628833217973058938355570828254702704813329516825099,21033026139263069894344854900653338934138337468106848852⟩
def resval7Tail24 : Box := ⟨-72766968025780598867254777033973339640315258727434483641,19902686946700444192597313126284806353657782523792597110⟩
def resval7Tail28 : Box := ⟨-73915142601038545822552105503100099342113300241449220548,18754512371442497240268532639580092575008522829804556712⟩
def resval7Tail32 : Box := ⟨-75081433979717540973473892639803982456256191864632840631,17588220992763502089508865719364157872083216250430116331⟩
def resval7Tail36 : Box := ⟨-76266128023021333036232364595761473854617643024564834108,16403526949459710026740661169050369116586625423765034355⟩
def resval7Tail40 : Box := ⟨-77469515102697054647958110749802732894029539573166302793,15200139869783988414956295649122148800440575668594504767⟩
def resval7Tail44 : Box := ⟨-78691890172206131018537206391673275803756008088621109044,13977764800274912044140464686433528094443920045888236184⟩
def resval7Tail48 : Box := ⟨-79933552839018179271157650319058862709641385449317444084,12736102133462863789487243845182288132821336938476395224⟩
def resval7Tail52 : Box := ⟨-81194807438045617880350270245819377615478736826649665328,11474847534435425135003940661511075271671949263552537076⟩
def resval7Tail56 : Box := ⟨-82475963106236983092694968747512369177011076156234140067,10193691866244056863357045514527459564301203791335039115⟩
def resval7Tail60 : Box := ⟨-83777333858346644969393091553872216299527427785982832096,8892321114133622067672481840386501888213143044859228716⟩
def resval7Tail64 : Box := ⟨-85099238663059952485179477854872358186762721913541108803,7570416308371690164232034266873773760695372110758614364⟩
def resval7Tail68 : Box := ⟨-86441987523548145089750293497744802212506377259819279186,6227650739282259431964751256711852578093160004303654950⟩
def resval7Tail72 : Box := ⟨709694618736462231094395753183243843679054506761450952227,2212496353880050133493842635984420448567804244575808656⟩
def resval7Tail76 : Box := ⟨-862531349908422002074754340716752916144874028655234509,327399275972327584909010372110112862834732518477382678⟩
def resval7Tail80 : Box := ⟨-876120437328273293154181931929782673166993707547372329,313789481110014788404876094373969446934731817011359802⟩
def resval7Tail84 : Box := ⟨-889944555195564103880916077753352759836754202377378396,299965362285840129465428526280794423545094875840079068⟩
def resval7Tail88 : Box := ⟨-903986801826897592068149760016728904149948578358422187,285923115654041645652585123725870925021443207250490158⟩
def resval7Tail92 : Box := ⟨-918250618093896422053736808969211915714229350826372473,271659299387041708881259435499025544332913479906334925⟩
def resval7Tail96 : Box := ⟨-932739500096466243447210902955591088517996647027020455,257170417384471878005569584503013223509964336793185859⟩
def resval7Tail100 : Box := ⟨-947456999099175054201386110483357927168674867031562443,242452918381763067007232388324631892655520259537939406⟩
def resval7Tail104 : Box := ⟨-962406722401243260815851572997267255532994922051686255,227503195079694860376047477496986289239981855610472362⟩
def resval7Tail108 : Box := ⟨-977592334220701592147962672479710254692424538647734260,212317583260236529041203317517825362711041953050117713⟩
def resval7Tail112 : Box := ⟨-993017556592500943448844846601383468781195777371398945,196892360888437177739438892977721128335659699403993030⟩
def resval7Tail116 : Box := ⟨-1008686170280793312948154020072270901915136527575489933,181223747200144808240098613997526665316483218758949922⟩
def resval7Tail120 : Box := ⟨-1024602015705607426264978083536368523210594150568574048,165307901775330694929597636448609108602137782748790311⟩
def resval7Tail124 : Box := ⟨-1040768993884146179436952020874201057972538953617102334,149140923596791941919761504285992191260773974403142033⟩
def resval7Tail128 : Box := ⟨-1057191067386936628278680301798658390750970709395772127,132718850094001502722806225982446864599893195182197892⟩
def resval7Tail132 : Box := ⟨-1073872261309069446992324407754290525517192554912404672,116037656171870552672611289434167362465599991981817065⟩
def resval7Tail136 : Box := ⟨-1090816664259040884807840061163218763133792421768396712,99093253223589124328879998462036618750094465560626860⟩
def resval7Tail140 : Box := ⟨-1108028447261441660086235770779601266890660115011481985,81881484300200429121507405728235428957630765496914076⟩
def resval7Tail144 : Box := ⟨-1137135799407753060243619004223501660008998835112045133,62503471845704118391756898935668919003629413611406730⟩
def resval7Tail148 : Box := ⟨300540529605884563792489772715769030843167212963,96747372320328875487847321789064962892370744966⟩
def resval7Tail152 : Box := ⟨305239537025710470944456411648718699481750074437,92005030032211253630751157055625434619793417109⟩
def resval7Tail156 : Box := ⟨310055846380369747164199441281844390828995722467,87188720020715848604342453837644940206522451267⟩
def resval7Tail160 : Box := ⟨314948151905389489839279345907851620355028208084,82296414495516818867905209680547159894768123313⟩
def resval7Tail164 : Box := ⟨319917652083191467225166680665473244486020893071,77326914317714571264088539862136856764008387222⟩
def resval7Tail168 : Box := ⟨324965564951678713959875074682641204689538680266,72279001449227322975730421218693203793477239186⟩
def resval7Tail172 : Box := ⟨330093127768088226004000113657697467934686997734,67151438632817810903808352391586295325080666708⟩
def resval7Tail176 : Box := ⟨335301597312077120103395603153260833768239198578,61942969088828916803056605737647693914643264144⟩
def resval7Tail180 : Box := ⟨340592250193762517725285042198713773953138070583,56652316207143519181004212500344947533384693921⟩
def resval7Tail184 : Box := ⟨345966383166622171745239186860062481252683582118,51278183234283865161007554264459880928502431300⟩
def resval7Tail188 : Box := ⟨351425313445332287140474451656586846715541029031,45819252955573749765756859474168168189721794326⟩
def resval7Tail192 : Box := ⟨356970379028620437352137175911309363915181131173,40274187372285599554144160578676935817466963740⟩
def resval7Tail196 : Box := ⟨362602939027212708431659985739862539318781742606,34641627373693328475784105670475638845707629982⟩
def resval7Tail200 : Box := ⟨368324373996955451773070910632334886540201112260,28920192403950585179474582673159524064409372108⟩
def resval7Tail204 : Box := ⟨374136086277193301311219450013504425434071762153,23108480123712740543767105616212361077078539048⟩
def resval7Tail208 : Box := ⟨380039500334489191875909279984819065741284170861,17205066066418877435192988231496266053151975754⟩
def resval7Tail212 : Box := ⟨386036063118631588812031751564512182618233489597,11208503287466378715241343712917871987822935054⟩
def resval7Tail216 : Box := ⟨392127538129491703844901366545919257949124413928,5117263473986963252278435486384742407358777954⟩
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
def polyval7Tail5 : Box := ⟨19988962926957552979858386155277502508704660464345872743286,6096693243571591422021523046505560643028809926111787680899⟩
def polyval7Tail9 : Box := ⟨20304362819995896812978375592749935985963430884936848260562,5781291631011486620024972227258027862555450405483565901692⟩
def polyval7Tail13 : Box := ⟨20624741059999815521912841265384029472997959459336540867029,5460913390864651019707980204107878278270168446854196348266⟩
def polyval7Tail17 : Box := ⟨20950174480531694780827823330375760264055599944769630050149,5135479970332675098041744888477764484224272844455942264897⟩
def polyval7Tail21 : Box := ⟨21280742846074176746417721428982572852488278469313420907204,4804911604790192840670971113079230578972382710361454292506⟩
def polyval7Tail25 : Box := ⟨21616527179836826986727695166825785917122373910693719438277,4469127271027542597359193154445637167188231988612464276885⟩
def polyval7Tail29 : Box := ⟨21957609783477364831960573847984715421172729728341222161046,4128044667387004752036888175616650647203856551118338597478⟩
def polyval7Tail33 : Box := ⟨22304074257273934207603845204433865446140580652147687815806,3781580193590435376386732398405365656039034684933218178893⟩
def polyval7Tail37 : Box := ⟨22656005520615759983459220215765221537499974581588046455591,3429648930248609600530126972761665145314608975506152904522⟩
def polyval7Tail41 : Box := ⟨23013489832817122308388015081609565043554738206719563781402,3072164618047247275600919950425296035084381472865975926490⟩
def polyval7Tail45 : Box := ⟨23376614814259750239701751239880373350479321546354653965961,2709039636604619344287252960707922805592795363236862392040⟩
def polyval7Tail49 : Box := ⟨23745469467868816723390533804037375695528315611705632856104,2340184982995552860602728185327899418271537355946666404296⟩
def polyval7Tail53 : Box := ⟨24120144200927798750331667381323591518071318775279317391013,1965510249936570833772136792912904566275799096909511615730⟩
def polyval7Tail57 : Box := ⟨24500730847237549579574463427471426783404228775139002440751,1584923603626820011366352722406292084740241653745502381066⟩
def polyval7Tail61 : Box := ⟨24887322689625016166207281866451292505712028381538732605593,1198331761239354805450082678078106786682585425761820578058⟩
def polyval7Tail65 : Box := ⟨25280014482808859624542745673487689937827622722898737908920,805639968056811027783150068422379847850050575771671067691⟩
def polyval7Tail69 : Box := ⟨25678902490747593956650274143228083262555709214970186984157,406751971287464502212700483426538386384786526035538706737⟩
def polyval7Tail73 : Box := ⟨26093750000000000000000000000000000000000000000000000000000,2⟩
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
def pend : Box := ⟨1029734007868843399081278851326261019383330892369072024438136,11003650207537823119554119988008725320815948076800588194⟩
def zend : Box := ⟨1003644357281427734901660156250000000000000000000000000000000,9100262508772512480468750000000000000000000000000000002⟩
def betaquot : Box := ⟨428738153879039919705934584071627593019138472402158380405184,394746868937771980299106055896734882547828455117864956⟩
def crit : Box := ⟨120092400858635614935135814389539261406801657413401127878,30114773704556656506854450848885432662623940225423514160⟩
def subsonic : Box := ⟨748128967316706432008997057059845469706558271940089076038,18529984827966960991304371757883965148418071259059132758⟩
def pendTail4 : Box := ⟨26084090929237031496234659124630098734396368159340140386840,1533199847786168301688386100106204527354485668214437012⟩
def pendTail8 : Box := ⟨26084121624431237022800220047344960163954692653344673307733,1532825320517523071275453551120302929275905149274198153⟩
def pendTail12 : Box := ⟨26084121625577903504121428409799649646538534559244438758756,1532825286002075746093866616556627508426675426083797667⟩
def pendTail16 : Box := ⟨26084121625578391805298935957586021501681619847141877610464,1532825285976836136140112642985772202263350762556775554⟩
def pendTail20 : Box := ⟨26084121625578392823566129321235952602713375190510080040671,1532825285976753674288284142334430215919069420638464956⟩
def pendTail24 : Box := ⟨26084121625578392831114344199087931503890823293918429645505,1532825285976752735673718690663393570203514027073741796⟩
def pendTail28 : Box := ⟨26084121625578392831278411345738770591067598785458127032796,1532825285976752703601166335051806416508987750279678200⟩
def pendTail32 : Box := ⟨26084121625578392831287425818909640588212817901728547365881,1532825285976752700593365021670251108828722945777724544⟩
def pendTail36 : Box := ⟨26084121625578392831288451961430471522582391320589989155513,1532825285976752699857657719582997358632265200271662057⟩
def pendTail40 : Box := ⟨26084121625578392831288518153110342761448694359608466145567,1532825285976752699398945433715702360576205240129212067⟩
def pendTail44 : Box := ⟨26084121625578392831287895141959846451736315395629249825404,1532825285976752698669750136795631396488329798159094018⟩
def pendTail48 : Box := ⟨26084121625578392831282857745613805494623663392638274084437,1532825285976752695646172084125191080566811095668105991⟩
def pendTail52 : Box := ⟨26084121625578392831202641160267322114537178350434636605544,1532825285976752661289637006763469900916109166064736959⟩
def pendTail56 : Box := ⟨26084121625578392827830351824168064410252639571987618034224,1532825285976751495165494080279574071949746488982898531⟩
def pendTail60 : Box := ⟨26084121625578392368626379621267369020038197547506028794983,1532825285976614792722487246016375265854704521868217165⟩
def pendTail64 : Box := ⟨26084121625578124442885354228612854609707341498993972691027,1532825285905184152852595691923442941230357143452094657⟩
def pendTail68 : Box := ⟨26084121624440912799953471079428425908265302618487276500069,1532825036725021034457466666892143548674052279962011286⟩
def pendTail72 : Box := ⟨26083971766831462543443812465846914016253660890434933413102,1507046581653314403099346334658178306888225139143068612⟩
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
end SepticProfile.ExteriorCertificates.C01

end
end

end OAI
