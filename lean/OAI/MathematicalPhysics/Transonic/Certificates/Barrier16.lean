import OAI.MathematicalPhysics.Transonic.Certificates.BarrierData16

namespace OAI

section
noncomputable section
namespace SepticProfile.ExteriorCertificates.C16
open SepticProfile.ExteriorJet SepticProfile.FixedInterval
def cell0 : Box := ⟨250000000000000000000000000000000000000000000000000000000000,250000000000000000000000000000000000000000000000000000000002⟩
def resval0 : Box := ⟨112781747699618129701630136626219528102310666071626940098,329280983330597162560589783533187970054169411404947390⟩
def polyval0 : Box := ⟨3794639485005329710073500860219764464219347379346348421757,15115669966611752591096021196813766366148159641226383745⟩
theorem cell0_lo : Holds Q cell0 (0/1:ℝ) := by norm_num [Holds,Q,cell0]
theorem cell0_hi : Holds Q cell0 (1/2:ℝ) := by norm_num [Holds,Q,cell0]
def resval0Tail4 : Box := ⟨57257918539322928812713487025296653600959320549087,1728485277283681109662377115295812327720755366887⟩
def resval0Tail8 : Box := ⟨6845020246412235599011644803857589551150417863,372953806946647272195841604880834365399832165⟩
def resval0Tail12 : Box := ⟨6153663038075797485000380614442942461918555,508112405633875467669930025325832081562563⟩
def resval0Tail16 : Box := ⟨24354628418170266731785758168814058360078,26422401194138559786866986115409833989837⟩
def resval0Tail20 : Box := ⟨327884654152202310346255415404618179860,377206205780156446992260203521760179849596⟩
def resval0Tail24 : Box := ⟨12887189813288377554875511542594525706,6034452537811085592129581657359406506704192⟩
def resval0Tail28 : Box := ⟨1345632390732801190058969457846040279,96551195089191622799405381039238302331972102⟩
def resval0Tail32 : Box := ⟨350636790453723733416335668793316059,1544819114893920358096851568268279949622303647⟩
def resval0Tail36 : Box := ⟨-321943583988494785309188983802451792,24717105835750822330879997546977883036389741041⟩
def resval0Tail40 : Box := ⟨-139815156251900751318607805781421995768,395473693239733970077407901144416139870573480400⟩
def resval0Tail44 : Box := ⟨-35880862280760237705667231814850995741238,6327579058194652260430084959919592966781571855651⟩
def resval0Tail48 : Box := ⟨-9185829455291753984901191707508115552483047,101241256319381240683845052233714438257728036855200⟩
def resval0Tail52 : Box := ⟨-2351575334138503525026106689146671928619231062,1619857896507866965384817931375546819324637487779370⟩
def resval0Tail56 : Box := ⟨-602003346339573140586782472106964395865928576431,25917161965964888612842587129319833161830833941183725⟩
def resval0Tail60 : Box := ⟨-154112854940709054446063432824351494636156200889870,414530110647676004149892064240627791079260077294558371⟩
def resval0Tail64 : Box := ⟨-39452877578629014833485589994274420761364342859851445,6595494688427097250128007042829215065609660471831338944⟩
def resval0Tail68 : Box := ⟨-10099624361711085096594088263135767650705027178437325365,96059353041354457885443850503721189664780788334759765935⟩
def resval0Tail72 : Box := ⟨780175025362862109622536846688327609010269979817381814257,2468741557835019813405670471149419985175050205447076800⟩
def resval0Tail76 : Box := ⟨-26362645593300501683134223740995255729999921766550,591360517408819595985428495415334526720027943097⟩
def resval0Tail80 : Box := ⟨-1407994964281495902621929671295745232467955126,65829934423503304447687821897430818207942829⟩
def resval0Tail84 : Box := ⟨-787049952312399108063235577848417707119582,57814578792030390768162130847008042335478⟩
def resval0Tail88 : Box := ⟨-2152236463306456306886719038458881222870,387262361494195565615867160395840551781⟩
def resval0Tail92 : Box := ⟨-21186663316078606220779283538148639859,2545868425691156794099038212014011952763⟩
def resval0Tail96 : Box := ⟨-630271006402888494894190501430477308,40683893079054175502068142007582768743031⟩
def resval0Tail100 : Box := ⟨-50897997222490776401268678626378775,650940249812208976441728245328480747508134⟩
def resval0Tail104 : Box := ⟨-10461461613102329962881979294440641,10415043770940101018415179643840497696887610⟩
def resval0Tail108 : Box := ⟨-7105320112911148048276447794601492,166640700269753041241889450208225099667119759⟩
def resval0Tail112 : Box := ⟨-476022790743352060306231112544898121,2666251203881012390260381797913962970289781848⟩
def resval0Tail116 : Box := ⟨-120230555628037642034653551875843813738,42660019149400843399675322360151430327103720426⟩
def resval0Tail120 : Box := ⟨-30774220581077234510771936661932312848765,682560277539693586297901645669832900806528197195⟩
def resval0Tail124 : Box := ⟨-7878165875652236001316367552771212605647401,10920957054856445529181485925474834386513211948451⟩
def resval0Tail128 : Box := ⟨-2016809877847913715634365650528149772851612118,174733422118544025864256899056615861831138062868370⟩
def resval0Tail132 : Box := ⟨-516303321798571183972930195790241362675348414981,2795250719553629850871474217933512831918605836398156⟩
def resval0Tail136 : Box := ⟨-132173682710135574123698837071684479084972619555704,44600098706673390026794293324451258753847272552705338⟩
def resval0Tail140 : Box := ⟨-33836866227372944505593436728081907200210769233328682,681879712209709577096555858737993376012094322872326375⟩
def resval0Tail144 : Box := ⟨-8924213865245491121610010160925754660131814618525656282,2658605970775231756332457986544947409735516426260629370⟩
def resval0Tail148 : Box := ⟨58616966497138647598398358102395725670468786,1092318083069741542980759249726245500071134⟩
def resval0Tail152 : Box := ⟨1032558481454712469094753943933224978217,43092443968176177148103720211863545119⟩
def resval0Tail156 : Box := ⟨324191835342998823808204660286829188,21710066035995858728896015435428938⟩
def resval0Tail160 : Box := ⟨561174352329748878320327144803564,56195591694760612944930297723572⟩
def resval0Tail164 : Box := ⟨3702560829346885998710955075612,28034990308446839646961065372697⟩
def resval0Tail168 : Box := ⟨76200862271430770895212848522,440574458987235728276229949884994⟩
def resval0Tail172 : Box := ⟨4328988342336760131728056307,7048967217261304795332153450048835⟩
def resval0Tail176 : Box := ⟨629534604118027495783657740,112783458162551982949319025303125938⟩
def resval0Tail180 : Box := ⟨230722911361317167562555092,1804535327138912024591037278426591143⟩
def resval0Tail184 : Box := ⟨1840660825689510061091570300,28872565231514817326794630973534544087⟩
def resval0Tail188 : Box := ⟨422451445901314266331851917673,461961043308681084848325841416035746909⟩
def resval0Tail192 : Box := ⟨108048281219405566217965566185396,7391376591645320425186552163894326996523⟩
def resval0Tail196 : Box := ⟨27659871917787309116751905968442174,118261999535212374240466700185637137290183⟩
def resval0Tail200 : Box := ⟨7080921425266261627607868769766008257,1892185354200110487260867247128257107378092⟩
def resval0Tail204 : Box := ⟨1812715750920678792278416893889257630839,30273266246246036202306422123321715834001264⟩
def resval0Tail208 : Box := ⟨464055258149866714638822823161936841089057,483937208163590044367549026502870651318327225⟩
def resval0Tail212 : Box := ⟨118798298755779332020803237268068115878434122,7631622006057292191756477439473337313750327379⟩
def resval0Tail216 : Box := ⟨30421300325082332633575611851572036135660784891,93590022921448251422038509253860202014613418769⟩
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
def polyval0Tail5 : Box := ⟨2066605347915900651344418134015546201641822348429161,51929220804010677616822258922724427234523019823139⟩
def polyval0Tail9 : Box := ⟨198022694000571017870327950574819626292393974579,9823428017044837671970751974746085210366005586⟩
def polyval0Tail13 : Box := ⟨154033466212088606274661105118434679491294450,11847448574373234240916275349102763260294513⟩
def polyval0Tail17 : Box := ⟨534202862924701251796331101490953309273002,432587910939787941942216838504291930565370⟩
def polyval0Tail21 : Box := ⟨6319481566768913794612120549403196567311,5980446691958555967038704391013834576640307⟩
def polyval0Tail25 : Box := ⟨218005994850754064221854182465826865696,95671716686782909419449207817624110895450558⟩
def polyval0Tail29 : Box := ⟨19908597009573292750744741878218710006,1530746738805409903912828192828716633338025848⟩
def polyval0Tail33 : Box := ⟨4560927195310433297548830911465977120,24491947729716632853095010991845242691689349665⟩
def polyval0Tail37 : Box := ⟨8184637039333124455554777133737566809,391871163644733410612885868750736729019638853089⟩
def polyval0Tail41 : Box := ⟨1457604189632626255977115791026772586056,6269938616954846588525516875543542719662947101438⟩
def polyval0Tail45 : Box := ⟨372309209367262934669377837983796867758915,100319017522248932265256567730833731039383291934919⟩
def polyval0Tail49 : Box := ⟨95308518910303131807580320156668762299236053,1605104191004311537636019875877198417826768019117451⟩
def polyval0Tail53 : Box := ⟨24398960690052998400631130662621872295081353517,25681644182044484332465966761001345611842961219206616⟩
def polyval0Tail57 : Box := ⟨6246133579878741824677525115486963200532985998892,410900451162546404144288146227135363641330400239678851⟩
def polyval0Tail61 : Box := ⟨1599010193023791923542358768395620639596661722001501,6572908146559058608658829007795318418132598214273823437⟩
def polyval0Tail65 : Box := ⟨409346631987459411199867981355505458218486076071880724,104782767892285285673935672589302310121191285273022334264⟩
def polyval0Tail69 : Box := ⟨104793014640281618033504771979718952876692714652137734747,1578280969539222398796507593891503170124956126902877809056⟩
def polyval0Tail73 : Box := ⟨27031250000000000000000000000000000000000000000000000000000,2⟩
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
def resval1 : Box := ⟨112558380307083976355599944975178440599400464331724556515,253348932259612380010441873938622668356369827459591418⟩
def polyval1 : Box := ⟨3776565355878577215189819205096836800310680106609190883308,8960479247489768709148159768771884865324787260528489351⟩
theorem cell1_lo : Holds Q cell1 (1/2:ℝ) := by norm_num [Holds,Q,cell1]
theorem cell1_hi : Holds Q cell1 (3/4:ℝ) := by norm_num [Holds,Q,cell1]
def resval1Tail4 : Box := ⟨55601418459565377369456627264939411803074121901076,3077367895996129091749388917318738422779455984547⟩
def resval1Tail8 : Box := ⟨6451612612722724152110308477200567217316245957,6186418158772873766098139995740961038114570011618⟩
def resval1Tail12 : Box := ⟨-319959886647934807146552887728272474305548976,19551292320721445174361005112283121798741862603637⟩
def resval1Tail16 : Box := ⟨-2134286330430880603615142165885873866792247091,61790632836683685627629887291989682607738639604098⟩
def resval1Tail20 : Box := ⟨-13987402999600091759709128799083426888338502480,195281671717533559649705438121137412691088414292702⟩
def resval1Tail24 : Box := ⟨-91667846178551122786436484148860102414206364715,617139057276334919537477929536815511756596876607923⟩
def resval1Tail28 : Box := ⟨-600754396786802864646853232150424164497336142770,1950153142286742687439141597998795178387641081163182⟩
def resval1Tail32 : Box := ⟨-3937104014789005338549716734433129472460906321376,6161408544762788455391839137374470400727464426897960⟩
def resval1Tail36 : Box := ⟨-25802204871322898603296295587005212504376438241991,19459734660401021247731012209519845321400136208913460⟩
def resval1Tail40 : Box := ⟨-169097329844702626842108209813426858009830870316947,61414821651756780277342679114872759607194335815169173⟩
def resval1Tail44 : Box := ⟨-1108196260870243884954671418276645244845745041914156,193527399532833207899772060604719039019626998983970565⟩
def resval1Tail48 : Box := ⟨-7262675015239227754462946869850578195925474456632235,607881924036465501928308568192307029484724794171957203⟩
def resval1Tail52 : Box := ⟨-47596666979871638404364748206987176798100843113189078,1896564041134157919987356292895662175055925468389301212⟩
def resval1Tail56 : Box := ⟨-311929516719270898808392829732468986977765347070207054,5832578400283077578329904434885346981738978472056575423⟩
def resval1Tail60 : Box := ⟨-2044261280766473462290946025587695340806402120709741068,17375418061853494779429415329717753296709323124433224243⟩
def resval1Tail64 : Box := ⟨-13397270721825323833614327677303507198974872253930205344,47978505958818974282236648129542501318377595884269830514⟩
def resval1Tail68 : Box := ⟨-87800210355089991799558695906355872752581649955582894649,106177426364557413290217526620399512123445790340747529934⟩
def resval1Tail72 : Box := ⟨782987216142460877391482565061353625983646912255202268816,1531596304666089045774460006538329645893530851936014657⟩
def resval1Tail76 : Box := ⟨-25776330440881772658813600424725657285296567326565,399231166984027960412019261072054972558275974648⟩
def resval1Tail80 : Box := ⟨-1345914326941318461024064245076279799355333443,62538854481231810563476650646795742810769550856⟩
def resval1Tail84 : Box := ⟨-3470924198580221027700057776783543000826883,197521655382338224554236916600576665703429492018⟩
def resval1Tail88 : Box := ⟨-17931807516062532138977257571429109505613635,624256693632547207519695327892499347180562176414⟩
def resval1Tail92 : Box := ⟨-117505062054228733663656454600306508514699843,1972898588922144655533204536469042159237978723214⟩
def resval1Tail96 : Box := ⟨-770081052070964460852888628333414631995137853,6234935104814321019926586837122018591223899084155⟩
def resval1Tail100 : Box := ⟨-5046803179336174667212877280835579343583391320,19702860944742385014696459692259430512461366462462⟩
def resval1Tail104 : Box := ⟨-33074729315827538344307904665282790234490160420,62253646054239112605780732524204195532699605656014⟩
def resval1Tail108 : Box := ⟨-216758546044156190564119283829445569664186942301,196640038004450445360586721901864352647889328358885⟩
def resval1Tail112 : Box := ⟨-1420548807354959983116639931492686055201661689756,620744141525072412961961674917402844059920777632513⟩
def resval1Tail116 : Box := ⟨-9309708663881448015668417663721744979047996618114,1957037954608975428887383408302417353494449173798619⟩
def resval1Tail120 : Box := ⟨-61012106699613466929133977387782646096826804085721,6153617545125712000651941120911637769092662758101171⟩
def resval1Tail124 : Box := ⟨-399848942466588091656358510782437809926220216292561,19241449710215923168442126401592756460762040973395332⟩
def resval1Tail128 : Box := ⟨-2620450029349130036934822579202771367637353808169838,59455753119869750213239892760733646205628345173607678⟩
def resval1Tail132 : Box := ⟨-17173381312364266786955391477736269283159296895071330,179018075554320228490739986128899486735830906411800740⟩
def resval1Tail136 : Box := ⟨-112547471790430406040105320260834648575971593038660403,507514416595788099859908700946101784327375863760397558⟩
def resval1Tail140 : Box := ⟨-737591303398002293150164127459344198875773305058871851,1222110622180371051423985864743814488880119557528472431⟩
def resval1Tail144 : Box := ⟨-4943087812340919520777729251839561188668768431820546846,1339236473334010010459717162474188262856545689490429287⟩
def resval1Tail148 : Box := ⟨57750361694505553215963624601229663327400312,787771271456628355558224245881455056819499⟩
def resval1Tail152 : Box := ⟨993189280484890075640156642430222110589,2860161525256732827662251215530645861279⟩
def resval1Tail156 : Box := ⟨414642648288350153739858470017212696,8950184371085107882353115029451518623468⟩
def resval1Tail160 : Box := ⟨719214070469395004222323549154984556,28286629600103254482277572763157549201843⟩
def resval1Tail164 : Box := ⟨4710066198271816082760650933820826822,89397279619506593412242976040513461161086⟩
def resval1Tail168 : Box := ⟨30867868179003819107344860867423205677,282523568658904359066314808457086217609832⟩
def resval1Tail172 : Box := ⟨202295660466752900340455107484444896312,892809256819983547858258742882868220570605⟩
def resval1Tail176 : Box := ⟨1325764840411458406107368395822058904087,2821031734357049781887888507528957930014691⟩
def resval1Tail180 : Box := ⟨8688532458117337883869996841529542230576,8911354921795585793308305179102189060686486⟩
def resval1Tail184 : Box := ⟨56941166317516771782261969462320968679284,28134801108854680309087287367776690003162064⟩
def resval1Tail188 : Box := ⟨373169627578477248630207538875667591264061,88726657810002787331339631831075255339391999⟩
def resval1Tail192 : Box := ⟨2445604471298308004471936805204442607166168,279153850146242478893205270687126459008544771⟩
def resval1Tail196 : Box := ⟨16027513463100599551153228256513184399094883,873965824587398685931963410102147765165308084⟩
def resval1Tail200 : Box := ⟨105037912231776578342935642591731992261934328,2707780538890789465633833874120587019661300070⟩
def resval1Tail204 : Box := ⟨688376461602233856974053027134081484039602627,8201518890093827158673024600281917891406253482⟩
def resval1Tail208 : Box := ⟨4511343978785621012880201231831778402258410789,23585115404375812144560597207353534820581034639⟩
def resval1Tail212 : Box := ⟨29565543980543369289621109196587725795015819636,59233142529976006465533423684173827159046355265⟩
def resval1Tail216 : Box := ⟨193764693531720809675451273856107174366534775947,86886171116386933000998494847286264862757235321⟩
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
def polyval1Tail5 : Box := ⟨2011054398927386312839692069335646036031907392390628,117595522204364224703367795366248710833001512262366⟩
def polyval1Tail9 : Box := ⟨190751114306376875285674199945410997299996845309,272072238126781493536140226834247254061253539935588⟩
def polyval1Tail13 : Box := ⟨15394428665616077466091045240555538681338945859,859858854002979684255233978541824205533238801229564⟩
def polyval1Tail17 : Box := ⟨99950653541258108497671271192149591339572681029,2717526853233478601268397533044629509099127213135423⟩
def polyval1Tail21 : Box := ⟨655033432549986071874346871970901136999975164972,8588387703256904823772726535400294657591959658685520⟩
def polyval1Tail25 : Box := ⟨4292827067167063151200706552267200458569419337290,27141323723440069127123058766899251289517204410706076⟩
def polyval1Tail29 : Box := ⟨28133471466176762930104469803754873060056237848733,85765420070877101221090256457100055571102093293835653⟩
def polyval1Tail33 : Box := ⟨184375518600631200673081408773366073146029549308332,270965620862138567761526886080922099417780555450907833⟩
def polyval1Tail37 : Box := ⟨1208323398701074676380442573146093303057082197879591,855759566397215395734633003999867835705317277732443007⟩
def polyval1Tail41 : Box := ⟨7918868225727352761030177353373098390214763418440402,2700522857549020993724744702115608737803088327265429085⟩
def polyval1Tail45 : Box := ⟨51897094804126770483373833489117940828562658885781447,8508116260730880346892979182443940760792501636793412135⟩
def polyval1Tail49 : Box := ⟨340112800508325211553110901412821831990219531349760266,26713756570071450388346961828277423945480319922020449121⟩
def polyval1Tail53 : Box := ⟨2228963249411360913245438781233314791433447594393926082,83274623897112375033502078302688448393223452812490596096⟩
def polyval1Tail57 : Box := ⟨14607733551342358808982210987564837342096396477177889588,255625825825325302672886943151816736760185437841003891292⟩
def polyval1Tail61 : Box := ⟨95733242602091979396145293052121683890252262673361117399,758338253699486717173787256075821851311210172654160963843⟩
def polyval1Tail65 : Box := ⟨627397378732100430079422078567291320198458063885297142881,2071890313294861030225986320098110962441464170978362950406⟩
def polyval1Tail69 : Box := ⟨4111711593356631368700724711409501481482081307715232922456,4419370601782679083632939094598128658867988253096133724301⟩
def polyval1Tail73 : Box := ⟨27031250000000000000000000000000000000000000000000000000000,2⟩
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
def resval2 : Box := ⟨112448408139864313326221234877339075086676567484718175458,235580585125618299757346132647041601468415046504623619⟩
def polyval2 : Box := ⟨3767634497931141648376147407421870598197462060661843470717,7682994075205811301505146820793175453528520212157431332⟩
theorem cell2_lo : Holds Q cell2 (3/4:ℝ) := by norm_num [Holds,Q,cell2]
theorem cell2_hi : Holds Q cell2 (7/8:ℝ) := by norm_num [Holds,Q,cell2]
def resval2Tail4 : Box := ⟨-138528740065851904801840260929019275323436258247449,34095377821286673002406486201104239573714452310922031⟩
def resval2Tail8 : Box := ⟨-443638852965776739873262631406350163507237925618473,58050081602173622536516253748931679956638890166895019⟩
def resval2Tail12 : Box := ⟨-1017987165046543423207396309636180702912444919883602,98769728085817278124619786118327159502174781261748040⟩
def resval2Tail16 : Box := ⟨-2335870845178769477623621879461662225252096037663556,167897565926694432679577584774713724666219766334839261⟩
def resval2Tail20 : Box := ⟨-5359883467350820308607084703529788449194863608671262,285050844153504638472225895094167232862509117406855641⟩
def resval2Tail24 : Box := ⟨-12298775355075834857354387612395839139920972329086763,483129104834438940973250633888725819841736188736660520⟩
def resval2Tail28 : Box := ⟨-28220739528386630614111949256057187017384944899563682,816957351790335800725268951276654955894508759458318900⟩
def resval2Tail32 : Box := ⟨-64755239162926588138107726702913186652191902700535403,1377081271474927256857337103309805416809193435774304707⟩
def resval2Tail36 : Box := ⟨-148587211714630331310784573389167586625560984545813788,2311122220843740909669708243153019459297109415551765393⟩
def resval2Tail40 : Box := ⟨-340947848707328643831381108519075823491224771378790418,3855207851317281353245583156883126161880927363240979067⟩
def resval2Tail44 : Box := ⟨-782338090854083890399634830985063514161923222656019285,6376118280366575229392688333575660871312036113726616889⟩
def resval2Tail48 : Box := ⟨-1795151049410498290713665369191743886720393003629301170,10416859486416165490128127270101071082602840544517582093⟩
def resval2Tail52 : Box := ⟨-4119149160539421278014532680322495541836376505456089053,16714001674423516826891667577436704271667112251920989461⟩
def resval2Tail56 : Box := ⟨-9451789481639687483674660066990628245059001463064458601,26088646095206692723262831433071332781250972737968780465⟩
def resval2Tail60 : Box := ⟨-21688052780666703580415638717851626479916239597110366322,38942361264628063540180391737492210592390718012911785188⟩
def resval2Tail64 : Box := ⟨-49765352293502077566260344770178412380865556897653261449,53667457333547572648359549753909939979391208385267013448⟩
def resval2Tail68 : Box := ⟨-114191341964880175492510888290654179023065806503988817280,62260355267083018813306536911109905816934655187822489629⟩
def resval2Tail72 : Box := ⟨784391650740085043616082398138682240919042508207370162941,1063448005171106861786686078772213872856584506322363244⟩
def resval2Tail76 : Box := ⟨-27606735840080441528935755685247345908524187267471,401857628963558144751291682806839092136013452600365⟩
def resval2Tail80 : Box := ⟨-4846375797793433685959942407543552544022009124519,684176849112261309974404544628033843621780980161073⟩
def resval2Tail84 : Box := ⟨-11117461806185365594929771947039013965464767744648,1164323481078232359652090485070246825665574656958148⟩
def resval2Tail88 : Box := ⟨-25510098747976680517426149879684719248345727478302,1979740254901903508235994805754090694862771140729007⟩
def resval2Tail92 : Box := ⟨-58535409524345550815013082787612514834776382309621,3362333165461965990602741434315159604566290984110275⟩
def resval2Tail96 : Box := ⟨-134315206000712804863748336127591869218203642608877,5701535557491106657016458107555378432351638610050113⟩
def resval2Tail100 : Box := ⟨-308199339675175316064969993258875062653175829977241,9647504420117615372086207672926753653724225706766313⟩
def resval2Tail104 : Box := ⟨-707193442980017757073910025587967697473606288227163,16276797644113389367120240884081171622574218102061085⟩
def resval2Tail108 : Box := ⟨-1622724326148889861302479272923057663331754313225966,27351214654581887129241535167163435422554585736793702⟩
def resval2Tail112 : Box := ⟨-3723499227565338952788464884455895553967063627077956,45704761524235270187225349503068721903927429675085914⟩
def resval2Tail116 : Box := ⟨-8543932123445329423840110853537753739059018962853427,75778498546848421114144843870988705579313908466995948⟩
def resval2Tail120 : Box := ⟨-19604885530692661698766800482718476799685727107078499,124245458503261191827753668559253610030297898189885235⟩
def resval2Tail124 : Box := ⟨-44985321877366840031546655421790370326409200287096294,200417014300506957097811654852573342389812814959897315⟩
def resval2Tail128 : Box := ⟨-103223208380487929852884818202614746918788833667104542,315422343049987393908424090321069139110348822978447961⟩
def resval2Tail132 : Box := ⟨-236855718792205402480839409137379363548332237384375876,477335109470712004274274562103180985119747931898155552⟩
def resval2Tail136 : Box := ⟨-543488546873967708207022417497863240611622898556364937,674889475867345901698702552933108662593406994438635283⟩
def resval2Tail140 : Box := ⟨-1247087628040082400324033984337395723580669887789908221,831411624283201790825423662017910315635904049249443724⟩
def resval2Tail144 : Box := ⟨-2946131922488698957544307752941826525911628490602775188,676005809092775951335699693775094950082602810245383107⟩
def resval2Tail148 : Box := ⟨57573135531218938023567833617152610400777555,43948427650850163986339569882246124672912344⟩
def resval2Tail152 : Box := ⟨557376461366736023338939519795967366677936,73812286257363301003427582449107283720081431⟩
def resval2Tail156 : Box := ⟨1276718355069656712790956998260680595567983,125592967525645912515328350025151276348239430⟩
def resval2Tail160 : Box := ⟨2929554102308859466918289962205152147040292,213504528421965617848148776665197748451806552⟩
def resval2Tail164 : Box := ⟨6722147600452717115684625163245270145931178,362504841994454081333009515712533273402631625⟩
def resval2Tail168 : Box := ⟨15424623267499896152803441227566856137061298,614460320248004125420368063857333590514927322⟩
def resval2Tail172 : Box := ⟨35393302421444249328867319472087668023132201,1039162602884471708601659607094203914670010735⟩
def resval2Tail176 : Box := ⟨81213384247462277754428692207534711018349243,1751931550418523457368531133370666760201350518⟩
def resval2Tail180 : Box := ⟨186352030742680151554855784634821264246396131,2940912297617118919379725451586439663388276995⟩
def resval2Tail184 : Box := ⟨427602909098150849253120966799832328739668647,4907371971768878302802761361011335773613404302⟩
def resval2Tail188 : Box := ⟨981176578224026261522964089509242756790538581,8120055038615353749605400810493428070877769190⟩
def resval2Tail192 : Box := ⟨2251405351020264874936414051324847464788743831,13274893983662825723464774835547147198319877602⟩
def resval2Tail196 : Box := ⟨5166069153197159734868511257544712242010980849,21321112052492944019630549798886145706915375158⟩
def resval2Tail200 : Box := ⟨11854049508908269104150835421334201895611554459,33331912264730492211599553224917320259398926270⟩
def resval2Tail204 : Box := ⟨27200272701089383009335535932031322112560025883,49884983202627600002019798216493907218079837074⟩
def resval2Tail208 : Box := ⟨62413678503528515024380963239310994634296108443,69090364887422993552076922127407585792670348634⟩
def resval2Tail212 : Box := ⟨143214272478457193741328932740783643364013836371,81125819927225557722231711932786783124411445951⟩
def resval2Tail216 : Box := ⟨328622198163329234608353369288453570159583959426,54094832286255653058092324249592913283589141510⟩
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
def polyval2Tail5 : Box := ⟨21882190439930651612636876550265822499193826530295042,3052392781148251707387637901448734088998578436495875192⟩
def polyval2Tail9 : Box := ⟨45657152453593451074192359109665857965775180598270866,5195530233777450652144007127093863340717594376424289185⟩
def polyval2Tail13 : Box := ⟨104764367098199300541283847514055876978062732550235210,8836469609145636428650501616972083509069230702303212689⟩
def polyval2Tail17 : Box := ⟨240392057459073371389625791095406199348962845471782891,15012958365749495813812085996006363481229407853322908149⟩
def polyval2Tail21 : Box := ⟨551603020818865594595779124187604526634909326308979533,25469939392117571687877686158544067235261647397133319986⟩
def polyval2Tail25 : Box := ⟨1265706928062211926412358522401276524509780659064337446,43125895622286653289247637836645276144708555215534154742⟩
def polyval2Tail29 : Box := ⟨2904287988427754973343630113926900796476592642904418283,72825826149943320084912995929796986814749072306156228125⟩
def polyval2Tail33 : Box := ⟨6664172039130329786311623610432506359025166608034719860,122528059327286964415975526971129785761753676915644644446⟩
def polyval2Tail37 : Box := ⟨15291592687806634666423699164617446009302578826512593771,205104650409588299544946272322596518239998768377293578118⟩
def polyval2Tail41 : Box := ⟨35088050782118819699831217103885482491055218984100682326,340898209828847298803418873768177356484716305580704410602⟩
def polyval2Tail45 : Box := ⟨80512954590418366580081277817969663034476966638933821741,560903006868355986353035047256840874378953275456329088956⟩
def polyval2Tail49 : Box := ⟨184744826583020835166349261217074214480459171587820219282,909482486259602967283745731892726992555892975284468287727⟩
def polyval2Tail53 : Box := ⟨423915022406248152337851576077016542760482746357836307557,1442788465058719401439219337992849100895262294270249442254⟩
def polyval2Tail57 : Box := ⟨972714362536881781208848627155501125611168449878391277118,2211799375345878408987881261668139529648486074781830042464⟩
def polyval2Tail61 : Box := ⟨2231987971822325388588759372952226380384397854474466421576,3200651874228408150546220957587794166034490938327428571874⟩
def polyval2Tail65 : Box := ⟨5121514082899576409838670037162898695409371208408364358172,4146329652814480084661480621079545267214331728997501167366⟩
def polyval2Tail69 : Box := ⟨11751813659072809350766718749811499463060464492593572320018,4058718687700417878740808608612600016877362581149105943109⟩
def polyval2Tail73 : Box := ⟨27031250000000000000000000000000000000000000000000000000000,2⟩
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
def resval3 : Box := ⟨112265728374969578899723520267978375945653984882537861265,1754104531037037674656879384383530792145157841368378161⟩
def polyval3 : Box := ⟨3785710671976424946616449888071365812043276598537266702552,239043025052169478420999803177748940837564209497292251843⟩
theorem cell3_lo : Holds Q cell3 (7/8:ℝ) := by norm_num [Holds,Q,cell3]
theorem cell3_hi : Holds Q cell3 (15/16:ℝ) := by norm_num [Holds,Q,cell3]
def resval3Tail4 : Box := ⟨-190090822410233868631348752226236802798820021255559052,1993286627673999738168500401037125642514286911809950607⟩
def resval3Tail8 : Box := ⟨-281898912451228166700913694286051889450956184733612245,2544636378506397892011412872181081200627616692750049015⟩
def resval3Tail12 : Box := ⟨-417927868259393591728830292595280481962229070867650519,3241130249866202252185664325148091522391851139885848840⟩
def resval3Tail16 : Box := ⟨-619596924551387173664264187591075763372931285201592970,4117193847395720227944014794440929783666716776696624478⟩
def resval3Tail20 : Box := ⟨-918580401224430945554986534165892575509845378309932449,5213376537646224021371986160076513772402615686864135073⟩
def resval3Tail24 : Box := ⟨-1361836897632354289196374381555702899899498093058552450,6576216039569171829007528709579403430695420396026386514⟩
def resval3Tail28 : Box := ⟨-2018984656412010984134446878205418799882220109176198123,8257128672821356250010857978582605238372886048670966104⟩
def resval3Tail32 : Box := ⟨-2993235863937926836096222686451989959071861356841819155,10309586124104304375780223072601047091466534394944779631⟩
def resval3Tail36 : Box := ⟨-4437607244171094049237604308429097403700458616657907987,12783404939697264759792087786585792437429985996765075317⟩
def resval3Tail40 : Box := ⟨-6578952995575943809852250076341704791869587814800781794,15714306352216584840113043013274786430467576756128433965⟩
def resval3Tail44 : Box := ⟨-9753594704635132084761006741247248137263739751082984185,19105882719896841398146828506391425785565726455428342924⟩
def resval3Tail48 : Box := ⟨-14460144300507843780297251106739872312021018945386560352,22899553724067512542172992063164182436957321137650781482⟩
def resval3Tail52 : Box := ⟨-21437816469054467296821081838379043060830903735111683493,26925742439361740954295087316789832389606533277232309655⟩
def resval3Tail56 : Box := ⟨-31782530340635826354910099000545409384445080471378302712,30825947617328892883430055240766823366970107889446080655⟩
def resval3Tail60 : Box := ⟨-47119035481597688795441144965864920540755949233875784989,33930035361917886745724273338546612566761290432751520847⟩
def resval3Tail64 : Box := ⟨-69856096438496746103224779081121427829972309868196284921,35065027640585385165885295455081241695497666590143201801⟩
def resval3Tail68 : Box := ⟨-103564713852868978572889629551430110547594291871755536650,32259594050408903950398650727127138230279588825668612593⟩
def resval3Tail72 : Box := ⟨785091901804304333077417806077124140469143667840931307738,848641501524773551747889547379538133243207840957787403⟩
def resval3Tail76 : Box := ⟨-2341262137197116875058866830238022743348903512555649,25229875478817193590360251013337921873127190191970319⟩
def resval3Tail80 : Box := ⟨-3433434403825610308329170957738334562699015752099917,32225472237302686291837696910099196526221212460150197⟩
def resval3Tail84 : Box := ⟨-5090219514085332382011122828064385109055703817996577,41071598153609349636248950000150004429242461992942667⟩
def resval3Tail88 : Box := ⟨-7546480135148799927749623490237715247913551203709332,52211759521610909333569968434010580722525879505378735⟩
def resval3Tail92 : Box := ⟨-11187997350687876121587478696693013209691743581491084,66171330928725094987832838528649106292661585076788821⟩
def resval3Tail96 : Box := ⟨-16586710953630696376085549617796612602813099027381613,83557900169719571696281875610403875054296220338509767⟩
def resval3Tail100 : Box := ⟨-24590547497973592665102554277793945137364460743717419,105050484296196938420332912192348446430055038266007793⟩
def resval3Tail104 : Box := ⟨-36456596364436706016332068208558195860649077096447156,131368680863469662830783507604924633277530525136621243⟩
def resval3Tail108 : Box := ⟨-54048549288664029491157063607430212545466488388825575,163207695025569487316500609011458875214232428135733041⟩
def resval3Tail112 : Box := ⟨-80129413371644612801552667311177295382037951935228749,201117109638283441666037357234808702568505995906862466⟩
def resval3Tail116 : Box := ⟨-118795471326934586842827810114212760216082720770716632,245288916465236178150153930785949737288914163241192222⟩
def resval3Tail120 : Box := ⟨-176119647130506490882839284106900351735005958199597510,295201526960312338888364767368190125576581639465395866⟩
def resval3Tail124 : Box := ⟨-261105324629840155714854803330486207271172211107400525,349037973448498666761233994882905953731989347139349455⟩
def resval3Tail128 : Box := ⟨-387100426674913266411831850671892394033202110568408607,402753423850756199653157341843964969474267155923080818⟩
def resval3Tail132 : Box := ⟨-573893851243120838655317372901910725283711543063010932,448602187236899553561210412099503582237278517169793883⟩
def resval3Tail136 : Box := ⟨-850823532616357543378112790025014203181107459767854131,472836721775014136139116273606792635103486654965372571⟩
def resval3Tail140 : Box := ⟨-1261384419636703673208274647621118653245166400361223172,452144564879364272399186617262035085754968116063978739⟩
def resval3Tail144 : Box := ⟨-1946054451590728598510931018354808011447533646912157987,343503081069525445091785244731227228884859609058670081⟩
def resval3Tail148 : Box := ⟨564101860636894086572202550286421526879317661,4953494597798549170431029007860124339822331178⟩
def resval3Tail152 : Box := ⟨751618463028600019040788299110524814085068733,6316635093797100854481248153864995904947980551⟩
def resval3Tail156 : Box := ⟨1114306858238009206780757838059792697229125194,8035816620660933279093081703060211988684532519⟩
def resval3Tail160 : Box := ⟨1652010202278625545758245478688046780201558622,10193174830682829880816434373000874779894638661⟩
def resval3Tail164 : Box := ⟨2449179675212545678374876786095996013165943837,12884865684197418698873695035734641558901707976⟩
def resval3Tail168 : Box := ⟨3631019392738765943350148978011586960145344442,16219489183543529752711589291019051844192685291⟩
def resval3Tail172 : Box := ⟨5383150106902976577430174933669416602510397763,20314092955916510370171527677690672423356888208⟩
def resval3Tail176 : Box := ⟨7980762959129250700269941997503479857247017664,25285301660425078117278597270367452763257705072⟩
def resval3Tail180 : Box := ⟨11831841235141214286710921401190198501673486266,31232352560554834964864756650723288682478980412⟩
def resval3Tail184 : Box := ⟨17541238567103363319287765884688898269429364701,38207008437237106483088539995442313103098447574⟩
def resval3Tail188 : Box := ⟨26005677759955344899587204358464441975771416486,46162561562048744561536231563449309853506826815⟩
def resval3Tail192 : Box := ⟨38554590838468636558849911083323526278480749527,54869956958210079627896820473440318853878934411⟩
def resval3Tail196 : Box := ⟨57158920772702913066952073648871644023440529400,63782731857482496207517538767598282143232307184⟩
def resval3Tail200 : Box := ⟨84740679458599524219557427369654339787283494726,71822918502325532601424950610302533679894432578⟩
def resval3Tail204 : Box := ⟨125631881393647631085862192703554638540100118061,77045688106938773693696413829031029423336091874⟩
def resval3Tail208 : Box := ⟨186254933561400593670775405100409935081209189639,76118936952997946819102774329498795896637183067⟩
def resval3Tail212 : Box := ⟨276131344197964123275907840420462322880904737221,63521672705658102534195934300208909140558971337⟩
def resval3Tail216 : Box := ⟨409379957738284974278603003626350256653109495415,30316435708095693125390660737927337138227216099⟩
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
def polyval3Tail5 : Box := ⟨33404860594161923991928945802821721566256523896329501877,301580624916464728398738604203377351255669525983199723661⟩
def polyval3Tail9 : Box := ⟨49521290374357303940588733741267592053281782153583516329,384127679614237307901841029867115322572344117232122300370⟩
def polyval3Tail13 : Box := ⟨73417547459885765775438471592596152631058662492903281203,487957640394959025441630649878878928998104678529255206347⟩
def polyval3Tail17 : Box := ⟨108844827225890037768722208258878288192008796734026029624,617876838181439786764798731553506548999330804978056857529⟩
def polyval3Tail21 : Box := ⟨161367368207564462351952632697872022138988177837217670588,779401640466701951959206446599238111798783184653345972497⟩
def polyval3Tail25 : Box := ⟨239234405399855373478857507887769783910893064895784644702,978627081068820644061579212867667947906618527544507731938⟩
def polyval3Tail29 : Box := ⟨354675801946551297057262146696150429779868936458094125925,1221892501800829472810520918199093802592139794391820199331⟩
def polyval3Tail33 : Box := ⟨525822881855877611373614925600289733203090069138864684025,1515105125144386015948156595229260651826463590816158872407⟩
def polyval3Tail37 : Box := ⟨779556151183064046993396737670086413653711395283458314456,1862503263469168586685688426340632314064500358798474700079⟩
def polyval3Tail41 : Box := ⟨1155727173192737492085704656806990252330492424884375721479,2264519854928718663583622593049877958022656224770339350618⟩
def polyval3Tail45 : Box := ⟨1713417688807910729262467982244429563811173811300852165700,2714222987438365826155946105206354530914956131188530456234⟩
def polyval3Tail49 : Box := ⟨2540219045131204996138230967854888062672966824942028567678,3191531263184369924107653827223222669547069940751527273901⟩
def polyval3Tail53 : Box := ⟨3765989366980731011638784202096261529014874930022063744759,3653980770417185393506631578055794695157528670180077672244⟩
def polyval3Tail57 : Box := ⟨5583249184512502158719118557395035084231776706816947080635,4022186132514852940434211955659100925225277464575940936422⟩
def polyval3Tail61 : Box := ⟨8277418871565034926553046424623376760618161189846036868674,4157184761752599746167134529764646694031012233921996099673⟩
def polyval3Tail65 : Box := ⟨12271647012542413719081077418023140237056445264602980906472,3825423283035170236262812318911449947545848719413957359860⟩
def polyval3Tail69 : Box := ⟨18193270573644351821899051641070512570734760609373611116325,2645003071966517813646931191513051767318091866008665731783⟩
def polyval3Tail73 : Box := ⟨27031250000000000000000000000000000000000000000000000000000,2⟩
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
def resval4 : Box := ⟨108984486514886493026773487457019600070306582768915948020,8937790733774795312425551095329461685358763842923888958⟩
def polyval4 : Box := ⟨4611619951054962636249080262157877239306085668722513087404,1894578135965303741276843824623603330515836793916611478829⟩
theorem cell4_lo : Holds Q cell4 (15/16:ℝ) := by norm_num [Holds,Q,cell4]
theorem cell4_hi : Holds Q cell4 (31/32:ℝ) := by norm_num [Holds,Q,cell4]
def resval4Tail4 : Box := ⟨-4098392121324867617503406470569909099268066846978996728,9677876357880790854154911726694444297471532342634335152⟩
def resval4Tail8 : Box := ⟨-4966149748877883831520643873981571293901894223768273688,10675639398273149270287064327719438104041118450235638219⟩
def resval4Tail12 : Box := ⟨-6017559144996606762647849045966519082689999283119175847,11742301976912349785498738303918887617093950987913224306⟩
def resval4Tail16 : Box := ⟨-7291567884426324444811630901502807148786095471046761013,12873175673946753406483709420243960409085630315672745681⟩
def resval4Tail20 : Box := ⟨-8835303639243280282444607075213452552287137150921348801,14059970146046527659562752996768381623600535151781694493⟩
def resval4Tail24 : Box := ⟨-10705871718530538816546436712108596385667657274109082418,15289676411597575110472563732970363844571809461152904315⟩
def resval4Tail28 : Box := ⟨-12972467493312833252398423756643204141884757125049746511,16543166559510239745015184806648456005178882576068990345⟩
def resval4Tail32 : Box := ⟨-15718936046448024288332876276871464059672422391798770518,17793442656984823034038597886977944314830992581487058402⟩
def resval4Tail36 : Box := ⟨-19046873739301537281890842403645337017465413552782067566,19003453228174894021753056855752980952083072730118775709⟩
def resval4Tail40 : Box := ⟨-23079386427230356040478467396180006710541677006044493859,20123377397575540555872874264046971423508632906913997648⟩
def resval4Tail44 : Box := ⟨-27965643346410807768282059476424881360918091856075010025,21087254509035541398462730766585833310981854198262361496⟩
def resval4Tail48 : Box := ⟨-33886395127728026530260852078629777177288807074528242451,21808809877542574806942010590541001495087089576453464942⟩
def resval4Tail52 : Box := ⟨-41060660058081028674414204633475408881220640984752509831,22176294254388991934464775655167594303839894716861593311⟩
def resval4Tail56 : Box := ⟨-49753825924838931026897793376869810324921980818945601801,22046114309495265658252356424354088704726695605821500480⟩
def resval4Tail60 : Box := ⟨-60287467143915096486552282472464125905701732817602755534,21234982406396881641328175301015015316501784757215576766⟩
def resval4Tail64 : Box := ⟨-73051240317635656850952975849641256979972663908239034968,19510254282275373635986148295519419176336335322870162991⟩
def resval4Tail68 : Box := ⟨-88517201458977853596580746384092317286864185647596300843,16578047910131913185889961787233414388888261060753683700⟩
def resval4Tail72 : Box := ⟨785400963525116919887334004354472693579895612939259168163,825229075565155385453465619097926654857202540363892526⟩
def resval4Tail76 : Box := ⟨-52500188265438922557151542140221217975521422473786804,126886140167728096352341768359544716882111722007703989⟩
def resval4Tail80 : Box := ⟨-63584633930152569971332536069091051270621929908149864,140063715241686564254750036322281360376579894202189747⟩
def resval4Tail84 : Box := ⟨-77046465866504186277868549637250518944428788077423527,154178130008053030089901556936224695818405486864521608⟩
def resval4Tail88 : Box := ⟨-93358373815453258082194309294468518374042040524836674,169176600314012407542610055095084750946151169114843080⟩
def resval4Tail92 : Box := ⟨-113123760623177251772902056624389122999409449629740822,184961364709951763705630974609490787134800464243694520⟩
def resval4Tail96 : Box := ⟨-137073780256998406876245939719166762557177138967710893,201375381571818774613696688432421338551988364109533065⟩
def resval4Tail100 : Box := ⟨-166094383093681183844255838428518915987194839168341499,218184554054270843658214717116177162180197303227671358⟩
def resval4Tail104 : Box := ⟨-201259088671423964493542379070635351667381862886835338,235055484358156245544152380812011188953185072538258017⟩
def resval4Tail108 : Box := ⟨-243868696932431397977980442601324363537352637910952309,251527714983556541998319549782225466208277394449322929⟩
def resval4Tail112 : Box := ⟨-295499406939162378728420150950000876460499604376154125,266979181009805722860634746102656674267085795520457903⟩
def resval4Tail116 : Box := ⟨-358061123054224448127561215708566980068511869015093315,280583312575476637279024102883769993048512010738776035⟩
def resval4Tail120 : Box := ⟨-433868105424820585445636291175766607411642707742761792,291255879557491073281766082635779132651936850903705711⟩
def resval4Tail124 : Box := ⟨-525724578248658694136372288018068269857464595653468275,297589247508213570758623954256031221137329428808253901⟩
def resval4Tail128 : Box := ⟨-637028462611021586707453060581810192405432946196994430,297771198855082765456816325018564227627206157285025509⟩
def resval4Tail132 : Box := ⟨-771897071140225942500534593661516058569689352305449084,289484846348921940744813314606422769654921485754550287⟩
def resval4Tail136 : Box := ⟨-935319414147485711744676881048797922251704716731865697,269785402663582374308449404158332619320277274051366530⟩
def resval4Tail140 : Box := ⟨-1133340882357412267611753704992645196966656901832193729,234948633376196697940177210380654416335064406596443445⟩
def resval4Tail144 : Box := ⟨-1445615657236354453655949601739123614899200503264735997,177029779684081968776594140481285677951240866167758312⟩
def resval4Tail148 : Box := ⟨17370224992656217632585640810474870957148478797,36911146069711383139183649734557324226614473987⟩
def resval4Tail152 : Box := ⟨20978672766332791885420633625565649203405146446,40587745279591090665888192751072212489027689446⟩
def resval4Tail156 : Box := ⟨25420175507493341814614632467070398491830693872,44483018191684851579656347523132689882494049823⟩
def resval4Tail160 : Box := ⟨30802013055203037837343420372578531715725360254,48566849413543994620567035762528652271110084606⟩
def resval4Tail164 : Box := ⟨37323267417410993872374576833902029497020421986,52793020498108384323038714540250280881461459042⟩
def resval4Tail168 : Box := ⟨45225170452821634656279221340853572003443256658,57093863675588703870690218825668837322567612118⟩
def resval4Tail172 : Box := ⟨54800026471761908369822982291076246336900232175,61374141230144165306751598368796584110604094612⟩
def resval4Tail176 : Box := ⟨66402025050155309254583850519179288675381679655,65503415185847838598261925396980344391932420756⟩
def resval4Tail180 : Box := ⟨80460343080919855782365776310689847118028724661,69306558701397207676451879637735063848031546882⟩
def resval4Tail184 : Box := ⟨97495020728802092928032172982631763301960687465,72551982862123178000631440746130528286553632466⟩
def resval4Tail188 : Box := ⟨118136198566168001951406499083107296038401024213,74937057848529722181915668833834517250246240033⟩
def resval4Tail192 : Box := ⟨143147427502850196029152485710064407350850767858,76070092096918602711102283118661367991939618580⟩
def resval4Tail196 : Box := ⟨173453913782460621538976349744584208130969857762,75448092595138986826299230788116293155274440985⟩
def resval4Tail200 : Box := ⟨210176743873753776682576743835491316595211803717,72429358466526398093459666602237221929062566377⟩
def resval4Tail204 : Box := ⟨254674355291718611483881243237331687698048415246,66199751921394749391740991796080565711520002697⟩
def resval4Tail208 : Box := ⟨308592787421883405787458004848596147098130534030,55731237527322136942372958934117429403463184284⟩
def resval4Tail212 : Box := ⟨373926571264079180839309078605241082835545105940,39730972888406573340495286832930476365249465952⟩
def resval4Tail216 : Box := ⟨453095158747060629739778407515004944790072236631,16578696386842862571458679758362660900980799017⟩
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
def polyval4Tail5 : Box := ⟨1030756132448429322284647636695980469290679958882876529904,2083840205089119950460487776090285482263909404501110091954⟩
def polyval4Tail9 : Box := ⟨1248980492248722425141088945511700700363267185159740732051,2287364538227776107672213096560775629083839004806655488244⟩
def polyval4Tail13 : Box := ⟨1513408647059524103809999793186415960104927026378829429038,2501796774891156155155388393052560426139227393259715785311⟩
def polyval4Tail17 : Box := ⟨1833820261837698506819217821821245919366947198703725308358,2725088567011036626813829436903897244836918009268859449190⟩
def polyval4Tail21 : Box := ⟨2222067885802503245309490737347290240808178858370883643547,2954167829594213031469881222965701591396693002158771334268⟩
def polyval4Tail25 : Box := ⟨2692513433223155617959714900278712833308907435286632105050,3184642085176347112627215062011059835281287356456666500164⟩
def polyval4Tail29 : Box := ⟨3262559453924572584758794040383681601910642790002941456355,3410428193201239362187021086959413424221409559791276520186⟩
def polyval4Tail33 : Box := ⟨3953292882052784078769749510298836944764528690898708416551,3623291402519624548718804864154823708642963382857134218749⟩
def polyval4Tail37 : Box := ⟨4790265076239289609843942322042372045316877910377123737690,3812272865810537030779420198926236750530549471447489180174⟩
def polyval4Tail41 : Box := ⟨5804437006125018297617906895961166152511362819364363237119,3962980112839075663989851438654709331067403476102655674144⟩
def polyval4Tail45 : Box := ⟨7033324549238486487251854169981968813771305705391537741198,4056709324311648041241998377266339182336097129158821390369⟩
def polyval4Tail49 : Box := ⟨8522386264631864782372612729059116161575406987037676522217,4069361361022241473336503264992778326019760218627274869933⟩
def polyval4Tail53 : Box := ⟨10326704979290312227939194969578093420694903475634735464215,3970105118496181118569040247313074558614718135201308541270⟩
def polyval4Tail57 : Box := ⟨12513025391944707127324900377745155758334443789865546869390,3719731573079986506816013973322741579095253974259116277704⟩
def polyval4Tail61 : Box := ⟨15162223068583639101426830028783510181367825252816985289284,3268629470078440333438899690040899730053941437560492813954⟩
def polyval4Tail65 : Box := ⟨18372296161855201154046525205394153679205995886301637993327,2554298503116350499984706814629430384487127034773725201483⟩
def polyval4Tail69 : Box := ⟨22261990613011453621801359380325302333488957586630619182185,1498297464501268079849671393808822462650789232970962497685⟩
def polyval4Tail73 : Box := ⟨27031250000000000000000000000000000000000000000000000000000,2⟩
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
def resval5 : Box := ⟨96778505021958584924295247543881079408080546433374782559,14393415315668613388104613273971384577104194188639058945⟩
def polyval5 : Box := ⟨8650757879994459458950024015071745395901760083956837183008,3792760423872870848763077972126111873619129484240229560139⟩
theorem cell5_lo : Holds Q cell5 (31/32:ℝ) := by norm_num [Holds,Q,cell5]
theorem cell5_hi : Holds Q cell5 (63/64:ℝ) := by norm_num [Holds,Q,cell5]
def resval5Tail4 : Box := ⟨-17124604207399776503155979930300477712138865775135187127,14597842482953022086023833829792824216162988624721259117⟩
def resval5Tail8 : Box := ⟨-18828760976350343284287449693495521239871480920260361000,14956331186987584237669833098434967361513458793322160633⟩
def resval5Tail12 : Box := ⟨-20702441636936615503901953852603554865610632658822695341,15279351811702456817041620386502305572209819243975257653⟩
def resval5Tail16 : Box := ⟨-22762575303171679661761746359969933067295701918230227290,15558748589859583388279936770297130104183827470610262612⟩
def resval5Tail20 : Box := ⟨-25027716223964092196035053353672065208349263600844167369,15785254008066998163878298427178888790305276781112460909⟩
def resval5Tail24 : Box := ⟨-27518265004926563465698299526475276602138036506203595520,15948358011810145629425045875692281708043807234793673209⟩
def resval5Tail28 : Box := ⟨-30256652349138142465218080451707801957041534348496636542,16036163531150228956019970236594783581158769942659829986⟩
def resval5Tail32 : Box := ⟨-33267541075453413293438446641917089691768062819399499079,16035226275511789352126719815949135895010686991343390953⟩
def resval5Tail36 : Box := ⟨-36578048239976724087642115665596954440472250067962788115,15930377143980680064463890467092446074350059128127300188⟩
def resval5Tail40 : Box := ⟨-40217989361205859777905333603963910637668986999058779356,15704525427381270238953965557878519466921578779074321132⟩
def resval5Tail44 : Box := ⟨-44220146948417305310126373626596797441886161819285822025,15338440790822359861565281928628059151334563732259643339⟩
def resval5Tail48 : Box := ⟨-48620565751748230462612816526338326505852627114874053519,14810511818759024538255417736630276335948241044514518301⟩
def resval5Tail52 : Box := ⟨-53458877393094733836079157643437843901150134015538505493,14096478676989832737208044692522816469993251550605401867⟩
def resval5Tail56 : Box := ⟨-58778657301559185870974946672660410783769871966431380478,13169137195279833673983697148274004218942974610551175662⟩
def resval5Tail60 : Box := ⟨-64627817168121469302035241131636005957924691473065222519,11998011398141080890242255296953315700486097565085599028⟩
def resval5Tail64 : Box := ⟨-71059036448786425869923095486893103710448598761586996266,10548991206881086911345272124031144543580255423466121610⟩
def resval5Tail68 : Box := ⟨-78130142186593865788570368437347140520170774075860446468,8783928260632469611303734174735107408577094708124099415⟩
def resval5Tail72 : Box := ⟨785415742668877999743489455329208164943383175457200512345,839203621649144884435173622465630978972382484652254012⟩
def resval5Tail76 : Box := ⟨-224221384363617649300835744054381154293550164352860422,194257198813176447785192690363932129807304114914417120⟩
def resval5Tail80 : Box := ⟨-246506251934564119101808680884794465009681356472600475,199154675628683612294993793978679775298165740345436064⟩
def resval5Tail84 : Box := ⟨-271036488901403137827547372701965614965108240346553344,203601239366577333657845457278840004407456764274362739⟩
def resval5Tail88 : Box := ⟨-298007771097913859382290749581613685324877841670403256,207490826206388577331877736012095864292972310418310930⟩
def resval5Tail92 : Box := ⟨-327663009489762899698020281494213983079211550571053804,210703025611274210036116168013311996548443935554650998⟩
def resval5Tail96 : Box := ⟨-360269288926072122837716294337368510809089037312974752,213101219510638989647972869766361234458283942183403252⟩
def resval5Tail100 : Box := ⟨-396120272304807610215079960072398377520968766661605631,214530694714822836132684582152060787100179744063604585⟩
def resval5Tail104 : Box := ⟨-435538845396931386704739974016692853797692297239036545,214816549648940702865109623003428375856558208679890858⟩
def resval5Tail108 : Box := ⟨-478880024862059633826645554710766569312809232297403392,213761373758169664969809139523073451632121950624793823⟩
def resval5Tail112 : Box := ⟨-526534155645494537852874945960681452504143627269829230,211142675725679993425693934374151517223744920609750602⟩
def resval5Tail116 : Box := ⟨-578930426553439439321717299614643347269038777517194705,206710034189767586013445059623746477516872384032055953⟩
def resval5Tail120 : Box := ⟨-636540735668826211444572180114748750680156499803300364,200181941942595844230960984677840822351247668592158697⟩
def resval5Tail124 : Box := ⟨-699883940420963653163306712676603164279984065887748551,191242311614142122423018722218339781998447405658743514⟩
def resval5Tail128 : Box := ⟨-769530530586534828221302721769712739041458725780923270,179536607563772932009423387286410723227985832315005634⟩
def resval5Tail132 : Box := ⟨-846107766308545735133973951762642355638933549221989285,164667565087868019806283013512330646497137734148950054⟩
def resval5Tail136 : Box := ⟨-930305327422840302956499414621300507117915347828620754,146190454070508353636402329003189808332198246699483118⟩
def resval5Tail140 : Box := ⟨-1022881653113195067908999678267290251390059513517363858,123607832672752210657182042046965226724307465103665414⟩
def resval5Tail144 : Box := ⟨-1195296163311765469389639588272904096467942326111667474,93737644890831463520069902933582890339014718686454046⟩
def resval5Tail148 : Box := ⟨94901759683283999168804527377615329644308711276,71378149707627723737509091147944473850368315261⟩
def resval5Tail152 : Box := ⟨104282949537965590028699479287199450646322291693,72747280782062975477151382389835974911132334424⟩
def resval5Tail156 : Box := ⟨114660314541414861366008174032555494127014493286,73880391951946947987703403058147959403022781881⟩
def resval5Tail160 : Box := ⟨126070349082421864333056865012161606924118616914,74729243935474197740383835475404271098043982009⟩
def resval5Tail164 : Box := ⟨138615814733901688072732081636361022805927360654,75239735646330057509181047190178443600879820929⟩
def resval5Tail168 : Box := ⟨152409700093568686081848762728247425470438263649,75350703904640290230396872614794641082321190080⟩
def resval5Tail172 : Box := ⟨167576237438731685480778760394572707850080130627,74993111531612087205639139368355826015735846515⟩
def resval5Tail176 : Box := ⟨184252021602837348568804408329923613858219845821,74089147568776487621297554802877536866186839577⟩
def resval5Tail180 : Box := ⟨202587240193554409704718041195667970806728565961,72551230401574112377181008805927449821222371832⟩
def resval5Tail184 : Box := ⟨222747026231862502317613656686510461165942447885,70280903633774806295514395241026513943389441774⟩
def resval5Tail188 : Box := ⟨244912945394458511519554327537234926970173213291,67167613516888257145832606261494403364676195032⟩
def resval5Tail192 : Box := ⟨269284631254075680411793221249409768844744328109,63087355590580990090424311020527543701036239420⟩
def resval5Tail196 : Box := ⟨296081583245228675615810188519592469920737911264,57901176925507696232903053614489488563853642000⟩
def resval5Tail200 : Box := ⟨325545143548456630141965312821714689088500848576,51453518967158116536909854067412905183373685767⟩
def resval5Tail204 : Box := ⟨357940670697535181607720338290155481286375308905,43570384445404145555504045174857615665817457410⟩
def resval5Tail208 : Box := ⟨393559929485900719968811089678039445761008800069,34057310125198552955134545501181711763471449751⟩
def resval5Tail212 : Box := ⟨432723718751473562705713554566170287319418270071,22697125310053457589395361067704676838274002133⟩
def resval5Tail216 : Box := ⟨475787348232586641855016373647293309173722317689,9247334062998325822938776378831455356763603790⟩
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
def polyval5Tail5 : Box := ⟨5377605716723524861141581342172009761014211549322968006011,3868045513090971394789838876683914267274537897256841442394⟩
def polyval5Tail9 : Box := ⟨5912737857940399743499933796178959219572656220965023852239,3934062032766529439672188512680719127397236381013709015979⟩
def polyval5Tail13 : Box := ⟨6501124026598713595281396255590687994870897940396207221764,3985913214978063444844437243216591832986082582001357676963⟩
def polyval5Tail17 : Box := ⟨7148061460859067674376941830710438471144073533548887297368,4020841261744985921335327311102618962589148903982356748140⟩
def polyval5Tail21 : Box := ⟨7859376692272045524432271354304812099420845344033117065945,4035726295675190682063232129684574219184557323781580784684⟩
def polyval5Tail25 : Box := ⟨8641476060224791409018165301662339227909830741404594139501,4027044617953500173986384177125722342067861350799746748014⟩
def polyval5Tail29 : Box := ⟨9501403409365095810432226198134896335075100470239215635224,3990822453332316085421039473303612836901349683680683284008⟩
def polyval5Tail33 : Box := ⟨10446903528787452577193881612869533226638023171837895261507,3922584697537796499311968926182134801558907776970196067491⟩
def polyval5Tail37 : Box := ⟨11486491904155930458673061838857478567660641025551965462871,3817298144109636250360482088483257699613466653958840676843⟩
def polyval5Tail41 : Box := ⟨12629531410974332877939701511046038700083049001056609058555,3669308613983631408257758033849135179781759747765441249057⟩
def polyval5Tail45 : Box := ⟨13886316639728510772782920808935141570140047323415665794582,3472271351961759884896165148412618751835463262331141887418⟩
def polyval5Tail49 : Box := ⟨15268166612360849430536904571157667344346026690032599750623,3219073989046966910964757494720124115791338479431388843957⟩
def polyval5Tail53 : Box := ⟨16787526725112053160502539615107304276418230143746619737395,2901751297844319223149683438986058471435897812266344772524⟩
def polyval5Tail57 : Box := ⟨18458080835861056117725278367752455120165816991056082097458,2511390889181113336847445386788475399787941521578787861740⟩
def polyval5Tail61 : Box := ⟨20294874505458591162357238637897912196440639543773114775514,2038028911043566089385227990961447960858774841838782966509⟩
def polyval5Tail65 : Box := ⟨22314450503016805116939828755383887204421850667131574257654,1470534715060430919706974365742694104349815955121091662610⟩
def polyval5Tail69 : Box := ⟨24534997883621956381274479323044740477057289903448591806208,796483345540468256557987726730249115626886371875771154996⟩
def polyval5Tail73 : Box := ⟨27031250000000000000000000000000000000000000000000000000000,2⟩
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
def resval6 : Box := ⟨79928485769597381271505461351370446001555169253087194033,13010487192550581465554164820748438528361806527975826594⟩
def polyval6 : Box := ⟨15304361387270482773036792632382749532429767163324080642172,3795809038878822888575942387122462125076072282605599251191⟩
theorem cell6_lo : Holds Q cell6 (63/64:ℝ) := by norm_num [Holds,Q,cell6]
theorem cell6_hi : Holds Q cell6 (127/128:ℝ) := by norm_num [Holds,Q,cell6]
def resval6Tail4 : Box := ⟨-33983164702702875560440927738346426318915360172169258641,12707217771712289462082751663756238895866206922238149848⟩
def resval6Tail8 : Box := ⟨-35623967687919846267494047318695932476523576546224548876,12554493488610146960097757501060724998572668594616741130⟩
def resval6Tail12 : Box := ⟨-37343933828946390604392910665278591071800886332302022378,12369975891508806131811266036034804817692427566488580754⟩
def resval6Tail16 : Box := ⟨-39146941907069438560221232078635607095421669341617824554,12151351127360640719315843984798499377845154183011421448⟩
def resval6Tail20 : Box := ⟨-41037001289011999322272727870981826334292256839537607184,11896169387830300787510835959065731430975778581979787495⟩
def resval6Tail24 : Box := ⟨-43018314911854106084603979946913792166241046233548637432,11601836991117408647369691854432920411667566374376410103⟩
def resval6Tail28 : Box := ⟨-45095288635306703030405512015210953284942415759896177212,11265608619783884494788025459997488602826807499587353984⟩
def resval6Tail32 : Box := ⟨-47272541039055162289522574923144503741808073992875766277,10884579157933213049702799255961434149525963895823676644⟩
def resval6Tail36 : Box := ⟨-49554913693124338962975645267996540776630010451624748204,10455675107455198483263302500783953279957527893509958838⟩
def resval6Tail40 : Box := ⟨-51947481924108644261810535735274716956317418925618276462,9975645562157971542209918967839950094064364306842353198⟩
def resval6Tail44 : Box := ⟨-54455566101208089632849917415983266330843320365162947015,9441052717559400375755763622527366593633090157629528106⟩
def resval6Tail48 : Box := ⟨-57084743467167132241920576422868416880638508561265828262,8848261893008757511145587131975064716793287569062493907⟩
def resval6Tail52 : Box := ⟨-59840860540424855687350687163476574088876137198570637029,8193431041654127674467383438730522684721430027610401892⟩
def resval6Tail56 : Box := ⟨-62730046116055214828427060794257210827304312072387685082,7472499722558965283683988691287092992572773097410401745⟩
def resval6Tail60 : Box := ⟨-65758724894404184159617335972554957435784244109523251847,6681177507999411268227727822897506620053726442392855483⟩
def resval6Tail64 : Box := ⟨-68933631762461836901166858515842739856216130034659828560,5814931797351967923631897475642954269027345053959510696⟩
def resval6Tail68 : Box := ⟨-72261733199163822022306671944175230097975882446144941535,4868971242647465322665661151302596814458403698063243905⟩
def resval6Tail72 : Box := ⟨785279242290295211737044447335916735839241791753107855519,792365007044435316764642173743417514636937936968413388⟩
def resval6Tail76 : Box := ⟨-448782215648924022281027976795880106121173295622683717,169985452754463102268096092171374457288611111800877336⟩
def resval6Tail80 : Box := ⟨-470423481415344544497853834499591029335180163857761779,168038113137215944177680767905421019907377374024422758⟩
def resval6Tail84 : Box := ⟨-493136066825290659196780732518941003090647649652778748,165673310382782278951155664041549644500765913548864101⟩
def resval6Tail88 : Box := ⟨-516945243334191118211504070352470844536379850799804412,162860402124928612688215200226333613714071252519028295⟩
def resval6Tail92 : Box := ⟨-541903954270889843759533877153820074543345102193148061,159567110936225601845240272569106205061031408182667543⟩
def resval6Tail96 : Box := ⟨-568067700479032165298215202503195670413418501907381722,155759261844123146001617433094046132406219963805006013⟩
def resval6Tail100 : Box := ⟨-595494662447548693221042777353424588697235351456490598,151400679887452607918305435694130634499609630698194525⟩
def resval6Tail104 : Box := ⟨-624245829686296419569868343348895400675118850164826151,146453082400738189084160722417854080632913836754085383⟩
def resval6Tail108 : Box := ⟨-654385136348818158843869591831561191966523438975572014,140875965742410569794303240188807842037950856081225213⟩
def resval6Tail112 : Box := ⟨-685979603403126602291893736331662111795033671255533342,134626486187323724809490248022548413907275278650711024⟩
def resval6Tail116 : Box := ⟨-719099487666657365901882662918304444513195794495829391,127659334690130628827650866435364724337308472822630997⟩
def resval6Tail120 : Box := ⟨-753818438036800991388591827535199642776537513915952714,119926605211533230781002540188339066030448869618699146⟩
def resval6Tail124 : Box := ⟨-790213659264424729078170691889137993187280237118072309,111377656284167788238263040424363111338669768598660115⟩
def resval6Tail128 : Box := ⟨-828366083634568396623711739174532510040871407140077901,101958965478883610673998233814060787424326417739131139⟩
def resval6Tail132 : Box := ⟨-868360550936097041582901056699082481987213246595773751,91613976415383640869241092551777416667935037730400129⟩
def resval6Tail136 : Box := ⟨-910285997135279506642360404088324813303775278546951692,80282937942605252566577421199492436088976658590887826⟩
def resval6Tail140 : Box := ⟨-954235778906193609496179076081271768657137665695491085,67902728481029601588373008556029065717333320804254048⟩
def resval6Tail144 : Box := ⟨-1070111319541164211755601082574237882149447704628560225,52077682909727701257879804561578822353334454237269997⟩
def resval6Tail148 : Box := ⟨218686815210814612217838137085083605759327012540,70472422307295095187475557754920609646193082132⟩
def resval6Tail152 : Box := ⟨229185572786892740225265572380747239872481685878,69129924789512468037417968850753710403406065269⟩
def resval6Tail156 : Box := ⟨240250914845374217545149842431217195330922705911,67571902704336306891644939946033035971972080778⟩
def resval6Tail160 : Box := ⟨251850505349529332021572376172606425494222622436,65782631656288605525954030981088350304267894035⟩
def resval6Tail164 : Box := ⟨264010137425333098980026276301612624184953675162,63745974117503107634143355731501512016223791974⟩
def resval6Tail168 : Box := ⟨276756850523721452586641084254269295741360266370,61444854960529133324328905376074878327932199091⟩
def resval6Tail172 : Box := ⟨290118989591722726885215977451457325623092191183,58861211125318016734079972863068242868809733570⟩
def resval6Tail176 : Box := ⟨304126268103010527292180478678649875656911340715,55975938709123492348069751159609764116225909566⟩
def resval6Tail180 : Box := ⟨318809834131943752434595582047888502580049538758,52768837335755256960513113872940886855392712007⟩
def resval6Tail184 : Box := ⟨334202339617737749681047522611095263571104329328,49218551667529867489300552024764203587204377364⟩
def resval6Tail188 : Box := ⟨350338012972789324288975135754203910071691649390,45302509916503017109552390294895499339476143535⟩
def resval6Tail192 : Box := ⟨367252735196615193870444329768196438641589520246,40996859204468882971212133320954096920854648610⟩
def resval6Tail196 : Box := ⟨384984119664658937423277072823419399126189582458,36276397613765610495561701066118358647106093388⟩
def resval6Tail200 : Box := ⟨403571595769393317030116395289797323551043100800,31114502763114114399845831166287212977844296112⟩
def resval6Tail204 : Box := ⟨423056496599711268362069684513646197243147370140,25483056734522413422105221592778669662216687314⟩
def resval6Tail208 : Box := ⟨443482150853598929280335428314075167114915474028,19352367168689409222988356819944646640011167370⟩
def resval6Tail212 : Box := ⟨464893979242794164009298157572733236161387522806,12691084333905191193106357240400412344644650636⟩
def resval6Tail216 : Box := ⟨487342153805110911256065124948932050705916875473,5465985059624663477708018268651648805199931618⟩
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
def polyval6Tail5 : Box := ⟨12102469478654000593508977012109728201567661144768848584656,3724581122571352942324793510563100712397076872414599941562⟩
def polyval6Tail9 : Box := ⟨12686788570286564741258456427587731151319768000116626603351,3644668421419179751046101115895418702096527305625669394933⟩
def polyval6Tail13 : Box := ⟨13299321314569147289080126101166537100980975314679423900459,3552619543455315681118759182775388587955778558125966081427⟩
def polyval6Tail17 : Box := ⟨13941427844467080030296500449813699528960604340151654311439,3447584711470181497856942339461530707371275716187489785716⟩
def polyval6Tail21 : Box := ⟨14614536016177204086552558911160800805565483092379596730516,3328664723609490899876386012482832787955526232814275592532⟩
def polyval6Tail25 : Box := ⟨15320142624624047601121297730485924716848184718135683641112,3194908287703524851342360318881918620131246940209845964865⟩
def polyval6Tail29 : Box := ⟨16059816731712841864928209844017101091660713044687427976107,3045309229785891959100596967684371294753357540446698574458⟩
def polyval6Tail33 : Box := ⟨16835203155462332439848156783982820161903203555964144616582,2878803559026746954535191789927176352631296410321584460761⟩
def polyval6Tail37 : Box := ⟨17648026127597073590059169463946820345894053737070297606865,2694266381864760122098460642227140791441920151413877823110⟩
def polyval6Tail41 : Box := ⟨18500093127732486075273584435297087749887581517926726965480,2490508657767187727805695859308877449808057888909815032998⟩
def polyval6Tail45 : Box := ⟨19393298902678779604249492566764489759330932858885696204020,2266273788672641027865538875947625271472261258419926445290⟩
def polyval6Tail49 : Box := ⟨20329629679801491653147919713604108930444801735236050367290,2020234033778008351381462437114203854718928470321102020277⟩
def polyval6Tail53 : Box := ⟨21311167583807919290586084675654808730443529303332765239325,1750986740918556532363620714896841065734269235472429019270⟩
def polyval6Tail57 : Box := ⟨22340095266781080149766917215527905016287264957906389535330,1457050385357583835167644975049273169254001284081060385499⟩
def polyval6Tail61 : Box := ⟨23418700761757048813908996197317918731092161172274795634630,1136860406348129116428038734897159567369146444549958471564⟩
def polyval6Tail65 : Box := ⟨24549382570648817229345436530845164923379689246200541131532,788764831352473143773269994776661449475738434529049046541⟩
def polyval6Tail69 : Box := ⟨25734655084925398023143085739762209109384510968714035444012,411019673011139501045577796002468718477580214470406934300⟩
def polyval6Tail73 : Box := ⟨27031250000000000000000000000000000000000000000000000000000,2⟩
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
def resval7 : Box := ⟨60113495198950090292294651368060557733205161760365894155,21125697309038227286909659368776619721580148514981259010⟩
def polyval7 : Box := ⟨24111460721154461024892091726917033245111084665979847134390,6629461943417285445052505178904454799269899438840779556889⟩
theorem cell7_lo : Holds Q cell7 (127/128:ℝ) := by norm_num [Holds,Q,cell7]
theorem cell7_hi : Holds Q cell7 (1/1:ℝ) := by norm_num [Holds,Q,cell7]
def resval7Tail4 : Box := ⟨-53052569208318956648626991314919821875670882050776095072,20121397551127970417708523562135944181706171121819563564⟩
def resval7Tail8 : Box := ⟨-53889729376404009908869555880545157282438999760502555404,19284290907330709896522570990092217525423636193505587089⟩
def resval7Tail12 : Box := ⟨-54740044007806742117210279179758030568969578118610225951,18433976282009071260279048365980721069269908276025355548⟩
def resval7Tail16 : Box := ⟨-55603775567384571690296909774011917129639345646173617729,17570244722436412848015800959456747293410153676270139497⟩
def resval7Tail20 : Box := ⟨-56481135764283287989331230597986683678824600430092147560,16692884525537715666278370179785762058814833024289106699⟩
def resval7Tail24 : Box := ⟨-57372339641889768031929917309771159957586490871165707481,15801680647931235857897091679173911257002608479838728411⟩
def resval7Tail28 : Box := ⟨-58277605636709603838000954933140735748650585266895385380,14896414653111400059713189506310929583372142791984820413⟩
def resval7Tail32 : Box := ⟨-59197155631911721301152671285181585680375719372629403654,13976864657909282597157569931502271389230095908501183551⟩
def resval7Tail36 : Box := ⟨-60131215011712570124182413571558692507327294937039415405,13042805278108433774173978393027663836801176768555783745⟩
def resval7Tail40 : Box := ⟨-61080012716618411340082600101466654709246650281716285630,12094007573202592558161360061493480980620510412988586256⟩
def resval7Tail44 : Box := ⟨-62043781299539260971536340704580899179205349707108196103,11130238990281742926055299031606645203521304477884357391⟩
def resval7Tail48 : Box := ⟨-63022756982788243711565941368684045437592297128326443732,10151263307032760179248386628344200579621118441983229907⟩
def resval7Tail52 : Box := ⟨-64017179715980327200954710479023438587264760754693363184,9156840573840676514851973038040935591974672677593693582⟩
def resval7Tail56 : Box := ⟨-65027293234844616717891431375052635618829522324299932097,8146727054976373611107562284230028038603156828412146235⟩
def resval7Tail60 : Box := ⟨-66053345120961213496472188008706330769603578151292322699,7120675168856038540430163017012336004333945602027823551⟩
def resval7Tail64 : Box := ⟨-67095586857205737443340187448239396010477606652913011421,6078433427071954737519889483371594166711418723167665459⟩
def resval7Tail68 : Box := ⟨-68154181008911631542238678270630041451178741043240148760,5019742636389043202020912320949213000201206272057147529⟩
def resval7Tail72 : Box := ⟨785073691033218483645423764161587741177864386081401536961,898604795569668796870998756830935167679736131803852645⟩
def resval7Tail76 : Box := ⟨-703038152113324145745549115458574912173696198327397118,268818583112535201479499914033666558252836965000929378⟩
def resval7Tail80 : Box := ⟨-714105618156118470048196484782941166450177621630364379,257725725798678574172718997378829640328141131622750541⟩
def resval7Tail84 : Box := ⟨-725373338136820879867880992130182571107210696183307757,246458004511611638056988974722086142300319373560408341⟩
def resval7Tail88 : Box := ⟨-736818850392776292172691794259710184912337103396130734,235012492254952734775148492526195447537646514186386955⟩
def resval7Tail92 : Box := ⟨-748444958962971419034251488341707947881506368258383025,223386383684755763199229042077500621889527958795725700⟩
def resval7Tail96 : Box := ⟨-760254513437699603981403376584206647923322695015112754,211576829210027561011165634991057019238896976014637692⟩
def resval7Tail100 : Box := ⟨-772250408371029882050408818245988672225883294620680074,199580934276697282466723911067740392061138421975922662⟩
def resval7Tail104 : Box := ⟨-784435583989588596612140307469737122865468255025379733,187395758658138567871525097676730111568086287050441857⟩
def resval7Tail108 : Box := ⟨-796813026913215255996666343181441144448859106088825276,175018315734511908482027856477326513828037535249867612⟩
def resval7Tail112 : Box := ⟨-809385770886991202115835061723356906841184014469114377,162445571760735962362343775879006667945942373131231081⟩
def resval7Tail116 : Box := ⟨-822156897524818819120047979815569454078166018364788767,149674445122908345362926838836276529779935006341438396⟩
def resval7Tail120 : Box := ⟨-835129537064733521258339576060392822146354683776214073,136701805582993643277770260712639855478300802460072991⟩
def resval7Tail124 : Box := ⟨-848306869136133649705685909877332202007083583706946654,123524473511593515996580104520113991532159088852776744⟩
def resval7Tail128 : Box := ⟨-861692123539116399472911077605194745576419589372121656,110139219108610835735837279379832846199489508867350336⟩
def resval7Tail132 : Box := ⟨-875288581036125968548078105636405069594115086735153659,96542761611615550650697363748474632305914727431441349⟩
def resval7Tail136 : Box := ⟨-889099574170776661965941467291911391946431392749112771,82731768490748202302529013833426671630121847423410580⟩
def resval7Tail140 : Box := ⟨-903128613925797506008811004983351064681576502745714831,68702848073592250461629892158375507057608984093482163⟩
def resval7Tail144 : Box := ⟨-986645409947628728715976697101235829887514412441984744,52144173288331408523120444749664027913238867255286659⟩
def resval7Tail148 : Box := ⟨379481290147658661565489822085147137496633623143,121217334435270610157021186067051114332777750592⟩
def resval7Tail152 : Box := ⟨385411219732934761591139928543565127137595564954,115230000944081502258339745529068846307871382874⟩
def resval7Tail156 : Box := ⟨391492540760569589865555212361313726886216657861,109148678945937902577108234924859521265295537732⟩
def resval7Tail160 : Box := ⟨397669818636485725052643575486638222836951477551,102971401069727710069263288816428714827914406980⟩
def resval7Tail164 : Box := ⟨403944566471850391697445473453887905297826476603,96696653234362553858163495842491530591210175636⟩
def resval7Tail168 : Box := ⟨410318322224216669815278677315541703719397913355,90322897481996272655564105928870194053876222726⟩
def resval7Tail172 : Box := ⟨416792648118534973511687108574878049101771171810,83848571587677968899520390303801308360066625003⟩
def resval7Tail176 : Box := ⟨423369131029772778110364203015041073901050314090,77272088676440164297788689055908219085179475258⟩
def resval7Tail180 : Box := ⟨430049382871861547775168477879932528742816791330,70591836834351394632626533574489450419101709806⟩
def resval7Tail184 : Box := ⟨436835040992781241848491059038011390795683165305,63806178713431700559237744870452643974447243971⟩
def resval7Tail188 : Box := ⟨443727768575878778666765542420855376776772346128,56913451130334163741019574026492990989825415669⟩
def resval7Tail192 : Box := ⟨450729255047518818456445279901149636510410289490,49911964658694123951990590103433731149770390406⟩
def resval7Tail196 : Box := ⟨457841216491166781596633191499576054223161373739,42800003215046160821810880577519275385634052871⟩
def resval7Tail200 : Box := ⟨465065396068005595490658558425254154868572896756,35575823638207347299240705084945677642988112749⟩
def resval7Tail204 : Box := ⟨472403564444189308750190649612406126653600766356,28237655262023676017937818228340772441370842843⟩
def resval7Tail208 : Box := ⟨479857520224858310123505547071031825358106299076,20783699481373358461234102899377122043796975721⟩
def resval7Tail212 : Box := ⟨487429090448955896460972067245785186436324017562,13212129307931703112228184735624907217638231193⟩
def resval7Tail216 : Box := ⟨495122670163058844294717808480164458517946238483,5520961133064337512392587801989772000514230020⟩
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
def polyval7Tail5 : Box := ⟨20673666947367709099869096137860325564262258625509738245631,6305674486210436931174972192751940503162398509923803656101⟩
def polyval7Tail9 : Box := ⟨20999870368892030625994436404180167896949601239110584400648,5979469094456707192959754792935225958073172331148070844260⟩
def polyval7Tail13 : Box := ⟨21331222875147975395569553820348377041677673971004704153056,5648116588018715544685825372170560719800894954633807520871⟩
def polyval7Tail17 : Box := ⟨21667803722596758715323888016239223960547964259837704548771,5311535740569795850808186825357781662374105594452517183052⟩
def polyval7Tail21 : Box := ⟨22009695407944303914367532222122636134451589903057504670946,4969644055222250198597552974835148615326568692177087523932⟩
def polyval7Tail25 : Box := ⟨22356981729776759361532865735206375050457633035257380157512,4622357733389794746352856111074199974518081542066375902360⟩
def polyval7Tail29 : Box := ⟨22709747808920548752476163402176095731682930977028785707287,4269591654246005355247918353176492150832735244556097334982⟩
def polyval7Tail33 : Box := ⟨23068080109305586386381869996007422538778013479969108855974,3911259353860967721329499498471489364495607828624440796743⟩
def polyval7Tail37 : Box := ⟨23432066459157822225735856339452405956337849882770143671903,3547273004008731881973497145969983072598954765938268500474⟩
def polyval7Tail41 : Box := ⟨23801796072526180058713744647404109178702467842263468143694,3177543390640374048995504495703534666478589337425337794156⟩
def polyval7Tail45 : Box := ⟨24177359571149164663340956181141821072048521129050923298650,2801979892017389444371111562758234196084009099075731581155⟩
def polyval7Tail49 : Box := ⟨24558849006666497534527995604415157064405616695007825401820,2420490456500056573215633209937445097914931427056604261635⟩
def polyval7Tail53 : Box := ⟨24946357883181225307138877245827860291723525568257216167605,2032981579985328801327856611033781983636189493474313894975⟩
def polyval7Tail57 : Box := ⟨25339981180177830955572080217237930132789537255246002424821,1639358282988723197942668741529293386875071929087954494986⟩
def polyval7Tail61 : Box := ⟨25739815375801975280472321102277165872981492204284642551138,1239524087364588506746934840454653480957580448789499380201⟩
def polyval7Tail65 : Box := ⟨26145958470517722680438268457622687382667678576653489182925,833380992658396378197208369576973080004636920725883271569⟩
def polyval7Tail69 : Box := ⟨26558510097609707651241987143328762543349604800441008377149,420829447828692307727662862949053961448660309305651292119⟩
def polyval7Tail73 : Box := ⟨27031250000000000000000000000000000000000000000000000000000,2⟩
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
def pend : Box := ⟨1030736527056042123325839194390291589830682980930787382286906,4395608529623144105402515529898213698003174033244404439⟩
def zend : Box := ⟨1003754445359512956966582031250000000000000000000000000000000,2716654966353045957031250000000000000000000000000000002⟩
def betaquot : Box := ⟨428749996643575321956946073122976755938382900062450141989824,394770767122888755057284278650905573616306264623394256⟩
def crit : Box := ⟨119980147674554803096776981265851086113826155702247438051,11109395163803187172176859450074647227873014195297481112⟩
def subsonic : Box := ⟨516630531246890213974151417872075541192583614393128166012,5819342709157726030067535944118453767119637986917496063⟩
def pendTail4 : Box := ⟨26977742877915502131472174106255198049105267035576199427416,1562209521755399595692066193740700176405568684896236518⟩
def pendTail8 : Box := ⟨26977777394170162069561333128382792227875455071462928543888,1562067563210857772957087009090619371540934469839346294⟩
def pendTail12 : Box := ⟨26977777395619249709604636782184644658585031625466590443674,1562067546622910961182542784930193095034561694014811203⟩
def pendTail16 : Box := ⟨26977777395619942943426812007732886738627739824323844656009,1562067546609576379459918835821691974100274923787309594⟩
def pendTail20 : Box := ⟨26977777395619944565894121261896551372343940834180175091971,1562067546609528615250231702366082645278349880885668905⟩
def pendTail24 : Box := ⟨26977777395619944579368416053261575450682854716277022419974,1562067546609528014475960973939139548991354902621684722⟩
def pendTail28 : Box := ⟨26977777395619944579695288231817316215045104121561153049269,1562067546609527991662045401596903275517118706124901506⟩
def pendTail32 : Box := ⟨26977777395619944579715136882340644802831597068122293352339,1562067546609527989275372906745291195428016917667876746⟩
def pendTail36 : Box := ⟨26977777395619944579717541058229220349559808694938241537446,1562067546609527988622617724635936868390993749672689165⟩
def pendTail40 : Box := ⟨26977777395619944579717547945653496211142699406323027630249,1562067546609527988167005612313683900477830387680690344⟩
def pendTail44 : Box := ⟨26977777395619944579715160426348354528004544789018035949838,1562067546609527987356175776839858562420777465198689026⟩
def pendTail48 : Box := ⟨26977777395619944579694987222191472336815332040934822430940,1562067546609527983596205063329264839605126384808009846⟩
def pendTail52 : Box := ⟨26977777395619944579343910241333217846111962391865972671065,1562067546609527935917550705389094082809203716144730827⟩
def pendTail56 : Box := ⟨26977777395619944563108533320201903873885284592156564781478,1562067546609526135938764440436834405707627616492155107⟩
def pendTail60 : Box := ⟨26977777395619942138786741549310373717445674811195122828113,1562067546609316493679873301694486608009042274121763447⟩
def pendTail64 : Box := ⟨26977777395618403885186855088503710446991064065816634424078,1562067546508848543163762963941808892050868538509925835⟩
def pendTail68 : Box := ⟨26977777388716387678919897454625598554724810765582275184467,1562067205847409488522074467481363721180187378211173484⟩
def pendTail72 : Box := ⟨26976882363755171403074687063337263411232207548967689826730,1531093673964341366947531120600993908000720082704616491⟩
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
end SepticProfile.ExteriorCertificates.C16

end
end

end OAI
