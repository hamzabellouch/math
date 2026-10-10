import OAI.MathematicalPhysics.Transonic.Certificates.BarrierData22

namespace OAI

section
noncomputable section
namespace SepticProfile.ExteriorCertificates.C22
open SepticProfile.ExteriorJet SepticProfile.FixedInterval
def cell0 : Box := ⟨250000000000000000000000000000000000000000000000000000000000,250000000000000000000000000000000000000000000000000000000002⟩
def resval0 : Box := ⟨115797247405401466731022425585324025482722724420984901129,314895126372791384350965384258922324029145817514334339⟩
def polyval0 : Box := ⟨3818568157936502663871144388977612623885482035371196651971,14911373285525627664020536792321283538948725414439744929⟩
theorem cell0_lo : Holds Q cell0 (0/1:ℝ) := by norm_num [Holds,Q,cell0]
theorem cell0_hi : Holds Q cell0 (1/2:ℝ) := by norm_num [Holds,Q,cell0]
def resval0Tail4 : Box := ⟨60276314375839300927633428864445095510393761893177,1773776520571768257634071822138588439381432849308⟩
def resval0Tail8 : Box := ⟨7387207508690928278727951638708139341493903883,394791660111135289877943984923855057841162994⟩
def resval0Tail12 : Box := ⟨6807011187537384715374950645325197157010289,552385843778520879480600121005743994870151⟩
def resval0Tail16 : Box := ⟨27607691212381540061073703316417774230694,27365138552553729729838944952855577732278⟩
def resval0Tail20 : Box := ⟨380794446079566137537297940356030368884,386999536234813163733983647848705432543620⟩
def resval0Tail24 : Box := ⟨15329480706795034263310296702225883735,6191022723695946952993829614408641112127497⟩
def resval0Tail28 : Box := ⟨1638905511484414556387805745530258150,99056310094121163800132153729403551903065561⟩
def resval0Tail32 : Box := ⟨437577191628128461900962835250854708,1584900953631575539517837341483941469976726502⟩
def resval0Tail36 : Box := ⟨-270949153821897770611231391405841411,25358415255041310207437135217280647291128444789⟩
def resval0Tail40 : Box := ⟨-142550610947157415449090822682561170547,405734643945519879325061946050624446781234577830⟩
def resval0Tail44 : Box := ⟨-36607898683110700010674624977408233333289,6491754268804851766189422925343350269492225821035⟩
def resval0Tail48 : Box := ⟨-9372059608171980798825423180048699888376158,103868059514547984314771680040498799479635322192791⟩
def resval0Tail52 : Box := ⟨-2399251321161859748786969027787603504217009546,1661886702934172381192202892714422898108155371704984⟩
def resval0Tail56 : Box := ⟨-614208421814528257695360219190492109087176865285,26589611426518654658065137039648796964844670818265136⟩
def resval0Tail60 : Box := ⟨-157237353356455219323261962402722658223765546246143,425286372796756700725715869750854852776717439991162701⟩
def resval0Tail64 : Box := ⟨-40252743174273073416185204196367356379814888227388708,6766845004882486068442131710019802150039948512100036100⟩
def resval0Tail68 : Box := ⟨-10304248887275486770449141164895098170583297894370045279,98609050899993750156574846903264742323678826046821880628⟩
def resval0Tail72 : Box := ⟨807056148645979626307901462327204805988129738462771383701,2484089835109476877958610786691953144992182235669387078⟩
def resval0Tail76 : Box := ⟨-27963893666198075251134851577401315967980091961869,610501729795867999741257438290548265455740898682⟩
def resval0Tail80 : Box := ⟨-1531220941228337844221907416886914902220628150,70261803844946017828432478546359603656313536⟩
def resval0Tail84 : Box := ⟨-877399052225987541466256094777751330848626,63372475331944194208804156153848264262224⟩
def resval0Tail88 : Box := ⟨-2458998131461557194050632745283443561508,422110744863836762852109188532762001531⟩
def resval0Tail92 : Box := ⟨-24803139447417749039481163790820563822,2646804047725437533166744048686426183593⟩
def resval0Tail96 : Box := ⟨-755849320790880031390701702650808044,42291135532450332238124167994005949925482⟩
def resval0Tail100 : Box := ⟨-62508938502818998676673156869491073,676655752727355659683792039126801616965768⟩
def resval0Tail104 : Box := ⟨-13151064067694720637490524144453604,10826491768967734572807582125085403154411810⟩
def resval0Tail108 : Box := ⟨-8674187992011293879697406861360215,173223868222249443697589086633498694609381342⟩
def resval0Tail112 : Box := ⟨-493050975386413423101029193190581093,2771581891109350773468240204920690644717582676⟩
def resval0Tail116 : Box := ⟨-124075145764201482948520289473332392972,44345310141458638314501315509448299262604010438⟩
def resval0Tail120 : Box := ⟨-31756783635634793824731780297067656237112,709524932491514607321650193376160460145439939079⟩
def resval0Tail124 : Box := ⟨-8129689177718248361898243194526488687080266,11352391298283330891799175996372919581869111094611⟩
def resval0Tail128 : Box := ⟨-2081199612841111767765783758421988172374803792,181636309648046064765391957064493887101794144962262⟩
def resval0Tail132 : Box := ⟨-532787091984723323994421210926571952445818173701,2905681466501539452075716464561400785598000265560068⟩
def resval0Tail136 : Box := ⟨-136393543441520052474622169513899012675426428195066,46363034549109057488639341483838554998479149734384381⟩
def resval0Tail140 : Box := ⟨-34917350151081591588755424789145828031833607926915889,709073831986860249428386175305812635587656899356376016⟩
def resval0Tail144 : Box := ⟨-9297692488178741184945026494180763548827197099638784264,2787834936020985349226344948064291581831824070584857116⟩
def resval0Tail148 : Box := ⟨64312448548928788382821976258741541030905675,1159369830726233889021642249549932702390547⟩
def resval0Tail152 : Box := ⟨1161631182757289239788413176671299351929,47550822807077129088422089808847559715⟩
def resval0Tail156 : Box := ⟨373914231392835313551649364327083963,24609622163474682397999347593129619⟩
def resval0Tail160 : Box := ⟨663449661974097510770053347934946,65255804625018708675235871133335⟩
def resval0Tail164 : Box := ⟨4486060760900953684851406357116,30500422192438386198640471533461⟩
def resval0Tail168 : Box := ⟨94596635822264162821043923457,478470976748503347377935508918029⟩
def resval0Tail172 : Box := ⟨5504780610943715974658113837,7655261001881722518780849080627163⟩
def resval0Tail176 : Box := ⟨819736388571719161608665181,122484154265292618242366272783467151⟩
def resval0Tail180 : Box := ⟨305913193313714583971178313,1959746463781042840169246832801720106⟩
def resval0Tail184 : Box := ⟨2044165865710884352384582274,31355943417251527688195003625002328945⟩
def resval0Tail188 : Box := ⟨456821023763749164413754471582,501695094248482002801528405228317655833⟩
def resval0Tail192 : Box := ⟨116807760894572227151050267687689,8027121398470971815699456351179862162139⟩
def resval0Tail196 : Box := ⟨29902091865352820656042327388214900,128433914342350545508966398853754902959968⟩
def resval0Tail200 : Box := ⟨7654927124185871605479157307552705236,2054935452984272495531781086882487721217633⟩
def resval0Tail204 : Box := ⟨1959661148368224737675853880776467448032,32877130065516971139368446125625140444370887⟩
def resval0Tail208 : Box := ⟨501673294701367168115830445245782818671852,525563762378872228306477369655270080080415148⟩
def resval0Tail212 : Box := ⟨128428603605600495565753810347772954202941516,8288618510519158162490061904959043927303292101⟩
def resval0Tail216 : Box := ⟨32891869926556511470982764703843010236794631244,101788238665132915496935988210695722935650933926⟩
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
def polyval0Tail5 : Box := ⟨2132323168436895651294126493356924437183492648673130,52748305861412118145318675905682670415563988174598⟩
def polyval0Tail9 : Box := ⟨209461036376985492769696753783112395842782833755,10238602398156916705579547295965654903319523815⟩
def polyval0Tail13 : Box := ⟨167001784694343079741415682044011943978195560,12661320147910028931597662822375246318972499⟩
def polyval0Tail17 : Box := ⟨593524753615472123966519278406320596322624,442963444046882912956475951636967158404790⟩
def polyval0Tail21 : Box := ⟨7193424915437827687788653979784995411610,6055984745823779454314949208077851659901294⟩
def polyval0Tail25 : Box := ⟨254169193839813824573701440659587272612,96878409210639629776565054811814189879288862⟩
def polyval0Tail29 : Box := ⟨23765821559990228818601035074945176491,1550053707881600348582679983954104796379033219⟩
def polyval0Tail33 : Box := ⟨5567890922272737975233641112060445350,24800859218337098531026050209272661586647895670⟩
def polyval0Tail37 : Box := ⟨8875337739256089176396238078827754745,396813747456507558898925915567520612700284853851⟩
def polyval0Tail41 : Box := ⟨1475143210391665050902331842580700962713,6349019957928723833249556185972779663194327624489⟩
def polyval0Tail45 : Box := ⟨376566701907892753678504017479331757927474,101584318973843772736249794903571611777351403814003⟩
def polyval0Tail49 : Box := ⟨96397632703439213720039027978045107903877156,1625349013208810453134898114997230895108154130300440⟩
def polyval0Tail53 : Box := ⟨24677767163977996279874683772067578174418666322,26005561075935866427874592218171213286600565101353596⟩
def polyval0Tail57 : Box := ⟨6317507912289896836845182019367539353359669065246,416083054551400272035756835926156523204673679908624928⟩
def polyval0Tail61 : Box := ⟨1617282021366690191338512020191492756922323935668424,6655812670947962373378233907966868285458683859966821271⟩
def polyval0Tail65 : Box := ⟨414024229546043782997457698781358987977466239940191632,106104855041358555930868983005436206097769617205231741695⟩
def polyval0Tail69 : Box := ⟨105990594507740593227158950352532103572258708585448534659,1598311691045317213765687805407226379520384107207943202456⟩
def polyval0Tail73 : Box := ⟨27406250000000000000000000000000000000000000000000000000000,2⟩
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
def resval1 : Box := ⟨115566495060853090184615650858921346650031535773890050499,236256785117950028628917439744234900988234991128261401⟩
def polyval1 : Box := ⟨3800266672642076358950186493013188477603144140942826389503,8675285076877173133018689739519979711969834138548731683⟩
theorem cell1_lo : Holds Q cell1 (1/2:ℝ) := by norm_num [Holds,Q,cell1]
theorem cell1_hi : Holds Q cell1 (3/4:ℝ) := by norm_num [Holds,Q,cell1]
def resval1Tail4 : Box := ⟨58522215976635881639479122169313874903158350752551,3124516750338980021716137565521565422727253049399⟩
def resval1Tail8 : Box := ⟨6963710490329709016745068204720825688543694780,6311241115807046735165240019618190570703755577738⟩
def resval1Tail12 : Box := ⟨-324429031735479153161227406715523258673799466,19945762529169210916746294560783710386712642929266⟩
def resval1Tail16 : Box := ⟨-2167528016235187727772679616607078268318706393,63037336235851817880917624178669899520079820625380⟩
def resval1Tail20 : Box := ⟨-14205274864446099623337638425548598836199089011,199221757312051996799431345464116117330560006053597⟩
def resval1Tail24 : Box := ⟨-93095691533708498140444111109966180496299193705,629590934213760192108278225574850875821509225975375⟩
def resval1Tail28 : Box := ⟨-610111924119731502675649187808019322424837325167,1989502377653141445008935441524572358061199739377959⟩
def resval1Tail32 : Box := ⟨-3998429505919599747548476975323262343066609312684,6285739809158020361932112955583563231429555711454634⟩
def resval1Tail36 : Box := ⟨-26204107609996767746256780096707995976190709190328,19852474770142703084612988307171925569046890810126853⟩
def resval1Tail40 : Box := ⟨-171731239632875929003862055073737825002911129747131,62654710645610225061540502755879060791079713023541604⟩
def resval1Tail44 : Box := ⟨-1125457852058016638268086264873172057970707862315690,197437123908710302084587944579300674481112473623962166⟩
def resval1Tail48 : Box := ⟨-7375800579247414179614226708679649914698055998068919,620180013380711707518233819508159052315862552601031825⟩
def resval1Tail52 : Box := ⟨-48338046676155624080187402916543522006461893850894289,1935048229542974160612837388027675584991106940263237855⟩
def resval1Tail56 : Box := ⟨-316788222696831089426949057763451429151899283801762086,5951691860168543839125678470535996209658604819677764574⟩
def resval1Tail60 : Box := ⟨-2076103296258878242990269976797084704394392145812296547,17735389311308954766238460681785445271643498260422964228⟩
def resval1Tail64 : Box := ⟨-13605950551058288969456501807803299685681185352272757701,49008149531765585618501150737376444776318113374499971211⟩
def resval1Tail68 : Box := ⟨-89167749835113208982411754170169168719358587961050572734,108723544686117664067715590248925632589927994986180833264⟩
def resval1Tail72 : Box := ⟨809983583678451461717277672735707596891784604593032706135,1508129873884136745918866072437615059433962946496564274⟩
def resval1Tail76 : Box := ⟨-27338251325940944545376403483647255413351310320225,404332944304704125524931713129017389855293220202⟩
def resval1Tail80 : Box := ⟨-1463294053879795118259409959195962557094748327,64656285818952988163232054359480233543483923181⟩
def resval1Tail84 : Box := ⟨-3633286266986217858266089384109628500114550,204207217268212080310854344320479453531336882679⟩
def resval1Tail88 : Box := ⟨-18445223013564223849346249325684936818610043,645386110547969408351581463706190127978233343633⟩
def resval1Tail92 : Box := ⟨-120867960859017892534534206264207304838487407,2039676239546623810755220998923532001354610397567⟩
def resval1Tail96 : Box := ⟨-792120124853948530244051221635847383369484752,6445974046743658339915090585096065377896037341274⟩
def resval1Tail100 : Box := ⟨-5191238446030485117519652573232420545399441017,20369773437087007031049020341130281850053701247717⟩
def resval1Tail104 : Box := ⟨-34021300279574297055903128694751007901178645031,64360928785355547576456637859441621394009630056766⟩
def resval1Tail108 : Box := ⟨-222961993512153965672750912345569356148883569212,203296880252445732292655916409051601904501994812716⟩
def resval1Tail112 : Box := ⟨-1461203720681224059563818322069299367794729332907,641762001402346157433890651959662355129563635106001⟩
def resval1Tail116 : Box := ⟨-9576144703856447092387126464365559240840106831374,2023326824573859715242903376037776659967921406654513⟩
def resval1Tail120 : Box := ⟨-62758221931193626888547521737546938224805379021301,6362219063687267375418356622143208652323256211134227⟩
def resval1Tail124 : Box := ⟨-411292283248272355938900925561840182634588230145258,19894808767595260363824668955476930058376699536432407⟩
def resval1Tail128 : Box := ⟨-2695445107496018276179013960980022384466141444859889,61481861917392299707852615813885225327652478521205106⟩
def resval1Tail132 : Box := ⟨-17664869056517569884301497173990653479818490879987309,185167113639451511093946376870961878882432628543809257⟩
def resval1Tail136 : Box := ⟨-115768485880799469059215335612369445035925452168508692,525280743406569914361584350137974853896172174413229338⟩
def resval1Tail140 : Box := ⟨-758700636258439116668244951390741243191149175468634893,1267331729443727545197116064936902048379446379891338796⟩
def resval1Tail144 : Box := ⟨-5122199531693342732075940057366085649986891896402433341,1403807679912007541876795674712271021335697277545996090⟩
def resval1Tail148 : Box := ⟨63355865163130674778852708913535812259394951,822548382095405690121953110754613682676777⟩
def resval1Tail152 : Box := ⟨1117082650578398792870708852006751524439,3111171410624322870041033870134686914465⟩
def resval1Tail156 : Box := ⟨470858427528910993477867717712912634,9735745507968904922259687262413207797620⟩
def resval1Tail160 : Box := ⟨781981951287721914432634662669539393,30769360120408715018612924740145177895591⟩
def resval1Tail164 : Box := ⟨5120808619488807548327790029867640912,97243721447655139174256403450695764243468⟩
def resval1Tail168 : Box := ⟨33559705144935797071614684563330071522,307320805931704804851570128115656135512172⟩
def resval1Tail172 : Box := ⟨219936883103079184518935785773218587812,971171638462732980116507174107091793573693⟩
def resval1Tail176 : Box := ⟨1441378357074555822680569372854038673476,3068635699279133787902460779020654338226021⟩
def resval1Tail180 : Box := ⟨9446217200919656680143709527610202142557,9693513435575243020560737006971016546154381⟩
def resval1Tail184 : Box := ⟨61906729047945716564722548150851632001721,30604237358738444356295218061705616975678355⟩
def resval1Tail188 : Box := ⟨405711939488616148325661488110951264648615,96514447152774542256664178309296448584015171⟩
def resval1Tail192 : Box := ⟨2658873766632594146616279859762404257501721,303656690771878128904947785140732654548502517⟩
def resval1Tail196 : Box := ⟨17425195117003381216364858942740114951119633,950683255770141632839462002864033306674982246⟩
def resval1Tail200 : Box := ⟨114197758718794088042107248367060082349144473,2945503024331936442738494388320652398718632299⟩
def resval1Tail204 : Box := ⟨748406431539584094104597199489347737737193372,8921759006250456136112870234106164661363811119⟩
def resval1Tail208 : Box := ⟨4904756389782801559934803132583651998006504299,25657741784009751352271580366251600594567912937⟩
def resval1Tail212 : Box := ⟨32143811603451461708323224138496340936629763954,64448775320553612815507828693563248188992724474⟩
def resval1Tail216 : Box := ⟨210663931421600367740185625363722111886808958135,94621401448986859655693828592365184066563222515⟩
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
def polyval1Tail5 : Box := ⟨2074667050866051698070077008956605746293079407981570,118719707363122796174489590735813035154718615866181⟩
def polyval1Tail9 : Box := ⟨201607532078447392441641020115215466491438619454,275615704928929807429683999586922293289133147671547⟩
def polyval1Tail13 : Box := ⟨15602527268765199961728200999746993080529855068,871057410992819847525064402119567839737919626574668⟩
def polyval1Tail17 : Box := ⟨101235879410518411946654816142778778741630507599,2752919159136723208294265578758402047924928239419378⟩
def polyval1Tail21 : Box := ⟨663455938720917065862509145616024390812600763667,8700240506872006566169345823844814448332057935824854⟩
def polyval1Tail25 : Box := ⟨4348024798607481507280154381975231903033704353303,27494805240361194252832422758751082116537770863737738⟩
def polyval1Tail29 : Box := ⟨28495215318745595284668169774827038384986512044780,86882408931358475145853610970707193499247753843576810⟩
def polyval1Tail33 : Box := ⟨186746243112806196839233745903898343078591619708392,274494629825397857100910088661606625681411677628101729⟩
def polyval1Tail37 : Box := ⟨1223860178864059939725073463811187205353969288958763,866904933321614073470817815534205318429996165517278491⟩
def polyval1Tail41 : Box := ⟨8020690068203490505722212291511765772469401527766106,2735695002970344678864959524713885716430446961390444991⟩
def polyval1Tail45 : Box := ⟨52564394430978384644930489739225037908263708136875859,8618932116900729407322407108559763218919439623276217961⟩
def polyval1Tail49 : Box := ⟨344486015342859954281485940399085747912874040052254740,27061725180964759761627685258499404362730888401462969779⟩
def polyval1Tail53 : Box := ⟨2257623550150968101294300345244814876660602315386706087,84359537761636077931719045144358772534252361572985644223⟩
def polyval1Tail57 : Box := ⟨14795561698269473045339474912455962171450245499572975158,258957441953798301016638216187585884173884204488509731902⟩
def polyval1Tail61 : Box := ⟨96964193145799433385062154923998051541884043119396703498,768230485063221692383072618029827503604861462936028519368⟩
def polyval1Tail65 : Box := ⟨635464536221600239023651599459007736526643636490913624094,2098977903567476206254410312517916551756793792806445342109⟩
def polyval1Tail69 : Box := ⟨4164580571557634424807324189333715747329143077795437891763,4477608032718831562337332351287311903990389919708433196656⟩
def polyval1Tail73 : Box := ⟨27406250000000000000000000000000000000000000000000000000000,2⟩
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
def resval2 : Box := ⟨115452900519199023925139623473669280005301436875679151280,217346644429433457941803210263997724877827421589484426⟩
def polyval2 : Box := ⟨3791224073824721301926462459158938532999567078639686150836,7381053110776188197214066981649414278851052074181617109⟩
theorem cell2_lo : Holds Q cell2 (3/4:ℝ) := by norm_num [Holds,Q,cell2]
theorem cell2_hi : Holds Q cell2 (7/8:ℝ) := by norm_num [Holds,Q,cell2]
def resval2Tail4 : Box := ⟨-136491844716494449467001366969110218184056014527642,34444342204083706624385990446495988446806960128731537⟩
def resval2Tail8 : Box := ⟨-445560752886024409228490570626385287696777565964839,58644930225097529996486389321711939124287118985213546⟩
def resval2Tail12 : Box := ⟨-1022398297355067295723324260497152230884502966979165,99783381966835966205651666802495600311299825603678476⟩
def resval2Tail16 : Box := ⟨-2345992619801765387054516171441971358436637422757817,169624218119974225248994392091155650836646641202054889⟩
def resval2Tail20 : Box := ⟨-5383108866387071743671515514210895405404889151633781,287990478468146399992871661419521465313811541156663026⟩
def resval2Tail24 : Box := ⟨-12352068298293599666203962347726919950608470425687179,488130319757620721978861557471543313948233412743031651⟩
def resval2Tail28 : Box := ⟨-28343025384159172012365042099256499156329580276385546,825457833206855032201081526546430935679366952409594617⟩
def resval2Tail32 : Box := ⟨-65035835985303580744562294381654724439419131412328928,1391510734938808949128054568182031180359453270503093550⟩
def resval2Tail36 : Box := ⟨-149231068489648663664502902945225773019597239091973729,2335573077493343807381490397351200041255324825395551028⟩
def resval2Tail40 : Box := ⟨-342425240871734702091089951912570014266904010623703523,3896540932367056285545265511077259008150501744567868673⟩
def resval2Tail44 : Box := ⟨-785728111262561024635222996568107611434924246316743393,6445761037253094070544935173791683945160873689347803327⟩
def resval2Tail48 : Box := ⟨-1802929781859990864869173135495267530872076986813656372,10533671447761051720434689841668047693772310898166024296⟩
def resval2Tail52 : Box := ⟨-4136998220789760672936590910549844433353803386602389777,16908698837322604927096463710676991515654168146102254552⟩
def resval2Tail56 : Box := ⟨-9492745891168978442628311972714716143278984564491057763,26410284158821942058600703363051377175487935580186812793⟩
def resval2Tail60 : Box := ⟨-21782031256730609418512268495878187752779940396978086028,39466952951827754876615543723700842787033352176746952064⟩
def resval2Tail64 : Box := ⟨-49980995069564197151662661239650013226778241385259220937,54507067944507594580819998019621102852485323331338887131⟩
def resval2Tail68 : Box := ⟨-114686104546378641085904083534214075506223995492280561941,63565760150971751115519452166000410152631796576090821265⟩
def resval2Tail72 : Box := ⟨811445562050901655054258505578845042365054987329887313786,1020587753951182507505819507197057255496528433765935466⟩
def resval2Tail76 : Box := ⟨-29186737124739854846891851475890964237884481511312,411408113751690660262936971328541837174064174454144⟩
def resval2Tail80 : Box := ⟨-4931072101991542579176549126293847658976833706070,700475347887912845686257050179507341839328064092181⟩
def resval2Tail84 : Box := ⟨-11311542712340172135679539904183554556339587387461,1192078214030961570874617384884649416747363633243833⟩
def resval2Tail88 : Box := ⟨-25955436129300662725178482281925796635309051719958,2026974359934912530873725419159484477433320479888672⟩
def resval2Tail92 : Box := ⟨-59557279578093463587873444919560287398107234223955,3442650319201651347177955600399938393411525063033989⟩
def resval2Tail96 : Box := ⟨-136659986500073059534131345334968691601994385206524,5837951560606028196979825904298721910907255324994738⟩
def resval2Tail100 : Box := ⟨-313579667212938955664438831503011416750221494094454,9878843863377060328107050495487554775846212508279337⟩
def resval2Tail104 : Box := ⟨-719539129248526470267948895674017010461160650120054,16668285436056195262485946200306926404976551697370051⟩
def resval2Tail108 : Box := ⟨-1651052707343280356346864952521410270992961259384204,28011808358665940878552053119074326861648891925216250⟩
def resval2Tail112 : Box := ⟨-3788501461028998329304961518300709109528851239877281,46815029953537336601328891817542987492818816003774238⟩
def resval2Tail116 : Box := ⟨-8693086087671875445673116490376288982399207709234712,77634304447131834626401528361761563540823984179327271⟩
def resval2Tail120 : Box := ⟨-19947133848312875302123377321355974247170403803811858,127323583198982416916920989357489717276974828474107276⟩
def resval2Tail124 : Box := ⟨-45770644020973798305639497870337236518263069040897903,205466697514103886421068678857121870171750656516938783⟩
def resval2Tail128 : Box := ⟨-105025206629968924926725496721006329343935018783067795,323574606334495238982316226533212243109260113568574568⟩
def resval2Tail132 : Box := ⟨-240990579521109214502433826603387924770691109039954740,490181779455359312731416789249986970362160098587928688⟩
def resval2Tail136 : Box := ⟨-552976388089847756214425353306711908453373635002079042,694371376351126373562481704152964069787741231557714657⟩
def resval2Tail140 : Box := ⟨-1268858479979550844974664498865014922535171068239435236,859061941197826626804441438961814960893373790989483301⟩
def resval2Tail144 : Box := ⟨-3027705734644113579598625032722723085626711712592865963,708050954649902688951838902654717431319488729620784390⟩
def resval2Tail148 : Box := ⟨63156535095026855339433258363833146419421340,47790834341540277883504093164540279052618887⟩
def resval2Tail152 : Box := ⟨606570177641921920241458664837959570978629,80328618899326557263827737540100687208985416⟩
def resval2Tail156 : Box := ⟨1389319449387786255425036601012936125199234,136680657875665535412730140300067191579653512⟩
def resval2Tail160 : Box := ⟨3187928191215907999283351564755426128975531,232353356986598031116175248703710789307903621⟩
def resval2Tail164 : Box := ⟨7315012145977689036731143667240187357361120,394508021625743344809819537755203417867278544⟩
def resval2Tail168 : Box := ⟨16785008788156788218664389292386287158564189,668707347033981308887447433931277099954321462⟩
def resval2Tail172 : Box := ⟨38514839674403498765121796521847170494291434,1130904856055491265300247603876821906206588138⟩
def resval2Tail176 : Box := ⟨88376055911967628231451407699797911692003207,1906602317144945714726524452272170108573227246⟩
def resval2Tail180 : Box := ⟨202787479438629965674861512057059260680502322,3200557550149507081605883430140994119364417311⟩
def resval2Tail184 : Box := ⟨465315649049054774747245809082264531358814548,5340640719627750450189101291972172064152452647⟩
def resval2Tail188 : Box := ⟨1067712138093163884888280313257275411195806544,8836993103931073600009804495220837122863718916⟩
def resval2Tail192 : Box := ⟨2449969632788543411855661066463410154359644015,14447020234488123285331440112272492868133746704⟩
def resval2Tail196 : Box := ⟨5621694263311157926592679020719049215691084688,23203824477365737878021507062214155389616599454⟩
def resval2Tail200 : Box := ⟨12899525760315117325196145892239371309447536397,36275536614450633044402480800258950356180602232⟩
def resval2Tail204 : Box := ⟨29599219923252472380672982676292740328681950100,54291265494090585882695044511482929988649425492⟩
def resval2Tail208 : Box := ⟨67918296869553824382860569097868890402133429332,75195167632534858601940677619476996570144787872⟩
def resval2Tail212 : Box := ⟨155845156211104079767558198632911251169351836139,88300096107681770421067502980961237245329259611⟩
def resval2Tail216 : Box := ⟨357606792993197440829053424984562900788727874257,58898603756831454783845360526824942604491407854⟩
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
def polyval2Tail5 : Box := ⟨22205220706338918028820378188538949952163438715399461,3092509515672600199105686382438753899977957364449816638⟩
def polyval2Tail9 : Box := ⟨46254704741408850538216211802429026219303022356919854,5263816222588594817811406515426926612029961617812243605⟩
def polyval2Tail13 : Box := ⟨106135484912370495951012470549026658625295387408194853,8952610753676123828339809541917730998906668315333328492⟩
def polyval2Tail17 : Box := ⟨243538220979711156798401459642642655971365941118708966,15210282933806205082468924678205421770147002762601464999⟩
def polyval2Tail21 : Box := ⟨558822199856195940449135105228805219007920099240543166,25804714430714814018575560681930144512651410549542883600⟩
def polyval2Tail25 : Box := ⟨1282272038436163640405643775905776128579367931947196613,43692757548743691502214893658613913142737743402298748012⟩
def polyval2Tail29 : Box := ⟨2942298249744491002417433865188118782783269114257314977,73783116656164999145476198167863941383230654027761973249⟩
def polyval2Tail33 : Box := ⟨6751390290790062016615673691566975008494351291663480792,124138780244239205612036933734392286397331699102818104738⟩
def polyval2Tail37 : Box := ⟨15491723472470064217545832297757122658011137788878462914,207801128885497399420019761375933432220289302025411194962⟩
def polyval2Tail41 : Box := ⟨35547270385903789380556896757502413480574582892351814992,345380477743306844128596151718138719664440232721388194785⟩
def polyval2Tail45 : Box := ⟨81566678758117388778668007251126399788487827199900139099,568279242248649272969893877158896971247190254425081080458⟩
def polyval2Tail49 : Box := ⟨187162699453519876486581642261837945288319946031818743586,921445752209835494865847401737352230051939549837783742002⟩
def polyval2Tail53 : Box := ⟨429463067518149877807329349879906349829488088037090743407,1461774007872563826287914881733847750901206735718424714564⟩
def polyval2Tail57 : Box := ⟨985444893136426338726141373319433187803955453484774663039,2240922062632154875782502978793496667840505774671736339016⟩
def polyval2Tail61 : Box := ⟨2261199415867418110819769755076933002856227122540899881974,3242840172149301994561742987284262344800724108838442409793⟩
def polyval2Tail65 : Box := ⟨5188542590202667523606619618265344022924514303992850739124,4201105953134795760619622688830156143051400524503442160836⟩
def polyval2Tail69 : Box := ⟨11905617149593216923400855685800802206957254694558142086190,4112708861375508093121855272282250257591779395273192130492⟩
def polyval2Tail73 : Box := ⟨27406250000000000000000000000000000000000000000000000000000,2⟩
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
def resval3 : Box := ⟨115269800829841410951249704091186897578893706677658222867,1729760093177817672523031024624104118577324807420795452⟩
def polyval3 : Box := ⟨3809541321381805855549728553723863637460279922730302113998,241793572809202169939179576462840237202770959026132286046⟩
theorem cell3_lo : Holds Q cell3 (7/8:ℝ) := by norm_num [Holds,Q,cell3]
theorem cell3_hi : Holds Q cell3 (15/16:ℝ) := by norm_num [Holds,Q,cell3]
def resval3Tail4 : Box := ⟨-188051413816128260820395298568326298948456755721471932,1986821551512010759996689045366191565284239689045113468⟩
def resval3Tail8 : Box := ⟨-278879625287865220601399602957842582686186885234112523,2536650004754896681055320692088338262400235667964348505⟩
def resval3Tail12 : Box := ⟨-413451639518605402619465477233141518114695318314818809,3231359229986115026793997710806003143160407343334962832⟩
def resval3Tail16 : Box := ⟨-612960713445046603382952515174021551182628217227426437,4105386449897999030548955338992260063272629815716603088⟩
def resval3Tail20 : Box := ⟨-908741918786702038043810442608969111031468004675292123,5199339062879496279885001965907165680176420057612737988⟩
def resval3Tail24 : Box := ⟨-1347250903436802614912878213363574766183011826944295310,6559893693392352770874542321670343544578375963172843605⟩
def resval3Tail28 : Box := ⟨-1997360261794320433130407785130341644036634387162894056,8238741037915220861011209619740496224074625824562327376⟩
def resval3Tail32 : Box := ⟨-2961176723072217892934675850167123410093773287308120891,10289848161426833925480453346860750808491475418369583702⟩
def resval3Tail36 : Box := ⟨-4390078121103456687636983186866137174900458319904427910,12763880729869972645276654416427892493791279980800402982⟩
def resval3Tail40 : Box := ⟨-6508488925779397721266061819253853873676701909123877020,15697967316341978372693202765705648115833265915875288929⟩
def resval3Tail44 : Box := ⟨-9649128541326654815476767348418244700525791345022642049,19097978940819844022094320054071572429777392251639685822⟩
def resval3Tail48 : Box := ⟨-14305268499153997342149358553431890638036577579513234199,22908962334425320136362993121425042096208089797641545279⟩
def resval3Tail52 : Box := ⟨-21208206104460464450200495891704986290176356951003502835,26967039957948506169872998025689408520399094901397959936⟩
def resval3Tail56 : Box := ⟨-31442122613488448016368803063953588381590910157044551664,30922577158285049460859531028093967574448199630901248742⟩
def resval3Tail60 : Box := ⟨-46614365664505988002625007165586563788565765498314788524,34119124987200986154848620032928181637480838126837736487⟩
def resval3Tail64 : Box := ⟨-69107900657846247315490514557490638213009883201113093371,35404692782636173824472809058817323216358647803474667853⟩
def resval3Tail68 : Box := ⟨-102455433959268657217167855749605940473048241428026142732,32839970192920032156740965407035806239105223060209868786⟩
def resval3Tail72 : Box := ⟨812174562367639498306586029225381114277506258058522204530,796274092352253519529171956048507895434713282820322586⟩
def resval3Tail76 : Box := ⟨-2348106059953764726004632810281695614732290631457352,25485905875304453867066533518961120172549551917826243⟩
def resval3Tail80 : Box := ⟨-3441306781101214710830578872347687918116830647165375,32555931962151883523638256171665221710999654694890803⟩
def resval3Tail84 : Box := ⟨-5101890500670271342412034477628174218347289813066792,41497910875912736305474437528192245648768070035209885⟩
def resval3Tail88 : Box := ⟨-7563782899319844831677742486492713781823222227941780,52761443430832423400496345357833884536603173466536781⟩
def resval3Tail92 : Box := ⟨-11213649479393647361659820520055258434300270253160352,66879664748215626419897843871991652883777679017631081⟩
def resval3Tail96 : Box := ⟨-16624741392041709497090286678244862441740951253273293,84470042632068908264105765951861832482686170773775079⟩
def resval3Tail100 : Box := ⟨-24646929339119143582332810092818435434177886614569746,106224137639727541007199742238109792962730592993331974⟩
def resval3Tail104 : Box := ⟨-36540184988280747056497503785841024236946218676712489,132877419861609550591746962711414420182434284269874403⟩
def resval3Tail108 : Box := ⟨-54172473195620231024161020925075629267760021320218435,165145100166205162481349645542871839639077896912787139⟩
def resval3Tail112 : Box := ⟨-80313136156026641978810152210977856700931765077522571,203601856196380054093906469856349408926237284411163238⟩
def resval3Tail116 : Box := ⟨-119067848645646909990192205191941475114200529998970547,248470974836966921794336405390409149735069096514923027⟩
def resval3Tail120 : Box := ⟨-176523458797080445186081475415197847865949779132163995,299269614501814963870739648458641967195518649785210787⟩
def resval3Tail124 : Box := ⟨-261703993648362427775398299695282896670784213870373265,354228349101591342369089864197627444073510164423949952⟩
def resval3Tail128 : Box := ⟨-387987980511035027135729911020340257690461161482734312,409360009898070663392801697398395350402297646005577230⟩
def resval3Tail132 : Box := ⟨-575209689857858935586129094657450600232548017585134716,456987799514037720840684793625582388350658322995981853⟩
def resval3Tail136 : Box := ⟨-852774322750187845298680407403883892923196350807025629,483444831117957337865808700683813494348080910305926392⟩
def resval3Tail140 : Box := ⟨-1264276621844671596380208914340275898348463011058530344,465510402975940173507607431527610033296952437188139257⟩
def resval3Tail144 : Box := ⟨-1978770614914304478672956379376227878080296642182077698,359235843717653608661204207171286835561827428069512349⟩
def resval3Tail148 : Box := ⟨614530742884085230645537420759310626935551399,5391749878418661230188976108643664094798918173⟩
def resval3Tail152 : Box := ⟨818167449863212295627255432759163567230606353,6875539644931359408951767298590299906648962058⟩
def resval3Tail156 : Box := ⟨1212968556070593151779696467549088077143823905,8746828309017487229752354615713449722846307372⟩
def resval3Tail160 : Box := ⟨1798280621560057290512938445406679099706550379,11095057597265351826751731979126659706740558776⟩
def resval3Tail164 : Box := ⟨2666032172548618040564520819216654708720123114,14024887600466764282550601536704147567685231833⟩
def resval3Tail168 : Box := ⟨3952513005951433532042381903221303347487942029,17654521428504583215794782330236742293895003805⟩
def resval3Tail172 : Box := ⟨5859778896546818437837942670045058811987338786,22111354114742258276062689567078433739055173586⟩
def resval3Tail176 : Box := ⟨8687386648624064107935089027460328190613961097,27522315534641929595945898780787341001628941400⟩
def resval3Tail180 : Box := ⟨12879442742654795824528217654355913024650713772,33995402536999923451415968571967721741695163024⟩
def resval3Tail184 : Box := ⟨19094355077150376139619190962951268565562463208,41586926112922743513927576928459832499836047728⟩
def resval3Tail188 : Box := ⟨28308243073655354535235997135449143695471452812,50245997796915153506576014884702062130810441389⟩
def resval3Tail192 : Box := ⟨41968247823992496670956156427899955484056270319,59723223379833850293446458296858438560758827283⟩
def resval3Tail196 : Box := ⟨62219821301987125628628477426634185316306874055,69423680067177584996802128134332855636142884051⟩
def resval3Tail200 : Box := ⟨92243692876738457153941403792441155958779456085,78173857853722352816201687302344518289509579903⟩
def resval3Tail204 : Box := ⟨136755437374846713033349619230682465637443469543,83856604198910976999211425160176400423179811572⟩
def resval3Tail208 : Box := ⟨202746107276727551871387105247106511623285586531,82844623717432195747720490026645348879224769897⟩
def resval3Tail212 : Box := ⟨300580253462290316898585614376285272415280581426,69127877910304251913846562125896610323924596379⟩
def resval3Tail216 : Box := ⟨445628192084519706195097977800952689562297286037,32977231390616429675248505339377177982169607291⟩
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
def polyval3Tail5 : Box := ⟨33844751936973767292462108171858301547159690485840975224,305559411076316487205330751205065846793388404412438360289⟩
def polyval3Tail9 : Box := ⟨50173357035281364331422963402773508712297170899947607513,389195680901462272369732664145309227880769977410867227169⟩
def polyval3Tail13 : Box := ⟨74384265695120541073860761568992614849932084848102647129,494395769021484979938109985581903230365299306334953336115⟩
def polyval3Tail17 : Box := ⟨110278030634744028144784164922155132637352274210943442142,626029492430494266959647572217051084404194757813575477822⟩
def polyval3Tail21 : Box := ⟨163492156937422086082257182645802152314810476705160348303,789686111341164057838796618163078855287577047797440946322⟩
def polyval3Tail25 : Box := ⟨242384500577301377177238067409717438805266399336290665614,991541247371447682436448464647136869749028301192357126448⟩
def polyval3Tail29 : Box := ⟨359345960201595078449446091110040337965710617050184047166,1238018144836809234798320419467023658372165568756002522561⟩
def polyval3Tail33 : Box := ⟨532746602219411748604251049317428323415667897762293945925,1535102365440773240471500189736477244097352172618342333075⟩
def polyval3Tail37 : Box := ⟨789820879069028990884591787804512466885007757238935794329,1887088749465842780846458412057952225192048233035525594993⟩
def polyval3Tail41 : Box := ⟨1170945095500495762144741171519745907896147188139913745407,2294416868265654488366497099756631773420520519007229114752⟩
def polyval3Tail45 : Box := ⟨1735978945368994564097788895096055249227186867952788934827,2750064741690332306374584428516277142355241039718878128571⟩
def polyval3Tail49 : Box := ⟨2573667126105803554851428796254927207414434918735781796161,3233688114884222040909599856293556908421651746974605377486⟩
def polyval3Tail53 : Box := ⟨3815577656438557050399800105383001811899250290608877047994,3702265959828550455680615983254462580846497374410277342656⟩
def polyval3Tail57 : Box := ⟨5656766061406592924533295940207720581835855512064461203245,4075370219792047289791437951185614062392026757758678209327⟩
def polyval3Tail61 : Box := ⟨8386410959159783457250963073664820377177700599151042306922,4212211921326830140659490750873213173515779199228838293304⟩
def polyval3Tail65 : Box := ⟨12433232700896845750550646364384857736138827823823681251217,3876166787425179989888683333117026958798511701320806868870⟩
def polyval3Tail69 : Box := ⟨18432828687743523009181256183576984227342953951860812791589,2680313261475111630628740044430498573190134747169447957303⟩
def polyval3Tail73 : Box := ⟨27406250000000000000000000000000000000000000000000000000000,2⟩
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
def resval4 : Box := ⟨112075958597407789765927980407921587830493602581600310592,8764999675408737706032727117134679893584438108895315800⟩
def polyval4 : Box := ⟨4646356243506601134731913346690867577143878198483988328569,1919216566343303868082232095619104989602347472689686617837⟩
theorem cell4_lo : Holds Q cell4 (15/16:ℝ) := by norm_num [Holds,Q,cell4]
theorem cell4_hi : Holds Q cell4 (31/32:ℝ) := by norm_num [Holds,Q,cell4]
def resval4Tail4 : Box := ⟨-3989739479222342354608721414130328296511733375960624776,9510631671182406230117908242873295765159701982211769717⟩
def resval4Tail8 : Box := ⟨-4834497133123505835626070462935446353921215780697481835,10494038377288642211576190905617323406364376939618621062⟩
def resval4Tail12 : Box := ⟨-5858033669926889980253375612566944664345802686051912396,11546155794398977265480203586524248821599992932232789662⟩
def resval4Tail16 : Box := ⟨-7098268441457291960714727347294113458751044691695934324,12662641566816485267958807801493585002808872059840324335⟩
def resval4Tail20 : Box := ⟨-8601079765997076268768316237729164315129119183025954606,13835676921545174780326743735554120267646235418803347600⟩
def resval4Tail24 : Box := ⟨-10422059091055747993748599879928976873633812114068200177,15052883634010930215803742357398638282443098601580553253⟩
def resval4Tail28 : Box := ⟨-12628567418577604084235011434880490499167767837818688821,16295965475508742821177337271707805021678280005250214523⟩
def resval4Tail32 : Box := ⟨-15302227098522861594273512065689237591993923950047545125,17539008784526343885092984105389315398281722340741076376⟩
def resval4Tail36 : Box := ⟨-18541941173018766422906020788251157634565990357415337008,18746362782499520313205822663538933173842042070231256043⟩
def resval4Tail40 : Box := ⟨-22467551961562263811201232843142461017367352615144235846,19870002472458774186299875817389886983687609318350111112⟩
def resval4Tail44 : Box := ⟨-27224274224321498231876607080232909173708259770368298708,20846255279834924782316671432312136586026690004793378791⟩
def resval4Tail48 : Box := ⟨-32988066893493448983652121094753387236281400033919706752,21591746175565430467981317469653202379251438349130775163⟩
def resval4Tail52 : Box := ⟨-39972142081841658092272694613437917897654070583865661900,21998383838739989053969551185414056833692491844816180506⟩
def resval4Tail56 : Box := ⟨-48434852147279961570460041351866785336292703334605737071,21927171225983671466891649598963052578933225513630702662⟩
def resval4Tail60 : Box := ⟨-58689246568908903186865090135924768666555336015806531415,21200576207875030708153080283248434453079692441524515758⟩
def resval4Tail64 : Box := ⟨-71114652151096589819993894454864157611978448498731053321,19593139875770211800950447662649776573292135568743753466⟩
def resval4Tail68 : Box := ⟨-86170564373008683984469413085296890873355568234050361866,16819926675942912301953231012792930635728621456397994863⟩
def resval4Tail72 : Box := ⟨812498592164282275592874332290301289581543000821586766375,767339154817146467826515138635338679444090171062275734⟩
def resval4Tail76 : Box := ⟨-51783421269660438956554826859185908315665852123773790,126367963007279220038319452616821886947935330303546233⟩
def resval4Tail80 : Box := ⟨-62714263362828949718814979989929824224930941014650150,139530193197535151977534269652919069538169735527593880⟩
def resval4Tail84 : Box := ⟨-75991824483716198025513537725766379179343320093575134,153638776000768503605807176799705454997442893319630373⟩
def resval4Tail88 : Box := ⟨-92080448821016348773044174171623177974364571374282633,168644685239600297327514603190371282855196494526269782⟩
def resval4Tail92 : Box := ⟨-111575279482633235082216644427711165486419460836052253,184454933336287984292333528792346745955831652730087209⟩
def resval4Tail96 : Box := ⟨-135197462121694572832668415602510332919651435165658869,200918529216686595838173492057462863998001434394906356⟩
def resval4Tail100 : Box := ⟨-163820819888621292511582125977867128946302504414252557,217809009572359423377014907275118958881812336286656637⟩
def resval4Tail104 : Box := ⟨-198504177577114699354613067240012587417802723293016024,234802569163757803923465892401338667862416685268823128⟩
def resval4Tail108 : Box := ⟨-240530529284108489166987064218142122383724828852557702,251450763258840860106594654596379068024321121394020760⟩
def resval4Tail112 : Box := ⟨-291454498458693371546435437318671868203592157765454159,267146525025900543332474955425554482481396001293158534⟩
def resval4Tail116 : Box := ⟨-353159845964803854985825269457693181947430188376282394,281081959907917554590979159069760337652577060998873748⟩
def resval4Tail120 : Box := ⟨-427929153474912984625208119233274807683249891462528913,292196036785833359893976777401253372692493056129407861⟩
def resval4Tail124 : Box := ⟨-518528259897377541089853366405570819430601968556706075,299109878816146418300125900343613427596025468438214663⟩
def resval4Tail128 : Box := ⟨-628308574278907466225028440156918420075749623309338228,300046849084147834278724206562160522070719606926099762⟩
def resval4Tail132 : Box := ⟨-761331049903693083120831023578093262043873744772093956,292734008073720506276714897315055491810660272299405633⟩
def resval4Tail136 : Box := ⟨-922516405616227153689386162821895755812057911808745953,274280767651315299107434967291114764527504838556255955⟩
def resval4Tail140 : Box := ⟨-1117827347030279013040059886888498274887219822239773202,241029640331178493817099256440062751203487959383536993⟩
def resval4Tail144 : Box := ⟨-1453880810952521015827412516088071638136835813650934704,184594007978580841905820436581235517588250340496384897⟩
def resval4Tail148 : Box := ⟨18911239080923466364990397831905196738660789268,40178864117100862254378871926445165840755466435⟩
def resval4Tail152 : Box := ⟨22839242273407288580487096730862665033219229191,44180785801986897128338185168530984999752125195⟩
def resval4Tail156 : Box := ⟨27674655715314740108548856336869415361665125086,48420627242741561419723831286145624158999163999⟩
def resval4Tail160 : Box := ⟨33533800991638445852632500165652655702855287039,52865628390769177186506692398549167024689808790⟩
def resval4Tail164 : Box := ⟨40633416383860171971435903884743333127160013718,57465455286721057014342085686227344828609521971⟩
def resval4Tail168 : Box := ⟨49236128270573160436544907190191995027767169205,62146420107700185628940812476505248152033363766⟩
def resval4Tail172 : Box := ⟨59660165027109032615792410114028284729528659166,66804817413243002742268449057408791267595666349⟩
def resval4Tail176 : Box := ⟨72291128813009920862554409911411327101789851873,71298616766543306214576857566776591056701453376⟩
def resval4Tail180 : Box := ⟨87596259626243797862985934132867269351750805411,75437132208728665822332572227282213827034589086⟩
def resval4Tail184 : Box := ⟨106141719274515102795603714292334988526544970271,78968204459485624942254194097459933466039038319⟩
def resval4Tail188 : Box := ⟨128613534626022585039491261042439913374357006374,81562328607518988014628079601176280570946186629⟩
def resval4Tail192 : Box := ⟨155842974864745314502898379703222587266013182153,82793034458241481149450689988390661002337185338⟩
def resval4Tail196 : Box := ⟨188837301496413466444216195728929212047636602807,82112673774165331711662329863270589026818002345⟩
def resval4Tail200 : Box := ⟨228817028598151023170777162427767268748701910950,78822582487381882285430380041099482724953322043⟩
def resval4Tail204 : Box := ⟨277261071629333164213127659185801731127957269316,72036359434631610627035631331609741393435097392⟩
def resval4Tail208 : Box := ⟨335961454932007581929285503116471902780445868103,60634727586154465990798333284919689024419762651⟩
def resval4Tail212 : Box := ⟨407089601728772401700286268045834011202180984966,43210108571750703448104912640644038853837354340⟩
def resval4Tail216 : Box := ⟨493280853781499888906403425046045443130157232300,17998410733834995398423700695660897087636745765⟩
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
def polyval4Tail5 : Box := ⟨1044363693171194154676953463157465949806798944041113164687,2111383291472078482585109169772227764376524435144078039465⟩
def polyval4Tail9 : Box := ⟨1265468905426034997377599386459725082424996809212035074844,2317598957521138547214469584322401035569204691166402356700⟩
def polyval4Tail13 : Box := ⟨1533387907922016250089384218413945150843419308879959290873,2534867136906807233051889931629846707862037621100877443764⟩
def polyval4Tail17 : Box := ⟨1858029435914606418857300512794371150119560268664038756330,2761112523917679955653319390751340370410669141374057043108⟩
def polyval4Tail21 : Box := ⟨2251402510017087526165537036230170736989925459995019764962,2993222571245925429254877976731839855754638856937064524947⟩
def polyval4Tail25 : Box := ⟨2728058643277706354086878881451128816628774529034007640253,3226746920656892931311363897084312128274622411776915202598⟩
def polyval4Tail29 : Box := ⟨3305630125243892912252324169660566650613445523086399138397,3455522245961836443210664430481926271389928627501140532364⟩
def polyval4Tail33 : Box := ⟨4005482269175548388103695680448161569925332080822442861925,3671205222272311340714356243575602090555463580031651332844⟩
def polyval4Tail37 : Box := ⟨4853503749907883329415075198253087719306603023788526906619,3862692484971920121727244319664008396208521056142620579137⟩
def polyval4Tail41 : Box := ⟨5881064268253155494158678083256754509529632591803196287443,4015401738676112799236613586056038541524179513076608672658⟩
def polyval4Tail45 : Box := ⟨7126174967512997759193733230929615230989934788926922034191,4110382446646360208863894846728008523179781403610826718000⟩
def polyval4Tail49 : Box := ⟨8634894527805031576934245808989592898289326959907726055376,4123217553143385341309514999830777927019673723064425761981⟩
def polyval4Tail53 : Box := ⟨10463032951931415409796934075349564986640946215876027746351,4022669196035514653943780328294376775562455921447422937402⟩
def polyval4Tail57 : Box := ⟨12678216068613742893020511547309817696002850401937439561387,3769011028015972855883242169303216426082914047825393753242⟩
def polyval4Tail61 : Box := ⟨15362387122443757391962174238416872531708658291173484315992,3311977185542323906665073190766988940338038348541905282231⟩
def polyval4Tail65 : Box := ⟨18614837988466380291817162738102760388430981298329517095846,2588242643835213551674710750313456878057615304515229125197⟩
def polyval4Tail69 : Box := ⟨22555882268462926394598317154888049326570492704102714199986,1518331083311713524281163808371949420808235573119200945146⟩
def polyval4Tail73 : Box := ⟨27406250000000000000000000000000000000000000000000000000000,2⟩
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
def resval5 : Box := ⟨100397592240223199147997144448509156090608691724841423688,13958546404320589580713053434236557755186868269022209781⟩
def polyval5 : Box := ⟨8738895147319477541908238793604614349869996901799666399871,3842532731709146685282067114492839910888016875979165038130⟩
theorem cell5_lo : Holds Q cell5 (31/32:ℝ) := by norm_num [Holds,Q,cell5]
theorem cell5_hi : Holds Q cell5 (63/64:ℝ) := by norm_num [Holds,Q,cell5]
def resval5Tail4 : Box := ⟨-16445403770435355293459523928283515966379463401032434232,14176904425075546797502874888193380176939334623562107141⟩
def resval5Tail8 : Box := ⟨-18081975315713739625047745206788659383833012260900827009,14531450572972492122364695317792351683946333328029373048⟩
def resval5Tail12 : Box := ⟨-19881342120146672588039817939554692907662369219186302190,14852603500929347880896708983101626624354746915688021526⟩
def resval5Tail16 : Box := ⟨-21859766836900499607880383437517552526492835196654801379,15132574362772563866712181062577383022437086940566666063⟩
def resval5Tail20 : Box := ⟨-24035067817644315929195149868360717945867657417853739152,15362509479259706212156326680969088678082011701288640924⟩
def resval5Tail24 : Box := ⟨-26426836539884654060848723674366164551198724547890694413,15532364919882491642763662682811807536613818789262749731⟩
def resval5Tail28 : Box := ⟨-29056614060938851545230337042540202132878981145736702576,15630767954291727222375298274272310867352288903588779898⟩
def resval5Tail32 : Box := ⟨-31948085023801886322283744895162446222349494980545605528,15644863409450675516842577087475370977185622070499762776⟩
def resval5Tail36 : Box := ⟨-35127290968846459734496717485990541278164546224659211615,15560143345346269653304543548118241666912161445665069023⟩
def resval5Tail40 : Box := ⟨-38622864872517555047621667640143537519707317980915358102,15360258298740425376920405271932189388051960934162084665⟩
def resval5Tail44 : Box := ⟨-42466289025354267676864236514288878526763859350611569206,15026808164361375578581908903046023620977344713652145461⟩
def resval5Tail48 : Box := ⟨-46692178571873355380490370348100658837258780304694191419,14539110584549511744727269693753875481435700903439797924⟩
def resval5Tail52 : Box := ⟨-51338593265968139765772013830083387318910004935530797262,13873944499837553861480545500779853552302358182286470412⟩
def resval5Tail56 : Box := ⟨-56447380249594604048715254316296490711278568874416829917,13005266272229403489900290257982467699580218311522695054⟩
def resval5Tail60 : Box := ⟨-62064550941917531745949147852704762439922861942019746650,11903895527810015884244223225912444722297310763753414468⟩
def resval5Tail64 : Box := ⟨-68240695425595939901559073262742219854326086734919961312,10537167572997394727680725111636062090118541222993434004⟩
def resval5Tail68 : Box := ⟨-75031300679473701753332314488133150553710898264393323954,8868545082173547349481208193603037191275375929017420583⟩
def resval5Tail72 : Box := ⟨812525473793797589239563525854713101918350613233925509917,776400746893812477597470996190301085990562972507922629⟩
def resval5Tail76 : Box := ⟨-218163945205088957464288841461951535273755855273472229,191194469974116899896220911449584175730819266773160029⟩
def resval5Tail80 : Box := ⟨-239844348130289980196660933761251625724340368574073789,196101804727582181825375133904519481735984970216724816⟩
def resval5Tail84 : Box := ⟨-263711648081965763899244156243391586428083385117415064,200579652266688464906753021467733825829921733355632518⟩
def resval5Tail88 : Box := ⟨-289954023445247618394288061951165606918561972258501849,204525422854219055578679974615694835093291302639219353⟩
def resval5Tail92 : Box := ⟨-318807820298482423068376337971886616116172106952516592,207822600365068875859098602531913956739291107067536821⟩
def resval5Tail96 : Box := ⟨-350532905444102881879899563000717453149025063669473233,210338940784886266947895025551558099267410960944384559⟩
def resval5Tail100 : Box := ⟨-385415005453896251247314007954295094609337209607307654,211924638344024431854029266909151363589660416153393281⟩
def resval5Tail104 : Box := ⟨-423768280015909384889658455552206961990559628724040833,212410291705354677820221849624383334415165141038635621⟩
def resval5Tail108 : Box := ⟨-465938151360128298951433136527424907158889298016528503,211604649154590106878192491994165887412251746857164302⟩
def resval5Tail112 : Box := ⟨-512304415244914934364607678247485889058758343422517774,209292109591294707350848814128645895017937532276549937⟩
def resval5Tail116 : Box := ⟨-563284661522768249198848585644222966211149478526492501,205229953731243601680864129355428379309214896791682890⟩
def resval5Tail120 : Box := ⟨-619338035092152112651046184275556007754129905059153870,199145277300575304749546831464770482242272771149737864⟩
def resval5Tail124 : Box := ⟨-680969371107761581447343577813443603430801077882688965,190731595104766002233922633628965835905057292834935437⟩
def resval5Tail128 : Box := ⟨-748733741692294073753710377660127176254298953032216451,179645081663916786002085616579520645550238698999028380⟩
def resval5Tail132 : Box := ⟨-823241455098932398549670973694759917410433576633825824,165500410590529408371285297350570067070415538380415820⟩
def resval5Tail136 : Box := ⟨-905163552370630139458098563245676196405636312505321324,147866151012947851499720788280044160849019453156779981⟩
def resval5Tail140 : Box := ⟨-995238042381291878526920555135685314754441429569858790,126259666114446504822930256515532265524971362625534397⟩
def resval5Tail144 : Box := ⟨-1191330259190064185933458654734392847659424101276360015,97214520678307923916048789640155774842846575533920941⟩
def resval5Tail148 : Box := ⟨103325452519736869050455846394881059676636211988,77691510593902411270198855162347367606662272411⟩
def resval5Tail152 : Box := ⟨113538823368144994914621311103701483366220690945,79180776654058511901516958162661217520793324125⟩
def resval5Tail156 : Box := ⟨124837255311642445854817130885286168318989291195,80412941060316470477341383251326481796650688583⟩
def resval5Tail160 : Box := ⟨137260013794426308441905053747337100660687781791,81335517456433906305384921085006770260231810194⟩
def resval5Tail164 : Box := ⟨150918981195665265774040731443502952892644025568,81889596469855667281439871032159220306679908415⟩
def resval5Tail168 : Box := ⟨165937174676741447179292745397785781014209678947,82008579403854599732072699908400996534506987254⟩
def resval5Tail172 : Box := ⟨182449853037374435118889496587953047831201255876,81617294243256887877337433497296161772732974302⟩
def resval5Tail176 : Box := ⟨200605734900615542918887495605165469192601841197,80631015982660580357773124403291740033491575805⟩
def resval5Tail180 : Box := ⟨220568338121776529178679640528179728573398491877,78954381239168648546787667938400130253749858520⟩
def resval5Tail184 : Box := ⟨242517452484121666110107130581078610918182106060,76480186094807032491829530063153785005112707768⟩
def resval5Tail188 : Box := ⟨266650758944905347898494048166159391143518079359,73088054978941719649304151845654161504076865204⟩
def resval5Tail192 : Box := ⟨293185610015218671371309569539650293700194513929,68642967150952806056388485943018058276362342147⟩
def resval5Tail196 : Box := ⟨322360987308332609509450975682127954301722627091,62993625966563885827402612380376245076615856942⟩
def resval5Tail200 : Box := ⟨354439653886863264928553554009092137983783706833,55970654594787003157051406475603642600559677847⟩
def resval5Tail204 : Box := ⟨389710520793507145507630721098830811752131083104,47384600182370317310293726949409842290156480438⟩
def resval5Tail208 : Box := ⟨428491249079133473576568187170054501278696680659,37023726623459318624301068405664548564580347609⟩
def resval5Tail212 : Box := ⟨471131110849081704947198583953276073131108965164,24651574062034932110609429725877415401861984883⟩
def resval5Tail216 : Box := ⟨518018233927187007496987004825991973534408859518,10004074150320848947584926391139283543208513698⟩
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
def polyval5Tail5 : Box := ⟨5448683391685642911747849689459987923360836103822710129647,3919218416126686865337232474888869509546878654512828704229⟩
def polyval5Tail9 : Box := ⟨5990888520122894072389857067941116396945376101225266332149,3986110596683336096425613795710066051882294104919751561252⟩
def polyval5Tail13 : Box := ⟨6587051588375431058786011881629230379915146104989692721557,4038650412107915341932436010132054474153824137486766097979⟩
def polyval5Tail17 : Box := ⟨7242539814178996807756855084716556408764967818505437348229,4074043627736381917786163593865653833900746180106950453951⟩
def polyval5Tail21 : Box := ⟨7963256740320436806291063680439094999019727853298758746245,4089129143643711531012643839767018023639587434717441737157⟩
def polyval5Tail25 : Box := ⟨8755693380947927198621310534291776744489352844915678430261,4080336701943629050013750118509019663814378926019720534639⟩
def polyval5Tail29 : Box := ⟨9626986681593604299854738108540378189400394279112326137512,4043640020470188263101642060283785337136790595341904519123⟩
def polyval5Tail33 : Box := ⟨10584983796856856481429118218082766323548130081541647126845,3974504862823815209922012983848799832550426242761468550946⟩
def polyval5Tail37 : Box := ⟨11638312764464667182360407736325257153667781283816394585072,3867831514887838038140158518144335614929991015960802563361⟩
def polyval5Tail41 : Box := ⟨12796460212222744702915515575653521442086706823561179853230,3717891083502631639060007445986660938588177892148840127653⟩
def polyval5Tail45 : Box := ⟨14069856797711848439398088043342982607072435807160785160748,3518254973038076960066307110996645954039646916950136658966⟩
def polyval5Tail49 : Box := ⟨15469971150227373229855141977023142138510277216652917773792,3261716829576168492324995713296355934293390252352271071983⟩
def polyval5Tail53 : Box := ⟨17009413161034258173610015847317338706169147063348048824798,2940206169691416641038303825192993963589388079312547974972⟩
def polyval5Tail57 : Box := ⟨18702047552203294890912716012249294028318628757294266237728,2544692830722815579269417906642369700697806790139554321682⟩
def polyval5Tail61 : Box := ⟨20563118746867216065850789193898663064062978720167028867458,2065081291225577150597810725969292636862647473112760589724⟩
def polyval5Tail65 : Box := ⟨22609388165533863138968955579871302297686716112330739770026,1490093813156337964140628793079483716452384106710344997973⟩
def polyval5Tail69 : Box := ⟨24859285309647066167164813417325864697366906643791335968565,807141244887177986175073105506960505211955273153628205737⟩
def polyval5Tail73 : Box := ⟨27406250000000000000000000000000000000000000000000000000000,2⟩
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
def resval6 : Box := ⟨84507622059409879809114258411962781313666411890919233995,12511538425271077389218528230197851099042514951637810084⟩
def polyval6 : Box := ⟨15480530258388841617433948609770282433460045307474747521868,3845644701686990609242272880132230032813047846335359642756⟩
theorem cell6_lo : Holds Q cell6 (63/64:ℝ) := by norm_num [Holds,Q,cell6]
theorem cell6_hi : Holds Q cell6 (127/128:ℝ) := by norm_num [Holds,Q,cell6]
def resval6Tail4 : Box := ⟨-32328976190927071525336738696970347664832913873359713806,12238594134472509685979601856303120841743275822293948951⟩
def resval6Tail8 : Box := ⟨-33889916021406132381397950074878375801799583553127446744,12098081891806778007420422102471599631270139626326514018⟩
def resval6Tail12 : Box := ⟨-35526160153984074131706840033376582150009678206974583887,11927476194902689284173015841302597038932227353326416211⟩
def resval6Tail16 : Box := ⟨-37241404028283904062119999849784108295707139316943353246,11724580676252576858415413172432303989631457159593724468⟩
def resval6Tail20 : Box := ⟨-39039461849696011786097493120316755996464325147738363391,11487069783339939818745113661608215957397773431555651652⟩
def resval6Tail24 : Box := ⟨-40924331970845394500162513514022437945083016656902975851,11212481253042736284025906092612114765645997189234193526⟩
def resval6Tail28 : Box := ⟨-42900205789414580165045354640241639847032668876230857725,10898208732379241767238202818248372462793079675386337279⟩
def resval6Tail32 : Box := ⟨-44971477068587116670962678861215298523188697695369066325,10541494018273544543178395981334704257468992140258156315⟩
def resval6Tail36 : Box := ⟨-47142751707486743650911003370441023470750737388122067941,10139418897043438469954156327881160432537441353740999075⟩
def resval6Tail40 : Box := ⟨-49418857983344583184359826407230116363769592828959027900,9688896563468684067766257146839399883247208985392830129⟩
def resval6Tail44 : Box := ⟨-51804857288169942714105353937397682993027816926392199027,9186662598299264781324084074921525292287648726431656799⟩
def resval6Tail48 : Box := ⟨-54306055383799933594578141563290512628986800588469825906,8629265482015749080299390173111712026561728085724349672⟩
def resval6Tail52 : Box := ⟨-56928014200355830556921194446607327405910508487854969857,8013056621554921501083412013731994571549460695582249472⟩
def resval6Tail56 : Box := ⟨-59676564204342458499777609968965373554744986997506868871,7334179865560955944088788257504866119149650535932125995⟩
def resval6Tail60 : Box := ⟨-62557817363888711855942979703219276888593657924897029204,6588560482512649152213840942371634726885482156276045808⟩
def resval6Tail64 : Box := ⟨-65578180732332216434076244722878979569331793847299844828,5771893574470901368237699240077597304080483209937903986⟩
def resval6Tail68 : Box := ⟨-68744234829706803230164650541915503123491945553882942001,4879627581944153332993379591410446082839617091746640993⟩
def resval6Tail72 : Box := ⟨812402549134263914122743020873437739428273217405565438019,727275091976993064915813191676925280260894826359067332⟩
def resval6Tail76 : Box := ⟨-432541392925406925811270050765060376987773196970084164,165943269367030851786260387622690875068458628626359791⟩
def resval6Tail80 : Box := ⟨-453396933492947775386241504887432628670738909294107155,164133671331131320776903182345461403235874212239208481⟩
def resval6Tail84 : Box := ⟨-475287457467738266974627272469849726500300501773741076,161923858828013227563999957813412443736645282374494645⟩
def resval6Tail88 : Box := ⟨-498234882587368620892841782529248712994738590218231000,159284371318769248942857728457090252222497108970235435⟩
def resval6Tail92 : Box := ⟨-522290235786622076572781286314239460783701145224458624,156184170115413537042038420171287082854089356882339237⟩
def resval6Tail96 : Box := ⟨-547507009106716771248002682949553310024585330633758568,152590389911554821250012318768526743510998995475904850⟩
def resval6Tail100 : Box := ⟨-573941277246945987642326239490923051929092922285630690,148468240117986727277174830310210400717909832514641500⟩
def resval6Tail104 : Box := ⟨-601651822257583885045347589597647488239234144983098241,143780901119545500940385858001526585140268302843917255⟩
def resval6Tail108 : Box := ⟨-630700264253902776772662369343758068208082313042330475,138489415179322936673560121409262821426668203947770492⟩
def resval6Tail112 : Box := ⟨-661151198441215554820981561860073421711610982138028971,132552571720829666551503333056575036632662020785708313⟩
def resval6Tail116 : Box := ⟨-693072338755644786249793547451449227037161833784739370,125926786705362895601664974857744744874642125045222253⟩
def resval6Tail120 : Box := ⟨-726534668440033357087352354638214010983488225021663299,118565975807821079078948979433276446046601309849622371⟩
def resval6Tail124 : Box := ⟨-761612597889833275533373857083216526416976609086877016,110421421079508410914163884912645513170651281836367592⟩
def resval6Tail128 : Box := ⟨-798384130119975643801371068268750598430274536536374071,101441630771050790938662963661542940251808851101765885⟩
def resval6Tail132 : Box := ⟨-836931034220693697782124579612459597723996217403958172,91572191972365392156004555548948991588610537694313762⟩
def resval6Tail136 : Box := ⟨-877339027209772923981116058803602818607775561612090686,80755615708453283337987144643121972940391390460099991⟩
def resval6Tail140 : Box := ⟨-919698153962721533705859610529220373797836654524666402,68931165924485779486460779881339372812604991898711218⟩
def resval6Tail144 : Box := ⟨-1060028491858404254222859859455143403884320825310474693,53510109059626229429299011092873839203138396644928663⟩
def resval6Tail148 : Box := ⟨238104584562865795989679490645739889275232468648,76688209808910372521241481573271158049626356763⟩
def resval6Tail152 : Box := ⟨249535065782850567179192580970565246932437826939,75225230719879399530741719432775170641184594666⟩
def resval6Tail156 : Box := ⟨261582904644074993563470058417157772848691213104,73527507988114792890257695659007780614390423748⟩
def resval6Tail160 : Box := ⟨274212428151641848104260728223755813324555080631,71577960146916673957568452857466882449162776775⟩
def resval6Tail164 : Box := ⟨287451719580933235864042453561347453369634972647,69359015426060300379944657671993054961582633724⟩
def resval6Tail168 : Box := ⟨301330219228215916898058762116757747512726407015,66852081160964393338277569858742421942777674064⟩
def resval6Tail172 : Box := ⟨315878788801468881380786927315881901114024480242,64037488989925614517131472859064461883475100070⟩
def resval6Tail176 : Box := ⟨331129780047429946078478033112728722612099961425,60894437244655860836966654646332733940561786299⟩
def resval6Tail180 : Box := ⟨347117106692380293719554213335298615378893542698,57400930378558787321719738388263009442783514667⟩
def resval6Tail184 : Box := ⟨363876319856313406375646373151108483706545999089,53533715283954720721819617244349498840480015500⟩
def resval6Tail188 : Box := ⟨381444687108186819465627283862024032573359110332,49268214342102516533787924571922896042247735009⟩
def resval6Tail192 : Box := ⟨399861275338052359562394735528746541858965438684,44578455042138248481645634570979471399349734525⟩
def resval6Tail196 : Box := ⟨419167037630348149316630562525035267654358572186,39436995996942751675214010667603632419692330561⟩
def resval6Tail200 : Box := ⟨439404904331533072278439007078779494892330401931,33814849175444483328872762623175190347473016707⟩
def resval6Tail204 : Box := ⟨460619878514571443441061338828173019979508082457,27681398161941513104694727952705638102379914900⟩
def resval6Tail208 : Box := ⟨482859136052583876755696405454425752144425261645,21004312243664317847064352408396755701468305073⟩
def resval6Tail212 : Box := ⟨506172130609405930776924355487577634622807328975,13749456113477319230710442498478681794407694600⟩
def resval6Tail216 : Box := ⟨530614756169250731691994016686337238244746692147,5880625215194799783834599028191936815289095965⟩
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
def polyval6Tail5 : Box := ⟨12262524465569530729449504240099653434898402983052106801395,3773878901059399047547218745717709018946533215907252793618⟩
def polyval6Tail9 : Box := ⟨12854571131378171378038928640819609766364850732512633767889,3692910639793292147801237891037059470468284324499517899325⟩
def polyval6Tail13 : Box := ⟨13475204610682360220623167273161968265616303631571670524199,3599645740912809081983720124196631639430645672786585650759⟩
def polyval6Tail17 : Box := ⟨14125802988416950312003337812946845109145998770236958294223,3493223191185073334544025565188876974249214012889632996180⟩
def polyval6Tail21 : Box := ⟨14807813004144589453405826074715911077651314660411124844784,3372731898171530067330998988864097271377176052807946049338⟩
def polyval6Tail25 : Box := ⟨15522751247876982122206428651657592286387054155980854717883,3237207990267396943257503650071461689624816366206308493171⟩
def polyval6Tail29 : Box := ⟨16272207532336124587536288884803248027136553087495334272898,3085631988304621528100085265581702629855210633187326297606⟩
def polyval6Tail33 : Box := ⟨17057848428230828364701904181486452092437726755482274590201,2916925831670301390752276632034403433940923287120516763485⟩
def polyval6Tail37 : Box := ⟨17881420970220609920624497559786888579998790935776370711315,2729949751629556044623521498500907547029839166658688302237⟩
def polyval6Tail41 : Box := ⟨18744756541807780045218475997323890024109030041111796817383,2523498984182080589877248354104145587631470993221522712637⟩
def polyval6Tail45 : Box := ⟨19649774947796591691270316838378034891283512184463716908929,2296300314401902303304657447408517658766665273210861722841⟩
def polyval6Tail49 : Box := ⟨20598488683375399599788311355359065102612988189281169225829,2047008443811519072728905199173753983676219622064421024753⟩
def polyval6Tail53 : Box := ⟨21593007409315016875660732652812924876461921730868101913964,1774202171923716046584829470554339594429514336953489273557⟩
def polyval6Tail57 : Box := ⟨22635542643234795640516508672771292965573497975585215637301,1476380382645980944079503750797996912833427609200776620418⟩
def polyval6Tail61 : Box := ⟨23728412677368444420937845230825439416223950047777466473208,1151957825782568600750404550223622906498738323841298158912⟩
def polyval6Tail65 : Box := ⟨24874047733779720382854081008515151564333529224013806453636,799260683386084852966096037675675777586211939250175216311⟩
def polyval6Tail69 : Box := ⟨26074995491777744715818990979249715187926271289861318312758,416521905211913125618331202762289523579974757380622589956⟩
def polyval6Tail73 : Box := ⟨27406250000000000000000000000000000000000000000000000000000,2⟩
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
def resval7 : Box := ⟨66040758506351425213751640173814911475290826740756909334,20217886032640940704954683462439288961048187200768525013⟩
def polyval7 : Box := ⟨24404205325840415930495359514935560930868862449976340415818,6716834193908877021270663886109478057384089763454480046415⟩
theorem cell7_lo : Holds Q cell7 (127/128:ℝ) := by norm_num [Holds,Q,cell7]
theorem cell7_hi : Holds Q cell7 (1/1:ℝ) := by norm_num [Holds,Q,cell7]
def resval7Tail4 : Box := ⟨-50080120011088913436117803719328176857123545898790296592,19279465623241335703046258166338882985886717418002121420⟩
def resval7Tail8 : Box := ⟨-50870381408227474688491312072661618884122848430119046830,18489260609462645256412110552371156657465077528632410354⟩
def resval7Tail12 : Box := ⟨-51673054388081274676888483585352073109112979997984146028,17686587636178315980465628737009601265649968832087499155⟩
def resval7Tail16 : Box := ⟨-52488392568088034451274199970447252259366856495596154696,16871249456177285710264240249438920987379208561619601331⟩
def resval7Tail20 : Box := ⟨-53316595796529364424960076144265649988098162068680034977,16043046227735977461454460562632757380658822071236693065⟩
def resval7Tail24 : Box := ⟨-54157867068285407454371599931590454159844352438542892621,15201774955979934705066842679120771461405610657819742434⟩
def resval7Tail28 : Box := ⟨-55012412581243625750030934837061874025799321200870778196,14347229443021716418841171724001586141790182064716044743⟩
def resval7Tail32 : Box := ⟨-55880441786844249708727084669235420456668563906243218903,13479200237421092460877438947116151063233974550449790857⟩
def resval7Tail36 : Box := ⟨-56762167441417419655708730928840901050148876205828869203,12597474582847922513954947303438572569040436207054551220⟩
def resval7Tail40 : Box := ⟨-57657805658330343960067983258733797522053702456090487904,11701836365934998209452723072181929742650709477267479506⟩
def resval7Tail44 : Box := ⟨-58567575960957275863935068708647431737301146534475478475,10792066063308066304732301083386222584353838453143097236⟩
def resval7Tail48 : Box := ⟨-59491701336485292343630490929024831623828945781131490438,9867940687780049815960291955802187487286293934820144801⟩
def resval7Tail52 : Box := ⟨-60430408290569062775808376224199538595799842782289578761,8929233733696279144333184780976755787981150253521443503⟩
def resval7Tail56 : Box := ⟨-61383926902847987463736401541308715120470963998875771945,7975715121417335869418875718767832959623329341549143305⟩
def resval7Tail60 : Box := ⟨-62352490883334429285804943373965307732112303943539284115,7007151140925609970579222252517442622924559622424054216⟩
def resval7Tail64 : Box := ⟨-63336337622111873783236002892155247739756871736594154268,6023304394206883435753743025621658798272169516819010329⟩
def resval7Tail68 : Box := ⟨-64335573384321122140170009095536925214515761160927374024,5023929453233602974777823073838537708131370113597100708⟩
def resval7Tail72 : Box := ⟨812214138094053643721584956919888043696106254996523176921,829561115365066548288008934801354060459820861780213882⟩
def resval7Tail76 : Box := ⟨-672322635635600395688577260516378286582614417437443761,261072296788285966306210822996013875171504354985721016⟩
def resval7Tail80 : Box := ⟨-682903898813201313284828104667037869625721167518178751,250464127595520675889963235568630711089536751982222155⟩
def resval7Tail84 : Box := ⟨-693679293359586061659784506716257201532126304420781976,239688731630986493731457471314213319277119703259696027⟩
def resval7Tail88 : Box := ⟨-704624711996233140511065449122939017820275223093015949,228743312993557372880567556322120205880256841486343469⟩
def resval7Tail92 : Box := ⟨-715742836075908214316246707301174120970726965243581824,217625188913880200313683582200346521823383092633293482⟩
def resval7Tail96 : Box := ⟨-727036390680440015648005149371247657190675147320511085,206331634309348378926544243191019224205181633291020343⟩
def resval7Tail100 : Box := ⟨-738508143890919202980765653547608836520027493179634077,194859881098869191029403295783259704021121582916369066⟩
def resval7Tail104 : Box := ⟨-750160907465403654502098967343061496275706153486572821,183207117524384739467711521286599099198036041384180104⟩
def resval7Tail108 : Box := ⟨-761997537528086085839678961667274307240487448119907867,171370487461702308124140110908148960809845851575240760⟩
def resval7Tail112 : Box := ⟨-774020935269337876620522199081125048933545045216326018,159347089720450517342869797741298999205587237373382715⟩
def resval7Tail116 : Box := ⟨-786234047656798757452667028405533032033694796795524568,147133977332989636517594149256808096276253730254925652⟩
def resval7Tail120 : Box := ⟨-798639868157686630907416721133427461509631995607819925,134728156832101763137785221306559913364675416062776651⟩
def resval7Tail124 : Box := ⟨-811241437472504567710502469801993829727116186345876876,122126587517283827996102986064681763132735003883547799⟩
def resval7Tail128 : Box := ⟨-824041844280324913105821624868029459022551184221837048,109326180709463583471851495312522098330807334504237810⟩
def resval7Tail132 : Box := ⟨-837044225995855200583478849028308151211786210311642361,96323798993954337649778679832851572335117899921764256⟩
def resval7Tail136 : Box := ⟨-850251769560082139101355144555788549341910108810644038,83116255450271891299737478380778097888446646661887251⟩
def resval7Tail140 : Box := ⟨-863667900165092387535788938962950490541575577428128442,69700304754060298897880532108995555142071693810519008⟩
def resval7Tail144 : Box := ⟨-972484112084360245345332535264987873745050559977397116,53571021785769637690461322105437191286758286744869186⟩
def resval7Tail148 : Box := ⟨413184301412241730709924974082569307652914035146,131910934992725957136842857187685652000771655315⟩
def resval7Tail152 : Box := ⟨419640416342811935106397002126986908134398976583,125391894051916236982079146693866730182278293904⟩
def resval7Tail156 : Box := ⟨426261832492415829990070729730521972807136518156,118770476812200106808743320194486088002363047335⟩
def resval7Tail160 : Box := ⟨432987727657825781086453929772643304722887521014,112044581646451847736594923705279890039799039285⟩
def resval7Tail164 : Box := ⟨439819749298733681706584844299188421138128415153,105212560005543370494882430627810357616438130638⟩
def resval7Tail168 : Box := ⟨446759571961981341118751848588355691760291525835,98272737342295707365992623270180398266832200291⟩
def resval7Tail172 : Box := ⟨453808896617065696092861869683077412233963114086,91223412687211352318485985109432123287358661059⟩
def resval7Tail176 : Box := ⟨460969451072721641278632298741545977731004857266,84062858231555407128887194248190174237214408954⟩
def resval7Tail180 : Box := ⟨468242990400412124813806656972798153299821291450,76789318903864923593260164950555868590040533758⟩
def resval7Tail184 : Box := ⟨475631297364500956231044071011420604684432683122,69401011939776092175942817317968940377709812063⟩
def resval7Tail188 : Box := ⟨483136182859213223287516723173011422739496886285,61896126445063825119560274145546612622598674222⟩
def resval7Tail192 : Box := ⟨490759486352490414712752578018887455137529984944,54272822951786633695286950592665725998181546054⟩
def resval7Tail196 : Box := ⟨498503076336849038937433470365573352931429929873,46529232967428009485474386710314186436594413756⟩
def resval7Tail200 : Box := ⟨506368850787353246022981922989945012490401085819,38663458516923802959456210198034668361127952665⟩
def resval7Tail204 : Box := ⟨514358737626813770283930812367898614280511739951,30673571677463343277562111508109324421445084781⟩
def resval7Tail208 : Box := ⟨522474695198358019205935695555111755175742262975,22557614105948232762999446631912585443605166720⟩
def resval7Tail212 : Box := ⟨530718712830092708950097323319964992409550938146,14313596554527690586819556325726201251874438463⟩
def resval7Tail216 : Box := ⟨539096833499017261259297231799919329388620944939,5939330120203038643285460334084275516158404521⟩
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
def polyval7Tail5 : Box := ⟨20947179188806955468384240001651133125514741648353968812065,6389165989039450142048521166407260622214570317306606173297⟩
def polyval7Tail9 : Box := ⟨21277698239413660598487935681612086138733727239814181939436,6058644907354542878169783374334763813282602532087265411515⟩
def polyval7Tail13 : Box := ⟨21613434532779691066255464443389005317210985046573787852380,5722908613796282391009534231402833702570737321474897842245⟩
def polyval7Tail17 : Box := ⟨21954468338197240019070433290669724359413866877817004215682,5381874808378585991616637217088440451574105117074003083513⟩
def polyval7Tail21 : Box := ⟨22300883243794142733814967467493902364629857178924967280317,5035459902781682775502285564428491400491961684270277623224⟩
def polyval7Tail25 : Box := ⟨22652764156810179144581973371945863795201591938721985016125,4683578989765646358990817949874007301208095056372745593252⟩
def polyval7Tail29 : Box := ⟨23010197324218626492872864497178778785183663895239335881246,4326145822357199010513446867244572343308381819824057865262⟩
def polyval7Tail33 : Box := ⟨23373270353865485336709710383918760227410343334217904296071,3963072792710340166661715444395925191943921900165372299079⟩
def polyval7Tail37 : Box := ⟨23742072235942401523166121012977042889514386466138950307294,3594270910633423980202954246717211172846816603901934826755⟩
def polyval7Tail41 : Box := ⟨24116693364798405317258404880657330332537007965965442958266,3219649781777420186110652655925450762848346028195847654179⟩
def polyval7Tail45 : Box := ⟨24497225561095813347298680836379098217735634235469650996878,2839117585480012156074266981833237444981430504781370839931⟩
def polyval7Tail49 : Box := ⟨24883762094315723834223433886850415482861333762164123662865,2452581052260101669192635419328651762140664383103194931946⟩
def polyval7Tail53 : Box := ⟨25276397705618621264043112055746926896456092200211591300560,2059945440957204240371132623593745128714697807516870987647⟩
def polyval7Tail57 : Box := ⟨25675228631065693763782140648096368174703949605605396249856,1661114515510131803967420337245329513221065153863459494826⟩
def polyval7Tail61 : Box := ⟨26080352625206569119452767272305420956994789193489307846181,1255990521369270155851462362614119313468329516826132667306⟩
def polyval7Tail65 : Box := ⟨26491868985053623035956400592464067363740264260356203192719,844474161535905685006629191077816265074699005987536256976⟩
def polyval7Tail69 : Box := ⟨26909878696838872779983754758851348701816020085467239369200,426464567274918031235306657946869862696007860087178502023⟩
def polyval7Tail73 : Box := ⟨27406250000000000000000000000000000000000000000000000000000,2⟩
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
def pend : Box := ⟨1031116987934153609332957932621105103956910751618742694709563,4051585595683618808090779939935031342200594688125752740⟩
def zend : Box := ⟨1003778200326649003408046875000000000000000000000000000000000,2364947119601087851562500000000000000000000000000000002⟩
def betaquot : Box := ⟨428754733950139814452399575302669994537875158805559847110057,394780327016570256872561276666309780764230812672044052⟩
def crit : Box := ⟨138144150189469829117354599665315607828353950619817437494,10101599724110303482403868856810551854561513569531721073⟩
def subsonic : Box := ⟨464412188613765801928875931219642034502713597383186371290,5119082937993204483039198891966908369064473093242476936⟩
def pendTail4 : Box := ⟨27334724105162231491933103327607453470136988239156563743897,1583785774198365012661321865893105474119273570786147807⟩
def pendTail8 : Box := ⟨27334759489146880963230982032894078382105723525920338677209,1583655921542129429592524601505102660897442206143080679⟩
def pendTail12 : Box := ⟨27334759490669434525211267279269796076716216059405238427395,1583655905655848348032317249335957968043207981443324654⟩
def pendTail16 : Box := ⟨27334759490670180947024985838065260313314700617076644957055,1583655905642799390853469107893253638524935651960945686⟩
def pendTail20 : Box := ⟨27334759490670182736722285750168585956192606921930561750682,1583655905642751660385502832092487495625833550881728812⟩
def pendTail24 : Box := ⟨27334759490670182751941610610076475029751616147911658331176,1583655905642751046627617938461812574708763751174708827⟩
def pendTail28 : Box := ⟨27334759490670182752319303787401157291596825178849640417105,1583655905642751022780816214259122034744085543858348745⟩
def pendTail32 : Box := ⟨27334759490670182752342711509387011587351977131619183307388,1583655905642751020227096529128401564034371506872180110⟩
def pendTail36 : Box := ⟨27334759490670182752345579502554682932843644238360907837676,1583655905642751019512003175793532945473131301355996152⟩
def pendTail40 : Box := ⟨27334759490670182752345540171559668792646850806635091596803,1583655905642751019001024448232247667455389842033550842⟩
def pendTail44 : Box := ⟨27334759490670182752342396984212492565053804511290543127843,1583655905642751018070406834612385131116892280121369853⟩
def pendTail48 : Box := ⟨27334759490670182752315578448746690157895708472092545947428,1583655905642751013657101138176233571233263404571827791⟩
def pendTail52 : Box := ⟨27334759490670182751840905853422602492639613474486111524292,1583655905642750956484106646594648069076224289188576085⟩
def pendTail56 : Box := ⟨27334759490670182729525899529929026438048119779685713501555,1583655905642748793561014651747690443486690418265397943⟩
def pendTail60 : Box := ⟨27334759490670179342689713675164444645955045385547844860178,1583655905642505936473814089489226723565139080738778122⟩
def pendTail64 : Box := ⟨27334759490668005114246489731055873280301635529920292068018,1583655905525669730894529027828713199350697242899729571⟩
def pendTail68 : Box := ⟨27334759480879658974443415752204868295228300451655911948186,1583655513514212065122600665651976508233223306848944006⟩
def pendTail72 : Box := ⟨27333524135345007879311975789809071987665468335128415871147,1550234864281024167257782385987254326345792709763832509⟩
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
end SepticProfile.ExteriorCertificates.C22

end
end

end OAI
