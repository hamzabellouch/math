import OAI.MathematicalPhysics.Transonic.Certificates.BarrierData05

namespace OAI

section
noncomputable section
namespace SepticProfile.ExteriorCertificates.C05
open SepticProfile.ExteriorJet SepticProfile.FixedInterval
def cell0 : Box := ⟨250000000000000000000000000000000000000000000000000000000000,250000000000000000000000000000000000000000000000000000000002⟩
def resval0 : Box := ⟨106212866263516246004111386717785081303576528062981164781,440915484071454660813635780196863267000065216561705819⟩
def polyval0 : Box := ⟨3730391564803411758059310691513132274841617180548736800792,16873194010940009114374108154667388864305528734925157587⟩
theorem cell0_lo : Holds Q cell0 (0/1:ℝ) := by norm_num [Holds,Q,cell0]
theorem cell0_hi : Holds Q cell0 (1/2:ℝ) := by norm_num [Holds,Q,cell0]
def resval0Tail4 : Box := ⟨50378884735150975535034143012560487945126774870375,1775373381876203060426140664581411139468571522751⟩
def resval0Tail8 : Box := ⟨5628077978423066815984314700418501683804012078,347255437398552498130883738569071384449419759⟩
def resval0Tail12 : Box := ⟨4729726674185629279874679707388266833561547,438027409257636548297821411128192655202738⟩
def resval0Tail16 : Box := ⟨17505431394444256325852707224015258223846,24752856398563298621651521754285756165041⟩
def resval0Tail20 : Box := ⟨220495022970115754071872221499327942665,359618329514024415159661125372036409920797⟩
def resval0Tail24 : Box := ⟨8112420755977124830932038498430892135,5753264388278726004539110255335426296739939⟩
def resval0Tail28 : Box := ⟨793411681564814851154623743671366705,92052198800485589052101583922977205422776110⟩
def resval0Tail32 : Box := ⟨192908448104246848364953409411887035,1472835176616910149496993140414797157498855024⟩
def resval0Tail36 : Box := ⟨-411153851073127519792423657798267131,23565362824192277734964025908710384106679281159⟩
def resval0Tail40 : Box := ⟨-135027358999930212073618841751963373582,377045805059767109633317256922868614897426573492⟩
def resval0Tail44 : Box := ⟨-34609984765411093573388179358299822004715,6032732848507864351659287586254947796788906491309⟩
def resval0Tail48 : Box := ⟨-8860306987640185265012751761849495382475511,96523717269578759062114383135431401359905413190385⟩
def resval0Tail52 : Box := ⟨-2268239888906751933121567349091752178990768486,1544377349838196282122550177432972516279940635366170⟩
def resval0Tail56 : Box := ⟨-580669436956575136553739763155459594884455602369,24709493219803663382396060678802003849905721685841875⟩
def resval0Tail60 : Box := ⟨-148651375367624933945702802039728265711230162241924,395212530849880818931039622021086890856835404911767579⟩
def resval0Tail64 : Box := ⟨-38054747445784678395924816500125734751650231224640601,6287724164335777386029124020559739213211505228184730067⟩
def resval0Tail68 : Box := ⟨-9741908128804174772547468182642591301085812372669279275,91470487870951049357020948889349664582833719573771933222⟩
def resval0Tail72 : Box := ⟨728381317311728501684545418388476575247344858433039125276,2719417170399975961088011887724610490254445344983916142⟩
def resval0Tail76 : Box := ⟨-22990330247406483910962551327679070381099881580764,606838888383124844009084692735565516064312551698⟩
def resval0Tail80 : Box := ⟨-1147278586756924876538448280406420053684631404,60557145337750195387908169906782641431827054⟩
def resval0Tail84 : Box := ⟨-599392169349471406507562895150083137939372,49277245021378128568024138505728307886571⟩
def resval0Tail88 : Box := ⟨-1532495915357458534727482799247361681029,328576846470308296998924579793089323557⟩
def resval0Tail92 : Box := ⟨-14110944971837504129978279288581653036,2367812235262864786028262920780301450264⟩
def resval0Tail96 : Box := ⟨-392840419108703004217227412536116757,37848218964884404031813480981570157119059⟩
def resval0Tail100 : Box := ⟨-29705058538563549203239114720766805,605570109173271947523517172871048818278528⟩
def resval0Tail104 : Box := ⟨-5723578622427321207098237365635991,9689121603099390062554568531428844551431264⟩
def resval0Tail108 : Box := ⟨-4434982916126299570446767298897553,155025945610805820856533364156150986908086537⟩
def resval0Tail112 : Box := ⟨-446516812384233690154681143863633543,2480415129357530878009403322606932037436916132⟩
def resval0Tail116 : Box := ⟨-113522592150744212288159269581667477233,39686641963298899171885635462991356399513575637⟩
def resval0Tail120 : Box := ⟨-29059607860759149037525336966243120298516,634986244169432185057340077309872722221982362562⟩
def resval0Tail124 : Box := ⟨-7439244813395741729987287116168716190000145,10159772932419460524312324657419213474456726140682⟩
def resval0Tail128 : Box := ⟨-1904446432857343691675277806044175630329163778,162554581500211996340698950769671215456718780293445⟩
def resval0Tail132 : Box := ⟨-487538283392535216741029432463596977828950945184,2600416236869161147795921114100800303348872668203491⟩
def resval0Tail136 : Box := ⟨-124809811461874316683454968245921496682248006573102,41489650598162848380304462624534361235623226090459309⟩
def resval0Tail140 : Box := ⟨-31951443597058886935369149711835431242241609306611920,633879990194922111436634552303228779373098857906372470⟩
def resval0Tail144 : Box := ⟨-8278732324943797304988319134235671940026347616748261002,2421823885193667583838514837116169387813338963804380710⟩
def resval0Tail148 : Box := ⟨48203585004899974718374007552525118920873599,1068776465533812368683822345951389594209213⟩
def resval0Tail152 : Box := ⟨793204286225980881532868244627591253594,37235158814461808610854166961722074781⟩
def resval0Tail156 : Box := ⟨232704704555313036525534202740499335,17404349810462511798160642241802578⟩
def resval0Tail160 : Box := ⟨376510184269532497102688688871168,42072906576886087110180335865939⟩
def resval0Tail164 : Box := ⟨2322853660586527862150728201298,23806508656458819713038717470283⟩
def resval0Tail168 : Box := ⟨44720710009700606278552502258,375368549770398166028054971371313⟩
def resval0Tail172 : Box := ⟨2377833430258274553347535366,6005752314675882479019419310515768⟩
def resval0Tail176 : Box := ⟨323835956826984959087482918,96092026655718837578509706305087876⟩
def resval0Tail180 : Box := ⟨113646715717538360436949990,1537472424560992592418685586753507533⟩
def resval0Tail184 : Box := ⟨1502914833142430313921580306,24599558791094291644928754889465946172⟩
def resval0Tail188 : Box := ⟨362691561750863610493533481883,393592940317607427260775017442772229481⟩
def resval0Tail192 : Box := ⟨92806845997914681351139017371965,6297486958075724360498753409990605386899⟩
def resval0Tail196 : Box := ⟨23758357236915844255153112839314431,100759769055756215395940375329219935411879⟩
def resval0Tail200 : Box := ⟨6082137258911416903524913105127153282,1612150602888570866687492682494154518319801⟩
def resval0Tail204 : Box := ⟨1557027088620863595091443604540241873179,25792949933338497741799054172606006843979221⟩
def resval0Tail208 : Box := ⟨398598942398617811272137754333366110994539,412313512432617028596957052083504662965807240⟩
def resval0Tail212 : Box := ⟨102041374791078047148692337292640276237647593,6501352431970407616500951432059812128581958609⟩
def resval0Tail216 : Box := ⟨26125151125569457583888177915039003316329911242,79530390476997372978274518916658708851420615534⟩
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
def polyval0Tail5 : Box := ⟨1897943134087887601495471125784412259694162255934865,52977784105226019730325869912443710962844836624852⟩
def polyval0Tail9 : Box := ⟨169948101986566245472736996188836893673201593090,9325334772582730617775355356885589842780768066⟩
def polyval0Tail13 : Box := ⟨123575279409004166771536809112399348473053717,10499098968541745907384555221038494846008851⟩
def polyval0Tail17 : Box := ⟨400782911292725062945187253612480262458856,413677028332322568947592785624867905614672⟩
def polyval0Tail21 : Box := ⟨4435761916592009403883579468637696029511,5841657256174113954038413907987636177939217⟩
def polyval0Tail25 : Box := ⟨143240978823233531294322992247507003857,93454644116508992936696229120149219798119456⟩
def polyval0Tail29 : Box := ⟨12252370431662772204085559906650317533,1495273784138112828151233007945597812095179943⟩
def polyval0Tail33 : Box := ⟨2639970144510510789062458906940728650,23924380485388361297719130554522827884649840932⟩
def polyval0Tail37 : Box := ⟨6916381018720183523151308384572681554,382790087746490497557588780449558565744877367858⟩
def polyval0Tail41 : Box := ⟨1425382713370895379264533870235789051560,6124641402609326533448248067427616486637793393116⟩
def polyval0Tail45 : Box := ⟨364471981736362688173118412162073791295231,97994262100060184093692161035367085906094127903008⟩
def polyval0Tail49 : Box := ⟨93303563577486939307175037383721913566066846,1567908106128892311464894172774569328171146305198121⟩
def polyval0Tail53 : Box := ⟨23885703153801325395898859985914325403127298751,25086507305215940112691336021790431105539138010433917⟩
def polyval0Tail57 : Box := ⟨6114739852989560256829631203223674061221271852825,401378384314864669328340410529603433108259595079402874⟩
def polyval0Tail61 : Box := ⟨1565373400462816532538567541947346288041871380970401,6420586611479562504589822952441859150179767828122209283⟩
def polyval0Tail65 : Box := ⟨400735598756029457911689305574105435094950644990079382,102353696164709910210270822251204912901416477554292642067⟩
def polyval0Tail69 : Box := ⟨102588413589370616300272769607087704146776939776802355690,1541482545974498798684678222016250561346979581178433284484⟩
def polyval0Tail73 : Box := ⟨26343750000000000000000000000000000000000000000000000000000,2⟩
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
def resval1 : Box := ⟨106005992016843801410560344335168440465427713667921664882,371591085467432444236913210014316775417031511117031499⟩
def polyval1 : Box := ⟨3712921000056003897724341931689243714791747389073458942651,10940424192753934322338971706590661946177984828638081287⟩
theorem cell1_lo : Holds Q cell1 (1/2:ℝ) := by norm_num [Holds,Q,cell1]
theorem cell1_hi : Holds Q cell1 (3/4:ℝ) := by norm_num [Holds,Q,cell1]
def resval1Tail4 : Box := ⟨48944551631601362735642066469187357723162559305033,3150531568097021859935645307677954358129941282568⟩
def resval1Tail8 : Box := ⟨5301183412684716090895288993158708456256443425,5987732264452239447148504110423785748889170157917⟩
def resval1Tail12 : Box := ⟨-314067469353667332961960981745047602628392627,18923341056880106209912211617945347252260232476200⟩
def resval1Tail16 : Box := ⟨-2087049809522274805132602256643700628888358991,59806021219697204473291005913449562988738460201183⟩
def resval1Tail20 : Box := ⟨-13677793374226177998389489961150415999864122344,189009479252518047918294515441332205365947910114506⟩
def resval1Tail24 : Box := ⟨-89638787924556356750064538175339195801720699031,597316882246549877462133983102347363404118555175114⟩
def resval1Tail28 : Box := ⟨-587456760587235981230007784062621849433896339235,1887512165274313208839974897826572112521330980288814⟩
def resval1Tail32 : Box := ⟨-3849956626188665630173467289630351338208202524455,5963477243879177250397926910631038473294624214036628⟩
def resval1Tail36 : Box := ⟨-25231075745390972194919332831048999980108685748144,18834469706098728749772362781957362422149634523908486⟩
def resval1Tail40 : Box := ⟨-165354378004994740349481456847786184329567853118225,59440613525107284938652943853321635011568201424353320⟩
def resval1Tail44 : Box := ⟨-1083666451693533923793118575483709555695805304209587,187300627168019349776529718581135236076543980689896960⟩
def resval1Tail48 : Box := ⟨-7101916457818742974118578366397590235651551178016176,588285480661273824349097583092941021575451378321070884⟩
def resval1Tail52 : Box := ⟨-46543119697960848061970338114275048240897774495655379,1835175073666084704845392495004957436525778096553614893⟩
def resval1Tail56 : Box := ⟨-305024989252550098119028464266096119458198461613259577,5642133745330105464190083168083302004744939461929954936⟩
def resval1Tail60 : Box := ⟨-1999011769563694033801839900410874170094230261655581657,16796946700226513280639230379587465576981629341403009558⟩
def resval1Tail64 : Box := ⟨-13100723530256748376663808381043290595170605475491394483,46303787186392673823254392926288043333472900213455825855⟩
def resval1Tail68 : Box := ⟨-85856852587683730451753958887501945484246182705343485402,101890691123611588123216807382844985886514752887998223617⟩
def resval1Tail72 : Box := ⟨730962368044446179712676791654897362424805137482313373025,1861421856918764723282767576671462104929194038744352341⟩
def resval1Tail76 : Box := ⟨-22487240612889507573215271285410163561035099634735,445725272478931491478451097934456675475756498216⟩
def resval1Tail80 : Box := ⟨-1097537675844270727089197467246575138473041470,59045955506594334071024475478397612868370965366⟩
def resval1Tail84 : Box := ⟨-3172618924564091508744815335998270921650223,186482845689045188772859490331150312622863609977⟩
def resval1Tail88 : Box := ⟨-17121015214191550547105277642134934607240187,589369002002949730919070371299948584320133950319⟩
def resval1Tail92 : Box := ⟨-112195135142600780318106722780902607873785068,1862639004003418562680067280690953268190560435274⟩
def resval1Tail96 : Box := ⟨-735281955848706170214127430497452911769627647,5886478384417098106904843634751085206437070551067⟩
def resval1Tail100 : Box := ⟨-4818743823652452813792707371746002931836717383,18601683707921853030806439351375667569889268989660⟩
def resval1Tail104 : Box := ⟨-31580119522530454605043901692109385338262447350,58774156024265654305432139013831037342151111700695⟩
def resval1Tail108 : Box := ⟨-206963471302827396721352835888338035064618642954,185648202612768458288852490937926999437517275302304⟩
def resval1Tail112 : Box := ⟨-1356355805530198148657215638513399650588042918245,586037749349065464383062950721107949515761473116047⟩
def resval1Tail116 : Box := ⟨-8889013407122697628090885625948673032670412781045,1847566430044438898279002696423831853094987466351648⟩
def resval1Tail120 : Box := ⟨-58255038264919312703931722086252309835835006343689,5809060931162238329150626636532829280243862265850654⟩
def resval1Tail124 : Box := ⟨-381780218772975705202825874308185642321032793150907,18161835684601745113742508711622064858199555398258981⟩
def resval1Tail128 : Box := ⟨-2502034841750610740990155413068022529009953903756597,56104948754100385388855219377368136610512374366082464⟩
def resval1Tail132 : Box := ⟨-16397335538904663758302381056827968197181067459686321,168829674344284388486981004922476330988557485441618880⟩
def resval1Tail136 : Box := ⟨-107461578195229268376468835395649349131959043820352647,477947243169497506988129975301181633638700099774124968⟩
def resval1Tail140 : Box := ⟨-704260261866387346012169439503235286928952565476124109,1145920752137573718036463944563994245301667808509851149⟩
def resval1Tail144 : Box := ⟨-4656586498749905344174543452862394370922166906679601494,1222798544908981463945532374283240999055626763983471211⟩
def resval1Tail148 : Box := ⟨47502565581764765851511154039151577906159034,824757959147445493896921887838885442930605⟩
def resval1Tail152 : Box := ⟨763436289855654450921727409176541865648,2431716423146129535020419364260156710257⟩
def resval1Tail156 : Box := ⟨312325133094430139314410905440730148,7602602707554862726050008467065892240915⟩
def resval1Tail160 : Box := ⟨611175619552877934472532810480035863,24027655178657640790652861071775129410554⟩
def resval1Tail164 : Box := ⟨4003133036262122991660159830215245422,75937183247018084448200054292086774527858⟩
def resval1Tail168 : Box := ⟨26234919054718056009552878371990756413,239985415855644949803922792131687120775095⟩
def resval1Tail172 : Box := ⟨171933165263338149843592394419678409529,758383407554649015029091415063356970337124⟩
def resval1Tail176 : Box := ⟨1126781191856883986391008609325227421271,2396282690713044793307962937980807395741864⟩
def resval1Tail180 : Box := ⟨7384473218951621116659682422321245311284,7569613363912588640463135326642344999913626⟩
def resval1Tail184 : Box := ⟨48394883687720849757771180169680796927388,23898660008974924661386226137559617128682955⟩
def resval1Tail188 : Box := ⟨317160709735847050600905877797431045766550,75367358457197946013360544385223800792389390⟩
def resval1Tail192 : Box := ⟨2078544427324846985757463487968420360813036,237121911211379486563321417939006608996279186⟩
def resval1Tail196 : Box := ⟨13621948758916120086657422599565133521432313,742369614741186467221130738754131047392645667⟩
def resval1Tail200 : Box := ⟨89272803386432855973379483001772047959821027,2300033866441051986117878554571855196503349188⟩
def resval1Tail204 : Box := ⟨585058244273347415777772170800826030650686399,6966330736909829491902846455231996105084078421⟩
def resval1Tail208 : Box := ⟨3834237709679104357679672689430558809384568731,20031880551844797332259752933201706140310253975⟩
def resval1Tail212 : Box := ⟨25128060278550658017407606189233265553215024866,50300659183439847293152450907894222548606498217⟩
def resval1Tail216 : Box := ⟨164680385748483683582714040412339066543015989129,73712473729517568845485099445420585695416916673⟩
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
def polyval1Tail5 : Box := ⟨1847738588207359787775055085169229799795681745205493,118730939823065612312081433361366093228234676219054⟩
def polyval1Tail9 : Box := ⟨164108344463981898814580055732606164295447162324,265566704610065492121161401587998315072263564607766⟩
def polyval1Tail13 : Box := ⟨15006069227276305533820230879040217721798266195,839297769446274125075295287385395404489119893118756⟩
def polyval1Tail17 : Box := ⟨97590179485783160931814861647788814328972755995,2652544890194827596763221365430224185134239362801405⟩
def polyval1Tail21 : Box := ⟨639564617978181793769087223704744186057267877455,8383020619107177117158609721124912199052581855819228⟩
def polyval1Tail25 : Box := ⟨4191450654784454950556273101264279079884556867577,26492314809007215313072449407882975913326161354380045⟩
def polyval1Tail29 : Box := ⟨27469091010398519092313822312004911804802251758670,83714575383970341916750795152973511912332632791601962⟩
def polyval1Tail33 : Box := ⟨180021434845682926373860338618012396769779723397165,264486193202130451958177005371695683074935525718295754⟩
def polyval1Tail37 : Box := ⟨1179788475404654856048354948887853293011975860905252,835296149142692752661807610729046776230107352920879543⟩
def polyval1Tail41 : Box := ⟨7731861752411940427062086771225849690597561708881259,2635945175657871221253127504468088604508496071213608547⟩
def polyval1Tail45 : Box := ⟨50671529180606888184157823747782800884810062152286106,8304653428560534954067433172374475814196532175394334186⟩
def polyval1Tail49 : Box := ⟨332080933638025304877499328130384750126303242430540923,26074872019222867435506723543307195790913539989661439940⟩
def polyval1Tail53 : Box := ⟨2176325606690162972701820248422335531469270057887000976,81282686194944263716225463904689345531635642985087356749⟩
def polyval1Tail57 : Box := ⟨14262767496004677735474036046777910628988981058904873063,249508924123975751022136756709663423142331733231431570056⟩
def polyval1Tail61 : Box := ⟨93472473061821905885153613727993358717175864775448890353,740176330082811677155206839402889492053239670895132938837⟩
def polyval1Tail65 : Box := ⟨612581199463515431748385133702794967332750799742612570863,2022160696898953148120932012612884416396173852996578277516⟩
def polyval1Tail69 : Box := ⟨4014612196695599068420304742449863286954954660483171013386,4312473339333510947916121132515533422912913450490430485951⟩
def polyval1Tail73 : Box := ⟨26343750000000000000000000000000000000000000000000000000000,2⟩
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
def resval2 : Box := ⟨105904106600442307530695336126171690713873211540919433484,356962163488545002760554540535683554998322775560745298⟩
def polyval2 : Box := ⟨3704286926237814849000008352481218654484842280318930838880,9730539740764331122445958300338782356918153371251869741⟩
theorem cell2_lo : Holds Q cell2 (3/4:ℝ) := by norm_num [Holds,Q,cell2]
theorem cell2_hi : Holds Q cell2 (7/8:ℝ) := by norm_num [Holds,Q,cell2]
def resval2Tail4 : Box := ⟨-146119075196370622076199787206567773294352434574433,33836164313125781864888943623744236353801177245899781⟩
def resval2Tail8 : Box := ⟨-446022785960164396181798492740559922523021571037354,57606944176916209310566722842796123544775499881669643⟩
def resval2Tail12 : Box := ⟨-1023454759430222963983599535619767475107182186535307,98012352546525719886592622113828461553843526461708883⟩
def resval2Tail16 : Box := ⟨-2348416770831073253896467715442983184698726584654670,166602298240285235961347836625959262273469012334077271⟩
def resval2Tail20 : Box := ⟨-5388671317326880009491556818362757978494664430847452,282833789609615967304713769074021242790991814340282640⟩
def resval2Tail24 : Box := ⟨-12364831884469950594901633538021809384623138075241914,479329961933421997858382001668578275994684223402363482⟩
def resval2Tail28 : Box := ⟨-28372312677449077055259806746100172537851167436984380,810437298100595672004509474877015648072434849530970768⟩
def resval2Tail32 : Box := ⟨-65103038536091269549017255616718914178611143578208124,1365869125456774742043434596402063298862429383269038791⟩
def resval2Tail36 : Box := ⟨-149385271296567957990454430422928381859497366356778205,2291790065527579973585295780267815764992607168521706310⟩
def resval2Tail40 : Box := ⟨-342779074251317450263843782137059719818636837227345810,3821758276698999054384725705278371322856096386088975205⟩
def resval2Tail44 : Box := ⟨-786540016460710073773635248201211485191785250768979939,6317976847134665354083543481641798970052037826359780109⟩
def resval2Tail48 : Box := ⟨-1804792777520713396830298932326660204017171155206809305,10315199339633246513376904768434384660793425343874309083⟩
def resval2Tail52 : Box := ⟨-4141273046027711606705994506601128833444561037106337225,16534898429133729288754101469481628309856564731705685984⟩
def resval2Tail56 : Box := ⟨-9502554894593044837746293390060201507983675752057591976,25770080824799394615510710701779205355517285194214187877⟩
def resval2Tail60 : Box := ⟨-21804538971744922387170852472807009331160284739291728001,38369020339636773515223412975118982830011887867434569158⟩
def resval2Tail64 : Box := ⟨-50032641223662649464552520487102070731524734605062130286,52620794400576793565436319657085413463147897627841679710⟩
def resval2Tail68 : Box := ⟨-114804736263878197581279926103274998697687584376247931921,60317453409328304440851955793236616095958502885423248548⟩
def resval2Tail72 : Box := ⟨732251393499925537990359861982949750776686006580462964505,1432827714802723090001960790848391651457858684705833958⟩
def resval2Tail76 : Box := ⟨-24317831070151360668651201951125249115795416147794,389076809797335838838501871536169664824451467928061⟩
def resval2Tail80 : Box := ⟨-4755368740638675952807481050971773975444839059336,662240362999634348578488378550491793258575635173812⟩
def resval2Tail84 : Box := ⟨-10909193852897912351769229183342615541162450282430,1126954220633961625745217364188516214289029203417160⟩
def resval2Tail88 : Box := ⟨-25032208004146300641946240627042273708489297280838,1916112541461909882151278885994635812645909857402153⟩
def resval2Tail92 : Box := ⟨-57438842606080465183381609893655874387590757584216,3254068401795135546441748504063896196896321180338058⟩
def resval2Tail96 : Box := ⟨-131799026260681345517974946800817423073438419649849,5517486135366694907219927439130864996333824160200561⟩
def resval2Tail100 : Box := ⟨-302425719863449896827293672836136007071708814871296,9335005359697454635944112078927214810158806798786722⟩
def resval2Tail104 : Box := ⟨-693945309231856414420620577196181255212472366782013,15747086636574667896518677095624707495894215341959784⟩
def resval2Tail108 : Box := ⟨-1592325191198450395748122347834977981375219602952131,26455349465204516518615162284134037030352948949408278⟩
def resval2Tail112 : Box := ⟨-3653745447651750466380125835331202518924880649568996,44194349259814535446038689818664596169547595137454295⟩
def resval2Tail116 : Box := ⟨-8383875272480134399558511087627235957402118786898464,73242861887778885632329800825648157396326637456997498⟩
def resval2Tail120 : Box := ⟨-19237619476112814281607630412256044287759666221486667,120013990439930895042586883575852851726250345748222802⟩
def resval2Tail124 : Box := ⟨-44142594096373705863501650615705536246953310189034667,193414504702508024411725942772800194413699278509521233⟩
def resval2Tail128 : Box := ⟨-101289487297361722331746275837829851674435340360237244,303972435518223295990024800037042630319514671731467635⟩
def resval2Tail132 : Box := ⟨-232418607174821825857345033343383636609019965949417955,458940341535152625910752801436900636450229837104067846⟩
def resval2Tail136 : Box := ⟨-533307161513306309386919950720084538962009968055876987,646120682688200975216697716518924072960474115964521917⟩
def resval2Tail140 : Box := ⟨-1223725344294174004854817626556093933501055220641487703,788326529842039939313277755152615106288500261923566381⟩
def resval2Tail144 : Box := ⟨-2839795754248225295043008281988202519167264661825774231,620117341592522798512641005449098659493498029191579031⟩
def resval2Tail148 : Box := ⟨47368616873605980364138752184228786471774299,37462067409814449448101913430633410944929737⟩
def resval2Tail152 : Box := ⟨472837693268856493636144831892287489002308,62643861316307927440399480379496502215957703⟩
def resval2Tail156 : Box := ⟨1083252716777213464906354874395334935402965,106589752817088343086744788934726026044915495⟩
def resval2Tail160 : Box := ⟨2485628517920815117663834141169493311126920,181199764974734729939676453901273228055129214⟩
def resval2Tail164 : Box := ⟨5703517052228142843153565321663698271290169,307655654853024999459109051711581029812320011⟩
def resval2Tail168 : Box := ⟨13087276129501584817357569999903975876332521,521489636875041709523401085480939738580692400⟩
def resval2Tail172 : Box := ⟨30030031456287017664379123498565375299616488,881934581482742210559751879811601831395233032⟩
def resval2Tail176 : Box := ⟨68906835948294032911707802961181175102465414,1486864532064310594694033747616686083279057433⟩
def resval2Tail180 : Box := ⟨158113455435993057916395267496511343300483723,2495963813776680225585132352769392420573509572⟩
def resval2Tail184 : Box := ⟨362806744002424321284859679877420088612250056,4164931904350391076030693637896140396743171857⟩
def resval2Tail188 : Box := ⟨832495457965158093867039489310218032415536071,6891626784289374129080871351013113663113901411⟩
def resval2Tail192 : Box := ⟨1910242019999460832828476925951608853482528787,11266769518640507507647217412685807451275003387⟩
def resval2Tail196 : Box := ⟨4383236617159226402017860381694826941963826874,18096163325476887854514351019241778413812575437⟩
def resval2Tail200 : Box := ⟨10057763906801129731548388028909838576620650318,28291099968683053646969166073706101985803997183⟩
def resval2Tail204 : Box := ⟨23078520198736716385446481748571151012051403744,42342948536783170593750719458828423411222864749⟩
def resval2Tail208 : Box := ⟨52955915400183021805100466822668887063392776989,58650222017852771481873899705606060520077008945⟩
def resval2Tail212 : Box := ⟨121512512594892669452599931359109430607614805745,68882630638194570280346312947345496359739255352⟩
def resval2Tail216 : Box := ⟨278823194052926045510859236854255098901136637232,45983257042397761578727972611275798268813559049⟩
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
def polyval2Tail5 : Box := ⟨21243316619185838249614660208778867203778046002040984,2978755563962273887182432921310421313373385478909006434⟩
def polyval2Tail9 : Box := ⟨44560111607483226893063422508743004649933480772756199,5070179461583268125576587730649433562181648957803904812⟩
def polyval2Tail13 : Box := ⟨102247159302940539362538330087694092558100537785818945,8623272472861398541179822931101053023239637460775173119⟩
def polyval2Tail17 : Box := ⟨234616078736654253512030287547338321543797321406313933,14650735196932276117535571289293710246367043951180626415⟩
def polyval2Tail21 : Box := ⟨538349474320319782227285254736508529459668546462532490,24855402639439978095830388227797061211233530700521809477⟩
def polyval2Tail25 : Box := ⟨1235295373028123568483378597265565557758946807563782519,42085324642782857030888063658706285903524786980648267249⟩
def polyval2Tail29 : Box := ⟨2834505709420927100152845461596496103481776377895515199,71068559507056280750453844103254009330857180314240841082⟩
def polyval2Tail33 : Box := ⟨6504049794216234651183810370249268849631382968098805274,119571316772502067438481079465538504020641715691668550613⟩
def polyval2Tail37 : Box := ⟨14924176580433288540350668497851627357844906034570402346,200154832772868737845343570520107446348294764119822776101⟩
def polyval2Tail41 : Box := ⟨34244978690356640094891386650315737753610243868067024041,332670315899866225408326896858482888300888517879402957944⟩
def polyval2Tail45 : Box := ⟨78578443452652665007399450533691911909626068126614317850,547362850442204834826518216807018471957194484991174128203⟩
def polyval2Tail49 : Box := ⟨180305902108226079421672067457685041840964207218878997062,887522311050181383861872451711464341981568546821236373370⟩
def polyval2Tail53 : Box := ⟨413729477278971476900931132617977945921388605773006420052,1407938311599344629001884204298665748341214372835528199000⟩
def polyval2Tail57 : Box := ⟨949342635865504547212507559523129169254607027825624868279,2158342188476679048154947461537086337283077327097463607540⟩
def polyval2Tail61 : Box := ⟨2178359265574799242341719632392317190904616682947293752699,3123213845839441887749084252763397989160324761827329506359⟩
def polyval2Tail65 : Box := ⟨4998457786101271327035843401837866817696847802919164129277,4045791886685700882583328382116934276926945322323464997014⟩
def polyval2Tail69 : Box := ⟨11469448918116296090944206582171567448764023923134505699830,3959641767431742886627577078465335587121108130350848408580⟩
def polyval2Tail73 : Box := ⟨26343750000000000000000000000000000000000000000000000000000,2⟩
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
def resval3 : Box := ⟨105720063373038717840610136560432469107756587803294962209,1917741429997316188962381757160245869240071057850562600⟩
def polyval3 : Box := ⟨3721966064132829790697857855886947828159921577329373975330,235506134608639290307058038466223170983375410196615738875⟩
theorem cell3_lo : Holds Q cell3 (7/8:ℝ) := by norm_num [Holds,Q,cell3]
theorem cell3_hi : Holds Q cell3 (15/16:ℝ) := by norm_num [Holds,Q,cell3]
def resval3Tail4 : Box := ⟨-198057135637631944942262289939339954134027085333644593,2044536102862158356426469712835880271495676261048445750⟩
def resval3Tail8 : Box := ⟨-293699694654196422140403332147084782984286801203913649,2609484019833366385280786717738035694357460971155695895⟩
def resval3Tail12 : Box := ⟨-435423058769363737045443098711039782570864416888520078,3322859375609593226605156215326513097313314345203185819⟩
def resval3Tail16 : Box := ⟨-645534333986788114653965849793358660599428999936303950,4219706112822492490900559188324763540189639732008364741⟩
def resval3Tail20 : Box := ⟨-957033781190991630277861301742074250480586044751400768,5341206177763949884346031467313873810004998920889777912⟩
def resval3Tail24 : Box := ⟨-1418845768720106185052722111434207535254274075578643477,6734466901898581369251649573382464487595506883187114363⟩
def resval3Tail28 : Box := ⟨-2103502880441372056177322906053314346612117501071934245,8451272412035987111964860413800846730512823678965708744⟩
def resval3Tail32 : Box := ⟨-3118537945118972721866198011178113660807718193886788946,10545022619183174645391677758960746949181336125731034443⟩
def resval3Tail36 : Box := ⟨-4623373234034382290619578802732084342808392506834376194,13064628842846714595563369386177373839779712096825943609⟩
def resval3Tail40 : Box := ⟨-6854359458618054839271736726283785403546377506757729552,16043436178132158800830938139299200418713674288921307295⟩
def resval3Tail44 : Box := ⟨-10161897214374322894301657537453016832036209694075441773,19480175572787395645966014913673737705915685947347701561⟩
def resval3Tail48 : Box := ⟨-15065471196681050390782951061400442226234508129220716891,23307326475999056001082904514547611450416221451804491863⟩
def resval3Tail52 : Box := ⟨-22335240909244033202420647103148065912603760207022927595,27339814266593269482528177731767376273494483580268753318⟩
def resval3Tail56 : Box := ⟨-33113002571328040476798868347149053459709732213290144863,31193257497880318511977711309848482333148879450473364266⟩
def resval3Tail60 : Box := ⟨-49091520603878644738946658670025616058873241048255600265,34155394159490440530949779365062892387635239651649802309⟩
def resval3Tail64 : Box := ⟨-72780394648388839999648631835690501777744496176063817841,34985922503627298127381031566626428787580156158506020842⟩
def resval3Tail68 : Box := ⟨-107900184553829324563509996088000271547920694793159180323,31607400362407859345242909412186971246523485587392533657⟩
def resval3Tail72 : Box := ⟨732893952975624946954889831598593613782998512615865135916,1237821357573011120202126079585836655594098271636799801⟩
def resval3Tail76 : Box := ⟨-2376803014075351333949441906043335277093352247571898,25241800378855831695410042320465964744206309388216977⟩
def resval3Tail80 : Box := ⟨-3490913617335548093098194077594979999891612027978760,32233509800072784227237890552827058520548729917804896⟩
def resval3Tail84 : Box := ⟨-5175435397481128496964091626084612386192173963282150,41071196547512135939207830969475289804539164855161985⟩
def resval3Tail88 : Box := ⟨-7672816528069656113595906682607780326570157936885077,52195218456841154618479860565853845876859736041111640⟩
def resval3Tail92 : Box := ⟨-11375296754381638413711642872402632102687858353653799,66126165779367018236626219697037171294743290424505385⟩
def resval3Tail96 : Box := ⟨-16864390771874925185081838007665337173930530639715896,83464218583418925092289988800469097843208948601939975⟩
def resval3Tail100 : Box := ⟨-25002220359389720979010233586426549841607790056337577,104877004187939419776930834174972077312126225401463054⟩
def resval3Tail104 : Box := ⟨-37066919959064977066976855787901672236842459351663001,131066706903824160061239408050842423455716788755497331⟩
def resval3Tail108 : Box := ⟨-54953381559799453668368777475433110553386379652189445,162702033157954669602684247190059590499945222459100871⟩
def resval3Tail112 : Box := ⟨-81470868046007558423383112940243600350528800198238771,200292396328169907702511927443961886754334564840328634⟩
def resval3Tail116 : Box := ⟨-120784238417560236430714635266109310053919371274651504,243969090847152739768070556266471079104907474889759773⟩
def resval3Tail120 : Box := ⟨-179068084089536750590519857889281153991515272150825814,293119060338951735514324745717383603526177260471851747⟩
def resval3Tail124 : Box := ⟨-265476515475843530625563864098567897819013918802005042,345787814346683312765624547868433432130999538427085705⟩
def resval3Tail128 : Box := ⟨-393580914363029868424861959481070422668240583342455308,397724154659174980484693472573292196797587173596141206⟩
def resval3Tail132 : Box := ⟨-583501466685988603342438046940911635626511765751659566,440873229678247792032647904859237909277370828130521837⟩
def resval3Tail136 : Box := ⟨-865067256063179471899309791466820861574452047986755581,461024992848651163879933865029671311591529323343774290⟩
def resval3Tail140 : Box := ⟨-1282501290077450477966828292831836273109734938649963546,434175916947655517699691094003242517835083302875430706⟩
def resval3Tail144 : Box := ⟨-1929969772238596348148732961620602904080816670232378721,317983800836388634581066838727290763352769241091769643⟩
def resval3Tail148 : Box := ⟨476894543340064689320509620210051166134821671,4202883796387693886294543537330989603460572316⟩
def resval3Tail152 : Box := ⟨637345300109754233037213667323965263245061386,5359289867755133069901141750573631743464667862⟩
def resval3Tail156 : Box := ⟨944892068067718989405317158339686073749240286,6817980679432448137385244863945069852700235708⟩
def resval3Tail160 : Box := ⟨1400845130784233626558183337595244998513351149,8648490738174614897180408613376416308613920919⟩
def resval3Tail164 : Box := ⟨2076816122385398774229282590798483556469757028,10932433764193660887404258372549231401411815915⟩
def resval3Tail168 : Box := ⟨3078973622006514952210956154636637997516870059,13761998241042277569110102993154533722563175636⟩
def resval3Tail172 : Box := ⟨4564717339599258832690978707104394682093311428,17236565268139322189065769480304882594796015525⟩
def resval3Tail176 : Box := ⟨6767399448150922233197484889591446714589307978,21455195257641781879778165115665883890496081580⟩
def resval3Tail180 : Box := ⟨10032975074608679480156049479445186525267385519,26502253896034889047906557743402513875897916304⟩
def resval3Tail184 : Box := ⟨14874338306603557418545314790980357652621403164,32421913857744035807161900469317260406003847341⟩
def resval3Tail188 : Box := ⟨22051877774442027742469832595301839318810786531,39174930755783826472625740279524710563483620958⟩
def resval3Tail192 : Box := ⟨32692903936643743692114222699334965469052834344,46567542953961324591326408749270411473006680208⟩
def resval3Tail196 : Box := ⟨48468705420151467647101281073698734469947841173,54136976504247421344236630435795616233985022663⟩
def resval3Tail200 : Box := ⟨71857043034721341944925251693664385922381725666,60969939100536052526558807571274291840168250315⟩
def resval3Tail204 : Box := ⟨106531308994835118951440363975946995649019405487,65418302881041015069533464962968524925127453376⟩
def resval3Tail208 : Box := ⟨157937473027796832649624567609854522277082084743,64657880333145562804259018240613846338513476958⟩
def resval3Tail212 : Box := ⟨234149431032514586621860602706990887432893805128,54008772989720780582667106030133384496627636337⟩
def resval3Tail216 : Box := ⟨347137894043599662851320441022904948245196086541,25894625068743798159465514375857310936807064966⟩
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
def polyval3Tail5 : Box := ⟨32597339088308205932879872787295677184210727958338874540,294277512816659753219100720402100493466896517569864499833⟩
def polyval3Tail9 : Box := ⟨48324339826606869072137056077956894522864021391810613071,374825303724449202989192460878249774030624990775462171485⟩
def polyval3Tail13 : Box := ⟨71643014295904221752321778527597393198526784989842025583,476140393691440244738843678578886725835182461307068555047⟩
def polyval3Tail17 : Box := ⟨106214001730892760212262127122392230931360735706821647297,602912584458761755187702752952983785565836663783322593748⟩
def polyval3Tail21 : Box := ⟨157467050689856297585554913259366617837863858757669825539,760524454545208892187388163133896898627604590761816511341⟩
def polyval3Tail25 : Box := ⟨233452008670057238050164132908926664281065723958543830220,954923127864959690951681483501283147412950661189757310355⟩
def polyval3Tail29 : Box := ⟨346103137852160510935780588947744089793605537030112450119,1192293957416162836254542521187777322879317583110672174718⟩
def polyval3Tail33 : Box := ⟨513113520476963271891615085930106727545457423240925280622,1478400396273749594891061429680627254658123894971733107539⟩
def polyval3Tail37 : Box := ⟨760713949402927888329712841394703068889434011516253227306,1817377034264720870926875112155182493420211576096750476469⟩
def polyval3Tail41 : Box := ⟨1127792758760838356230433684743182385913390222906062245715,2209644687276554810912464920105768458778993311310953940710⟩
def polyval3Tail45 : Box := ⟨1672003658815102965050223717967225708753250131099860765050,2648436844167743427086185870276957859986770874280475616611⟩
def polyval3Tail49 : Box := ⟨2478820876774161057192715399727295823612726075119520906689,3114154704529223064399889228877093318043007171135930478353⟩
def polyval3Tail53 : Box := ⟨3674963811673638490171789167635196085520538093309151126550,3565357130475469298604263701536553200919439105621240335201⟩
def polyval3Tail57 : Box := ⟨5448299691055601902007653677000623311466250109675247145757,3924572867259142372958207115264903385239671084781592486769⟩
def polyval3Tail61 : Box := ⟨8077350157643598376401135335009138394880737217079846543162,4056192083970530238639596990345917286650272888493619635148⟩
def polyval3Tail65 : Box := ⟨11975036115637480509952871862192806404923786347809523843379,3732298686270646601627024152919726895302839277537332307396⟩
def polyval3Tail69 : Box := ⟨17753531473630364181474518754813257186770008011008572519393,2580214602206965828132439541167219214740883125190313408007⟩
def polyval3Tail73 : Box := ⟨26343750000000000000000000000000000000000000000000000000000,2⟩
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
def resval4 : Box := ⟨102175193505863422556731425076201452682324787878514461395,9600846484778728207982790571280365029867336060214266955⟩
def polyval4 : Box := ⟨4527880539775547316169816239197168318946469591237381856085,1850892521715702804903277642981494642420197722181415018296⟩
theorem cell4_lo : Holds Q cell4 (15/16:ℝ) := by norm_num [Holds,Q,cell4]
theorem cell4_hi : Holds Q cell4 (31/32:ℝ) := by norm_num [Holds,Q,cell4]
def resval4Tail4 : Box := ⟨-4426761436140365790320876115445752332256498600445882958,10269198809651189408820743870651617170593842838189899849⟩
def resval4Tail8 : Box := ⟨-5364031993420743995199633411379054933238741986467032195,11321977804185424158944624103710758816448300420964890854⟩
def resval4Tail12 : Box := ⟨-6499679107288412377858208283293231827622884330894523669,12445801736955363871520981974738240265083831537255895283⟩
def resval4Tail16 : Box := ⟨-7875759971079698003055115846509245777405816977567986784,13635149387492443782735875235336503047110337025386254071⟩
def resval4Tail20 : Box := ⟨-9543178070509266298683788589652912371570334601042408340,14880547314808616468447485761953985210485843267049749353⟩
def resval4Tail24 : Box := ⟨-11563613926766687091647525577425824233249819461176453808,16167355124976678141197767297285746930728911564005547835⟩
def resval4Tail28 : Box := ⟨-14011806764932003121852208356625485392845450318827260760,17474243475832257731448516091162558435320295894766940240⟩
def resval4Tail32 : Box := ⟨-16978319240089889931262486242144470844202100744610928444,18771291886521876979149983828084989957742052245615528158⟩
def resval4Tail36 : Box := ⟨-20572887497981808601890529401869012609476937809828063448,20017618009416572268582189377351511748547827781846845058⟩
def resval4Tail40 : Box := ⟨-24928480494419975426874867938374677858530530765266983288,21158430255769532575195930653855626678852440298543737164⟩
def resval4Tail44 : Box := ⟨-30206218734323954929739472511787678929148108480130670182,22121371571463042379981517095679962480057435531264917852⟩
def resval4Tail48 : Box := ⟨-36601334382577382319763143476379993781174141395627454808,22811992799458441974474062389882144081592813961771446378⟩
def resval4Tail52 : Box := ⟨-44350393220948252907988839688543452024071815420206761842,23108158304388362526372227050910354251770141456623920849⟩
def resval4Tail56 : Box := ⟨-53740045603064811770532886634117822526171446810112707398,22853142991706028985688175950288247483281372348704980434⟩
def resval4Tail60 : Box := ⟨-65117630119575270700824762276044958018856394391031301543,21847126852869348449552010262286847036884677086711349768⟩
def resval4Tail64 : Box := ⟨-78904022218478021230055832816233170641554785471100431299,19836728674210489471021608105388838817878991525169889682⟩
def resval4Tail68 : Box := ⟨-95609169816111803474735343502331769407907962836930851445,16502139468711161014657365807309089146696461622941534147⟩
def resval4Tail72 : Box := ⟨733171878178107413463386185856199316642546173788838585183,1228274789386029469930363789068323347373364461190261599⟩
def resval4Tail76 : Box := ⟨-55331923570581513045210772506874349205227188223306957,131325646811537487758220685917044583836034753794940118⟩
def resval4Tail80 : Box := ⟨-67019792501860544315911748657059843172298441998765821,144887968221524477676321203595448887598761572467052736⟩
def resval4Tail84 : Box := ⟨-81208900012020761972889928226891209613370455488852038,159393523731639525336055629136052534633868688790396136⟩
def resval4Tail88 : Box := ⟨-98402058539831107091610113456722735580472867719915455,174780605502307219093759695028741432339506053222697528⟩
def resval4Tail92 : Box := ⟨-119235270068995407783152186163680362860810514109982573,190939360643947579564521062634868939044918033707721538⟩
def resval4Tail96 : Box := ⟨-144479189148992153802399414459955025190972037641981378,207696531353795431262142806137809845394069673301446338⟩
def resval4Tail100 : Box := ⟨-175067629612206116036056000286556420988839622428526196,224796594700972462973105546792842510737401154964137133⟩
def resval4Tail104 : Box := ⟨-212132107873546882774949731663426352493154240469384042,241878173293221974284302941347183073268847152510023461⟩
def resval4Tail108 : Box := ⟨-257043699572297322957843522156414360206547566682411631,258444615890724980872984001885092419589224161527519627⟩
def resval4Tail112 : Box := ⟨-311463757901274455158210298376159220820801196531679887,273827400475150201412455822497876105183994904801622607⟩
def resval4Tail116 : Box := ⟨-377405369777205170094685905878541531238609173823496649,287140711671638830950513233351893037347793001534872564⟩
def resval4Tail120 : Box := ⟨-457307823216519893256836923686694010852327464480536723,297225178091845641752139866590120787463932674599421094⟩
def resval4Tail124 : Box := ⟨-554126840586524792903624690961669754056712822426831150,302578308922712895926866652985944092819113012785009382⟩
def resval4Tail128 : Box := ⟨-671443915607415509430758900341934971646511134112767470,301268625690290164381076627583733090515516856971478381⟩
def resval4Tail132 : Box := ⟨-813598798659573089977552690843132827551404558527177315,290829823649814022650077966155182005668087529351906744⟩
def resval4Tail136 : Box := ⟨-985850031249469910910661599604464987342216757124658332,268130492280433821790419199655435499393547873357749842⟩
def resval4Tail140 : Box := ⟨-1194569511028527681361139335478496801094271811975261855,229213940051341556120695689629796947268569101016339657⟩
def resval4Tail144 : Box := ⟨-1474698973236383625164980781867047114663123637740417229,166718717213676039752776550051744351688548224090279211⟩
def resval4Tail148 : Box := ⟨14724162079666921740422831467231023520340417100,31318953365953498751137176594337416662215077385⟩
def resval4Tail152 : Box := ⟨17784647008678448254451044797216146026106155537,34439324238974763828570743090528569976389534783⟩
def resval4Tail156 : Box := ⟨21549926215893656141655971084681233056131464200,37745749881290333187638326408775349160195326859⟩
def resval4Tail160 : Box := ⟨26112373159898043966128476894767828942293640649,41212596016824211314203055296869053771059093432⟩
def resval4Tail164 : Box := ⟨31640759472552560417517242486826099858021120872,44800758240039099598370274076890732165166081702⟩
def resval4Tail168 : Box := ⟨38339589200472571213979849560950833658928776194,48452958967894483123165837471000057486170617538⟩
def resval4Tail172 : Box := ⟨46456663005706596570594458344839629144495443056,52088560100420554116684649786960952526640984158⟩
def resval4Tail176 : Box := ⟨56292244717092215869233553977023160492755635184,55597096038267308339898069691623714141400477027⟩
def resval4Tail180 : Box := ⟨68210168580118390609419172964012443438118256548,58830231553600137130487077418165824295081782038⟩
def resval4Tail184 : Box := ⟨82651298080417039660222853139052536867060669774,61591783138758310920160581465481529552272709225⟩
def resval4Tail188 : Box := ⟨100149834204765318658547316840156089139261733726,63625362171362579256251655243528866903990745997⟩
def resval4Tail192 : Box := ⟨121353076408831791470645390880427718322707043417,64599100439658591188854226386291480799830917404⟩
def resval4Tail196 : Box := ⟨147045367282166195121866300080450602497720529039,64086799491607927492110150818465912751785489580⟩
def resval4Tail200 : Box := ⟨178177106662732527811274933958920235641984401223,61544700320516336595512773487976897679175365356⟩
def resval4Tail204 : Box := ⟨215899908480510717569648468918592726262128719425,56282893512369978622668217409678176688136347797⟩
def resval4Tail208 : Box := ⟨261609200839288341504610801860522612010120044070,47430175398492975799907558564975001180609506341⟩
def resval4Tail212 : Box := ⟨316995845200181462273412094204647427843587614855,33890894778054046012559241400531762369711852374⟩
def resval4Tail216 : Box := ⟨384109442759825346133673887050324747830826182880,14291933292924666067639150235597211096558309330⟩
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
def polyval4Tail5 : Box := ⟨1005779176152383766033665806564408803434918053450284078537,2033286893684163063709643331025126805303882272486150870732⟩
def polyval4Tail9 : Box := ⟨1218715727226163273191295561777566093439919200122907093399,2231871572676332904490424027228284222042936070454427142822⟩
def polyval4Tail13 : Box := ⟨1476736371280349339544381009998361945551816587414693488928,2441098770981411765053451713206161894377463811488063275946⟩
def polyval4Tail17 : Box := ⟨1789383907848197950198942091838382561423470469571840138763,2658969624049995453672312612647285633330702676149089679202⟩
def polyval4Tail21 : Box := ⟨2168223680229558219749294269405010601061207671053057906134,2882486323185285275793687215595686432901052090154292746514⟩
def polyval4Tail25 : Box := ⟨2627269590884817164877499938990727120451064133665758452973,3107362640045202758092609973193850257270980759586335332755⟩
def polyval4Tail29 : Box := ⟨3183502498440232608040113216364954140811290660341239362882,3327662625232836624418293606842954701029651501115678592305⟩
def polyval4Tail33 : Box := ⟨3857498367406605749351564433726210405288461698495870800794,3535350826840858296929006596956259761678994404239048617263⟩
def polyval4Tail37 : Box := ⟨4674189406741561201207999586096019920227930550368252921328,3719733673196229991186233163723522702995415602593734636556⟩
def polyval4Tail41 : Box := ⟨5663786353014961564984425054464769466400093637426300873635,3866767134635941162030534186063301665606384813060718271878⟩
def polyval4Tail45 : Box := ⟨6862896014939378648611133469582797473164278183535421397485,3958200261016482645158198671346291955814692350361653232553⟩
def polyval4Tail49 : Box := ⟨8315875419064626156964528662062744248061807875834515537069,3970517471467038214485985426146996275850850533697473786199⟩
def polyval4Tail53 : Box := ⟨10076472648699183458747042423674890802318340129574478201903,3873634291567611232672949722129757105601463658845835834285⟩
def polyval4Tail57 : Box := ⟨12209815073372453157776687713411636722783682508082185830860,3629291276128201971957070328661865636361662784241046517461⟩
def polyval4Tail61 : Box := ⟨14794818516695775512974437660794825863659238555461386880877,3189078741226894540868908928972516098915943071575904452519⟩
def polyval4Tail65 : Box := ⟨17927106481683488037074712121857128118708432030429345796078,2492010193656474801282585195188825486447720100024813114536⟩
def polyval4Tail69 : Box := ⟨21722547453103786399849739659261281290610887963579438534128,1461544423235117488671691222081399460199611376163378818203⟩
def polyval4Tail73 : Box := ⟨26343750000000000000000000000000000000000000000000000000000,2⟩
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
def resval5 : Box := ⟨88497549613105880235066621606388491361251736108897817327,15835039525484517855991196747127536245042654243930635539⟩
def polyval5 : Box := ⟨8469014646949103367047649070572181003915086922739280883371,3702943201140787853330175328641033978681750536095387856427⟩
theorem cell5_lo : Holds Q cell5 (31/32:ℝ) := by norm_num [Holds,Q,cell5]
theorem cell5_hi : Holds Q cell5 (63/64:ℝ) := by norm_num [Holds,Q,cell5]
def resval5Tail4 : Box := ⟨-19041770503014726866825548533079790995805113746832861140,15940538479306361385766836174697123110995229594849106311⟩
def resval5Tail8 : Box := ⟨-20936700505585970581096693263437224709976453980825973445,16320202557666384151711538635618061440826851152938725782⟩
def resval5Tail12 : Box := ⟨-23020145658775166142505574999111843897656307914791158277,16659195276978037389123773633793182212203172500251692179⟩
def resval5Tail16 : Box := ⟨-25310917824925019721979607944567445358083871576242163416,16948367500344284175101097549974074046182506211633666232⟩
def resval5Tail20 : Box := ⟨-27829648458187897682168349069113200244891295995412496331,17177328827395022048015532848299255862713669349483101160⟩
def resval5Tail24 : Box := ⟨-30599022076696024242282293056531551254678058308891116011,17334301660175941149339180194748442008889842917116366071⟩
def resval5Tail28 : Box := ⟨-33643980571901805536749305067414946641296070950767737120,17405960193610667185060452768878425803847194151966490935⟩
def resval5Tail32 : Box := ⟨-36991947843475873614237337868923376094272099148960697043,17377251890479419333766057682679799705015023738938857262⟩
def resval5Tail36 : Box := ⟨-40673076787985050659444302360675723843880744351375626914,17231199600670420786988585372913459002183708392145636001⟩
def resval5Tail40 : Box := ⟨-44720520865815684689699880936410104711802085783116992818,16948682295175623169033652542522371912996666928958723912⟩
def resval5Tail44 : Box := ⟨-49170732692163576346936758944158254936966520884775273375,16508192176617216423589858832958375434336272922528284180⟩
def resval5Tail48 : Box := ⟨-54063792341299352545962852864902925769908708293917294513,15885565698202365062020577502290690412951777884508462655⟩
def resval5Tail52 : Box := ⟨-59443768320925693204387357804847690657968577747363566012,15053685769772356987943071152041273387430864635003061012⟩
def resval5Tail56 : Box := ⟨-65359114467680426512990258615849403104669326982967486107,13982152150685777189132675576988568382814881201572522942⟩
def resval5Tail60 : Box := ⟨-71863106338355912614646699748055172714572138224475696873,12636916722064016245762435564439610727650421639822176179⟩
def resval5Tail64 : Box := ⟨-79014321025237295259729035905607647500770970694713314592,10979879992368432881218743341862418935366873545456552904⟩
def resval5Tail68 : Box := ⟨-86877132211020311506955050461401270666278186317641068953,8968441987568443422249720764268396777709115490256762264⟩
def resval5Tail72 : Box := ⟨733157232597864400946545528717441444284430725271557966653,1255341830149314045786957118524038458872912374312531819⟩
def resval5Tail76 : Box := ⟨-243300437185134755860397712768006019761767215067148751,206883745036247020260233361439574644742118441477141780⟩
def resval5Tail80 : Box := ⟨-267487427634957274964023226770248293456889318523048229,211943930265992138417034613287642109141784226482995189⟩
def resval5Tail84 : Box := ⟨-294105535809791505858422531748437293918248288133013072,216498371012914408158846471912833514002493053534460931⟩
def resval5Tail88 : Box := ⟨-323372456415576797721540415439491331426433211024582782,220430834610108462465398918470757451443575847297392282⟩
def resval5Tail92 : Box := ⟨-355551775931413049032160504537694600941457824100092866,223609517938911429233250493541009986184331886263349504⟩
def resval5Tail96 : Box := ⟨-390933311912995567883397181543090154104135005810211097,225884956481238986623950738973288276064449975291499652⟩
def resval5Tail100 : Box := ⟨-429835722133320489022458968004265251278613044918190575,227087971234297590547902908519302757813784606600542035⟩
def resval5Tail104 : Box := ⟨-472609374519079642153171801597611766206307187418056771,227027392127285820574466526648634679901817746348477173⟩
def resval5Tail108 : Box := ⟨-519639502679670474510648407508705868570476476256471128,225487534425777128836132879196714908311562087455755639⟩
def resval5Tail112 : Box := ⟨-571349675448035597332447951703812424573273216669829406,222225402212482270896776589150248460148429519058817348⟩
def resval5Tail116 : Box := ⟨-628205611681158921727461365177697227991395082729969350,216967590368111875499879615011604137988690826963736326⟩
def resval5Tail120 : Box := ⟨-690719374677568805965982242022968170912619537527424030,209406853540241090717658707771054388883473638380313996⟩
def resval5Tail124 : Box := ⟨-759453983988154513547743307954955479521833948733566573,199198307354120230243318137996815575838546581806319421⟩
def resval5Tail128 : Box := ⟨-835028486155784039672578256602019794858456199214429757,185955223557219991350616138609263879185045133429481264⟩
def resval5Tail132 : Box := ⟨-918123530052480925245543142987117628948111434986439980,169244376865871889492487315551194918644822983650104327⟩
def resval5Tail136 : Box := ⟨-1009487497032615626366267176802060023169509120335668064,148580896960574155298855208768237297984027490464339634⟩
def resval5Tail140 : Box := ⟨-1109943283120568945529443252617450799740111313582775079,123422569726972654279883159512223639010427186743482117⟩
def resval5Tail144 : Box := ⟨-1246974051566647421187817372800810282792909638651239085,91036596890766416110329339172661512604809276900142008⟩
def resval5Tail148 : Box := ⟨80441956230850424303128206593046291138209029380,60593628571841177288917474715118449036262627645⟩
def resval5Tail152 : Box := ⟨88395331461676088966321303855324892375018844234,61759841195371368451038700242499308951494387160⟩
def resval5Tail156 : Box := ⟨97191693972329004925992128395420424468280890672,62726543149070888432653349540721438553579519447⟩
def resval5Tail160 : Box := ⟨106863397645594100894193358269299868475957592718,63452697628262712203534832094393698841222239729⟩
def resval5Tail164 : Box := ⟨117497548294980783352087705731623252033153212630,63892472202503421277847708881342083689124516611⟩
def resval5Tail168 : Box := ⟨129189920585503492459181556721401366005214904105,63994049979187166276842121721539679133186070145⟩
def resval5Tail172 : Box := ⟨142045819875219115945739486835923386272981576918,63698941500211011392229794847585039184174824047⟩
def resval5Tail176 : Box := ⟨156181030629778663376461201965565327225662095852,62941222162191578867276177721218057276526353380⟩
def resval5Tail180 : Box := ⟨171722859215481252587468085864258473286515004303,61646687341352590884366924347803422153831649896⟩
def resval5Tail184 : Box := ⟨188811280462362674371633730196972107813772311085,59731916616971024736511839728409597398403421579⟩
def resval5Tail188 : Box := ⟨207600198323643250001257968662859575565406078560,57103237603770688623765580811339781560444532910⟩
def resval5Tail192 : Box := ⟨228258831985449416275924379670583078114657332940,53655578930465627868848222125326524414282791273⟩
def resval5Tail196 : Box := ⟨250973239910569981640930352055841689164087554830,49271200829749538817355086932863805844731127844⟩
def resval5Tail200 : Box := ⟨275947995542287369334778654077647077585969548907,43818290624455537325212743164664272483149249725⟩
def resval5Tail204 : Box := ⟨303408029760224793259415590263075757390117107126,37149409094429767705840011912023493528264188330⟩
def resval5Tail208 : Box := ⟨333600656681980384894672706817273071502049242152,29099772276830554044815404376883311027746144626⟩
def resval5Tail212 : Box := ⟨366797801072098655087863971042979859281319725020,19485351673743603785783372721222228528409470461⟩
def resval5Tail216 : Box := ⟨403299188643319877117634532606829855929835147768,8100697222583482996711664245083905536676391266⟩
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
def polyval5Tail5 : Box := ⟨5247144981511589602317211277150874760028772518433010872661,3774124554972647569692026463789436346248994882928233402119⟩
def polyval5Tail9 : Box := ⟨5769294937017871916983236322109346803530520751311840405114,3838534161799754323764271827694749499285220300864660433338⟩
def polyval5Tail13 : Box := ⟨6343406867150077453432909177379647030989558531946167914845,3889121739967030081668920846121281036699174680626791062024⟩
def polyval5Tail17 : Box := ⟨6974649610145519705810977457216050887902463292821852693768,3923196367368230516888017447582175100773771993484106928559⟩
def polyval5Tail21 : Box := ⟨7668708346018343810526795364711582345032725747622304818320,3937713830706357317608513654204942204571529112518284690212⟩
def polyval5Tail25 : Box := ⟨8431833996470025847678770016014584193477325602616677335526,3929235890397622926419107446987292710542549840686538168851⟩
def polyval5Tail29 : Box := ⟨9270899522595773557663112803387312949723162089738909955005,3893885147605219569488317687596467381441524319064124509096⟩
def polyval5Tail33 : Box := ⟨10193461825037020277236131413836571340733658775327484489431,3827295034924153060816911785535623989483494094757114874464⟩
def polyval5Tail37 : Box := ⟨11207829803918969876483523994674253050388818467818490878017,3724554420421479941549568323025879760287002505633347204567⟩
def polyval5Tail41 : Box := ⟨12323139191543313472897565991146870699107811764047071823222,3580146262331179337330073270760487054658786284200743983120⟩
def polyval5Tail45 : Box := ⟨13549434831804009250195976527572066215469906626076364914990,3387879693973741533777244535242999664872134886406364998348⟩
def polyval5Tail49 : Box := ⟨14897761147361658985302954416729902893213587160288759093359,3140814854883943787221937389507734658311738783207652489311⟩
def polyval5Tail53 : Box := ⟨16380261609353667079059429310559477339036914274229143922741,2831179714095998210483411367455800891651717342444383025985⟩
def polyval5Tail57 : Box := ⟨18010288105497171938086379582356591832644594634409895711422,2450278054403871424893888619993859534947909084084133754906⟩
def polyval5Tail61 : Box := ⟨19802521191589930844664879764334914445815634129044003815896,1988387701471532165870139951237235272827699849011374881219⟩
def polyval5Tail65 : Box := ⟨21773102309437624577087178592803651522040697736742555442415,1434647988126467233309582790728449422337204321196363145125⟩
def polyval5Tail69 : Box := ⟨23939779193933924042931108490461709378811115610085421284716,776935337785460375886957198242610790249925857516497113542⟩
def polyval5Tail73 : Box := ⟨26343750000000000000000000000000000000000000000000000000000,2⟩
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
def resval6 : Box := ⟨69055067379721212398348146559223939641446765650227372969,14647269560807608600847491482850331391348097040423669982⟩
def polyval6 : Box := ⟨14961048479673715260048777442866900732751099325664563853141,3705877180498392011308791347607367791839566022560470671160⟩
theorem cell6_lo : Holds Q cell6 (63/64:ℝ) := by norm_num [Holds,Q,cell6]
theorem cell6_hi : Holds Q cell6 (127/128:ℝ) := by norm_num [Holds,Q,cell6]
def resval6Tail4 : Box := ⟨-38529153700627112593042530166768280343968954562990454027,14196400625579232216596955510191129174801120462412238276⟩
def resval6Tail8 : Box := ⟨-40389435495913791169397685782169902470703113559300926992,14016531691796579638327523284539566368664007750588630921⟩
def resval6Tail12 : Box := ⟨-42339483902787213429735481360614117802774932118248410066,13800402570932963239804444728820211995670836032355576001⟩
def resval6Tail16 : Box := ⟨-44383682884337416977578815668155109302912681336333680445,13545382913186978544995469867548595996605001388653640350⟩
def resval6Tail20 : Box := ⟨-46526578143942765280302432959971377497187048556565458274,13248688158823273279716574434772080691219374210872200287⟩
def resval6Tail24 : Box := ⟨-48772934851432125323559797846181419914667292697699063275,12907370404229226790715473429635194452120271892834585146⟩
def resval6Tail28 : Box := ⟨-51127748244510330406835504978416444155662918926815796756,12518309594223513192310090765568125504861195468632394635⟩
def resval6Tail32 : Box := ⟨-53596254736704092735727783806444340008253541085318821309,12078204259908079525997452248683092303430784244447717307⟩
def resval6Tail36 : Box := ⟨-56183943561608097683294729339251629906811379526651293570,11583561779041571576013437719788557709829668495754549999⟩
def resval6Tail40 : Box := ⟨-58896568979328678407051145463606550193990006857247898100,11030688134915428984937859738445624704547629045085253872⟩
def resval6Tail44 : Box := ⟨-61740163072268630731415919675877451505505392755965319090,10415677148523621002857520908586096597951386269625474523⟩
def resval6Tail48 : Box := ⟨-64721049158707236551768364888925183844974561146625204965,9734399157568126486446151063193864734491784032409838519⟩
def resval6Tail52 : Box := ⟨-67845855854003358965498442089342708358780604222565471710,8982489114532084663434817238923432254180996947285803963⟩
def resval6Tail56 : Box := ⟨-71121531810689591531728996334155551521060676497972118489,8155334074678064437952028655601832211230678805288207815⟩
def resval6Tail60 : Box := ⟨-74555361170233837794449408355774821052238341695827644408,7248060043386794400302824569681282325370868200336791491⟩
def resval6Tail64 : Box := ⟨-78154979758967611538867127321862354266124524536331027915,6255518150520106025858373501329372629214311075372417352⟩
def resval6Tail68 : Box := ⟨-81928359920769083910192499584680182937579622301524497641,5172267190289644028637855457999363194685219129735411216⟩
def resval6Tail72 : Box := ⟨732985300364717000600880493783128421743735719811645302478,1213891469792600418573248001723168702618413489432503249⟩
def resval6Tail76 : Box := ⟨-496562920074129643806372469867348769668257283241355223,185145972424204030050481743794104418245002359725185974⟩
def resval6Tail80 : Box := ⟨-520514461253108048398317319563094876350054445216919072,182897528212794593176401128229459400303104273405377992⟩
def resval6Tail84 : Box := ⟨-545645497032942608935447036482145455336061234864174915,180184245735263719224129694106824728894480233319409792⟩
def resval6Tail88 : Box := ⟨-571989889228594034300276356082633301563844677316738603,176972062204416999936430582910348096877193022461837664⟩
def resval6Tail92 : Box := ⟨-599606218981225206036069156013023905904084102276616079,173225165077806052338785041201410569606849664395367197⟩
def resval6Tail96 : Box := ⟨-628555896898516091603178108429601993978758419492589944,168905639089831189279606566500773739912039635264097305⟩
def resval6Tail100 : Box := ⟨-658903298563467320598535404548280052456806145979235393,163973352797159450668167043222948477959200543229955482⟩
def resval6Tail104 : Box := ⟨-690715907686272659562321114932865082661296327910357805,158385839290490424267780900922778750859408122859856723⟩
def resval6Tail108 : Box := ⟨-724064466168273557173200914357382585147889174368910508,152098170755329338844223113307869086368490093670827721⟩
def resval6Tail112 : Box := ⟨-759023131411175303365722231618926676562498772417405359,145062826572290443119362930121159878107301365335256102⟩
def resval6Tail116 : Box := ⟨-795669641221333091367548801392997135238467143704179584,137229554632132397158327676303832166581778925704147989⟩
def resval6Tail120 : Box := ⟨-834085486675806683354140241241509392389572215519275158,128545225524635368410576428210985151063696128063128339⟩
def resval6Tail124 : Box := ⟨-874356093334587025706489477948695226338592402912467204,118953679243547404040956492493497658569496263459841860⟩
def resval6Tail128 : Box := ⟨-916571011201957622363858202780101347310752327501926246,108395564032116938572848581283071779453339551063365866⟩
def resval6Tail132 : Box := ⟨-960824113859414465187773133622893124918116487201931150,96808166975147683398773586965646572807971852633771867⟩
def resval6Tail136 : Box := ⟨-1007213807218036508709401225621992366315988684528609125,84125235923346101286779129072499857717189957980869840⟩
def resval6Tail140 : Box := ⟨-1055843289901603340445064380126560827792482309341934766,70276787918578974040505957767438324795290129112883519⟩
def resval6Tail144 : Box := ⟨-1133089148560120886951324563147995633424871853943796020,53183122104390744134309207602146806583732621220251760⟩
def resval6Tail148 : Box := ⟨185357678193421511784548998282582478159746789153,59893714437158636919781892995799828039925378349⟩
def resval6Tail152 : Box := ⟨194257848185081106721845057080665179996128612609,58760774628788602815018167267022920462722775515⟩
def resval6Tail156 : Box := ⟨203636839757881034155987506591913764734122267108,57445490935676896706515030874519184110682388535⟩
def resval6Tail160 : Box := ⟨213468660603521720150432403211250295654749980130,55934369279421689173164748143859640816901932753⟩
def resval6Tail164 : Box := ⟨223775173068331128206592077730222401211172452527,54213736856626544531598279045388485098722010915⟩
def resval6Tail168 : Box := ⟨234579295809454762816480811525543116309792424626,52269126329092915844974365875035589553179533004⟩
def resval6Tail172 : Box := ⟨245905054023382261105316127412264450137524690710,50085233163204608809851023868334068561750200822⟩
def resval6Tail176 : Box := ⟨257777632870723802343341454960878956548459350670,47645870788928381338603027528121966778582235505⟩
def resval6Tail180 : Box := ⟨270223433480611706615520150240061931976575196364,44933923452973570384292173789390213357168935115⟩
def resval6Tail184 : Box := ⟨283270131659059284499212607500802788965600939981,41931296650285460166576122411852890132850195847⟩
def resval6Tail188 : Box := ⟨296946739431826779936764811071382211822082658401,38618865012318835177273042993463559726255027080⟩
def resval6Tail192 : Box := ⟨311283669558647667237212598057447487151905139836,34976417524521786649749010492873614930636406661⟩
def resval6Tail196 : Box := ⟨326312803162275997728290332534361609765847852260,30982599939148268321737213724754529827877949576⟩
def resval6Tail200 : Box := ⟨342067560622741939119744140941871511199483485246,26614854242896738933356359070480136074437086760⟩
def resval6Tail204 : Box := ⟨358582975894463529722726235961112070450182356493,21849355031926380641533197895214169638333323701⟩
def resval6Tail208 : Box := ⟨375895774411480496651478733497422312051726405053,16660942639515025163259411737679869374591359853⟩
def resval6Tail212 : Box := ⟨394044454770386021732975547736455024460459548215,11023052851964574364021408733970587433812589166⟩
def resval6Tail216 : Box := ⟨413070107197057498781529987465408898253112337365,4907569612407039776311155249138246147271526785⟩
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
def polyval6Tail5 : Box := ⟨11808697784563835549360150938705640852259165911587851721137,3634105000418373069421189324818719159005633070170661872874⟩
def polyval6Tail9 : Box := ⟨12378833407036666641059467560964509630131611414629649384537,3556129940706052532195256427658677396090799303233963283473⟩
def polyval6Tail13 : Box := ⟨12976497721855140062960570024265552056114053167435570901548,3466313231733810760322692778797851262832920493143166297219⟩
def polyval6Tail17 : Box := ⟨13603017957386353843709572590972649278423173127979390105978,3363825715739378662425927291999450336985918262422564296838⟩
def polyval6Tail21 : Box := ⟨14259787310510407673654941689064053513760876842916492376408,3247790015582659364446221963000520262420878993425861939325⟩
def polyval6Tail25 : Box := ⟨14948266243416996072995372289269041353373148808351810900861,3117277928161972366412237081998770797701550548423018859415⟩
def polyval6Tail29 : Box := ⟨15669985731090262017453631301973668153187258807447089980855,2971307700689263408218526223125402893913548459146041867719⟩
def polyval6Tail33 : Box := ⟨16426550665747505062896345682855077927778719891600506418134,2808841166865882499069946951625953091040908526056033422994⟩
def polyval6Tail37 : Box := ⟨17219643425648217142352676159591432098095490642000057673376,2628780735917541815183427876895770086328625594473569112537⟩
def polyval6Tail41 : Box := ⟨18051027616209323772746655653143742431942343773634023533390,2429966227101567954414495404397783080217377308157852316305⟩
def polyval6Tail45 : Box := ⟨18922551991745772127278162055160418379749291243694649950315,2211171541933907903291308496074291108259555845212473027465⟩
def polyval6Tail49 : Box := ⟨19836154566557265471688460975158939565476166604431254943538,1971101165999747943564412314018182731434899524766197169044⟩
def polyval6Tail53 : Box := ⟨20793866924502993696305343890096658443720267215656095310771,1708386491809187580546968804937270257659809985131957983217⟩
def polyval6Tail57 : Box := ⟨21797818736647588714175598748814845041011879458649473692394,1421581953737258474667068308284813406720890762150374427403⟩
def polyval6Tail61 : Box := ⟨22850242497024226741060368930545197001940330503873731333080,1109160965644728112193512298078553668359504816917529300749⟩
def polyval6Tail65 : Box := ⟨23953478487049605219498947617573463927748459114734620548291,769511651311079870474366455125833526726395774543948026379⟩
def polyval6Tail69 : Box := ⟨25109980011207728009636614045194612897927465812526311544814,400932354089762292959319780658527894531413208094484204099⟩
def polyval6Tail73 : Box := ⟨26343750000000000000000000000000000000000000000000000000000,2⟩
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
def resval7 : Box := ⟨45661102582732821460069688977750520975649258066579756437,23995169959587175411936417304493574908482086798078035589⟩
def polyval7 : Box := ⟨23554187884873760782621423520952685349111434131431709200408,6470640660030207409397943587563475791831311472341861626449⟩
theorem cell7_lo : Holds Q cell7 (127/128:ℝ) := by norm_num [Holds,Q,cell7]
theorem cell7_hi : Holds Q cell7 (1/1:ℝ) := by norm_num [Holds,Q,cell7]
def resval7Tail4 : Box := ⟨-61093390373056706699622432239856079237268415447988342348,22741315813086294655829519113363520007519185393738492812⟩
def resval7Tail8 : Box := ⟨-62057418401671672061471994345288835639896006780242126210,21777334635305453549110375449319135073045262190688304422⟩
def resval7Tail12 : Box := ⟨-63036609267045518865343472510482488377826435777365432052,20798143774890734450194888996426980600923121370566065905⟩
def resval7Tail16 : Box := ⟨-64031250572500917798997716802329629607725855514970974909,19803502469439258980838531744706549290788717493378786101⟩
def resval7Tail20 : Box := ⟨-65041586112429837460295924168978928352210327561399707545,18793166929510352789894291476353728310804023192478131372⟩
def resval7Tail24 : Box := ⟨-66067863522837871444570042401926415690365595083800742349,17766889519102318958366687514569575472566085173224090351⟩
def resval7Tail28 : Box := ⟨-67110334347122577907369596986118210565852873079935693857,16724418694817612500290777422688150702690753336242847464⟩
def resval7Tail32 : Box := ⟨-68169254097731490033714156451790182674342294005400141076,15665498944208700374265347462574472174311087017768735645⟩
def resval7Tail36 : Box := ⟨-69244882318788928810103848169755263970554903727220865539,14589870723151261597890255892795718884544751401710042295⟩
def resval7Tail40 : Box := ⟨-70337482649710977235688522293424010557017340181678113248,13497270392229213172238242106274464300028386233447853623⟩
def resval7Tail44 : Box := ⟨-71447322889824221590104705088287493121635198190821497586,12387430152115968817485938530016346442214865200721617810⟩
def resval7Tail48 : Box := ⟨-72574675064004098126880031394245528998234261706015170922,11260077977936092277511386773437875212677617479020149602⟩
def resval7Tail52 : Box := ⟨-73719815489348933282725655322260197624740203277818394027,10114937552591257044821197891317668126441861197608148457⟩
def resval7Tail56 : Box := ⟨-74883024842906015021253290747653674731916575131126123785,8951728199034169777889603715747320431001554758102078493⟩
def resval7Tail60 : Box := ⟨-76064588230465038327019930714380325985777219984490545084,7770164811473669806200553023867549258164745259109830326⟩
def resval7Tail64 : Box := ⟨-77264795254587781618482807777055228738012089726364589737,6569957785276984630585515961049877880430954558921609200⟩
def resval7Tail68 : Box := ⟨-78483908175664280364639489682110306561005558153456379244,5350810041536353761803170205018979454395716663702782479⟩
def resval7Tail72 : Box := ⟨732734742093559717413661285939628786764441712174703975963,1333211355112038623915291835996939296776678886246785319⟩
def resval7Tail76 : Box := ⟨-790176271529577661825774863287997468050517670916111192,296216334885054337329339013715110069896535086849801264⟩
def resval7Tail80 : Box := ⟨-802621933501398246679957626093918277238370146550742614,283748412888606099837030318515785205953670028520035003⟩
def resval7Tail84 : Box := ⟨-815286333913660723817324883153345060688376983435658517,271084011402155654261547803854925484095369563103131044⟩
def resval7Tail88 : Box := ⟨-828150564285117677265910484210767620268671424854781703,258219781030155182999353589588226790137130364748208053⟩
def resval7Tail92 : Box := ⟨-841217776623286270170831364832580616914215802145906453,245152568691985247848591885195854363320606919040502445⟩
def resval7Tail96 : Box := ⟨-854491173737093173173569540138129478917372480535048387,231879171578178332984476187967538940082340794739097827⟩
def resval7Tail100 : Box := ⟨-867974008972438638187745521135514917860886649878679370,218396336342832867658641468454115770095274799000592456⟩
def resval7Tail104 : Box := ⟨-881669587009080029712661581628818050645093604158044428,204700758306191476112444232726128895181202243909571910⟩
def resval7Tail108 : Box := ⟨-895581264670616629460839347908228298008612701316197906,190789080644654876361012916441116581444802628285921861⟩
def resval7Tail112 : Box := ⟨-909712451747256262910973015432342018350166855606308151,176657893568015242910186845012760213259679777918400714⟩
def resval7Tail116 : Box := ⟨-924066611831564196113953772650873287000935292540006209,162303733483707309708621779266769296350909524550019155⟩
def resval7Tail120 : Box := ⟨-938647263167399137545103525571908976710525233291571882,147723082147872368296560246012162082249413607046528497⟩
def resval7Tail124 : Box := ⟨-953457979512244421751257143510593695769601325465618919,132912365803027084510398835175129078000826267536229288⟩
def resval7Tail128 : Box := ⟨-968502391013145761410795885633003112532542632486733587,117867954302125769140591993614132837741401649009033884⟩
def resval7Tail132 : Box := ⟨-983784185096475738317343216347562497483216103061549747,102586160218800529399200151313933206594698400001032808⟩
def resval7Tail136 : Box := ⟨-999307107376787375462905185668444798137368792601819006,87063237942891852601973862204149333847643316954907550⟩
def resval7Tail140 : Box := ⟨-1015075003830194289760370237458211297680992565048509779,71295378402190014582231322804363489010534667193911901⟩
def resval7Tail144 : Box := ⟨-1057157523918971205037083083896427838235843257378642981,53289653152979215059342739406365977450500664152534536⟩
def resval7Tail148 : Box := ⟨321635212868883865185781848741110551764408887896,103019376047179188867860097980184740801473499467⟩
def resval7Tail152 : Box := ⟨326662651569621389658060128821658503624146690410,97944525652453843299943527718531162261318036226⟩
def resval7Tail156 : Box := ⟨331816991608570410474849346649448270236415445770,92790184862225493880429043999776173152306774053⟩
def resval7Tail160 : Box := ⟨337052661634745818651895870142777044829695338476,87554514835836358708245675928557664207639101309⟩
def resval7Tail164 : Box := ⟨342370944189474534136249827853856220717531000233,82236232281107308489421237069427344720593122680⟩
def resval7Tail168 : Box := ⟨347773142798136367226987972155008179550453117921,76834033672445473408237903659299308243863135603⟩
def resval7Tail172 : Box := ⟨353260581554371230500705422972663827716564602800,71346594916210610097995249125580058880884959206⟩
def resval7Tail176 : Box := ⟨358834605444412434950504698142965047364283883990,65772571026169405646398047941646665936258517167⟩
def resval7Tail180 : Box := ⟨364496580676746178934811018066422219459787979043,60110595793835661661882314470994095300744758292⟩
def resval7Tail184 : Box := ⟨370247895016972979509202757081886657326517570584,54359281453608861087444795195678145246018874082⟩
def resval7Tail188 : Box := ⟨376089958127952813087536152248240831601429348978,48517218342629027509117357287817929774710441659⟩
def resval7Tail192 : Box := ⟨382024201915317334256543826178751443063776658665,42582974555264506340314707778540468997540316224⟩
def resval7Tail196 : Box := ⟨388052080878433858710207702657721930980121965436,36555095592147981889945131940985278962795452623⟩
def resval7Tail200 : Box := ⟨394175072466907132662689901692029746104412020232,30432104003674708057198984921867521038463220106⟩
def resval7Tail204 : Box := ⟨400394677442706283181659438105497987916240225279,24212499027875570481808211885346942580307800779⟩
def resval7Tail208 : Box := ⟨406712420248012080236023388975933428807995135950,17894756222575240518505519982233651340478120844⟩
def resval7Tail212 : Box := ⟨413129849395097077155895218238212887657920939127,11477327089747695632193998260714677278736277767⟩
def resval7Tail216 : Box := ⟨419649265207995309199587776411300407983951334275,4958565884447500853080922475746818935158230449⟩
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
def polyval7Tail5 : Box := ⟨20171655415901730725757780635269673810537227054085055734944,6152443977748025143567856630555230714932621157028847926401⟩
def polyval7Tail9 : Box := ⟨20489937864678157632958207428488137704002225824769502382716,5834159711756972954957367612322762882313583922247592773378⟩
def polyval7Tail13 : Box := ⟨20813244253987712414817176917671667174564231152692792692212,5510853322289839810215963633947102187652006481851095208874⟩
def polyval7Tail17 : Box := ⟨21141652026489484883956262420291858696711434209115678318854,5182445549787956397072735365840460943613496322173430550193⟩
def polyval7Tail21 : Box := ⟨21475241675671593342281631852392964227254152271292370558076,4848855900605847591416198063018178529073015607704790751609⟩
def polyval7Tail25 : Box := ⟨21814094965268463060091833948818862088864481937919405929637,4510002611008977869922690409075839289314740049778605522657⟩
def polyval7Tail29 : Box := ⟨22158294949147274046190340632376793663177986989201499532677,4165802627130166883712366568299169353718620441423579337735⟩
def polyval7Tail33 : Box := ⟨22507925991664584716027067691506351330807095562372371912624,3816171584612856213867084013452146847333531827536589285937⟩
def polyval7Tail37 : Box := ⟨22863073788344265888154096992701423519734137736758550776549,3461023787933175041738641029698318836394718847411151559002⟩
def polyval7Tail41 : Box := ⟨23223825386881707840757613402311778967380927917364379820558,3100272189395733089134847342174158620587172342222680610174⟩
def polyval7Tail45 : Box := ⟨23590269208479448305335106874354448158751478729641125585216,2733828367797992624558286854293345663963909842409777414332⟩
def polyval7Tail49 : Box := ⟨23962495069519450815337826970014906321420408596461503472603,2361602506757990114567685654654257936496174723263783000839⟩
def polyval7Tail53 : Box := ⟨24340594203577345344625329710538159228643565528824572528381,1983503372700095585557188469616609007271826096059439545302⟩
def polyval7Tail57 : Box := ⟨24724659283784027004805163927951925788417811902576356634989,1599438292493413942126925098085784459974836560970845961367⟩
def polyval7Tail61 : Box := ⟨25114784445540097622524890155220999240140847445903500189075,1209313130737346732769252293627393280337547268816477419286⟩
def polyval7Tail65 : Box := ⟨25511065309592473006684714846192520570375991412121051732539,813032266688259452023755191577753049746424671309455062689⟩
def polyval7Tail69 : Box := ⟨25913599036826863406913210424389953372986516706585780757364,410498567615492959017763728227957834622342091234412320407⟩
def polyval7Tail73 : Box := ⟨26343750000000000000000000000000000000000000000000000000000,2⟩
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
def pend : Box := ⟨1030018262193074469454021408966602026263073538018358467674243,6566351829498737997958141914134877869207585415103152684⟩
def zend : Box := ⟨1003690671532905534538046875000000000000000000000000000000000,4833693807543128906250000000000000000000000000000000002⟩
def betaquot : Box := ⟨428741311879481855511979670439776254345915563918349215493449,394753241570766181521058343215944052068695097170030029⟩
def crit : Box := ⟨104691086315546499210657797454156134322115699594261960594,17371484824275790681691628063076395327840473455880091988⟩
def subsonic : Box := ⟨652631193396989766314780559019327411134315337683418449119,10034651265570180112930159320224383513175236893805476354⟩
def pendTail4 : Box := ⟨26322533726296053577037819309631499668657857153631535518457,1531804493942685215847761728284328167499336384538269377⟩
def pendTail8 : Box := ⟨26322565989308221577559464526577999487801698422119987972194,1531585724363303607166569605757574569038991763062533788⟩
def pendTail12 : Box := ⟨26322565990574794638151699690060073971821934980631180752235,1531585702095280688136471214507196937939907188550498809⟩
def pendTail16 : Box := ⟨26322565990575361392055425741232958683035135178292470215457,1531585702078344661291986802584004938988041854029861180⟩
def pendTail20 : Box := ⟨26322565990575362633539844081287350006461905806511435560503,1531585702078287166048810413757363907635573979271772549⟩
def pendTail24 : Box := ⟨26322565990575362643200575015610491125438453406779331677429,1531585702078286483631181033655381182066747850033780001⟩
def pendTail28 : Box := ⟨26322565990575362643420679078237654926734421383313300931009,1531585702078286459253961145730212745655453987666259877⟩
def pendTail32 : Box := ⟨26322565990575362643433305319536736354234842828944228318255,1531585702078286456859892553069130275353740947574851751⟩
def pendTail36 : Box := ⟨26322565990575362643434783254108820555947600561223111574063,1531585702078286456245946545494993055606203073487666014⟩
def pendTail40 : Box := ⟨26322565990575362643434844651431503405506517880292592432180,1531585702078286455844337791503408459916212407473388402⟩
def pendTail44 : Box := ⟨26322565990575362643433733309929055324210014364357972531750,1531585702078286455174357335628138829119141911788946610⟩
def pendTail48 : Box := ⟨26322565990575362643424585184355565744697827690408544492590,1531585702078286452259323163255329587420206820641005652⟩
def pendTail52 : Box := ⟨26322565990575362643273076367406574854693376545649867173756,1531585702078286417519223375249365584123567436409498592⟩
def pendTail56 : Box := ⟨26322565990575362636624214953119496194579075074112519210632,1531585702078285181809538870122759310625631184179771474⟩
def pendTail60 : Box := ⟨26322565990575361691569942996511334039971763733450527923418,1531585702078133552751670889902556762081173687695673358⟩
def pendTail64 : Box := ⟨26322565990574787181918168368268760463186735900551385525310,1531585702000450593210009687998900072718675591126512813⟩
def pendTail68 : Box := ⟨26322565988067565213869554200645562512873565657417321110520,1531585437578431432417057582557158617147178026063591601⟩
def pendTail72 : Box := ⟨26322231028422477786302484340187472030939499711731051695422,1504713386545365745674186266956330851905311503502371215⟩
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
end SepticProfile.ExteriorCertificates.C05

end
end

end OAI
