import OAI.MathematicalPhysics.Transonic.Certificates.BarrierData40

namespace OAI

section
noncomputable section
namespace SepticProfile.ExteriorCertificates.C40
open SepticProfile.ExteriorJet SepticProfile.FixedInterval
def cell0 : Box := ⟨250000000000000000000000000000000000000000000000000000000000,250000000000000000000000000000000000000000000000000000000002⟩
def resval0 : Box := ⟨124136541779223463547151460589753335921874778316474617013,305469830867284722300005884419851831453390571176155087⟩
def polyval0 : Box := ⟨3874773911937298408482257522202104060260778994955192239533,14806085249903354583581749789374170271497958353788251838⟩
theorem cell0_lo : Holds Q cell0 (0/1:ℝ) := by norm_num [Holds,Q,cell0]
theorem cell0_hi : Holds Q cell0 (1/2:ℝ) := by norm_num [Holds,Q,cell0]
def resval0Tail4 : Box := ⟨68475738775897360497696403428544797084300701975967,1955633446220311575832482872243717571114597531703⟩
def resval0Tail8 : Box := ⟨8889585799584507731614837667809130767847293957,465253811936577556857747963700042027411527803⟩
def resval0Tail12 : Box := ⟨8672404390313300684430884770458990732107649,691236237841984378777741120505119469374563⟩
def resval0Tail16 : Box := ⟨37215550643975041903545872142332382382793,30288761092471696278241130541333481916513⟩
def resval0Tail20 : Box := ⟨542732296500415614398142679731602539409,417093933107026414882365750883034811152419⟩
def resval0Tail24 : Box := ⟨23081513638154808672090287675845891716,6672137367321408184919977275995592620956738⟩
def resval0Tail28 : Box := ⟨2604434212527763871023409925554455470,106754118100572601618679779147032639898713831⟩
def resval0Tail32 : Box := ⟨734396157161288193424887595807912093,1708065877176275519312723303824545482894746024⟩
def resval0Tail36 : Box := ⟨-85505135044251337846966985744434690,27329054029965094050376110351886835949594698982⟩
def resval0Tail40 : Box := ⟨-150924093593032258147479267823955990005,437264864335364685282931178753972539030198565744⟩
def resval0Tail44 : Box := ⟨-38849454382994628117236959287739196245370,6996237792937976982469396420745812306840890262882⟩
def resval0Tail48 : Box := ⟨-9946309258100231889687539059763237705021687,111939795362296861914123661706669471802296045468028⟩
def resval0Tail52 : Box := ⟨-2546263385202919891377182465517355764245249738,1791034338673849951834185021522868828638148766497605⟩
def resval0Tail56 : Box := ⟨-651843600289121524514944352731931814755553328811,28655938315337659679927481066852663130734870758617614⟩
def resval0Tail60 : Box := ⟨-166871955053719751985006319977662594768512724677939,458338570568292719646254710171361040671612430118109389⟩
def resval0Tail64 : Box := ⟨-42719175992030548734959695210344911200547239154276768,7293367871969247153893189050367407257767869810858560617⟩
def resval0Tail68 : Box := ⟨-10935078495910273308999805683050276998003657739444973224,106441720597592469228255711321492448728430978234219153656⟩
def resval0Tail72 : Box := ⟨887617884649585038448007678147288520751053028289234099419,2643372804863127615493250490117223453358070406443458331⟩
def resval0Tail76 : Box := ⟨-32601867356672835777534220710805367531889084091511,689201692949533398289237191203522144978569152274⟩
def resval0Tail80 : Box := ⟨-1891453275921501220013771507324244123351194459,85063977634130048985420943342537684001521987⟩
def resval0Tail84 : Box := ⟨-1147780150597806104770693981239661473272186,81488817038840859902057058166380882245972⟩
def resval0Tail88 : Box := ⟨-3404650814026291049043227036393221375289,535524225332148075372748277527835529911⟩
def resval0Tail92 : Box := ⟨-36323303802361360055221292836874352202,2965234508364856734917310030004145388575⟩
def resval0Tail96 : Box := ⟨-1169894125095056333214018606128840178,47360242669835760182041741228578475727108⟩
def resval0Tail100 : Box := ⟨-102164670832267127074455977172817373,757760179702316363145393055952508508909541⟩
def resval0Tail104 : Box := ⟨-22668620322912083956244049096252128,12124162429404276537432611678103629042146867⟩
def resval0Tail108 : Box := ⟨-14393960452557151630861283294694432,193986598731315250100174785071569621086597103⟩
def resval0Tail112 : Box := ⟨-547778232683425642739652148329826980,3103785579188203058785873807224803383497307996⟩
def resval0Tail116 : Box := ⟨-136133385259448013398804018103351149849,49660569139448692415078619152965406442137255584⟩
def resval0Tail120 : Box := ⟨-34837217653846193503340695511812719220946,794569073571644144993065342254906804462024344648⟩
def resval0Tail124 : Box := ⟨-8918228413303545234749692162782634418165705,12713096816313372444048639193479312432536957446496⟩
def resval0Tail128 : Box := ⟨-2283064705386839064333886382269903283720448878,203407408688213278751669426841507775882818861831985⟩
def resval0Tail132 : Box := ⟨-584464548928157727446364103409057558141240323683,3253970603574017527771784493478923349684952127212196⟩
def resval0Tail136 : Box := ⟨-149623042073983175863039726251979469075760440519601,51923258135059129410654475373954170083408759498508287⟩
def resval0Tail140 : Box := ⟨-38304997723645304087231537033427235759181505916403736,794861939734208834277934576823071817916423969439859557⟩
def resval0Tail144 : Box := ⟨-10492618913697942058552820215821094455319278907164524840,3191221230842149928202006625915668720064488258083846178⟩
def resval0Tail148 : Box := ⟨82910150265944335522635213349533178495744292,1423424633606930523474180248964803261078220⟩
def resval0Tail152 : Box := ⟨1587290076200449391135082056805552011225,63461174593270599671511716957232581415⟩
def resval0Tail156 : Box := ⟨541299011153519254492124698976153081,34937507782232037104466415112243938⟩
def resval0Tail160 : Box := ⟨1017009562995450683850723505402205,97920066125864698970746302985441⟩
def resval0Tail164 : Box := ⟨7277383592613798449196887133023,38795556169950293111343296733634⟩
def resval0Tail168 : Box := ⟨162286810826895482686923061278,605477221698600771607478723676001⟩
def resval0Tail172 : Box := ⟨9979405816859627957331553747,9687169801886906814316068074932680⟩
def resval0Tail176 : Box := ⟨1568900470642296053574745104,154994677715819158447184645703934375⟩
def resval0Tail180 : Box := ⟨612115331398709140505739106,2479914834959651019513418914433114148⟩
def resval0Tail184 : Box := ⟨2781665022995820311503808669,39678637353970143325796261150763079715⟩
def resval0Tail188 : Box := ⟨570818193491583251743859137071,634858197130107261581415695883149446306⟩
def resval0Tail192 : Box := ⟨145820289199164028524526801485500,10157731017381506187252706873536445865817⟩
def resval0Tail196 : Box := ⟨37328367382151183772693467855291931,162523661282827255478238201941452530398632⟩
def resval0Tail200 : Box := ⟨9556041572000636693497225817786177971,2600369621738545338224221794437875037359311⟩
def resval0Tail204 : Box := ⟨2446346159102695626104792859145488663793,41603620498558504335011570282715024911909520⟩
def resval0Tail208 : Box := ⟨626264734071151370186455102686316478625284,665070804915322228227892594858490546806187098⟩
def resval0Tail212 : Box := ⟨160324467890217511577342154011808701402695722,10490829067646627775462968667184924180216942858⟩
def resval0Tail216 : Box := ⟨41083538607630513570754319589032494611289994623,129356284627549472838524194806633623894332081804⟩
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
def polyval0Tail5 : Box := ⟨2293098708580116648007067140950762319029621932627346,55838087768400289530281701714388665827493703477283⟩
def polyval0Tail9 : Box := ⟨238605015788017148209331885447774751312933498730,11496396538559215047130697793178417868240856266⟩
def polyval0Tail13 : Box := ⟨201409661071140503246971077145030571506380171,15061980996153360450646224985053723230769669⟩
def polyval0Tail17 : Box := ⟨757374735813138007318217928695773195586200,473887639696838394537868304478909048186478⟩
def polyval0Tail21 : Box := ⟨9705312104004699096457562744166052314236,6281826801346009444805921080458410082364873⟩
def polyval0Tail25 : Box := ⟨362275385304220216983396699408653219668,100486064034657599474034933259694910392218435⟩
def polyval0Tail29 : Box := ⟨35751083884991778243445347213271735840,1607775837726327819031938821170421405112891715⟩
def polyval0Tail33 : Box := ⟨8817361182120514672971664936464661449,25724413242431772237867604780334527537517601455⟩
def polyval0Tail37 : Box := ⟨11163949615557003042070949267516802804,411590611821568449995984922030726314702162022666⟩
def polyval0Tail41 : Box := ⟨1527866749888844673957424295002232870735,6585449787726641893145726039068280575844940273222⟩
def polyval0Tail45 : Box := ⟨389257834397292987001583186016517269987980,105367196238727071538839272504805041699813533016049⟩
def polyval0Tail49 : Box := ⟨99643680486316238624045218091112170873723333,1685875046403866333627307308098172280278205704771755⟩
def polyval0Tail53 : Box := ⟨25508730820760542912767838236776283558004377274,26973976828030101936966127049698367576672637342063733⟩
def polyval0Tail57 : Box := ⟨6530234136898474551433398461995762470476493096659,431577507154184396394445567151093639226603284507608905⟩
def polyval0Tail61 : Box := ⟨1671739932570948103931139530995244263197036201006182,6903672858325695048333862389653159179109517282961215892⟩
def polyval0Tail65 : Box := ⟨427965492402216081800864280887352742935550848461477390,110057548131465500906393900752416788490818473418667443946⟩
def polyval0Tail69 : Box := ⟨109559997104100700074649625038168291030439010532421123858,1658208689105440901889056540782862215129875091942571655934⟩
def polyval0Tail73 : Box := ⟨28531250000000000000000000000000000000000000000000000000000,2⟩
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
def resval1 : Box := ⟨123885618260235068284264213826531335764296010674423403947,219653188565538642168852062677413963407425081332410413⟩
def polyval1 : Box := ⟨3855932925816951259506186874272777765162739689294739308825,8380402806255980266693667288536551463303391860184535543⟩
theorem cell1_lo : Holds Q cell1 (1/2:ℝ) := by norm_num [Holds,Q,cell1]
theorem cell1_hi : Holds Q cell1 (3/4:ℝ) := by norm_num [Holds,Q,cell1]
def resval1Tail4 : Box := ⟨66455715418587599702807472858884791346904910373405,3331557605751150921143940664853155526044869997917⟩
def resval1Tail8 : Box := ⟨8381795357773948245057182110830601482620296175,6710774376448788379163268214393275420400577420278⟩
def resval1Tail12 : Box := ⟨-339472976015656052609907567981727225694850103,21208363572545385645166229454957039627347507232468⟩
def resval1Tail16 : Box := ⟨-2277398572378044925627173941921093553210885876,67027721975974961916390855847517367419737679104500⟩
def resval1Tail20 : Box := ⟨-14925379058131872993614480527417228181821463603,211832973978689395816046291770936164812239077506008⟩
def resval1Tail24 : Box := ⟨-97814967299686210574036617158209666662671432142,669446163251159384874046459606166614131074917704210⟩
def resval1Tail28 : Box := ⟨-641040169821999029912861306251114196601934628322,2115448570002152487395208196061655429938154273108654⟩
def resval1Tail32 : Box := ⟨-4201120856958947158845874568163791148454196383783,6683687029810027585043045626792875309886852013661780⟩
def resval1Tail36 : Box := ⟨-27532465648169611749101057050914419529113529245053,21109496751274653224605494573686598342647578519240347⟩
def resval1Tail40 : Box := ⟨-180436766871846293969843366426930217922220861916852,66623013597723742322213366694368614445356153095836093⟩
def resval1Tail44 : Box := ⟨-1182510395371333516174463625842916345695672505983627,209949382114955464201262749261104728808954359351247798⟩
def resval1Tail48 : Box := ⟨-7749700127105563177386677826245310258380703685887070,659531342868495162203431735823249012495871177252064914⟩
def resval1Tail52 : Box := ⟨-50788434752998527343911151873780067301392041114073398,2058149182615813066090059784146189250359789112331548765⟩
def resval1Tail56 : Box := ⟨-332847085997201853722023395308306318384033740869212948,6332437235563437693113102866384765164562030186416841413⟩
def resval1Tail60 : Box := ⟨-2181346662775280308943072799786797008220808386991402052,18884243291771937253789138319604826240904093262563006169⟩
def resval1Tail64 : Box := ⟨-14295673463169058487419684829938315136734892441742530053,52281993530491697128977852142306672230908922730647608720⟩
def resval1Tail68 : Box := ⟨-93687652896682555855461676349764140899030052984076656562,116730242475262083768580310577218569157010653511006233288⟩
def resval1Tail72 : Box := ⟨890884962953751682300178456253443336744737110882290108997,1553551075219215659359627416690358894313429486094646991⟩
def resval1Tail76 : Box := ⟨-31862312306625948837983223869478360794509922361051,442991019252866771036998631914398242688693160866⟩
def resval1Tail80 : Box := ⟨-1806362653188106084477334490258912656885747215,71479917607294442779286390614536531775062253636⟩
def resval1Tail84 : Box := ⟨-4139587194948408360815775920166256696920585,225748127211909574779485000976178991642138078847⟩
def resval1Tail88 : Box := ⟨-20116232585546876749793621302501912568940657,713465170802435046070137638078756237799138041637⟩
def resval1Tail92 : Box := ⟨-131813479754746506266230499342811319740849936,2254834022283970612443485755946634618804983879640⟩
def resval1Tail96 : Box := ⟨-863852611225973180927954020782179240871454328,7125941751677928310842427214329945296760055416241⟩
def resval1Tail100 : Box := ⟨-5661344466426218253104885396746503805524801332,22518563775259174596295905444682519917389751629897⟩
def resval1Tail104 : Box := ⟨-37102187094631714345155502931865031056433054199,71150572265371211833786542937639558487585127209007⟩
def resval1Tail108 : Box := ⟨-243152893343268527467605635989658633262271124018,224745052783585767274817412524071460302338319377176⟩
def resval1Tail112 : Box := ⟨-1593526801814394165341489356978171178214659402498,709480308424035377228923969727650727156086371993081⟩
def resval1Tail116 : Box := ⟨-10443337248370771703576055606621449174884202537676,2236901129638265533623677321616924547647460863722726⟩
def resval1Tail120 : Box := ⟨-68441454990922732896622648366714759716944351923307,7034276860107582241454657751305583586958929083868175⟩
def resval1Tail124 : Box := ⟨-448537919428515250583148298222435100498766749183510,21999559471500096854845503297869973457753440715701521⟩
def resval1Tail128 : Box := ⟨-2939538108767039465761431068003892788523387416281071,68007535126760700149442747584782552718661509013137418⟩
def resval1Tail132 : Box := ⟨-19264556949690466233116165955497705526855929794293327,204963230066360724233387773314046914706672309781431699⟩
def resval1Tail136 : Box := ⟨-126252200503272900706872785800407483541094489184728242,582418336303177095479437189142564804966575714180516351⟩
def resval1Tail140 : Box := ⟨-827407134510729850128762668565532673401314998110284435,1412342310485385018439177508387663398678156138786384487⟩
def resval1Tail144 : Box := ⟨-5711643561294517956824509840445159913463053841921411959,1606169650934897636947056397532975928189529202378864651⟩
def resval1Tail148 : Box := ⟨81659468220587832482334091278507679846489984,981607277988378445950666292360242611122732⟩
def resval1Tail152 : Box := ⟨1525592336494187388771062037960683044735,3956718647490147137678561546678666186235⟩
def resval1Tail156 : Box := ⟨659961106288583201224506653465973017,12378682947452711435104085113683338132857⟩
def resval1Tail160 : Box := ⟨992736700750014120362038608076974848,39122243204656070860546875888432464510422⟩
def resval1Tail164 : Box := ⟨6499892553450291752079350231739503205,123642242871020804036195252995005474907159⟩
def resval1Tail168 : Box := ⟨42597653362902425140671333446012484090,390748490566748252623975895085685799349844⟩
def resval1Tail172 : Box := ⟨279167980163609298045387156840704667008,1234813654048392978946897433359450918298775⟩
def resval1Tail176 : Box := ⟨1829555274746403115653623906381410533092,3901673684716715581947018325459038810527536⟩
def resval1Tail180 : Box := ⟨11990173448570121088200547849491915869811,12325007720845429511591268478221736508907659⟩
def resval1Tail184 : Box := ⟨78578800712546457167426659319956990999804,38912426889895648729971819692804488133235870⟩
def resval1Tail188 : Box := ⟨514974028349742597198722346658544998370659,122715858771597145243783768448406438260476715⟩
def resval1Tail192 : Box := ⟨3374933792192871870177874728305942346898488,386095352587886181815580643897020522735429418⟩
def resval1Tail196 : Box := ⟨22117966100515236476950121399386266751142403,1208800469866154399014015445648016898668300557⟩
def resval1Tail200 : Box := ⟨144952302636338536672553528069441240953805894,3745357815974372067206780218194526439652670886⟩
def resval1Tail204 : Box := ⟨949959410557762445440091526742865685313689204,11345341705051608838846651517379289724027137540⟩
def resval1Tail208 : Box := ⟨6225653993155847632432431188672744599781949948,32633569285909845066301089380825609046001195872⟩
def resval1Tail212 : Box := ⟨40800446376716091895788462233998158096803928617,82013889226857681388362226807076206589355562692⟩
def resval1Tail216 : Box := ⟨267407723045916578033307088624682707324057362447,120760919316734623643505042262033773360795316009⟩
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
def polyval1Tail5 : Box := ⟨2230243155200987965327511662889598200254025734387285,123173089677657666406052485630234748542249728398815⟩
def polyval1Tail9 : Box := ⟨229267747230553410855197493541661976123923003307,286221431107275577244271107917626178032560979725167⟩
def polyval1Tail13 : Box := ⟨16220999405538882582679606150599774878626628433,904574684877685304407487757680253810797179007718265⟩
def polyval1Tail17 : Box := ⟨105080790700959378125214630817683674762753147251,2858848307837790506099098519988116760432963250504001⟩
def polyval1Tail21 : Box := ⟨688652983354436562038288544407871119765410070129,9035015881777830998419346591601605677510037443891077⟩
def polyval1Tail25 : Box := ⟨4513156135961788829890025699560480271385965939911,28552775249996351822255695864630601747924752585455134⟩
def polyval1Tail29 : Box := ⟨29577420050636734165414516354231678624125268957505,90225556307971531347555222153113825959146356602755227⟩
def polyval1Tail33 : Box := ⟨193838580043665682343214229284769791529642776910708,285056954436915197911841860910594246988534971337683895⟩
def polyval1Tail37 : Box := ⟨1270340518174125283251054629468043694902347366286114,900263030004560041897998234696012162511312858267557154⟩
def polyval1Tail41 : Box := ⟨8325303619905926543045346125930015549761863181918418,2840965348896389704533440050321938486233462153214522487⟩
def polyval1Tail45 : Box := ⟨54560709803415462244496638413722420512247913661432087,8950604809260432455022392062214340207589282402742723013⟩
def polyval1Tail49 : Box := ⟨357569067767663603122198572028613007979416425102929496,28103200967792152096757930353532554548399153508085475050⟩
def polyval1Tail53 : Box := ⟨2343364642522162437970915150577561957308881794389419757,87606723371098985580363878546123259369062451381761620307⟩
def polyval1Tail57 : Box := ⟨15357474521233428035025765441217804703219846024973495332,268929223398359493190390768367078061357743062516218284077⟩
def polyval1Tail61 : Box := ⟨100646745022399399592882251930567365788221919372636426379,797839608896350737953222931242115550605214217099350276436⟩
def polyval1Tail65 : Box := ⟨659598508224846898953717627237806432501890683064136302994,2180062067161486296526143835698074106348870246873365000610⟩
def polyval1Tail69 : Box := ⟨4322745180868015025385032467021701039796945936249693032686,4651984867421690099880701478784010768387211352218504944226⟩
def polyval1Tail73 : Box := ⟨28531250000000000000000000000000000000000000000000000000000,2⟩
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
def resval2 : Box := ⟨123762127724066183969294123775773384966209060685811000610,197935608547876774230637730580127310650347399379746045⟩
def polyval2 : Box := ⟨3846625285949165467584636176947921793281719078680421755366,7062240641206981825301185463354903215383325428687746478⟩
theorem cell2_lo : Holds Q cell2 (3/4:ℝ) := by norm_num [Holds,Q,cell2]
theorem cell2_hi : Holds Q cell2 (7/8:ℝ) := by norm_num [Holds,Q,cell2]
def resval2Tail4 : Box := ⟨-132862351644027948161907318455759963311773426037478,35744437528639320718743920949409326493378909451193932⟩
def resval2Tail8 : Box := ⟨-455147127137426985101788313837092346238997035202871,60860338053687511968564089326964335583506917487371798⟩
def resval2Tail12 : Box := ⟨-1044398340473982329900908003751110814616233272638627,103557126134567413173061214455743551125024205858807505⟩
def resval2Tail16 : Box := ⟨-2396473868159301987915817849266850793723034312815678,176049108922547221382805766587986158109733502671359196⟩
def resval2Tail20 : Box := ⟨-5498943014102329324249902966420494305654613445995606,298921343162848422130816175786473282113333717564445205⟩
def resval2Tail24 : Box := ⟨-12617861047310640126337226300174634305078163791967500,506709707541107507935128205387608684467177682226736673⟩
def resval2Tail28 : Box := ⟨-28952912769039993561230807037428324099834860362267563,856996991828278123573669017759954079923775011855589177⟩
def resval2Tail32 : Box := ⟨-66435282071069119861903721445000945226963432542283880,1444956142014984613496147159524907281927522230768108895⟩
def resval2Tail36 : Box := ⟨-152442234018752349856073889848050882765852946746851067,2425924810153041108235550416636196929031926971640763192⟩
def resval2Tail40 : Box := ⟨-349793573357128742247589464873678661701603484476583123,4048786773551520155782406472283899114476584091996151778⟩
def resval2Tail44 : Box := ⟨-802635468769748581199618497392121198499893511346235629,6701148413336801140935760365853066038558671968620547276⟩
def resval2Tail48 : Box := ⟨-1841725362602648456543491735841791867174333880413293378,10959398661182619189031739413365621047736959715317532038⟩
def resval2Tail52 : Box := ⟨-4226018464462979411009828075718375479999458078292833143,17612133972615094302454580218427942572259409080849309559⟩
def resval2Tail56 : Box := ⟨-9697011522252182530757149618521543334185619200001776549,27557912418718947903231097186097598270831305928841898471⟩
def resval2Tail60 : Box := ⟨-22250738668882093672263175692017336520122226409305595033,41304516833902709428872745857803879331636132461816667444⟩
def resval2Tail64 : Box := ⟨-51056489927093141568239280052007170744437572771190609419,57365970085704846228674393109949675198278020908992669594⟩
def resval2Tail68 : Box := ⟨-117153724088631045618735350174182743078914935058818480654,67809850720343141024778986043588834871660835909671049690⟩
def resval2Tail72 : Box := ⟨892516534221147971413526626411506701489559512138774951193,1009121498753276175649859124380165921027400995948746464⟩
def resval2Tail76 : Box := ⟨-33787392647212573752993592573713505535718313518703,443901252631965455929478664263185503578236623217634⟩
def resval2Tail80 : Box := ⟨-5231976601758719565586171361884376946128984468161,755869009544041793492091015258940100829511702244271⟩
def resval2Tail84 : Box := ⟨-12001228779595865021064511188016210427461393124645,1286400429881388253785292670620220618778560753902738⟩
def resval2Tail88 : Box := ⟨-27537987517582869730586163989485381276164079574851,2187477918194443349645219272561466610196680249657891⟩
def resval2Tail92 : Box := ⟨-63188598079862494598668414983065896973982507770432,3715530747936080176245277638712206505700222707996258⟩
def resval2Tail96 : Box := ⟨-144992400957946216084951851648766058439233591175263,6301335979417387751439914466474635670003417569036617⟩
def resval2Tail100 : Box := ⟨-332699204831059972002407662639543869227368473887484,10664452417833398238444188751594779775646566891454153⟩
def resval2Tail104 : Box := ⟨-763410773005438943080761091328797231063066605373374,17997244390023974023425830373064684131354451828482297⟩
def resval2Tail108 : Box := ⟨-1751720472661477039679975739000406066509591508750514,30253128984968042101249187880302856861962365154054441⟩
def resval2Tail112 : Box := ⟨-4019493466487257414495085777386087944509144670313367,50579366749443817298492167013760097783708857929627229⟩
def resval2Tail116 : Box := ⟨-9223119772406740035026320299187168643202932277740873,83920125310664347863206936373648831904139991890280300⟩
def resval2Tail120 : Box := ⟨-21163347831114040819561672902991165317385312279843705,137734916167327931855878850014388609275888883765148053⟩
def resval2Tail124 : Box := ⟨-48561365619547281463499346488109292678879445610013885,222512057678086341754656927163080938051084309473729388⟩
def resval2Tail128 : Box := ⟨-111428789511664818983024195758136316558855725755868410,351010503210995711569507215612118321903313185849586830⟩
def resval2Tail132 : Box := ⟨-255684224972453741268188135289410235583486820862391710,533216792516988933088039200537483354454052978858054981⟩
def resval2Tail136 : Box := ⟨-586692390658216618861061566078758594898748853150878577,759137916619146884170111338655131099166879880174170439⟩
def resval2Tail140 : Box := ⟨-1346223472549779725943478777295802145089279582268086268,949704126912747421042649013014536893333238287661832371⟩
def resval2Tail144 : Box := ⟨-3313316227347319109797084074005366379551413685747322523,809293902428552663222076050550832436196634655597636969⟩
def resval2Tail148 : Box := ⟨81389960419748231816745590223845452034398533,60776622135146748497907303204296532833736239⟩
def resval2Tail152 : Box := ⟨772093571330720479863478546258293377239480,102276977021540548944026377514890665652531412⟩
def resval2Tail156 : Box := ⟨1768210193123648912376267632630965657756143,174026389293074268560387498590912290171815049⟩
def resval2Tail160 : Box := ⟨4057329606050411019138795329191329106566907,295840495241841955994576270951119702503214355⟩
def resval2Tail164 : Box := ⟨9309938482671352876174554027483879956109136,502302510735684325314594026612069702586539655⟩
def resval2Tail168 : Box := ⟨21362561829065816084153027127813642620742581,851425689732100136409281972734803508532538821⟩
def resval2Tail172 : Box := ⟨49018481566809596002016489539597787002755551,1439919743503800651141630248563347500961953063⟩
def resval2Tail176 : Box := ⟨112477686634306684146109731262996054639731762,2427585191287067552311026623720754832378764409⟩
def resval2Tail180 : Box := ⟨258091021717234088010981897851871154853925003,4075144108630932870918101663794991571781760934⟩
def resval2Tail184 : Box := ⟨592215020456589516280781764184463319680697990,6800092807076143454428121939896233492803267996⟩
def resval2Tail188 : Box := ⟨1358895122042052117811382099804103641457515529,11252055674115413208286840007646768640847127245⟩
def resval2Tail192 : Box := ⟨3118117387981790821616714081203760757887552340,18395607918582548195614606905717123943545188422⟩
def resval2Tail196 : Box := ⟨7154824450781647859945536583490788425123453733,29546641128430152516791023783432213573098637036⟩
def resval2Tail200 : Box := ⟨16417442498736953383034411182663748518405751044,46193637473129576441482164666840291150084297786⟩
def resval2Tail204 : Box := ⟨37671422975289072541871375830265888450028877150,69140315285754563211733668662274653238268407778⟩
def resval2Tail208 : Box := ⟨86440754039125244354888274352500174249585529991,95775355880680627438163507766962459261805941288⟩
def resval2Tail212 : Box := ⟨198346740837893951679464577532156863913656886557,112505898423075826422771021674828873373876487103⟩
def resval2Tail216 : Box := ⟨455139949874194739673384946926468499077262529092,75173636896212001548380884365877070196975105583⟩
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
def polyval2Tail5 : Box := ⟨23137884097906641585128250404716099170474007028322625,3212619420539882686338526429632257405828852265949993343⟩
def polyval2Tail9 : Box := ⟨48043469124294585678354051853106879702831161264925500,5468262359676615738052317063925808081548563543019070777⟩
def polyval2Tail13 : Box := ⟨110239917661514425379638655087212702451741853106078539,9300333912572535458297853610583296146468976597870701858⟩
def polyval2Tail17 : Box := ⟨252956242149933149208175853997286929883813527945604827,15801067251351504723176951740402106040270465154230240773⟩
def polyval2Tail21 : Box := ⟨580432767952638511450072316486084840865794043867998964,26807022554570977808493355116923203201166732213484220687⟩
def polyval2Tail25 : Box := ⟨1331859594571044301851217448899940491995950346647469150,45389930076839492787585517495201008431320260134949847040⟩
def polyval2Tail29 : Box := ⟨3056081733475996680130508337410023504419626866840236577,76649228759692499265923784171468865715434124056273406419⟩
def polyval2Tail33 : Box := ⟨7012477591298726123780015887896432211973268018923824752,128961263258354817938289108849012764391365954352386379971⟩
def polyval2Tail37 : Box := ⟨16090813746834960783280360226607690974645969472240222734,215874385137038807004433851186841326397189907467370032992⟩
def polyval2Tail41 : Box := ⟨36921941448568887286682538682222315097805368763868695324,358800446984728469170125675177121603424633143450246714514⟩
def polyval2Tail45 : Box := ⟨84720995580456237433975451400966389166308602182898188555,590363928627284692202901089909953769045802830615348747099⟩
def polyval2Tail49 : Box := ⟨194400587036895766222484900635274620326310378456709307508,957264489828954649431684751118709599444303994582985623080⟩
def polyval2Tail53 : Box := ⟨446071106475613634140443183657157583517176453422279355075,1518618670634974998770834067371312455318338725219418467515⟩
def polyval2Tail57 : Box := ⟨1023553658274773986742899490862426981016728342998001138082,2328120363818092065301826439645230440761637801678870886668⟩
def polyval2Tail61 : Box := ⟨2348643694152748070424540542296934018378868434653304340130,3369164216922828131739419943387145098204928243396336646220⟩
def polyval2Tail65 : Box := ⟨5389192015022480050539763870214223585766878248149270761243,4365135849969753839087508462741433903199688292531606688677⟩
def polyval2Tail69 : Box := ⟨12366026990052066411830531553917648932190133473118000592993,4274425996728009159044305245128469633402489556977397266418⟩
def polyval2Tail73 : Box := ⟨28531250000000000000000000000000000000000000000000000000000,2⟩
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
def resval3 : Box := ⟨123576516677695169715107034072187257023722118336240316559,1710851700761440772777584282882895140170428506419853403⟩
def polyval3 : Box := ⟨3865698841353451828637905374174611522877962263144606492585,250628186526026361668327680152373820639160769646893987135⟩
theorem cell3_lo : Holds Q cell3 (7/8:ℝ) := by norm_num [Holds,Q,cell3]
theorem cell3_hi : Holds Q cell3 (15/16:ℝ) := by norm_num [Holds,Q,cell3]
def resval3Tail4 : Box := ⟨-184503856552164226153050907345829694784545433700929842,1991355716786356648803090364037577816659983547746343976⟩
def resval3Tail8 : Box := ⟨-273631695175168822534238514552446726439510596465932160,2543185162045543844815217116361047960269303973936538332⟩
def resval3Tail12 : Box := ⟨-405671348325627326975243539132672907111601008689011494,3240805887777939174821170513330751012418357339992644866⟩
def resval3Tail16 : Box := ⟨-601426080652330061549788141319774651572966009585757760,4119078258029517473742877240094472817712682765132481774⟩
def resval3Tail20 : Box := ⟨-891641305147643170191417524786739128513608501728558151,5219232222553206612904688476824935938010436357328410347⟩
def resval3Tail24 : Box := ⟨-1321898472016773433288443687985343178005858461415954451,6588861182529457040663601587449990001995469000021620967⟩
def resval3Tail28 : Box := ⟨-1959774138133867920708640048337310630720987606222492006,8281006992144487858598037480494099725242184084293998503⟩
def resval3Tail32 : Box := ⟨-2905453598594983734128721098118788657318454363698222576,10351629505680025143684629942771514036311936642362028382⟩
def resval3Tail36 : Box := ⟨-4307466074446130553906883127357335595378001062508538014,12854335373885069087142990113647743392672666360445209894⟩
def resval3Tail40 : Box := ⟨-6386012838572541594746954773255330543025642723242167129,15830595945977255929526904648129786116415720803525106683⟩
def resval3Tail44 : Box := ⟨-9467552215058854082600523648100715835934460642531508154,19292698121815329235355017437281976900418008138777794655⟩
def resval3Tail48 : Box := ⟨-14036073401459325172020654108173723972703540843259619386,23195171360563123756200048350093142770768773739359552652⟩
def resval3Tail52 : Box := ⟨-20809112224149401740513843796621924499597210714512091131,27388159019779550097708933411500581699232595107551639839⟩
def resval3Tail56 : Box := ⟨-30850447926000634314947745938558544074954460263639569926,31542764286189502332781732514398688131611868201466091982⟩
def resval3Tail60 : Box := ⟨-45737181239769563414716962209906145482612099614803002956,35033219857266809021291912572149033266950952722685571337⟩
def resval3Tail64 : Box := ⟨-67807435152702688297612240117307267099978819860484664545,36752940261214365313772060174680343716726535822992255229⟩
def resval3Tail68 : Box := ⟨-100527246995858105967049130151663538559959429006931698010,34829827635601989416732681258797120866290456615146803042⟩
def resval3Tail72 : Box := ⟨893330245142693918957915951010071191406469883652641566695,757169113932629731059374008021299285169069383763940010⟩
def resval3Tail76 : Box := ⟨-2397363679846184798036943269528700819514159024813607,26561197032939403359236890688672582142636226736557661⟩
def resval3Tail80 : Box := ⟨-3507746706454286312388238283090085901671512607708010,33939529950790393504299027640130975126729217392899401⟩
def resval3Tail84 : Box := ⟨-5200390197359931287125129134420768137705253868984445,43276540325581290345332857573984965324567331833402770⟩
def resval3Tail88 : Box := ⟨-7709813144308744467537732567244091356927010870611306,55045428706239839256099758721203160979429197315513846⟩
def resval3Tail92 : Box := ⟨-11430145907501635802993741034382086073717522053552059,69808916411853622677453420384982384549387894587537393⟩
def resval3Tail96 : Box := ⟨-16945707116555378763921426529725608009656007104078935,88221368205148606860753662397346223082171293980336702⟩
def resval3Tail100 : Box := ⟨-25122775509944664060904619144419350506291000932020529,111020028406760369885931335680399715315648883331328447⟩
def resval3Tail104 : Box := ⟨-37245648410060126023844644125695603618456085248478111,138996421663721229042883695879069206031888299039437693⟩
def resval3Tail108 : Box := ⟨-55218354553886230076414803889777305606520495879709561,172933750223503100983447984098345731580364123028449910⟩
def resval3Tail112 : Box := ⟨-81863702467188864945039731357899486684632503530362222,213487928914361499503501846357936314222630750628382171⟩
def resval3Tail116 : Box := ⟨-121366633174417284303602416609293835324963835133642982,260977357229953771204993758841775250913035039292866998⟩
def resval3Tail120 : Box := ⟨-179931510598330477471975218123432220898029102695678998,315027417898279132441685503543816415209601404652273023⟩
def resval3Tail124 : Box := ⟨-266756584239015301968806526316008600658517074434714380,373986691572417934337865538383477130081068545697366100⟩
def resval3Tail128 : Box := ⟨-395478674070150195870797645216413829659744110171301888,433988018741269083273480323965452336148387580495275573⟩
def resval3Tail132 : Box := ⟨-586314981092129618685475038792206071983872954280204813,487461397773882538859317930831260509737497955762950831⟩
def resval3Tail136 : Box := ⟨-869238418187651243821694742268713356979529895650002673,520806199453297262048311853480213853030987600970853134⟩
def resval3Tail140 : Box := ⟨-1288685690686968341717926077642503848781736569117119803,510780746134556695136447221335923512972519296995362183⟩
def resval3Tail144 : Box := ⟨-2112191005289687042179913995151068585708559105856675146,409767390376760618844816137985555217767355596575365384⟩
def resval3Tail148 : Box := ⟨783781429234228720024058775245623774580373969,6868688529793142857803577054185955835105062004⟩
def resval3Tail152 : Box := ⟨1042268069622377689738232739513670932269072407,8759033428269768853408435391389497967182230033⟩
def resval3Tail156 : Box := ⟨1545207250000718558853648404606144549869762528,11142950715625266534627043989471880263718285198⟩
def resval3Tail160 : Box := ⟨2290839478039071565930681830225516016929013213,14134466603995481357732290220283639913810491488⟩
def resval3Tail164 : Box := ⟨3396272905002934297993057366620627255528606273,17866914441015003778994217946063515684580101204⟩
def resval3Tail168 : Box := ⟨5035127845419784508020747069511878544289858211,22490881950306263704391665940842811472107342398⟩
def resval3Tail172 : Box := ⟨7464804251264908616127733092665713457560532685,28168668893874889650978589988474880109660909490⟩
def resval3Tail176 : Box := ⟨11066909167041604129004691907934108713835164645,35061985569548654019455909661390566943985399860⟩
def resval3Tail180 : Box := ⟨16407192257023470290147525201865116130414747441,43308427406328216780610189315111271277421509736⟩
def resval3Tail184 : Box := ⟨24324402929105464988857806693319840277298998595,52979752137707693803354672649848255665088067105⟩
def resval3Tail188 : Box := ⟨36062025030772340917269200513750874961493155311,64011162257300097099783556677847080622425265073⟩
def resval3Tail192 : Box := ⟨53463579480669123236103623616969907768528996171,76084991425229450551509471899330676339591192375⟩
def resval3Tail196 : Box := ⟨79262169233334568010758255293680164310804449051,88443413836077164012091802178848764434759224477⟩
def resval3Tail200 : Box := ⟨117509742755726548844597494978510735106730532271,99591552889448114798119603111440002109587293985⟩
def resval3Tail204 : Box := ⟨174213496502562439094509418229815919027145478625,106832439525134866259165309659841340109934684348⟩
def resval3Tail208 : Box := ⟨258279370305065341195886699798639229682294354386,105545349961908386612465816423134708384436804319⟩
def resval3Tail212 : Box := ⟨382910822127313933750060751244682763792488303297,88074202662762313670766178489371587220492416823⟩
def resval3Tail216 : Box := ⟨567695204479577633139741016604541040709559931515,42024839166855418250680684067768621665124842230⟩
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
def polyval3Tail5 : Box := ⟨35161816269036922513460079694136791691000258749538136047,317473400090641120252508543022709621081094847725540765567⟩
def polyval3Tail9 : Box := ⟨52125739132304912699083402058199804628816672953719563099,404371208703169015791735624803107782263209422016026914460⟩
def polyval3Tail13 : Box := ⟨77278760219921451544623656369283268305735230066340627381,513674009339078908991994619520961986875970687581729292249⟩
def polyval3Tail17 : Box := ⟨114569249387695342195065254621646898218839120054658157873,650441727517132586618369119283219676694003441165347950379⟩
def polyval3Tail21 : Box := ⟨169854082388684786696084301297643456398826660262012396008,820481905412495674091397840916306628522092943662486529366⟩
def polyval3Tail25 : Box := ⟨251816342153680829613522962213050145652111482680509497818,1030211495802628546457177121391474523705076359626155814756⟩
def polyval3Tail29 : Box := ⟨373329090969696668393115279574169266066450048110967609491,1286305010527679948937803739184241558329104259687934108382⟩
def polyval3Tail33 : Box := ⟨553477224600463823761333425747465275523245291277576929878,1594982636648564798300265061606657548003917071219362168438⟩
def polyval3Tail37 : Box := ⟨820554962260623365339046245961485908210411570858246737034,1960708553133279642565242025515628352139752263817131904656⟩
def polyval3Tail41 : Box := ⟨1216509760770323825938209267473004867088437945359696906770,2383942303325574001735394242928263256457709502471110143581⟩
def polyval3Tail45 : Box := ⟨1803530617830117133236512525697080279738966428113588186968,2857392374221018867449855652763648063841909507266203563163⟩
def polyval3Tail49 : Box := ⟨2673815528936636079817424241244872053839284238262849088891,3359927665276958961076266508998432956028447156914438495700⟩
def polyval3Tail53 : Box := ⟨3964052183036533026756605932411358851214675593040690098079,3846859302908793683482446220848414786424656188525234336445⟩
def polyval3Tail57 : Box := ⟨5876886247304417571124617554558423592151189782420402071885,4234637607370405903145821627777661503301600365436144723317⟩
def polyval3Tail61 : Box := ⟨8712749068126389492812535493218846795654685146110741536262,4377005545996490824207606933540422075161961695345097310287⟩
def polyval3Tail65 : Box := ⟨12917043674131905883314904511267126947769837600120307415237,4028144639799249051091856676320650541847597876167343036083⟩
def polyval3Tail69 : Box := ⟨19150100438988592507535234517062043088044269040389805821709,2786094621309196711457680182470405913465907905886230449410⟩
def polyval3Tail73 : Box := ⟨28531250000000000000000000000000000000000000000000000000000,2⟩
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
def resval4 : Box := ⟨120583906817201361138405800215628127850544064583833459763,8431556594420340274867072774074556548865359217701143004⟩
def polyval4 : Box := ⟨4735187156732514455292011861549553164161338147660868565758,1993615078254692925476768671690882211620971588560487748259⟩
theorem cell4_lo : Holds Q cell4 (15/16:ℝ) := by norm_num [Holds,Q,cell4]
theorem cell4_hi : Holds Q cell4 (31/32:ℝ) := by norm_num [Holds,Q,cell4]
def resval4Tail4 : Box := ⟨-3740046848208403109638009525833617583147996132089948641,9173759829798631627764631345775782031906133518030558881⟩
def resval4Tail8 : Box := ⟨-4531950125781601348163947326696747564194941217935355248,10130602338462360051004190067313255989866119671196282854⟩
def resval4Tail12 : Box := ⟨-5491432863981617757397965429531451519291704979037296314,11156592054865125488049921360069400196167332840059498644⟩
def resval4Tail16 : Box := ⟨-6654052672469988642885573128489287875242810194958591184,12248299712924989908986481160838480161465712239749810040⟩
def resval4Tail20 : Box := ⟨-8062816766522652336539430570116171220378375760915014451,13399124060884581603300953916895967115733832705310284353⟩
def resval4Tail24 : Box := ⟨-9769837632858279546616235188885559852978820336766701167,14598288338331729290393974166193310712715156884447680657⟩
def resval4Tail28 : Box := ⟨-11838260763747904775789835202355542537057143300314054419,15829580095709037428710686618857939022133096910055393089⟩
def resval4Tail32 : Box := ⟨-14344600512003826130551005839533405469062865096755457166,17069773278138382471453461713465885722022011117196400897⟩
def resval4Tail36 : Box := ⟨-17381570481966301925797747468372786584549657352054270092,18286658406572406481700148779384582349897263268584960967⟩
def resval4Tail40 : Box := ⟨-21061513157284758082139235836178691337198421180051176532,19436590053176470960719065052384997975211573540749598743⟩
def resval4Tail44 : Box := ⟨-25520555633031490093930651027659820804942480366995159832,20461440522998089854295219103953486958859071015204159597⟩
def resval4Tail48 : Box := ⟨-30923645179472019350956583852863276499758336292974645452,21284823930927065030347731069730165062699054420381921973⟩
def resval4Tail52 : Box := ⟨-37470650911227481821493492012563007716981910050348791401,21807424742608034465298485328556383594936685004670335990⟩
def resval4Tail56 : Box := ⟨-45403757272545578852247265067904576611621640229895747879,21901228165572441847966919089166963194237008745248535422⟩
def resval4Tail60 : Box := ⟨-55016422835774774789399091945604976677188791189863558444,21402405118055100318060459487998106001371183826436490842⟩
def resval4Tail64 : Box := ⟨-66664235795534514815687614039602560463949100630240443142,20102550150211276830319720347155444089792681781638497051⟩
def resval4Tail68 : Box := ⟨-80777747735622456125360541729585929054174666256506585922,17737901741937130512166768752552559016047843997092058274⟩
def resval4Tail72 : Box := ⟨893697775838152538605026324720226490716147601178326029170,713476120641609198397628350291566656504701692432342466⟩
def resval4Tail76 : Box := ⟨-50437964503799272629570875085694444900812001081395083,126746376829178668980675844076799639513251940327071959⟩
def resval4Tail80 : Box := ⟨-61078585480572475643804089671355602137663119102970229,140062860995751923702377440031761842362441879925297177⟩
def resval4Tail84 : Box := ⟨-74009848332170377152254708974028449948937152819076291,154368381878423239700692547190188946525543367057952729⟩
def resval4Tail88 : Box := ⟨-89678858191360887021058492431708030148400102152847493,169624320751218487419964480686218093021224134267475264⟩
def resval4Tail92 : Box := ⟨-108665235611891192743016371345451568295549229680194050,185750473573813366951638438452724406391677622344360405⟩
def resval4Tail96 : Box := ⟨-131671317730110452012501593176436886107300594762524321,202611548252481512396356828261299312703200001924622146⟩
def resval4Tail100 : Box := ⟨-159548137131048431313229988078523952483326460037071443,220000341442327107255617442096609838886800197360435037⟩
def resval4Tail104 : Box := ⟨-193326902933900500343237651932380882101367980346972812,237616654893756725275774872530922331019016938324908716⟩
def resval4Tail108 : Box := ⟨-234257146903036255913647464458825414092543692761658861,255040954702334388608413889398477749342063694215999399⟩
def resval4Tail112 : Box := ⟨-283852945670542534851948490234775927785333018133128718,271701553024076351940303912904408224498394124631043763⟩
def resval4Tail116 : Box := ⟨-343948928905868335815988488586339902895312435321412805,286833818885691026504796746826861779551697543273354024⟩
def resval4Tail120 : Box := ⟨-416768145266321976406993468319853595282881835682628520,299429592032864669109743414174329808157794828900782455⟩
def resval4Tail124 : Box := ⟨-505004296600868187215652241159175344544048140477611500,308174568401911326721548770081133916617776097553067806⟩
def resval4Tail128 : Box := ⟨-611921382384850078063622039717954866268039369599505366,311370932082449262125394068594081161469582311296461870⟩
def resval4Tail132 : Box := ⟨-741474440396216545379645295641691514242285544080258870,306841907510231466348264101372561698030070439200559418⟩
def resval4Tail136 : Box := ⟨-898455850082785843934197251530045241522587674874611014,291814173956120280178958212155387156509524533632216613⟩
def resval4Tail140 : Box := ⟨-1088673096709059700317719371653584633700681602132134239,262773173489435072054904136895683625331408246309385031⟩
def resval4Tail144 : Box := ⟨-1511137781473764259922863403874465257279072019530054458,209731867764190208258310522285771008085193931314127806⟩
def resval4Tail148 : Box := ⟨24101648298575378391643076264590700102837391585,51195248039999290675015848750545723977350987923⟩
def resval4Tail152 : Box := ⟨29106660597068297017589894013487176747251752821,56294189649692368135207975476091018178377080216⟩
def resval4Tail156 : Box := ⟨35268981286309507140249635591065659166915204814,61696090851530392195411120793038557155066144428⟩
def resval4Tail160 : Box := ⟨42735960721510204032744179456767329684885370029,67359259074784393830363051530148858904033885234⟩
def resval4Tail164 : Box := ⟨51783813203710631947484591352409743687705505711,73219522067624266660265701627677724040999463701⟩
def resval4Tail168 : Box := ⟨62747233586049787481253009892429232105448612495,79182941564786258821202668811959112941591493112⟩
def resval4Tail172 : Box := ⟨76031776710104634980710174939162443948716055115,85117320428956694383239793560620173671468258755⟩
def resval4Tail176 : Box := ⟨92128859541951611575176742672403215723409505822,90841615067384150678026913380849903491741500612⟩
def resval4Tail180 : Box := ⟨111633939489048245529606363336914833458217236478,96112769447682869669180950418131607625084453145⟩
def resval4Tail184 : Box := ⟨135268541343114661627945386853619171579560675393,100609379213149641891417926414328959548690067445⟩
def resval4Tail188 : Box := ⟨163906947661638234246883189787413607460993041496,103911462991942353879753433864898604552302200450⟩
def resval4Tail192 : Box := ⟨198608539908843353744786042619382827406517566216,105475457931475294967706487211745436689072979749⟩
def resval4Tail196 : Box := ⟨240656986707798049720287688232007158621056045519,104603361589002962305611464761162432344540219620⟩
def resval4Tail200 : Box := ⟨291607728841162973595851179627578797876782092969,100404705067396138075154233286935511769407898711⟩
def resval4Tail204 : Box := ⟨353345517548383199955239841323368406724362852737,91749753591202630148389677033763026806625891945⟩
def resval4Tail208 : Box := ⟨428154134555080835632943286586530863610878787837,77211979513294510376370840879313270592284866720⟩
def resval4Tail212 : Box := ⟨518800873146119957523084452466256170953639012856,54997425591319683310133468314927299312970294930⟩
def resval4Tail216 : Box := ⟨628650943022450036821262933085520907265443518555,22857556600176249429829244088198635352255020862⟩
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
def polyval4Tail5 : Box := ⟨1085110464885572925179434948835186336584141832799974329762,2193863363177640722027103635469628736119004904557315526434⟩
def polyval4Tail9 : Box := ⟨1314842204722971815224255526118186403676426211283946291617,2408138614188572603526511571279752550063301100964116242476⟩
def polyval4Tail13 : Box := ⟨1593214285134920525260625997250317147524925890148603824766,2633899483735679249025583242883334492125045358760543385436⟩
def polyval4Tail17 : Box := ⟨1930521966559575840699896155627451464036160823219898397358,2868989952830531529688807834033141613266987126238291463647⟩
def polyval4Tail21 : Box := ⟨2339242811304475489623946967353081491104359292734747927387,3110176325224526616807771730267190072972006544832300533685⟩
def polyval4Tail25 : Box := ⟨2834496071542525075205531690183193912942328452683757680722,3352834937178483872739819867250377092321663998593693612583⟩
def polyval4Tail29 : Box := ⟨3434601974948318153290387744589262482623743581329118119658,3590562368689390873706707845615716766537996018965400031213⟩
def polyval4Tail33 : Box := ⟨4161759419867274403492280514845606422062624007206424019535,3814690197189895255528881757714291323985654084426057681215⟩
def polyval4Tail37 : Box := ⟨5042867148853432160502704224678247903221400026685569269373,4013682332593485378322915323056112900309157984747955594075⟩
def polyval4Tail41 : Box := ⟨6110518777127238691973006946876428508649078783350885165511,4172388085908559091933848070776287791032186398383254463090⟩
def polyval4Tail45 : Box := ⟨7404208483682539978533118353342852320576253429511332696561,4271118170302182293147293000117900946813701549272055403756⟩
def polyval4Tail49 : Box := ⟨8971791965527731298506309850731616554450781995104282021004,4284503583278071862253699734000618347445623616327797334552⟩
def polyval4Tail53 : Box := ⟨10871256698146634936580503226103028427195878281698771796397,4180088492038097037037386141335514875581861807638014116059⟩
def polyval4Tail57 : Box := ⟨13172866987007354487828948227862473403546296194705897450511,3916597501773242424381924159496608798785282408443566087865⟩
def polyval4Tail61 : Box := ⟨15961763159080913190805192646036106657753791291473023149186,3441804616624924997762640072859013191984570166600070757170⟩
def polyval4Tail65 : Box := ⟨19341111042745083631718386518352481891150542249471693050039,2689915305336928689759158651738218504226881838793325531001⟩
def polyval4Tail69 : Box := ⟨23435918511512492005904461260210892072155104558777025491594,1578353740508119908664812037163017727943952732957263246677⟩
def polyval4Tail73 : Box := ⟨28531250000000000000000000000000000000000000000000000000000,2⟩
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
def resval5 : Box := ⟨110195872319972607376491010129662498048524921452001204780,13000129353641920731549521404640869607979830519793198566⟩
def polyval5 : Box := ⟨8987648186376757394483242713336347157274306257225491257954,3992199764653864460221285546602600049079156012542730032150⟩
theorem cell5_lo : Holds Q cell5 (31/32:ℝ) := by norm_num [Holds,Q,cell5]
theorem cell5_hi : Holds Q cell5 (63/64:ℝ) := by norm_num [Holds,Q,cell5]
def resval5Tail4 : Box := ⟨-14798759055591119322916767080864729134594481894861347154,13232657491827954454276592030971550548388410020812809350⟩
def resval5Tail8 : Box := ⟨-16271478771686423094201215096962720006222402217982266774,13582604324876693637712450274735612497679981605107748192⟩
def resval5Tail12 : Box := ⟨-17890680119425667808340845524834447284510759602421235876,13904510684766855125895583998342312973128928386388986028⟩
def resval5Tail16 : Box := ⟨-19671010820137678614933357807293366073597286548272289978,14191498195359451040003547968308999267454969446535458179⟩
def resval5Tail20 : Box := ⟨-21628505126848921247066406375678463308813073053091290541,14435738798781516501100905379973188162789105146338613302⟩
def resval5Tail24 : Box := ⟨-23780792878383219215611046116840197036484031296840516355,14628342408436179173819898973643486991550519542613087833⟩
def resval5Tail28 : Box := ⟨-26147258287515041780053148893698882564663512729377395020,14759232821057562444128258326048871908593770997138843584⟩
def resval5Tail32 : Box := ⟨-28749214521585169807209811341398181504352972660672819325,14817010084100201518969376642655001210404012518177927612⟩
def resval5Tail36 : Box := ⟨-31610095655909527142769749155790804007350615733273366524,14788797892681007854522673080879725295630496790542422641⟩
def resval5Tail40 : Box := ⟨-34755667728784150582386726865251733523955184988633642179,14660074443478568864532539900140772370938366831748539704⟩
def resval5Tail44 : Box := ⟨-38214260798917254294842137746714732333508545134725562163,14414485011115593046234879016598509637067439686173826623⟩
def resval5Tail48 : Box := ⟨-42017024095274096471818102947904867107773824745608907158,14033634334212020242989582684016751698750187015923551310⟩
def resval5Tail52 : Box := ⟨-46198206557298235058852705323466739795263638645015830811,13496856701838211811746497975726258132213492298824532744⟩
def resval5Tail56 : Box := ⟨-50795465292146821277353267847215418976357082787104848521,12780961414692325140428247864956653484041908620721395563⟩
def resval5Tail60 : Box := ⟨-55850204726996232412783944286975038328722846861144662321,11859951056962214508570391245856554477573299105002196366⟩
def resval5Tail64 : Box := ⟨-61407949493211211889408841924334396206373032551852685946,10704709751823538825164556183627465519317921906260112095⟩
def resval5Tail68 : Box := ⟨-67518441629020615841658476726418972516321749618397086944,9282653082811858287900352514746192740133905072562717771⟩
def resval5Tail72 : Box := ⟨893757638672949374015910264208525779845413988064959517990,709655581707835988685238913089806360827798260281094770⟩
def resval5Tail76 : Box := ⟨-203962316358436304996213090763550124627602507119364979,185586174568514414132381244704306656880126340869544733⟩
def resval5Tail80 : Box := ⟨-224224628854953873031913390661882912869524094421657900,190618858664476928621166312276499719660445321994455821⟩
def resval5Tail84 : Box := ⟨-246537584755219763576110014436987028089728221246345870,195278957985543851661040377692346648486213161848352930⟩
def resval5Tail88 : Box := ⟨-271070941121070198992151125585113119434087775373217883,199472442431894318261310629032936406570583503106199310⟩
def resval5Tail92 : Box := ⟨-298045651714797036799573327230430554242784687002507618,203092387237936010522189722503874236504785325992747889⟩
def resval5Tail96 : Box := ⟨-327704659668495224583238547749159046604562602983931168,206017294275681723153234099361624853980323464888657554⟩
def resval5Tail100 : Box := ⟨-360315083781887280021676685144545865667382679772851699,208109386085302042661805393926142949920837425045295599⟩
def resval5Tail104 : Box := ⟨-396170624281268701336473825759429034907287289367901284,209212713533592046332619677886941711308969681782892720⟩
def resval5Tail108 : Box := ⟨-435594207980531859863840350201582674033975917376019769,209151057453749782387247874875988778704866781174882113⟩
def resval5Tail112 : Box := ⟨-478940896666472074958169792878818616499991830159343466,207725602613776058511606406059827224106451078686821243⟩
def resval5Tail116 : Box := ⟨-526601084902249723318961985136820684390235481067746034,204712360131262863238415657087404497406024294017537894⟩
def resval5Tail120 : Box := ⟨-579004016049480171318383474729579037099168633621001247,199859311996045232188515221857405820092255149706276130⟩
def resval5Tail124 : Box := ⟨-636621648175405176297644973167071608420561400114795875,192883248656284915945075004435197318989306444745178054⟩
def resval5Tail128 : Box := ⟨-699972904662779983332798290253252547489040249987572237,183466267642857291961210839564398902436246053205655042⟩
def resval5Tail132 : Box := ⟨-769628347804922383388763035795664091183887497148090885,171251897923718839402796888695785962306938410848525508⟩
def resval5Tail136 : Box := ⟨-846215317531270155760543608843361025983691104210337428,155840811061416302352029128180931700497460988316013867⟩
def resval5Tail140 : Box := ⟨-930424056827434634133089983487394821320849243253451922,136786059663561486935300477916271383217289616731549991⟩
def resval5Tail144 : Box := ⟨-1210488405306825815408783857058111777072205214342415949,109646042068433280042257912263617878432970698164001484⟩
def resval5Tail148 : Box := ⟨131704780603090171107718519056142874711342302794,98986188044955302392726963329018277870243125509⟩
def resval5Tail152 : Box := ⟨144722390191003380442433812452215028063106731163,100881746777108771978363905055359261081231760721⟩
def resval5Tail156 : Box := ⟨159123949196096837923923735445980649949425027350,102449327817977483815603824327374815888504854107⟩
def resval5Tail160 : Box := ⟨174958632398217273696199219651467191759366269270,103622097172861963473095044257466511040383086005⟩
def resval5Tail164 : Box := ⟨192369050701625738758371333925086902095394163567,104324953266997615714897380114794698429931104114⟩
def resval5Tail168 : Box := ⟨211512008070668384530607555905165340616001363036,104472992494396884146076178331850876001742523880⟩
def resval5Tail172 : Box := ⟨232559912287951044584719131406233662450073727115,103970382381109715775716637884061824346460812392⟩
def resval5Tail176 : Box := ⟨255702327715168837456169194086137402185601514997,102709112788396231585524245539467949699364629798⟩
def resval5Tail180 : Box := ⟨281147682572217487357297917451926410985777534438,100567612361824432339777926213846611773859275928⟩
def resval5Tail184 : Box := ⟨309125146110428996198023062803618190220788726614,97409216135000738555333093231159147318136828772⟩
def resval5Tail188 : Box := ⟨339886692586371620659691506779168919309977554245,93080468750079328008512995019637447110019651244⟩
def resval5Tail192 : Box := ⟨373709370625042372108006813462184075163917650804,87409246163794103729669555121034756801056365503⟩
def resval5Tail196 : Box := ⟨410897798411084817148229697765830218066058077972,80202676952723672214522237577338334566847128904⟩
def resval5Tail200 : Box := ⟨451786907180546575338985933481021918945513523369,71244842398551197586240324064187321057892522490⟩
def resval5Tail204 : Box := ⟨496744957721967578892326907226311148044496521323,60294232405300255186778440474049743632182592222⟩
def resval5Tail208 : Box := ⟨546176857054488614334192510400838814945321583419,47080931956196328851153182218515492094235811246⟩
def resval5Tail212 : Box := ⟨600527805402217747522402522095386504134010050055,31303510225603530287273596251684135680525732644⟩
def resval5Tail216 : Box := ⟨660299068346727728372455436300265325015920431163,12625182569808063337719837954158671957901481485⟩
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
def polyval5Tail5 : Box := ⟨5661529272716687597270365361220039862272356242359229944810,4072465896975672530246157191893476475129055187956361586270⟩
def polyval5Tail9 : Box := ⟨6224914875192263812622080824072800086629221485964595497383,4141980775399771857216261065501872986612946993415138220251⟩
def polyval5Tail13 : Box := ⟨6844366286951400787566963590259780315509409364819568756191,4196583257440455298197478157367959150764162237185840705495⟩
def polyval5Tail17 : Box := ⟨7525460317260919529266028551953894585610864554347468553008,4233369997329510787283632335259966227230935918544744690666⟩
def polyval5Tail21 : Box := ⟨8274331123195246335632383683125270650539030025088057694674,4249056454240614151152354187309339352993527269848574308165⟩
def polyval5Tail25 : Box := ⟨9097723282022023680557661100729293354423857480963390676513,4239932948978494723773250894514284260298389422592866227098⟩
def polyval5Tail29 : Box := ⟨10003052534871648373416454941428038158424077015136635454548,4201815967071674750217801603816718100786005712264298100563⟩
def polyval5Tail33 : Box := ⟨10998472575345569106265244735132051832754831228217156779456,4129994200437063238386394125368438630441311216917495994861⟩
def polyval5Tail37 : Box := ⟨12092948484367901493735584034481674410267281701547972387947,4019168777023705575865252429718135700654631933625521244986⟩
def polyval5Tail41 : Box := ⟨13296337472658663461823207472273432167452576623523005169005,3863387071298212480028067199322367955358614438128366881399⟩
def polyval5Tail45 : Box := ⟨14619477658021952957347154381466307595914241179070719208905,3655969426146287055546944861720654758698434125143291095148⟩
def polyval5Tail49 : Box := ⟨16074285677006581760573283015321467379363494981558675666980,3389428048156626796695081591918321085318749233782575171376⟩
def polyval5Tail53 : Box := ⟨17673864010061948888913969475268821854348869763605192979884,3055377262688474682295284445174673115524647141174686828114⟩
def polyval5Tail57 : Box := ⟨19432618986794876412144946435327234370246819750493899882253,2644434231901518030158055481735224860724212575689253832293⟩
def polyval5Tail61 : Box := ⟨21366390534121670320870624459404319373917603305175897346496,2146109147275695113192184310993964340941914191619152767833⟩
def polyval5Tail65 : Box := ⟨23492594835901647934580679801269162315206905631263530130162,1548683807219142639025557522402822667760704038205812445102⟩
def polyval5Tail69 : Box := ⟨25830381453907485989210316175745422897477637037288702614592,839077370634201038762485929840261674114232914769967378042⟩
def polyval5Tail73 : Box := ⟨28531250000000000000000000000000000000000000000000000000000,2⟩
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
def resval6 : Box := ⟨96708181137610736460889585728058517012652235405621353987,11390286780091869036932423241190813678731048776152215959⟩
def polyval6 : Box := ⟨15992912513499323432702375230566478407369826778891243762048,3995504308849375151123442427775297194560208254909059700631⟩
theorem cell6_lo : Holds Q cell6 (63/64:ℝ) := by norm_num [Holds,Q,cell6]
theorem cell6_hi : Holds Q cell6 (127/128:ℝ) := by norm_num [Holds,Q,cell6]
def resval6Tail4 : Box := ⟨-28240153858839440181790670686576833081568114388708087501,11169892079540780208627974018163777379657513109327068443⟩
def resval6Tail8 : Box := ⟨-29603688708558649046009627677320251393390356253283457239,11062422365399961121785291262539044472016540580949158686⟩
def resval6Tail12 : Box := ⟨-31032988857883111564146053946441646648521050255506744458,10929152011321673155800799408410601033839237882028756813⟩
def resval6Tail16 : Box := ⟨-32531297253979689816565451291904904293076676266996583740,10768177898242215187729503263116666354749415998885931679⟩
def resval6Tail20 : Box := ⟨-34101945702780834589518571809079514166068939458239305865,10577484603251740490300027630538164282239326903382070507⟩
def resval6Tail24 : Box := ⟨-35748426865244161431048399621373219399474420852034702623,10354937793419224018212003696816598694913533770143683541⟩
def resval6Tail28 : Box := ⟨-37474402032007821012043032205032448210644992053609082625,10098277796067477404068347119358526888382733364848578548⟩
def resval6Tail32 : Box := ⟨-39283709265033146439564063832535436750099128902729878273,9805112836789025376702217380663018997871502101561388451⟩
def resval6Tail36 : Box := ⟨-41180371932327488410531787080494108541022472641883755121,9472911928344133583166481888530662370305341573532960201⟩
def resval6Tail40 : Box := ⟨-43168607654733255649533472784043041939264786966447262067,9098997392863428519993450596998033018232066279902102872⟩
def resval6Tail44 : Box := ⟨-45252837684678220420876394587656519464239855548572651165,8680536998906046143790780533816778198053057914777906845⟩
def resval6Tail48 : Box := ⟨-47437696737742676173008991590746671239675094052540214551,8214535694009774591466675946727160854917131704793798668⟩
def resval6Tail52 : Box := ⟨-49728043298905965396351956767784671364240216429564198864,7697826912410276441468289306459580208350212080714541341⟩
def resval6Tail56 : Box := ⟨-52128970426390408357560289713219154048997104188957215869,7127063436599993589469239136639797139119654884342562777⟩
def resval6Tail60 : Box := ⟨-54645817077116107762134750901544462456287383324487612541,6498707790340989004778432040826094655518233754591355257⟩
def resval6Tail64 : Box := ⟨-57284179961412521862123925009728518021351410588230217089,5809022139105916090764891725054537917370259928465734641⟩
def resval6Tail68 : Box := ⟨-60049616667954512444749739035677737617888815025618645138,5054051347160172453062966604866330033358565194558617475⟩
def resval6Tail72 : Box := ⟨893670585835167393000319561973692428801147862476251942552,654033184336450763400722505083777166515084760792304779⟩
def resval6Tail76 : Box := ⟨-392495656086030203812815021836508128935382916174600577,157570591401600700526550063163329109456305102799610871⟩
def resval6Tail80 : Box := ⟨-411413109223347171020932325635251844420486603296853781,156151430581600265466136814464950304657728177751928405⟩
def resval6Tail84 : Box := ⟨-431276605529154862863266246615582129581518013603065231,154376225899643766192024679427983137928446504116946433⟩
def resval6Tail88 : Box := ⟨-452099136095823451358967884058750052231818363121912450,152218462981710289832259616469886827370774981800879779⟩
def resval6Tail92 : Box := ⟨-473927002389297622517261730888903839974965728075331820,149650210862626228952881396020845394447017282410336178⟩
def resval6Tail96 : Box := ⟨-496808743173755533428645441697797807539789449212110782,146641888548038859103271237129117654406838978066320051⟩
def resval6Tail100 : Box := ⟨-520795240721781559386994681808875529755245152675809114,143162175720742592651445502357932202597443990403375976⟩
def resval6Tail104 : Box := ⟨-545939833960607925056701845583984664285709050432964271,139177918848802700189001993541598959298540787608900908⟩
def resval6Tail108 : Box := ⟨-572298437082223892768209399517306525853791277471801130,134654032444486143424476001477953942825254718185364634⟩
def resval6Tail112 : Box := ⟨-599929663880120266005612102071855256348985827934178018,129553395229786644377696047106106204725651639315594486⟩
def resval6Tail116 : Box := ⟨-628894958089154954928804192137836845836587656123328604,123836740952236467046100390286139185348857795854395040⟩
def resval6Tail120 : Box := ⟨-659258730018377168573525453868315167140120538871972920,117462543581991440498521665277467485940410266730111701⟩
def resval6Tail124 : Box := ⟨-691088499780641517030268707860921579528142904316876994,110386896607845725791576560958807774411556006535698563⟩
def resval6Tail128 : Box := ⟨-724455047437512861093354981646453263365576738536311152,102563386135848305645582789743933985905471596112344867⟩
def resval6Tail132 : Box := ⟨-759432570393392419550090175745895058316879474697806048,93942957479519495152770469619848759876181826897613524⟩
def resval6Tail136 : Box := ⟨-796098848441721924029939631256330697133443755745514656,84473774913134225879539874105090702832215587517518722⟩
def resval6Tail140 : Box := ⟨-834535886888766625469994300308969227797306234016177126,74101059535556239910282376610056910049114366819346217⟩
def resval6Tail144 : Box := ⟨-1060132925691823315406513138755759962201466729502324034,59586080641389105705676896103706888512645644372021465⟩
def resval6Tail148 : Box := ⟨303528348782076525906711450438885176134411384911,97671672032940859509033797485760407701394269081⟩
def resval6Tail152 : Box := ⟨318098663403699294341954859496198343249998130488,95804000673027185993579297503649360485253386284⟩
def resval6Tail156 : Box := ⟨333456831207515199942767255708861977043920166147,93636917657948986224707936833348931878882915268⟩
def resval6Tail160 : Box := ⟨349556510558537059123274763688848979169654418304,91148724769832758425246465176489380376412588135⟩
def resval6Tail164 : Box := ⟨366433500946920714313149051935347821881374663257,88317019195287502419722057286608318985481944312⟩
def resval6Tail168 : Box := ⟨384125331843108968317397340431390315943687306936,85118096625636024580185782362578858319886409021⟩
def resval6Tail172 : Box := ⟨402671344684044307355961965238547191190464827819,81526881394389281759289073997146393320525748227⟩
def resval6Tail176 : Box := ⟨422112780356496059752169790633611687481909443108,77516853035626794925581136734475707292070126315⟩
def resval6Tail180 : Box := ⟨442492870904681899647888364373806247022399248699,73059969066091610551844910017108996873524032498⟩
def resval6Tail184 : Box := ⟨463856935665639669544534098516386829111816476931,68126583801323379996617476792806399658347546331⟩
def resval6Tail188 : Box := ⟨486252482046125534488171401800895679548750131785,62685363006769878178776011880419413578528554101⟩
def resval6Tail192 : Box := ⟨509729311165136692456797217620321407882297294753,56703194174964948230758605393769852969699367177⟩
def resval6Tail196 : Box := ⟨534339628596976590883391556702833869637962005268,50145092209525123730410090415264400658108122140⟩
def resval6Tail200 : Box := ⟨560138160461122709535402478986030114955513955632,42974100285874480816318434335523340903420670142⟩
def resval6Tail204 : Box := ⟨587182275117046867799579039002937563252844238936,35151185647232867992660510938757807652509831675⟩
def resval6Tail208 : Box := ⟨615532110734687371086312174272557618640518050065,26635130082466383995779184329507095685442236471⟩
def resval6Tail212 : Box := ⟨645250709269744452942178632919823280530391386103,17382414810226913972657175177837233051504398401⟩
def resval6Tail216 : Box := ⟨676415786052426477884827770971672228201492841944,7346748390175772072658794452746693985472247589⟩
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
def polyval6Tail5 : Box := ⟨12741827711637609911307437810297351733287428315479845868040,3921515124978000569503666937261569220775056993191823594884⟩
def polyval6Tail9 : Box := ⟨13357015531301639733480603484504161785544836868150101898790,3837386128771355886102499539067676640867946572190576397330⟩
def polyval6Tail13 : Box := ⟨14001907604116393857928996710707350074376611591564644203282,3740479986370935812044545269925980032318993981706842180956⟩
def polyval6Tail17 : Box := ⟨14677935808185802426896720801021636543835883384716970609571,3629902035689520818716758172856198880549962807042514991785⟩
def polyval6Tail21 : Box := ⟨15386603431513029024198854520514503927699681400847368741427,3504705576827177498310163164753815244732775470757723773418⟩
def polyval6Tail25 : Box := ⟨16129486342801400011044110780301602092162263217141389695595,3363889067882962842845771004953540311356264309073405467679⟩
def polyval6Tail29 : Box := ⟨16908236495507977720435223119787630127577319381410254230555,3206393186009252591001096132368465456072570094600610904749⟩
def polyval6Tail33 : Box := ⟨17724585601302802900833000232428431100578158475189490637657,3031097737295021570598475327711931780653798992895524048591⟩
def polyval6Tail37 : Box := ⟨18580348980887154296530933400691570484022186848138854090978,2836818407881424690247895312030672491537032758719800806699⟩
def polyval6Tail41 : Box := ⟨19477429600733743612801488930948676376694603046259982479453,2622303348339086908385540079749754713520685398380520719789⟩
def polyval6Tail45 : Box := ⟨20417822304725370144411343719173696940335213491494282271953,2386229582941960424076285394525783733945970617283493367169⟩
def polyval6Tail49 : Box := ⟨21403618250101956865130809736376550563348053765280313501338,2127199235058695194878409832951961118521347381682361250201⟩
def polyval6Tail53 : Box := ⟨22437009557580211631550621859022796438712574641620423177089,1843735559448252812271528107600283149174288216413030041500⟩
def polyval6Tail57 : Box := ⟨23520294185986414315478320887514931204606726108759492527975,1534278771790983271562641851824393196868887421840983526606⟩
def polyval6Tail61 : Box := ⟨24655881042242112585515622756639773145827907090707398024880,1197181665308539083841369321005346657347241202862131027047⟩
def polyval6Tail65 : Box := ⟨25846295338097133682321784743278497072413368637081725826705,830705003823522918224140266077554457775451613660999698046⟩
def polyval6Tail69 : Box := ⟨27094184467629570067252242758400606250545828554577837751126,433012672541885313361126224772035609472146679635995587068⟩
def polyval6Tail73 : Box := ⟨28531250000000000000000000000000000000000000000000000000000,2⟩
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
def resval7 : Box := ⟨81654390929911628030371972598945949789555136041725932828,18126110411783518340960560581539440655672694914687057727⟩
def polyval7 : Box := ⟨25265701065131727170913877045235706604201448845472914849765,6979111126885293264841240539508494977489085257360161765349⟩
theorem cell7_lo : Holds Q cell7 (127/128:ℝ) := by norm_num [Holds,Q,cell7]
theorem cell7_hi : Holds Q cell7 (1/1:ℝ) := by norm_num [Holds,Q,cell7]
def resval7Tail4 : Box := ⟨-42650734226372198512824884861323847438046854582356083238,17326623328337986277786211621906670694709142090911176003⟩
def resval7Tail8 : Box := ⟨-43323776728138738402139175832910118676948728634236783857,16653644914126765398238009689112505381260331607456312980⟩
def resval7Tail12 : Box := ⟨-44007373432606776929904100859248037104222258392169384233,15970048217570182523405106791429656337689475438924445956⟩
def resval7Tail16 : Box := ⟨-44701756456533943866157843872379592466838806388219170613,15275665193650324292016980239236945951592357113204184153⟩
def resval7Tail20 : Box := ⟨-45407096003106548217425568535098775633234650236035699278,14570325647077749282245986328848462519953059450415946605⟩
def resval7Tail24 : Box := ⟨-46123564952982166414007360476730003938221618607182456797,13853856697202131475802065293957375636316801982198812922⟩
def resval7Tail28 : Box := ⟨-46851338914658159007650566203011572437101656455300139064,13126082735526138896401631832574954838567727634281055098⟩
def resval7Tail32 : Box := ⟨-47590596267521140131856977601571252380713582189211742757,12386825382663157773359154994479227846263140719489304430⟩
def resval7Tail36 : Box := ⟨-48341518205568281292626151945582835661120849510443143153,11635903444616016612685260418405922955434133207081326123⟩
def resval7Tail40 : Box := ⟨-49104288781818455533494988714403812440667525755880817078,10873132868365842371554882567005559433459878230735352204⟩
def resval7Tail44 : Box := ⟨-49879094953424135287578950539920335952924266184281901473,10098326696760162615846565886408904277866451708871993429⟩
def resval7Tail48 : Box := ⟨-50666126627495101288802769248617241790864344151774389644,9311295022689196596542032744088797146717529060418111216⟩
def resval7Tail52 : Box := ⟨-51465576707645193691498378894057213003231206526315028948,8511844942539103697752842569623648727395928626198407631⟩
def resval7Tail56 : Box := ⟨-52277641141273479025396533284825747019949831110552281398,7699780508910778483804879832930961060860652667022277211⟩
def resval7Tail60 : Box := ⟨-53102518967580392443313472466395683692514157536165990771,6874902682592137015337600379268228619613034093366798830⟩
def resval7Tail64 : Box := ⟨-53940412348913688350626069217458362631775414487466986787,6037009283243866396983360459516472850117511405204846869⟩
def resval7Tail68 : Box := ⟨-54791219581392501254498590755015895220229099220537192157,5185888658716005473323157969011613771937173998874465745⟩
def resval7Tail72 : Box := ⟨893527446810186796983802166009227741118284526981533627726,747172940948042355042684921396011496377312600699699007⟩
def resval7Tail76 : Box := ⟨-594701091915002339051667676656721412244798690993184907,244122016375579956402298541011778388049742328798182210⟩
def resval7Tail80 : Box := ⟨-604053093869580205698140313730557852300860201282599466,234738696899239083836054212649732333150308038384798747⟩
def resval7Tail84 : Box := ⟨-613584317934002676770117642851845755919676990674842817,225207471088106164410593882945065441481752787830360696⟩
def resval7Tail88 : Box := ⟨-623265934918582574374346598284837365020208258988755862,215525854102507832816146352326224103419760138270756694⟩
def resval7Tail92 : Box := ⟨-633100316087853587082019968624547296176292744439709407,205691472933233933717955954920998555006113135778746421⟩
def resval7Tail96 : Box := ⟨-643089871874516354851674251421908803863481959530836436,195701917146571136876899824243121697550202161638164511⟩
def resval7Tail100 : Box := ⟨-653237050745987403813889334830749218785243991873235504,185554738275100087055592594900953779900229789942967215⟩
def resval7Tail104 : Box := ⟨-663544339803534778016962260139607816387120167915185294,175247449217552712788573343902259859215382858641440421⟩
def resval7Tail108 : Box := ⟨-674014265391870647863697398772750589264274245883536289,164777523629216842932273600571272508030947357521818686⟩
def resval7Tail112 : Box := ⟨-684649393718365277092350880434571030421823125414426739,154142395302722213703604286488524178031966143589614196⟩
def resval7Tail116 : Box := ⟨-695452331482031460652621831813506218060501709734377442,143339457539056030158402019181047412675014744570813203⟩
def resval7Tail120 : Box := ⟨-706425726512433575514204040365334554320302224800935149,132366062508653915460097504538503155853794639369412961⟩
def resval7Tail124 : Box := ⟨-717572268418677845446212900846172491263917722210863759,121219520602409649256096417360914591320252045145163082⟩
def resval7Tail128 : Box := ⟨-728894689248643120854585365496436695868866002229318651,109897099772444609880988600515443947836772165645052254⟩
def resval7Tail132 : Box := ⟨-740395764158665748304058242915723770497540006152522011,98396024862472607939424317309898666103212461911680680⟩
def resval7Tail136 : Box := ⟨-752078312146340117509658454617728925759491753722818052,86713476925473367712474674938401030265456745650122031⟩
def resval7Tail140 : Box := ⟨-763945663485422017804305334213833211348028568562608909,74846577954576012154352890831632102988762072127352546⟩
def resval7Tail144 : Box := ⟨-959884462927939426915896019808018101189103663705821399,59642367439051445801629081646537929941367898438313490⟩
def resval7Tail148 : Box := ⟨526744775383325440870709954992825015759465562082,168012800338638978444045197716231838978130708842⟩
def resval7Tail152 : Box := ⟨534974427670677800684417588775327652914444782418,159702145123299714727515265112306989252775705775⟩
def resval7Tail156 : Box := ⟨543415674356374034637672544260459307067224686998,151260896951963435597645208618103930111319315749⟩
def resval7Tail160 : Box := ⟨551990115177326666701107661161857037097212704633,142686456130523070572683973995982404300549353186⟩
def resval7Tail164 : Box := ⟨560699850284273911366332904972705220239934557567,133976721023574947379458908820494531230872801527⟩
def resval7Tail168 : Box := ⟨569547014456611764270996816584966605499418226596,125129556851237088499809999257633432594826453242⟩
def resval7Tail172 : Box := ⟨578533776158452465907720595519166924221595809223,116142795149396386738937597075668825611676758961⟩
def resval7Tail176 : Box := ⟨587662338069645021342012907001201639775340875523,107014233238203831297872797957922879020360174315⟩
def resval7Tail180 : Box := ⟨596934937625657215385659855987655912397326271601,97741633682191637253403012994112007632166313946⟩
def resval7Tail184 : Box := ⟨606353847565977154106750203092074281220272105849,88322723741871698532180894086185167940775105632⟩
def resval7Tail188 : Box := ⟨615921376491167923418247440940440288434076460467,78755194816680929220926541916984224917878368709⟩
def resval7Tail192 : Box := ⟨625639869428711895226792686703211678666653847964,69036701879136957414760822149189766477899930080⟩
def resval7Tail196 : Box := ⟨635511708407783371068497642649779196364628304043,59164862900065481610602002520869475915430541287⟩
def resval7Tail200 : Box := ⟨645539313043090442969877306481325692681313464645,49137258264758411182712400179887022557179355882⟩
def resval7Tail204 : Box := ⟨655725141127929351990913192196547096582163503077,38951430179919678264619664090797538075399621484⟩
def resval7Tail208 : Box := ⟨666071689236681903900927863900838730257624529269,28604882071249134624960732291181524022454785605⟩
def resval7Tail212 : Box := ⟨676581493580660605244367774592700411498642479775,18095077961947752701795579990863740304641527765⟩
def resval7Tail216 : Box := ⟨687268672939975253095424281729151793034753019954,7419093920542585839537318683935403332143808612⟩
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
def polyval7Tail5 : Box := ⟨21766254588223227674899701749786012125632293506552839204493,6639208393076475701530670621292906109241159247770129339863⟩
def polyval7Tail9 : Box := ⟨22109697502909371085024163444986110508269579328602647272392,6295763297444258038514838618883940737564728081351337468579⟩
def polyval7Tail13 : Box := ⟨22458561736396629991867167812394014170046046795245989386552,5946899063738646719379555501545330042724146957023395760254⟩
def polyval7Tail17 : Box := ⟨22812930624948408884297858751947986260463539698987840500287,5592530175186690799647797274599402983657186848557233156739⟩
def polyval7Tail21 : Box := ⟨23172891025131760060012112395449138473102457662080707736679,5232569775003338988487382190409676323104566307224096009184⟩
def polyval7Tail25 : Box := ⟨23538531164224169781067720579924407907459107275290336930348,4866929635910929259762226627080203081500061256024462180758⟩
def polyval7Tail29 : Box := ⟨23909940661622822895314467542709888277410201069394780665331,4495520138512276145254264950352505782456206105399717842895⟩
def polyval7Tail33 : Box := ⟨24287210550810390200673484897675341526708760765870298452639,4118250249324708839873583859829965320567002393378099882392⟩
def polyval7Tail37 : Box := ⟨24670433301667583200293407178581776427346981201255397276551,3735027498467515840250242096936104549798207862004633825740⟩
def polyval7Tail41 : Box := ⟨25059702843137774527881394667605492775389529078454889104409,3345757956997324512662559479804101204736570584894886552163⟩
def polyval7Tail45 : Box := ⟨25455114586249238624428278073267271939436584975896063107043,2950346213885860416123420889799842509701759148289214402359⟩
def polyval7Tail49 : Box := ⟨25856765447500655474327169971234181550001775252392792204260,2548695352634443566310342066095704430774744751348202037032⟩
def polyval7Tail53 : Box := ⟨26264753872615609253376852301048791184241835430543617883511,2140706927519489789305056375161496522345969405016404780496⟩
def polyval7Tail57 : Box := ⟨26679179860671904313670436091559807293255708903424849634020,1726280939463194863789046030195087799498945023585474219360⟩
def polyval7Tail61 : Box := ⟨27100144988611643242561865306731220351500112347564996423465,1305315811523485737979570851979359296272555572152282079420⟩
def polyval7Tail65 : Box := ⟨27527752436169160408946441600155828373791755701796107426079,877708363996029034876153620039008977905916734322207069011⟩
def polyval7Tail69 : Box := ⟨27962107271427382739800953418020545154602524899771314180050,443353781649342650594867967643884904058538091295534397168⟩
def polyval7Tail73 : Box := ⟨28531250000000000000000000000000000000000000000000000000000,2⟩
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
def pend : Box := ⟨1032241172509561035233255265721334964028456568410214950322387,3639682455985202499851863409237553233965692618126292798⟩
def zend : Box := ⟨1003834004182055196403300781250000000000000000000000000000000,1899811327288536933593750000000000000000000000000000002⟩
def betaquot : Box := ⟨428768946558175382218466512008073122255021033241946764468610,394809008822305128716986022887543143521170195431656015⟩
def crit : Box := ⟨205727299092109761187860030553800995309136386290959366741,8852997253353443555737074295927795532674698650900905338⟩
def subsonic : Box := ⟨338540666520522315388525519964378279235828316752735075166,4193085282084257628514073050492496421049165822210168590⟩
def pendTail4 : Box := ⟨28403768273867595964152958602605104786923196657773478610765,1655155602682629965122641427307156555416519674197584759⟩
def pendTail8 : Box := ⟨28403805758319787180409826795821510361392165635349307278691,1655040122294342856127753823241293218507824976826819424⟩
def pendTail12 : Box := ⟨28403805760027463364178152865346174593084174096419982687441,1655040106760973083503361283112367539794629790617860847⟩
def pendTail16 : Box := ⟨28403805760028349297580416850529166955135586183645584333486,1655040106747528623064039242014864878795841499474588056⟩
def pendTail20 : Box := ⟨28403805760028351543664697984804569786868956239253930926577,1655040106747476871003483462551757646261409495908028734⟩
def pendTail24 : Box := ⟨28403805760028351563834701082683040896283175451825192058252,1655040106747476169478361774231610476905189345102291556⟩
def pendTail28 : Box := ⟨28403805760028351564362007614888675249209711484739592252624,1655040106747476140712010665541002506973212334252366289⟩
def pendTail32 : Box := ⟨28403805760028351564396238839025027217395900356388206328184,1655040106747476137459288021637225408654754165626311431⟩
def pendTail36 : Box := ⟨28403805760028351564400536171473658134568769014925520323510,1655040106747476136497676101467646720980818262026559476⟩
def pendTail40 : Box := ⟨28403805760028351564400288448658119118507570534723061175406,1655040106747476135772794109130896115987054710200486097⟩
def pendTail44 : Box := ⟨28403805760028351564394408765691721960365002386102724351489,1655040106747476134382152088085967722911822911778240647⟩
def pendTail48 : Box := ⟨28403805760028351564343099600125961786479555867317723841869,1655040106747476127451364312548606073870587119978264059⟩
def pendTail52 : Box := ⟨28403805760028351563401359055388969931696953260546042346827,1655040106747476033441062264141123929732574475532130094⟩
def pendTail56 : Box := ⟨28403805760028351517501237756490053111266983497428513708975,1655040106747472736445416514325056885773029104520706696⟩
def pendTail60 : Box := ⟨28403805760028344339918922374589210009844034731734218167102,1655040106747099171211731957507515725727108115925097283⟩
def pendTail64 : Box := ⟨28403805760023649978779345506236267590281388891640589291281,1655040106567157555510820277537140795351047781681240092⟩
def pendTail68 : Box := ⟨28403805739016350975905267367147223170135360199167503193553,1655039525352528716561726315440095402708436089895707173⟩
def pendTail72 : Box := ⟨28401391820333921176787388461243813817497265837786477726664,1613791388974904694580043024602058488533858673424951402⟩
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
end SepticProfile.ExteriorCertificates.C40

end
end

end OAI
