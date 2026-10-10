import OAI.MathematicalPhysics.Transonic.Certificates.BarrierData33

namespace OAI

section
noncomputable section
namespace SepticProfile.ExteriorCertificates.C33
open SepticProfile.ExteriorJet SepticProfile.FixedInterval
def cell0 : Box := ⟨250000000000000000000000000000000000000000000000000000000000,250000000000000000000000000000000000000000000000000000000002⟩
def resval0 : Box := ⟨120970509520236913413603256872982714929466356550458963402,306025158540802459032613329098944739625497895072564382⟩
def polyval0 : Box := ⟨3854772978881020067202341468122676770099421858589191998208,14802501207263083587738696999133445227499850929239863551⟩
theorem cell0_lo : Holds Q cell0 (0/1:ℝ) := by norm_num [Holds,Q,cell0]
theorem cell0_hi : Holds Q cell0 (1/2:ℝ) := by norm_num [Holds,Q,cell0]
def resval0Tail4 : Box := ⟨65373358065936999407722089986363361376547567554022,1880696162771856712864453461051832502715919265022⟩
def resval0Tail8 : Box := ⟨8315712382742096988637959906726516434251792982,437276134813447643118585391188972327634193270⟩
def resval0Tail12 : Box := ⟨7950605971744917495261098926963690771210514,636153941237444819840021691162060990510334⟩
def resval0Tail16 : Box := ⟨33445115821539438383848485053574185768893,29132962416195521927448993740186982965326⟩
def resval0Tail20 : Box := ⟨478257462093437558093104856174610793093,405265994918104337728243609444624188974852⟩
def resval0Tail24 : Box := ⟨19950197318247077837678334933916830113,6483050062545868271134651293607302393068097⟩
def resval0Tail28 : Box := ⟨2208846158726668771785214261940259028,103728731961145511439928618399549455770731969⟩
def resval0Tail32 : Box := ⟨611092064254748741667252498639393493,1659659700830467102090756827857485325169530433⟩
def resval0Tail36 : Box := ⟨-164540557786407643933294561987085361,26554555209181344461505888168693357126405200329⟩
def resval0Tail40 : Box := ⟨-147649553618449406221891692674836086734,424872883206355466099369715999389777911966946404⟩
def resval0Tail44 : Box := ⟨-37969425471690667031253320668007616954278,6797966095700117221136866439650635262868734856407⟩
def resval0Tail48 : Box := ⟨-9720844475447704250434546154412807564064267,108767448417873939367955898822405062881070112955822⟩
def resval0Tail52 : Box := ⟨-2488542592528771358340290992395998637734909734,1740276841676542526084950113141938016752396923116046⟩
def resval0Tail56 : Box := ⟨-637067037834347185830335888028077492268829216353,27843832216423985450128215476567156926080187928720169⟩
def resval0Tail60 : Box := ⟨-163089156873125132426369734615788346074889099009021,445348419363633387145720494675271340700491563577683525⟩
def resval0Tail64 : Box := ⟨-41750790911608178129042720236007433409583603203256912,7086433321060775822473810406555745336115009299816987814⟩
def resval0Tail68 : Box := ⟨-10687426512856970108661189930048905095770533606296070979,103363070954455450682653573485905226002695878256324480342⟩
def resval0Tail72 : Box := ⟨856138925368169163321263209993148901303818572382268213713,2570475109899137601145858328246223247268470142092967142⟩
def resval0Tail76 : Box := ⟨-30802999665001461841927488861615606457940645806812,656353939791915733451762269609866644535072922452⟩
def resval0Tail80 : Box := ⟨-1750896096403683154552691394319126729540601166,79097389993489618605624701919157704835908994⟩
def resval0Tail84 : Box := ⟨-1041163439095720554958296234520689894826898,74187822783882931946122030959317814758908⟩
def resval0Tail88 : Box := ⟨-3027090554974481157687862204866698759840,489673343008506288636100948857781151108⟩
def resval0Tail92 : Box := ⟨-31662305896652975150098184367889907198,2838601490538535611147810672054784525301⟩
def resval0Tail96 : Box := ⟨-1000084138049500910017838331651963525,45344674903357069650849316981087156495970⟩
def resval0Tail100 : Box := ⟨-85678663660460191428918848469101397,725511628704121202111810749903591998534899⟩
def resval0Tail104 : Box := ⟨-18658687942262764594775509832646242,11608185685202637394228243136462305697757145⟩
def resval0Tail108 : Box := ⟨-11958232657969006352474489827936647,185730970848676523371539783889507076900375193⟩
def resval0Tail112 : Box := ⟨-525829982833374055846676229381468554,2971695533096470738190465184659102798862535994⟩
def resval0Tail116 : Box := ⟨-131358136502176313338531377026133607376,47547128406443442221095027823410668418903927095⟩
def resval0Tail120 : Box := ⟨-33617584919952008433117965341820357928750,760754022986879697768631210719521801335033621466⟩
def resval0Tail124 : Box := ⟨-8606025353096964978645176015572534307479887,12172056299645944516010065866611408760766331573620⟩
def resval0Tail128 : Box := ⟨-2203141145634210449704998044641811578445135125,194750835349776477348187854993132899317702660944666⟩
def resval0Tail132 : Box := ⟨-564004120422687200439423748908642685420332701819,3115484611790010451598533685286162945296527097551713⟩
def resval0Tail136 : Box := ⟨-144385140568746564827293273307970123719156008846999,49712392777381657389942253960614359264285273436833287⟩
def resval0Tail140 : Box := ⟨-36963685956276688321096109982567401186740933156778030,760745368173668666701949577096855670525191444264852035⟩
def resval0Tail144 : Box := ⟨-10014986121656395689238384646551715908077471060767499465,3031036383104106001644339043756284047848963380589914819⟩
def resval0Tail148 : Box := ⟨75357345822320328411483750988180457166147099,1312143479738708614475702457419566275562492⟩
def resval0Tail152 : Box := ⟨1413269895493860734607088622118195471991,56841650151003184373723223836344758863⟩
def resval0Tail156 : Box := ⟨472208930806775341190804950816915350,30618666915798897059775759742572134⟩
def resval0Tail160 : Box := ⟨869435676506667333000504856404943,84151968466081768504465519799760⟩
def resval0Tail164 : Box := ⟨6098223505968231089714022877091,35397507864617692576999512048663⟩
def resval0Tail168 : Box := ⟨133334153290828560488484655640,553543350611043880010644405301032⟩
def resval0Tail172 : Box := ⟨8041271075118867929205650283,8856310192234534709557243286775412⟩
def resval0Tail176 : Box := ⟨1240314699685789532831736345,141700931523279162751031546054099086⟩
def resval0Tail180 : Box := ⟨476210419916572180079307392,2267214897656679638997575981160134010⟩
def resval0Tail184 : Box := ⟨2469029474285727209059578861,36275438358062630983874388207885537560⟩
def resval0Tail188 : Box := ⟨524397616493230677306894230488,580407013238654413117221044088283131969⟩
def resval0Tail192 : Box := ⟨134014231977184230070253751021444,9286512086184708387392292843415256864321⟩
def resval0Tail196 : Box := ⟨34306444757221966796669669503752187,148584161216711706511516473742184789093162⟩
def resval0Tail200 : Box := ⟨8782434986411351746478371823462897632,2377338345936190990093253072190141109065724⟩
def resval0Tail204 : Box := ⟨2248303007015279866022280305749083833188,38035305751095074110949475398586067560504200⟩
def resval0Tail208 : Box := ⟨575565650377293944913079197677765087866172,608025299307668886822403724302600948778546467⟩
def resval0Tail212 : Box := ⟨147345283325860235306915654224891994008354286,9590268843551131690332013117091530662495959027⟩
def resval0Tail216 : Box := ⟨37748387570865102145879576418986154628245905359,118068149260967788687924197709500273582279577919⟩
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
def polyval0Tail5 : Box := ⟨2234839703894333707342512391038416234878432629340019,54598460922216008726062880590247560613081906497941⟩
def polyval0Tail9 : Box := ⟨227855133554501068341016377595886835070773919403,11010150138341019156339089636006796847337579467⟩
def polyval0Tail13 : Box := ⟨188495936904637047380515782186585005501370392,14133778555648789190214667822694245076092423⟩
def polyval0Tail17 : Box := ⟨694831621614008728421410898917866927700039,461854732368202609122633476453533737864947⟩
def polyval0Tail21 : Box := ⟨8730634095814231620275957534703522273127,6194138742396612945286253671872753189599472⟩
def polyval0Tail25 : Box := ⟨319655320382255196335306770441268658763,99085348776136420086123297540674721924528924⟩
def polyval0Tail29 : Box := ⟨30952975191509482914797804900308847891,1585364532267247996308259127730936445256880344⟩
def polyval0Tail33 : Box := ⟨7497214349775902266222749400904441368,25365832376699080650145310464362085569127030087⟩
def polyval0Tail37 : Box := ⟨10225724619939476798232514439046726403,405853317978230275539481358633625505371929904836⟩
def polyval0Tail41 : Box := ⟨1507330912462330105957046047374905524772,6493653086249861096129579790600664683090475994444⟩
def polyval0Tail45 : Box := ⟨384337143972108469308855665394272937015605,103898449019705636331574983391002104122500544188506⟩
def polyval0Tail49 : Box := ⟨98385201426532105161037110067349644307502798,1662375092079307993841729429183802924769072235109633⟩
def polyval0Tail53 : Box := ⟨25186570677470457175972932540945588919257721744,26597977860861538144685164657582280109580476958255695⟩
def polyval0Tail57 : Box := ⟨6447761343216776941693689025321813101556219621331,425561600997682697482687888493581315410371211705658887⟩
def polyval0Tail61 : Box := ⟨1650626898301390744588896636750739856586059687070078,6807438153280395339467922686077606319090304610711623440⟩
def polyval0Tail65 : Box := ⟨422560539230259477663962798602113632689388228800947074,108522859982987044895499747478255359766027343811905355594⟩
def polyval0Tail69 : Box := ⟨108176140098632235894462095254380312196306274627805511025,1634950948343902313519988367270707006457846504224804659322⟩
def polyval0Tail73 : Box := ⟨28093750000000000000000000000000000000000000000000000000000,2⟩
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
def resval1 : Box := ⟨120727217237870188011100116717600377809685397423450959906,222902685169522984654392591459506838583732855474197013⟩
def polyval1 : Box := ⟨3836124854225360146854024462278706235484510635191864606062,8444340586092249506335867763968689860317775887383158041⟩
theorem cell1_lo : Holds Q cell1 (1/2:ℝ) := by norm_num [Holds,Q,cell1]
theorem cell1_hi : Holds Q cell1 (3/4:ℝ) := by norm_num [Holds,Q,cell1]
def resval1Tail4 : Box := ⟨63454118369159832930275355784178208833398605178577,3244667071771328049584003227081062442514999518449⟩
def resval1Tail8 : Box := ⟨7840250605942882081478505073728739863199571755,6552156537645975499033707054151461671944810809242⟩
def resval1Tail12 : Box := ⟨-333437780810990859963052141116954794759988247,20707102675210026379254401323840164759136572570743⟩
def resval1Tail16 : Box := ⟨-2233483299624640524391202836038228649870784200,65443512814296800541142993064788447250344815348945⟩
def resval1Tail20 : Box := ⟨-14637553755672840038298265013853934065647288690,206826239723462956278274597369158077830705248934736⟩
def resval1Tail24 : Box := ⟨-95928675030492203606799285413688413506412876050,653623387165295905129891648199558236522209145520151⟩
def resval1Tail28 : Box := ⟨-628678164789512751357303742991916790596120008001,2065447184244190330777193573710776394089952093465807⟩
def resval1Tail32 : Box := ⟨-4120105220776012480503409744105253955442254592708,6525699904368103164064771003215789674182550071914084⟩
def resval1Tail36 : Box := ⟨-27001521574880560359823531680819393017724408123358,20610454311199849691080265304470086116992180989680065⟩
def resval1Tail40 : Box := ⟨-176957171793138825633416113955062170349611426465858,65047594595988725008211614686053744110724042380175463⟩
def resval1Tail44 : Box := ⟨-1159706521063515961919570955991979665807929727407159,204982086720321139416965648207974219440824802470073077⟩
def resval1Tail48 : Box := ⟨-7600252656441852048142669541285863069578540514203277,643909612402749143434716048966232752198605629165865001⟩
def resval1Tail52 : Box := ⟨-49809015809256945837301261775999918948757195115443571,2009283891044482051089989675404845225050728337686872904⟩
def resval1Tail56 : Box := ⟨-326428366007508953994481913777108773077872829855868090,6181322055653653431882367594597081132012375145881392610⟩
def resval1Tail60 : Box := ⟨-2139280939454799643268917250916288732235874308771263730,18428424096895217528136530726926003054484793722909324711⟩
def resval1Tail64 : Box := ⟨-14019991545371710673164055008024384203604513419692194736,50984113243465817658265749837429097827394419991643514371⟩
def resval1Tail68 : Box := ⟨-91881060870674753288232312654233243095322331084852895194,113563701427241811537282314570336072083771071763499799704⟩
def resval1Tail72 : Box := ⟨859273858886904539414824952179118438066409746782134323197,1524902513956406730403044096615338606350869129775244534⟩
def resval1Tail76 : Box := ⟨-30107658331962431493132502553650468207632558817786,425621552118707894548970324359404579775980244850⟩
def resval1Tail80 : Box := ⟨-1672516456789740307994849463883481851600900132,68753539332608039330788049531092673522785951777⟩
def resval1Tail84 : Box := ⟨-3938535314790271810797629457629286603689621,217141837432188189580498541098624739109302041811⟩
def resval1Tail88 : Box := ⟨-19447965712554017120864697438930004860633798,686265386577485109051875901269960225358151222780⟩
def resval1Tail92 : Box := ⟨-127436164910288112339566292345149570271566702,2168871538462598820345188786542209693210479813866⟩
def resval1Tail96 : Box := ⟨-835165467459436287545892578899523955603237734,6854272704872950536534721248652595228074591822390⟩
def resval1Tail100 : Box := ⟨-5473340401977248016792433053567192308386822004,21660052768325562473772441781021830222217006115702⟩
def resval1Tail104 : Box := ⟨-35870083657945354311078828001977647954643834748,68437891445159744891625199877355962670543637368346⟩
def resval1Tail108 : Box := ⟨-235078180260620030709746514760654503482615333622,216175822454027347167943473242559756259061161672224⟩
def resval1Tail112 : Box := ⟨-1540608362155958453467033471617678073413432838519,682424707222754143006368492985372100489364729516235⟩
def resval1Tail116 : Box := ⟨-10096530962225255531293823649996806393823707164900,2151571626935762217594211858824773199999610861968340⟩
def resval1Tail120 : Box := ⟨-66168625314039465041298553714416110060377276769655,6765770244091945715084446252425924238106679025661757⟩
def resval1Tail124 : Box := ⟨-433642702858092069928997741684418033060892376697756,21158657921437370095994660535615007088001421424444266⟩
def resval1Tail128 : Box := ⟨-2841920817451032350244895206135620165924616670166925,65400412019828655734487284440546885704214073281069652⟩
def resval1Tail132 : Box := ⟨-18624812269302317951740001441740439901194359321928088,197054659413997708876844126721259093174376806157609962⟩
def resval1Tail136 : Box := ⟨-122059569745012646288726065500088063400493791180953070,559594069202170385554658421264332930107164269101736289⟩
def resval1Tail140 : Box := ⟨-799930115035768127248318554240720092575768483654657716,1354432429172779741707570295629282510465012773283119829⟩
def resval1Tail144 : Box := ⟨-5474333991879761032712561208056592072707014810171806595,1525737227597431363497224338397180165750993055241116346⟩
def resval1Tail148 : Box := ⟨74226246913266058025199936318682644243093580,912978122001244422129067783926503944913894⟩
def resval1Tail152 : Box := ⟨1358597318784663532508912095292015178712,3610299017277638011872993648847436161515⟩
def resval1Tail156 : Box := ⟨582029165076609611608223612877114672,11296203130863382258379059267662348716787⟩
def resval1Tail160 : Box := ⟨906479546458147107857010665707149677,35701115270825824227589977161960039142850⟩
def resval1Tail164 : Box := ⟨5935481654860128911115059089252623524,112830081371082000444904642331780323199404⟩
def resval1Tail168 : Box := ⟨38898736960815661866518242041178878997,356578635990428740104243720531258659339991⟩
def resval1Tail172 : Box := ⟨254926761793662285594960190298721949528,1126832590400954270675470009549480012920867⟩
def resval1Tail176 : Box := ⟨1670688026047524447468767267551797812931,3560482452636443824811270085552993025411312⟩
def resval1Tail180 : Box := ⟨10949021047498794273327092466876230302703,11247213991416668468458845460744493552011733⟩
def resval1Tail184 : Box := ⟨71755504336886004580787081309693721058398,35509599201722703426881624074762553175420637⟩
def resval1Tail188 : Box := ⟨470256873222214685885278350759129382387079,111984395037287104483226091235831527064459564⟩
def resval1Tail192 : Box := ⟨3081875444349105197059304930993374749037391,352330357754297632417979051891124007025501058⟩
def resval1Tail196 : Box := ⟨20197378912086318226863543259304431882207983,1103080790209562654241669345832162064826127787⟩
def resval1Tail200 : Box := ⟨132365542438250236396369793708656904823630122,3417748177254863715973789632546694371518691072⟩
def resval1Tail204 : Box := ⟨867470818923495775171695520828648082436454241,10352641677884518598430915530690949093956987848⟩
def resval1Tail208 : Box := ⟨5685056758983659041934515295300082747532215175,29776039527295492594384199533371953596407506455⟩
def resval1Tail212 : Box := ⟨37257588227679385370767449233042571929785966361,74816987895758840960696765821377608341778406554⟩
def resval1Tail216 : Box := ⟨244183709602215647077573157398440191934408384351,110037411367528284435890334630158812781284716500⟩
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
def polyval1Tail5 : Box := ⟨2173876136166107746851601782799792999542611552569188,121352372316914418037777749484372188335486974563663⟩
def polyval1Tail9 : Box := ⟨219065708578706907960231292789844479412806112401,282101487594489883076358166573985425129337963863090⟩
def polyval1Tail13 : Box := ⟨15981216232507430842923794706443459830506167946,891554461160094699144772573464849801961520107944109⟩
def polyval1Tail17 : Box := ⟨103587503666279856949478967628978474896125726888,2817698743552496668714348348893969875468675220426460⟩
def polyval1Tail21 : Box := ⟨678866946022846197906275107942381170588680719750,8904968004550274310869110603474267180617203207616348⟩
def polyval1Tail25 : Box := ⟨4449022367272914209431245925754751018836101678329,28141792941844051859760945448824928608812556722182958⟩
def polyval1Tail29 : Box := ⟨29157112984391347081439795478974255555201473256034,88926866872670315774622387987798916104104747143051998⟩
def polyval1Tail33 : Box := ⟨191084055654344818078418933915622048870944253579870,280953880639748110303401898803723066659324206178672273⟩
def polyval1Tail37 : Box := ⟨1252288467136278302960222871909806451698358022553256,887304636989938131476138851316095434210975476914728867⟩
def polyval1Tail41 : Box := ⟨8206997698224295935640287577178181642374684760029380,2800071680289566424108211155132428601293283245245728713⟩
def polyval1Tail45 : Box := ⟨53785380115082730863449632301289598001742214880429976,8821762046611762011011386251963117129838271126412062497⟩
def polyval1Tail49 : Box := ⟨352487867122206207188856079723821152291631334434387940,27698624987718192035538369314036272671126771873004776544⟩
def polyval1Tail53 : Box := ⟨2310064485972092353836558450821711278514906641601229677,86345304536733365447458580656331697069958797068794435488⟩
def polyval1Tail57 : Box := ⟨15139238615266847050851940910843513562984543202629044743,265055507925629535152840687669352914307949678979225884093⟩
def polyval1Tail61 : Box := ⟨99216514189046596059554673753653619814046781977988236534,786337252656283558979005575080347391735931939029469346537⟩
def polyval1Tail65 : Box := ⟨650225347424577811595914305383279779554947099902809847108,2148561866337899336780683300639871787502160502870516973031⟩
def polyval1Tail69 : Box := ⟨4261317143634511444058827227131765225311418782037990065032,4584232821727071328061993956792169678829819173636146043911⟩
def polyval1Tail73 : Box := ⟨28093750000000000000000000000000000000000000000000000000000,2⟩
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
def resval2 : Box := ⟨120607470778484516074151852318592406436327234795417229634,202211973657091348464158056339504303195044565916267547⟩
def polyval2 : Box := ⟨3826911944284011976572196191186456636411804007935000742067,7132417879840281171134904138129127172376509330901862162⟩
theorem cell2_lo : Holds Q cell2 (3/4:ℝ) := by norm_num [Holds,Q,cell2]
theorem cell2_hi : Holds Q cell2 (7/8:ℝ) := by norm_num [Holds,Q,cell2]
def resval2Tail4 : Box := ⟨-134017771266171026820432596856031520609019618256337,35211013669878686673319229148689987499900475298204991⟩
def resval2Tail8 : Box := ⟨-451020636071151557828372506274860760067668106503163,59951424142000340189769035571221936931518638749867792⟩
def resval2Tail12 : Box := ⟨-1034928492753086965906471662146539939254952894204344,102008988476185234179249537086150527455017194782881264⟩
def resval2Tail16 : Box := ⟨-2374744377518116213033308910132874607975363611905803,173413628772388104759457386154095843873090766528565655⟩
def resval2Tail20 : Box := ⟨-5449082578582881274352865734548750069404365024145392,294438121262370065949254065726514687394821779096279327⟩
def resval2Tail24 : Box := ⟨-12503451415217717705464417761918582229700576847202743,499090878835738036229075089414570581859696127798367343⟩
def resval2Tail28 : Box := ⟨-28690388710048994740584829106032699147217688127491272,844066952692664384718787691820307878552529980906638372⟩
def resval2Tail32 : Box := ⟨-65832895014242183979077012487762804596002531877843284,1423052598690678268899672853191841847529695374007740774⟩
def resval2Tail36 : Box := ⟨-151059998167199180358184755631373313586444686516331146,2388912922372306932038079545657942844690639340488281152⟩
def resval2Tail40 : Box := ⟨-346621898388906743112625108490833527395164853073678307,3986459768637256120794567604010438983725056375068329806⟩
def resval2Tail44 : Box := ⟨-795357751227736854377445310315259566437875136696835524,6596688274652797542872948413327950565913626598259414297⟩
def resval2Tail48 : Box := ⟨-1825025929920554677335437324484039472160081233874943489,10785478244176350302269935233000902175442101296657862340⟩
def resval2Tail52 : Box := ⟨-4187699987510012267443580612127325644667442232458016718,17325263401536602392452178204385531790381771172526094874⟩
def resval2Tail56 : Box := ⟨-9609086039755443724635658624993051691252342459888189686,27091079741808426694546723405140958118441363900303208443⟩
def resval2Tail60 : Box := ⟨-22048985074091556494086583433656748524766941332063122644,40559877500361531295825930459073210388053434339584926042⟩
def resval2Tail64 : Box := ⟨-50593546632465337892898104626255860183412319249175038371,56214408831265055855049261883236698436440127327396366076⟩
def resval2Tail68 : Box := ⟨-116091547513104804937574195735192937146298719417039036236,66117840951560344132111123549819906835436788760879845161⟩
def resval2Tail72 : Box := ⟨860839446561943003219050702679966271494697953308234250256,1002580226508190269114369041853509493011658480919988226⟩
def resval2Tail76 : Box := ⟨-32000549844077654330905833818712853349198571768830,430773970762428615522978990055357082615865501904550⟩
def resval2Tail80 : Box := ⟨-5109542547825204221451715439461094016470661059181,733494745787700544924383131240969559716585504348589⟩
def resval2Tail84 : Box := ⟨-11720591771493178641328641072877410645857203706191,1248302915961562037265658278492725357386459064687377⟩
def resval2Tail88 : Box := ⟨-26894038751991416550208776980444552870986990861231,2122650435968876640410477565248675909742202582338506⟩
def resval2Tail92 : Box := ⟨-61710994834861405535634499645303465706040297467721,3605316980361234393385219065287759971437719947990187⟩
def resval2Tail96 : Box := ⟨-141601896204466271189126755616242762630037015549672,6114185936533184599360113166042138850408571225008206⟩
def resval2Tail100 : Box := ⟨-324919361004721498853759306930726484726631831158119,10347178499425688635309106369800586783402835081084376⟩
def resval2Tail104 : Box := ⟨-745559162592536123381723423375972642222561261957928,17460568632627355446144750825333207125458714452678185⟩
def resval2Tail108 : Box := ⟨-1710758211535466079037706593305512644738322084907739,29348092038035827475394868930136402032998517311163970⟩
def resval2Tail112 : Box := ⟨-3925501563362217875547725253619525436311400538839279,49059525767851450756675356159405192405720400581063551⟩
def resval2Tail116 : Box := ⟨-9007446183834820589532143320770946842430079575969946,81382671245840809036236395707214955883571433771305102⟩
def resval2Tail120 : Box := ⟨-20668463747900942050579754989816107185146070130986780,133533086019675642381359166540946605943557984025772805⟩
def resval2Tail124 : Box := ⟨-47425805825511579920070293114348466491320753820959983,215635230346080963514660214367046105964366091727585253⟩
def resval2Tail128 : Box := ⟨-108823136815263228511219062796087597084969171300508842,339947377203413786157738463984555778546042695722084505⟩
def resval2Tail132 : Box := ⟨-249705300736193062825940415900768925921516807058722755,515877383737192903653341519045146520834575263865721539⟩
def resval2Tail136 : Box := ⟨-572973165868156536193327802712682257629637526058495440,733077094732517273683667017982067881168998769251656013⟩
def resval2Tail140 : Box := ⟨-1314743219662721092891640339726758788336961558688657617,913321235650187563703729642573657686788242296362199769⟩
def resval2Tail144 : Box := ⟨-3196600848626990965485006828530496809197272902388018162,768977940605705966904130386647126075439485266726919776⟩
def resval2Tail148 : Box := ⟨73985052912985634854958339748133229317133409,55451805791351604965666682878250896055948457⟩
def resval2Tail152 : Box := ⟨704288641848192200954822156104549211360010,93283208148217596017477090529359375519402041⟩
def resval2Tail156 : Box := ⟨1613000762028774427006755986120590777591897,158723233412056757238642397797919800154410449⟩
def resval2Tail160 : Box := ⟨3701186573208835174186673479855935778793979,269825349619691379087985560338101020391609115⟩
def resval2Tail164 : Box := ⟨8492733560160191163944236675905452813030588,458131461459812765371952273443906827231278730⟩
def resval2Tail168 : Box := ⟨19487405433924651243409998126574161718921361,776552870618465140589207070235426974084345952⟩
def resval2Tail172 : Box := ⟨44715752337722033231435848028326805883198365,1313293814805380067461752499029890488905829318⟩
def resval2Tail176 : Box := ⟨102604654781168403910270269292679755842279367,2214099712989821258593333019415710331663018901⟩
def resval2Tail180 : Box := ⟨235436387232192586654131644023163842898779874,3716758985691578198147364665463275883703918225⟩
def resval2Tail184 : Box := ⟨540231752167255115202749359906865711043805124,6202039071446141441927842737314617028011878580⟩
def resval2Tail188 : Box := ⟨1239614443122902952556882500464008075751240293,10262401922358343318964837853848458567026172590⟩
def resval2Tail192 : Box := ⟨2844416236984089070578181429350886720659424546,16777515888385000780107977860182202932898324959⟩
def resval2Tail196 : Box := ⟨6526790466264810833917683592705401279206348554,26947359465226980958203750321689563114681532553⟩
def resval2Tail200 : Box := ⟨14976357270303234463995707956619782176040260896,42129064686960564720976857580058779106279461242⟩
def resval2Tail204 : Box := ⟨34364712372346807185955928664274299029357836277,63054616381069621671936081747248232010402320803⟩
def resval2Tail208 : Box := ⟨78853184063448301642515670909425306687069440905,87339889894962970629061865821706436604882233564⟩
def resval2Tail212 : Box := ⟨180936321435621258847673190975914682056986464021,102581725781022630379208980815489485470186365284⟩
def resval2Tail216 : Box := ⟨415185712854302426745223682135446321977799571551,68492307010848916633922566874066711420086354781⟩
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
def polyval2Tail5 : Box := ⟨22779562902497302396965841705060504525721070784246891,3165953905658753867327297355513420665222797244094677147⟩
def polyval2Tail9 : Box := ⟨47348545932747108915012214233013114307010937643168373,5388830499267176019609167428863787808954811130375117712⟩
def polyval2Tail13 : Box := ⟨108645371331156925235975376890922677853723489217527968,9165235720296228669733385484658996177888419704179829305⟩
def polyval2Tail17 : Box := ⟨249297400108194748025127473841523504536608053682453997,15571534316097869340521663645181528758084338202793917645⟩
def polyval2Tail21 : Box := ⟨572037198048087936166989977068078334625238351214970216,26417603247423619355691267429595228072985469097185607633⟩
def polyval2Tail25 : Box := ⟨1312595140621092456806113970931240272904412242332106403,44730539913378109291619057110472368373824987258449109814⟩
def polyval2Tail29 : Box := ⟨3011877565062284204940334971981760942128099527115773344,75535678112230814229473479964962045858824021419783559304⟩
def polyval2Tail33 : Box := ⟨6911046815725004595735024753755046415516475599667594338,127087615430919114978781524840472050895732296609393213271⟩
def polyval2Tail37 : Box := ⟨15858070939930461150345622421603311526640417395393411603,212737731043515733668491526764055391366521459700082788993⟩
def polyval2Tail41 : Box := ⟨36387890379163289165822674221381414970427295030629929212,353586455695053959469310737969243258140806596583681988387⟩
def polyval2Tail45 : Box := ⟨83495563316720189029568708828114946789169117238505994578,581783454392565046463096383964128258149620311725205670770⟩
def polyval2Tail49 : Box := ⟨191588713193675792524886873157879486793005658739537641051,943347920099632131144016773037788507805125577892850895213⟩
def polyval2Tail53 : Box := ⟨439618987705638345765064420772052918312210251961317426920,1496532803202062303677218935639049795747563915667060159040⟩
def polyval2Tail57 : Box := ⟨1008748642494195521003400045442219568678645496886957820790,2294240835039308073138270444818901195166181634250887835514⟩
def polyval2Tail61 : Box := ⟨2314672141539175931702769346241380019703264458019108217378,3320082085856613795085917003823517887367194258476894365359⟩
def polyval2Tail65 : Box := ⟨5311240974361003345340980941035756229558510433776678250371,4301400972942086859923637236140774932733543739476384666877⟩
def polyval2Tail69 : Box := ⟨12187160653224043090642298655307533954501433028396234914528,4211582347219769373851459677914909123740052813520101004129⟩
def polyval2Tail73 : Box := ⟨28093750000000000000000000000000000000000000000000000000000,2⟩
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
def resval3 : Box := ⟨120422954153868209344201901649426625361631259905638839794,1713034487155064531223096424330597258130126385618225837⟩
def polyval3 : Box := ⟨3845687556496717529559482918449964864466987958419849305459,247140295792493018104569321119275866747784326850832786977⟩
theorem cell3_lo : Holds Q cell3 (7/8:ℝ) := by norm_num [Holds,Q,cell3]
theorem cell3_hi : Holds Q cell3 (15/16:ℝ) := by norm_num [Holds,Q,cell3]
def resval3Tail4 : Box := ⟨-185631987357619865429351231931391154090125494029299591,1987178999094824710795495976306704668909997089902632228⟩
def resval3Tail8 : Box := ⟨-275299855406735835068904748985653519525993854963312771,2537566704615547961339414046157947913140614452698225904⟩
def resval3Tail12 : Box := ⟨-408144470375664551641468431102688938957228380630496692,3233218954152378471439931014766993969364419453083467936⟩
def resval3Tail16 : Box := ⟨-605092595695263826544931770127586161017062589937296331,4108791718187492751704144518203072522023514128407810162⟩
def resval3Tail20 : Box := ⟨-897077079157769333354699819462916395146842830194436406,5205226573081679479591674163855475192979552100291373420⟩
def resval3Tail24 : Box := ⟨-1329957252287192120124361660672687706384100879047631149,6569708370491366707010800311940547462987568401483634319⟩
def resval3Tail28 : Box := ⟨-1971721643553686271073761435064357622690213186646549154,8254697838015017573817129355948370543114157447010535946⟩
def resval3Tail32 : Box := ⟨-2923166314535453570461725107861194759411677085712248954,10315325085841565199954810879597229520380298423365265140⟩
def resval3Tail36 : Box := ⟨-4333725975150368472154690720564828579661241791228543495,12804007800950536261631211975325764352476659617602204562⟩
def resval3Tail40 : Box := ⟨-6424944326398238848558727984501010451202255174479201626,15760507935340998536642634881990713848877431322430936391⟩
def resval3Tail44 : Box := ⟨-9525269902623369916899630221005745572274761278557494378,19194647123062411045343437873859221052278691928776895468⟩
def resval3Tail48 : Box := ⟨-14121642477902280317195881652926257738228294641071848928,23057389269166230110658189190720576514270605698707096612⟩
def resval3Tail52 : Box := ⟨-20935972241455462857811823063979945067037833200619502517,27193707256339734755556045145657015152882124669946833259⟩
def resval3Tail56 : Box := ⟨-31038523626474317620628592533851733562248211278279997662,31267188483501078965652912204215496404036299562415533107⟩
def resval3Tail60 : Box := ⟨-46016011953025007834901062113298220907085342753613152012,34641116912928067096734784182988282642136019620999771650⟩
def resval3Tail64 : Box := ⟨-68220814272698814830397569093226238255282251957240079003,36192925907727963292740157335816516862744546501634645959⟩
def resval3Tail68 : Box := ⟨-101140183274270262112534980184918348866733995292395076146,34027148123666096897014519145501209120369742225743135329⟩
def resval3Tail72 : Box := ⟨861620200882178276238532259140043546410304896770375940245,761343600809007378296096380632381590601753862527577788⟩
def resval3Tail76 : Box := ⟨-2375469183442311665444815691841545679233579939199695,26110552826480288653039056243002370285817901707441205⟩
def resval3Tail80 : Box := ⟨-3477841749672046372867362859187412611587011440117182,33359942247862742623860555008720246647994935326918005⟩
def resval3Tail84 : Box := ⟨-5156054940908028244121981328223298706800533709676305,42531864175216622104367005707261079078358898650875113⟩
def resval3Tail88 : Box := ⟨-7644084126039145041910063655259573477112685564794257,54089752261774727203991880717638714084193642763065145⟩
def resval3Tail92 : Box := ⟨-11332699671761200824866917898639954226913346003532245,68584114185258036254235145250836854326957974959100187⟩
def resval3Tail96 : Box := ⟨-16801238674609732723612037061026057397736803049468611,86654135408029497276652975002385596259902762199762276⟩
def resval3Tail100 : Box := ⟨-24908594525326672607496018532150451407288375410834963,109018346627855441510032871864894321739624156647028840⟩
def resval3Tail104 : Box := ⟨-36928115435009481378361544024204904769511816493976931,136445435486767171007085126836649435913768576326389635⟩
def resval3Tail108 : Box := ⟨-54747597589049475295855040964778324973744752705870075,169691099363238024755624034250758560054363127389679610⟩
def resval3Tail112 : Box := ⟨-81165784022948647859310685321179073747481225275047293,209378698810930139365506453007786747080279783913342959⟩
def resval3Tail116 : Box := ⟨-120331937585835617507218098187115436870604496131859572,255789015046284485209483888412417300754699691719240961⟩
def resval3Tail120 : Box := ⟨-178397527695505984981277637445621867648436204772308634,308505440239281630974510638643882372295139936777260061⟩
def resval3Tail124 : Box := ⟨-264482385361465790844001335644387983458695549592232570,365832141188148852989248528500408526615233186976256089⟩
def resval3Tail128 : Box := ⟨-392107071606312761289767382109134766321985458527426661,423859206160710537795580268406314618842366248044541321⟩
def resval3Tail132 : Box := ⟨-581316428289026696037027533820097650369189011283405983,474983146619449675399687233123537928248020204580867035⟩
def resval3Tail136 : Box := ⟨-861827838071780814538650032134584573445267388325136421,505592387966277415349471703136541115127560813267022786⟩
def resval3Tail140 : Box := ⟨-1277699032278002482337368006774225370410690534392451940,492479131628881955555998589687795832996735988735446736⟩
def resval3Tail144 : Box := ⟨-2055880965317742192942731812188421190983195386643138311,389569790501825661819181005372968577350245587422958177⟩
def resval3Tail148 : Box := ⟨714493546748311485162122292797668027119718966,6263355133967007914506260223824267937367492783⟩
def resval3Tail152 : Box := ⟨950437766543273578308131415358590116274902170,7987073266929758479896895077451922367178927865⟩
def resval3Tail156 : Box := ⟨1409064921953667141978839773930245449200426170,10160883439607758530792226194351671628272529141⟩
def resval3Tail160 : Box := ⟨2089002333100326081375719248700305631427029034,12888738620877121276952690505541524942481615103⟩
def resval3Tail164 : Box := ⟨3097040229317941385167834016118704859179477547,16292218657789535610624502465821824597941797841⟩
def resval3Tail168 : Box := ⟨4591501900231003634531250622880461016503661025,20508635787185791963260652660012835908306321703⟩
def resval3Tail172 : Box := ⟨6807108767995499328585820815229358100931597812,25685980090919011474140034630650619782192097835⟩
def resval3Tail176 : Box := ⟨10091845933242443524191489738185069354549713345,31971701157282423233111559646688861628118268164⟩
def resval3Tail180 : Box := ⟨14961617011195873295217163106744743904369249581,39491254536945117672846840093469653997117841746⟩
def resval3Tail184 : Box := ⟨22181272392629978800878727349500469947853840639,48310053825226178909189803315072876020717575465⟩
def resval3Tail188 : Box := ⟨32884737297303861762465113332497613259211431351,58368982307899519011689608147458130245521103980⟩
def resval3Tail192 : Box := ⟨48753107034202380882309369878661523916436645151,69378325421039273685514758202550967368830616140⟩
def resval3Tail196 : Box := ⟨72278681261755646989446063042478035558451111494,80646979131068394000772841458450346691102492797⟩
def resval3Tail200 : Box := ⟨107156406693699802708758081593260880234064870447,90811713395270397881477396589252190819274628682⟩
def resval3Tail204 : Box := ⟨158864208575167528859819087675620978696747582391,97413099437686942180661179150694017474126189614⟩
def resval3Tail208 : Box := ⟨235523358284699880523975595916921371862131590697,96237425081886993819708475365456921376783161106⟩
def resval3Tail212 : Box := ⟨349174007312241846081213635784299246277577063977,80303023943369399310623552639763304992679129669⟩
def resval3Tail216 : Box := ⟨517674947824715620221212330572705228957554927808,38307700405053436691988782963637908258457158189⟩
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
def polyval3Tail5 : Box := ⟨34650096859254360515936408973482300217182634233114209815,312844254992114163310801218601291120743384528751078560243⟩
def polyval3Tail9 : Box := ⟨51367173603137464985817054820916200346184227593946379609,398474799184677272432225587642457955690095523534650181375⟩
def polyval3Tail13 : Box := ⟨76154152605589725255195855328312421900037658671614187524,506183497070245402991725253931599153251405914153482969474⟩
def polyval3Tail17 : Box := ⟨112901967849249243040908230619915132101187285827100286103,640956406652371206282833258289125763052116824085362157927⟩
def polyval3Tail21 : Box := ⟨167382262268453079140521950150771967165080873681601341093,808516254893782157814695056170868254415522371644163333667⟩
def polyval3Tail25 : Box := ⟨248151757279504820102061126262173421777607585061371120236,1015186222389517363104606870814280114824165684868445980215⟩
def polyval3Tail29 : Box := ⟨367896178521852058799945921162635857668109764387285872573,1267543186131758564071361281612932037874990705358275673572⟩
def polyval3Tail33 : Box := ⟨545422686725261309702935061422364041143842371713975941368,1571716161708102162477951527392348958747597072557966147002⟩
def polyval3Tail37 : Box := ⟨808613746383159738604071391690733845860058089032514826781,1932103519215435985101780724475775444477400151494902963518⟩
def polyval3Tail41 : Box := ⟨1198806369360223314448091960684475708772509930804921957202,2349157022605595339354357538058630241755665732812854109411⟩
def polyval3Tail45 : Box := ⟨1777284541162940220612796232922452314174574686515859885502,2815689855990084792638657841334907080369783544046706991529⟩
def polyval3Tail49 : Box := ⟨2634904535869719679764874553798391136610470364565257142160,3310876601746490636715018465203911723490012281774079600181⟩
def polyval3Tail53 : Box := ⟨3906364879876777665787964072811592998449903955113700942379,3790676357354154865237516060945926262677288741593613234900⟩
def polyval3Tail57 : Box := ⟨5791362217112678132428560701920181138866136644730168396851,4172752242604189024423701844361570340541440162494670805364⟩
def polyval3Tail61 : Box := ⟨8585955833920552033804140925718842869323389493111895956544,4312971676835118416790640232520353597787216354245446394943⟩
def polyval3Tail65 : Box := ⟨12729066982610076860202278875968683958857128601381232194654,3969088342745158293033373693941039567819287637772743037361⟩
def polyval3Tail69 : Box := ⟨18871416446159030477841629467123640483463796644095575942559,2744984894163673624773985921026556471061440768175885463589⟩
def polyval3Tail73 : Box := ⟨28093750000000000000000000000000000000000000000000000000000,2⟩
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
def resval4 : Box := ⟨117357844898356475443938372778794741012447457107049415336,8543503745406714016510657930721348919639132518769902728⟩
def polyval4 : Box := ⟨4702478560203224118478876960944158588259116518810772719265,1964649465847345436506105748954414728858373750237063660421⟩
theorem cell4_lo : Holds Q cell4 (15/16:ℝ) := by norm_num [Holds,Q,cell4]
theorem cell4_hi : Holds Q cell4 (31/32:ℝ) := by norm_num [Holds,Q,cell4]
def resval4Tail4 : Box := ⟨-3829936192958579925136486808685731067172261596329465385,9288833421554797038460231053841249520414803168547886679⟩
def resval4Tail8 : Box := ⟨-4640866874154436027482634484747966890237560419090005939,10254399473627992962894275710420610728214771044485801588⟩
def resval4Tail12 : Box := ⟨-5623408942920094685452657911549506911206466642161718456,11288841903227288327319087470768978654102935965105674029⟩
def resval4Tail16 : Box := ⟨-6813970093388908786526606851607731578625187771803953823,12388387344348736981143879218221271971208085129146354463⟩
def resval4Tail20 : Box := ⟨-8256591136235520633746603952536033937526813791474107681,13545978759449815767365301106359856536491584611556815837⟩
def resval4Tail24 : Box := ⟨-10004636982058999718155485493412986271230814368631572073,14750243016271463441989112689696874477322330662112752046⟩
def resval4Tail28 : Box := ⟨-12122770704184163551109692156937439684300763172603930978,15984194972968130497311846091674300588141998888285656752⟩
def resval4Tail32 : Box := ⟨-14689345531453800148153936214956283464411808651153290421,17223615453608417045853030447659358409636944356943310667⟩
def resval4Tail36 : Box := ⟨-17799303262245695231493716753170403430153754209166482534,18435027064701498667232908996318446717558132417011133709⟩
def resval4Tail40 : Box := ⟨-21567686316793662007801537847341749065975894299485241592,19573174753944286332714812513368792139608122508173759994⟩
def resval4Tail44 : Box := ⟨-26133893344369019904361161244986748594786006662619560619,20577897224670682406610095641876973384228400823111610460⟩
def resval4Tail48 : Box := ⟨-31666835807188702403013434868656993315972785993270555212,21370249984819681680523279614935910587665716427787796520⟩
def resval4Tail52 : Box := ⟨-38371186291518096156266696621911301452643844976594733897,21847709945211748630435730348943447042470226931451716886⟩
def resval4Tail56 : Box := ⟨-46494949681210239172600068732402346277459630060268034167,21878253895454725588532094205111510944875761408991078421⟩
def resval4Tail60 : Box := ⟨-56338637263758408411872324705563858357846003822702130332,21293057428183238909050972701711607772601337301743969866⟩
def resval4Tail64 : Box := ⟨-68266383120500268403638923858974217973050067722170777770,19877505194385053045707674402139574294525175615960246175⟩
def resval4Tail68 : Box := ⟨-82719173252436409048397622014321666450427546439724382720,17360132760133843757156304971899168463605750850486424253⟩
def resval4Tail72 : Box := ⟨861970858806343412403587493502576262230757877263459012108,723254178077975599091022852410977936211360118327155930⟩
def resval4Tail76 : Box := ⟨-50895983690929703709682987819656918649845067514988531,126422999786654399038842478554122579740751886218355718⟩
def resval4Tail80 : Box := ⟨-61635656029808628936614104809158786649907469073814169,139660613831267400820936572149279954319573345329517137⟩
def resval4Tail84 : Box := ⟨-74684859339906340351757806382235202903243244141404581,153869159207499433402081147823060893428537922667710598⟩
def resval4Tail88 : Box := ⟨-90496779289886240607727658589820773643413742450152707,169005991682716883468608905516855002609225209748585199⟩
def resval4Tail92 : Box := ⟨-109656323039583190560497697137085415234770596281231249,184986005153674544539857349259878620208088884910706915⟩
def resval4Tail96 : Box := ⟨-132872233431025484161403094437050896453686110677626481,201667938289567112966544916670407225952321727986292513⟩
def resval4Tail100 : Box := ⟨-161003304940070858626527832461210299529371930669142194,218837321425861375007643073050250965041060196033927575⟩
def resval4Tail104 : Box := ⟨-195090151887013280711107927846869760303477554128079139,236185113788898536948052510839830576016441304304511360⟩
def resval4Tail108 : Box := ⟨-236393702461354958881363899717424200435478633399558672,253281023918862610729403727782257267650683277149802029⟩
def resval4Tail112 : Box := ⟨-286441842516744472063766352063099185523974754636209034,269540280130020483222690401141381949685235630784962159⟩
def resval4Tail116 : Box := ⟨-347085934566300857044969147211111392540091892287536988,284182342209705546452212943945577581372670338681085875⟩
def resval4Tail120 : Box := ⟨-420569302708350890467085754526739619227587551443031616,296179709592049090331336030883121103123178796399873721⟩
def resval4Tail124 : Box := ⟨-509610216851933222214418290455990089108378583212257662,304194571909669613977041877533689209451420621429151583⟩
def resval4Tail128 : Box := ⟨-617502445964223220219733712193743255849286687279865856,306500549290336903990910742797555095943123768936177043⟩
def resval4Tail132 : Box := ⟨-748237099968912502629323804582682206246215419434690795,300886162796179825562197428395492736237371516321589891⟩
def resval4Tail136 : Box := ⟨-906650267466451849214290664774521974434432032632060758,284535936650411012627875580550078396558882420759073048⟩
def resval4Tail140 : Box := ⟨-1098602264156628169210987196167877315670784776702327670,253884118893278623191077325577462175316345733428928120⟩
def resval4Tail144 : Box := ⟨-1485057485716881481401522506662745193860667733306145385,199608487058632667497623491923608407694367440798525973⟩
def resval4Tail148 : Box := ⟨21974537173195304605397605458374643833402463113,46679551624313379338868797087134058532873248120⟩
def resval4Tail152 : Box := ⟨26538092956078627011503473803906198851953918376,51328790058267220995115168238196915474814135980⟩
def resval4Tail156 : Box := ⟨32156609028285571370771525088255774839594340584,56254313226104874439288031898751410468188637619⟩
def resval4Tail160 : Box := ⟨38964651947688110243999777098863542115491419030,61418091068844175484119462231166179642844006893⟩
def resval4Tail164 : Box := ⟨47214061037619289720195493952310042537876565291,66761620231461287556579369549324430243879799174⟩
def resval4Tail168 : Box := ⟨57209995425003282001882924165252568141415622117,72199258898837139692978483249571361065317193228⟩
def resval4Tail172 : Box := ⟨69322221062938095359520265916379794380331680500,77610483512134148704354648547465722635556220982⟩
def resval4Tail176 : Box := ⟨83998788977329872586808880619611297294404416058,82830235627969793999661847796040530679788640293⟩
def resval4Tail180 : Box := ⟨101782609406758489833231568957873595462037657629,87636917928869723482806022528688880254501176528⟩
def resval4Tail184 : Box := ⟨123331534939684707036891516792430345263806121487,91737500085489262375750387853630048099226810675⟩
def resval4Tail188 : Box := ⟨149442695557072864108267695559621999640805993524,94749075361570913511250599026043906417043959862⟩
def resval4Tail192 : Box := ⟨181081985773435630880875151784400930780190301249,96176062914994646029675240187762172342343859973⟩
def resval4Tail196 : Box := ⟨219419794653849964174565670289308033488136932034,95382073047609413648767240841576828119978515329⟩
def resval4Tail200 : Box := ⟨265874300418680677970395188640159829305329522299,91555236350841043289973371255176682892247856210⟩
def resval4Tail204 : Box := ⟨322163931174213113425361026901557308092273937858,83665534476961169423493533304462028205307133932⟩
def resval4Tail208 : Box := ⟨390370932377438826062987043264261878946187851603,70412350054362465074575980261724597596592120756⟩
def resval4Tail212 : Box := ⟨473018392673524861060318103414294872580751082382,50160063811660030827087751292886290289440136268⟩
def resval4Tail216 : Box := ⟨573171892119173033724961557871890650950757831068,20858680923421011195539142128043142339778208088⟩
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
def polyval4Tail5 : Box := ⟨1069278298152434873758974503013767804668135384787844082574,2161814954473100402353378068518861733685940475428479148889⟩
def polyval4Tail9 : Box := ⟨1295658194061833566548160532044436829954146119302444398395,2372958549677999246575654305989810291611769027091712844662⟩
def polyval4Tail13 : Box := ⟨1569968727826740230035607590283485113793668449996326466680,2595419466338913328878132207873024828780738082278581442401⟩
def polyval4Tail17 : Box := ⟨1902354971430891911014956217504526506102307782255906949184,2827073044916618758319666422273400043474153147146300543909⟩
def polyval4Tail21 : Box := ⟨2305112435161568950141490933768349150361669548910211124875,3064732659502880185460792349480428890443197943974696965307⟩
def polyval4Tail25 : Box := ⟨2793139775979778842008930786373894225789232072638215136377,3303841981860995119243588959453593587060421110284259144580⟩
def polyval4Tail29 : Box := ⟨3384489922988741620017081754694381811287698679925177371677,3538090877783138388067831410250092744664061873871987227048⟩
def polyval4Tail33 : Box := ⟨4101037884791937429218769644524655055524779354636640489638,3758937238405233887228825138872958068089542844868693507966⟩
def polyval4Tail37 : Box := ⟨4969289941819890125015964524180056945097532525230753376047,3955013105735711870295320808379335058173871768141151806225⟩
def polyval4Tail41 : Box := ⟨6021364156972460518914214672302977195373214039692743386504,4111388636297711916618164161353539758831767088951251023093⟩
def polyval4Tail45 : Box := ⟨7296178475268123920922921838887279159606278297182031416655,4208661580297547386785319542744700190932088521730016913943⟩
def polyval4Tail49 : Box := ⟨8840890362248416180509874459470615747218524745491611558574,4221832809292706714598480829742690642392812422158632512358⟩
def polyval4Tail53 : Box := ⟨10712641235715470367120291026188994033815694374320569212732,4118919727513199562797991526769194461505646401665045471851⟩
def polyval4Tail57 : Box := ⟨12980670220184195563915803470878071261822757043795089201433,3859248816392629324879786220844120276483144496885469702858⟩
def polyval4Tail61 : Box := ⟨15728875415281610893494303632442751706232027116733597817954,3391355682546811285400057430085510934037486893606567500555⟩
def polyval4Tail65 : Box := ⟨19058917423622986598443057585417558025994384599213978007070,2650405313659948888887216425365807324084963971711411857561⟩
def polyval4Tail69 : Box := ⟨23093980151928064960496934788984868426062972824369917414914,1555026187481651205818825063339921500649353692734633927202⟩
def polyval4Tail73 : Box := ⟨28093750000000000000000000000000000000000000000000000000000,2⟩
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
def resval5 : Box := ⟨106495092638070784657339522492977750336786217417956893142,13340178585307242359551132144144576059069754715547579805⟩
def polyval5 : Box := ⟨8892799252865121613401605500153139042929801984471222157295,3933987194511228860224683702344667367921273867956573483393⟩
theorem cell5_lo : Holds Q cell5 (31/32:ℝ) := by norm_num [Holds,Q,cell5]
theorem cell5_hi : Holds Q cell5 (63/64:ℝ) := by norm_num [Holds,Q,cell5]
def resval5Tail4 : Box := ⟨-15402788842114407385127774221183993782995971539000140666,13569725064214937070673110133105853376189226988709947347⟩
def resval5Tail8 : Box := ⟨-16935613342294323409138764668044333897773607058005451696,13920754011090285208482011774372799239996391804311753860⟩
def resval5Tail12 : Box := ⟨-18620903801649898508532861648556370861285716051325235452,14241739620592970284242632840397292358440034803839066382⟩
def resval5Tail16 : Box := ⟨-20473900249619946451430535189340613620010074804228115005,14525466982106239645059480603834734625257403142084734256⟩
def resval5Tail20 : Box := ⟨-22511291390383110160452489432690761463958535486841596862,14763729090527921195498499259913792706587663438002111442⟩
def resval5Tail24 : Box := ⟨-24751426639979988125165136086304456976466032677004687091,14947209699732162222494707936186321388262991488520708956⟩
def resval5Tail28 : Box := ⟨-27214481394702647078454621088370237810737889016929858849,15065353918594968805741021136005036205205868593519312341⟩
def resval5Tail32 : Box := ⟨-29922638737369174234042019533215982419013939777936671098,15106224693170758797681843948473221897866687136764685893⟩
def resval5Tail36 : Box := ⟨-32900289225477974122107215997659552168959131150264689354,15056343689989121435384227611088361242053110214938234567⟩
def resval5Tail40 : Box := ⟨-36174250560606481618519949245167420223745404747134582926,14900514942558364854315512990818918591305420906236103133⟩
def resval5Tail44 : Box := ⟨-39774009117469313145095775546316827013684477439278628388,14621629454602649253681031986047935205553749528399236404⟩
def resval5Tail48 : Box := ⟨-43731985507926149681264293980493423633361679590221278311,14200448767863835483043499785617362579501433546037273532⟩
def resval5Tail52 : Box := ⟨-48083826571696322631461341909873083982916593558375065716,13615365297739026420321987883239625779350103280561744797⟩
def resval5Tail56 : Box := ⟨-52868726423544676303911463454691500684521614994321609618,12842137014697833385148266379164742088039193596887151110⟩
def resval5Tail60 : Box := ⟨-58129779448387036630618552381292572156364823719352655327,11853593801236057193164143926548441239707660418671496064⟩
def resval5Tail64 : Box := ⟨-63914368410250718276300535935068924651408967029620334763,10619312540366972183783444893166480408243506900552767011⟩
def resval5Tail68 : Box := ⟨-70274355837706653390913571311828349903434142681131315729,9105253051050603668265880501929370691154308851627196632⟩
def resval5Tail72 : Box := ⟨862018100630797655339353943532887434139992485341859159707,724312822139760348311575496047342711153754778001594205⟩
def resval5Tail76 : Box := ⟨-209196330978260470235758374237281726762953236435905597,187467527565761410278325496468614862830631842188313212⟩
def resval5Tail80 : Box := ⟨-229981374958367268315155236957288473870889599526261896,192441946792549492611796240611989182239703103390323034⟩
def resval5Tail84 : Box := ⟨-252867194174872713505381529832264487756249431971972387,197022022541502474278608570308798327371891075821090446⟩
def resval5Tail88 : Box := ⟨-278030420277361134178729143481286462816367161935124465,201110521219661287301176697436165751631283551053338312⟩
def resval5Tail92 : Box := ⟨-305697679970403968619110496695253316977432623987226149,204596928766256092752420382206625988198839984996574171⟩
def resval5Tail96 : Box := ⟨-336118153711605551932928276284591931392069016162643213,207355728716620642454979838401829532618237894269481998⟩
def resval5Tail100 : Box := ⟨-369565818312511195693177941924838184208428250892125006,209244648866132574681618874019951874140364516497292319⟩
def resval5Tail104 : Box := ⟨-406341914463158654187590687024553394476390858642281476,210102716544117826831291893792437580935181090358811334⟩
def resval5Tail108 : Box := ⟨-446777659805003729040749878662381801899979548249707131,209748102332627100720827522854180933803668313840795795⟩
def resval5Tail112 : Box := ⟨-491237231986151616868056969511849356255303763696390108,207975730005416454630293751821546930194113819044576272⟩
def resval5Tail116 : Box := ⟨-540121048565270097766815214270224320155001422940680071,204554628174634718502613344658124068565792125499254857⟩
def resval5Tail120 : Box := ⟨-593869373304080074720510920778604085353561458670887380,199224996612252411847545332603630472014367904795594649⟩
def resval5Tail124 : Box := ⟨-652966281327882085538477244195553652259144537386409776,191694957436703956372771813850784047601428861854451183⟩
def resval5Tail128 : Box := ⟨-717944018865661379126583037409621998063610045961371000,181636958296729612719124732073771370176622992041578495⟩
def resval5Tail132 : Box := ⟨-789387796835066716073142819494834913996830221317334735,168683791315573271839069287334868785033588430471667344⟩
def resval5Tail136 : Box := ⟨-867941061483953520310522169207932668259743758817320298,152424187846375775472036780208206572548375372165963808⟩
def resval5Tail140 : Box := ⟨-954311635219583380500186037579826672921318610123828931,132397931799510294889724493048415787855347090893247862⟩
def resval5Tail144 : Box := ⟨-1199529759454050653257643393786448127657494591778612397,104563529792044352778339390205159335148903653294864348⟩
def resval5Tail148 : Box := ⟨120073447731159762086704691793511053707086768508,90256271076602962321900275836550545317359341828⟩
def resval5Tail152 : Box := ⟨131941659198382277991407249906401158587897575757,91985170306485070743719427134299261665353081358⟩
def resval5Tail156 : Box := ⟨145071387035147646480776886635752441235968435644,93415127630523829593595514056784103630457313957⟩
def resval5Tail160 : Box := ⟨159507676902275825742331559694263195887789298090,94485192731945574866141381645224906093723986805⟩
def resval5Tail164 : Box := ⟨175380545473588760638996428214199946049485101350,95126899844987268586207076280721032893328764337⟩
def resval5Tail168 : Box := ⟨192832949033908361672848670788989042950379239117,95262847033760362327643802191818590679174516102⟩
def resval5Tail172 : Box := ⟨212022069681119029254421528337071541734866300455,94805668883029564604804419629502730383149514227⟩
def resval5Tail176 : Box := ⟨233120730959523681103094968129545344159232430230,93656898000660427470463008909385492755780454610⟩
def resval5Tail180 : Box := ⟨256318954365636840978641151716437160111803760208,91705703667406228784218270895766935571412853783⟩
def resval5Tail184 : Box := ⟨281825670744403624503223720173831877708376884319,88827494787238250234641657354318281412033928953⟩
def resval5Tail188 : Box := ⟨309870601989242250820138776944577106700591446697,84882372972614797332557565780012870441151965569⟩
def resval5Tail192 : Box := ⟨340706329993120770842112552553876328233322689289,79713420146403313424139590539293785004739367876⟩
def resval5Tail196 : Box := ⟨374610571484323229661757914897126343190839419017,73144803442131911017086801795843376839331958989⟩
def resval5Tail200 : Box := ⟨411888679234825843878712294815868079304964037996,64979678422005911500848618677063449999438762386⟩
def resval5Tail204 : Box := ⟨452876392167990228472335263811382011077299857392,54997869691346705101187240448478805777174295150⟩
def resval5Tail208 : Box := ⟨497942859134010154926204431392789302353903433486,42953305850818020822930958816870009099539799766⟩
def resval5Tail212 : Box := ⟨547493963756570349987266293536429691126759005579,28571183366296519544232972060150816079625964428⟩
def resval5Tail216 : Box := ⟨601984104527859240400176654362043230074916874538,11544529316437285001537975256115083768771789103⟩
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
def polyval5Tail5 : Box := ⟨5578826264140982263331669088520052761485176802395555488957,4012919112877651796900370681896944670932338771154190846720⟩
def polyval5Tail9 : Box := ⟨6133982015765046726105382256708890810436018357966734253031,4081414841451798442261277576194455406182623153563472861937⟩
def polyval5Tail13 : Box := ⟨6744384550674887254343529875300594021740676209593109571942,4135215773082661599047201266032525641643409772859292982266⟩
def polyval5Tail17 : Box := ⟨7415529235659671591858511769935611649304706003520116888863,4171460957825066767671179781567957187250287455652997934299⟩
def polyval5Tail21 : Box := ⟨8153460620720681987430734683870610754368461090827667170677,4186913818470479491432996046467442262506648279719309465003⟩
def polyval5Tail25 : Box := ⟨8964824759096112398842064773465803691719899329696219412358,4177918848736661471731541421934933922551175619612271442352⟩
def polyval5Tail29 : Box := ⟨9856929063600353605840872335417615265197790496472957603303,4140353627649230462947427914353053529667921603642473790446⟩
def polyval5Tail33 : Box := ⟨10837808119591788224267965820250379483741817373544354264376,4069575649348894218346850432464948208456785763830264948861⟩
def polyval5Tail37 : Box := ⟨11916296047096316747104755555765941014240118271551006940074,3960363425774334080197072021224137401506917438687268507259⟩
def polyval5Tail41 : Box := ⟨13102106063803585584863822295495600009948099125988131437095,3806851263951942343518718800627226974075544703972540910958⟩
def polyval5Tail45 : Box := ⟨14405917965506480500366435739510800990414495081935303124704,3602457058245389846332149972141321355874659514593966181224⟩
def polyval5Tail49 : Box := ⟨15839474311861552595312497853837661643813850711910294834452,3339802370312056493900483741333636428558200987357025514865⟩
def polyval5Tail53 : Box := ⟨17415686183751033160611451007999087782618642259742732964449,3010623995052176547995837535488671728935696366758471303227⟩
def polyval5Tail57 : Box := ⟨19148749464732092025622416425315105307324547543686614303546,2605676128829656297408974164233955681376903859902357579122⟩
def polyval5Tail61 : Box := ⟨21054272693842415714473051948819074574153788961492590552635,2114622165931186467412044611076495343158263654744477577442⟩
def polyval5Tail65 : Box := ⟨23149417641270809240535080127081247012992657259280914937063,1525915049775478940185326990139277205228351965124310283760⟩
def polyval5Tail69 : Box := ⟨25453054077514614477218243636047040959020328913775082929117,826664988587474506506208065872860848138946287265772778612⟩
def polyval5Tail73 : Box := ⟨28093750000000000000000000000000000000000000000000000000000,2⟩
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
def resval6 : Box := ⟨92116861696600975500991639840190252051316382226542213381,11791212322223160024805044137632813558431133045738381694⟩
def polyval6 : Box := ⟨15795626035651879233493647514085567369102141012108450159063,3937216413443695947413616893665653457143307857268148279331⟩
theorem cell6_lo : Holds Q cell6 (63/64:ℝ) := by norm_num [Holds,Q,cell6]
theorem cell6_hi : Holds Q cell6 (127/128:ℝ) := by norm_num [Holds,Q,cell6]
def resval6Tail4 : Box := ⟨-29749816748221641913890087539997865961623862153529779131,11553928637757321383455116979460272675439973973878981653⟩
def resval6Tail8 : Box := ⟨-31186236807686389034152703805571750571578553436455750760,11433922950718190738160915212172388657754880270521743544⟩
def resval6Tail12 : Box := ⟨-32691944198937910058673399830876039872989111958838565228,11286520925503134393809013576937580376680274532655520912⟩
def resval6Tail16 : Box := ⟨-34270348867024324923093963457225681705589223457930697830,11109710835459531901256767994094813444335954244473179946⟩
def resval6Tail20 : Box := ⟨-35924960727954058490310283424806485896258263890395131815,10901362400276307527251315083863162754235981075482768098⟩
def resval6Tail24 : Box := ⟨-37659459152657954695611006841331914774150372491047253624,10659219846114366228704418539492392480347105011898038314⟩
def resval6Tail28 : Box := ⟨-39477701156320291091858564384784889204136383198910312096,10380895124942606077820106807500415203194000541134978858⟩
def resval6Tail32 : Box := ⟨-41383729975254739377531550884565515090181225281957056467,10063860783613555195155912399718770864668443256296108347⟩
def resval6Tail36 : Box := ⟨-43381784057874710581482449358676630991790383882433745794,9705442464920339798148407448649462968057775236627305396⟩
def resval6Tail40 : Box := ⟨-45476306489758063050142044260926795075689896667235692143,9302811022110204661535025288889876196853117181567765172⟩
def resval6Tail44 : Box := ⟨-47671954873764774890784613624811200977371963884653680404,8852974227411458275515230413571962918832888444995755218⟩
def resval6Tail48 : Box := ⟨-49973611687178061697406953059274152304044448221690073483,8352768054167108978876329996926000665276714749937048085⟩
def resval6Tail52 : Box := ⟨-52386395138900179887085274205246419722153284325425626281,7798847511157534903938178808818041625749414473971291618⟩
def resval6Tail56 : Box := ⟨-54915670550846104257627788888406919611877600423801912073,7187677006633979018978213126437919007917662153599104059⟩
def resval6Tail60 : Box := ⟨-57567062288835612876856786140600935140871255676307435613,6515520218471669810281231402802548090178423782401589057⟩
def resval6Tail64 : Box := ⟨-60346466256398602031817011251683066993655681295227359606,5778429445236317635025211626752622583660343624127862255⟩
def resval6Tail68 : Box := ⟨-63259830270248214949901093389179671917463307440877231763,4972228932341657662445005543802299728314319476842803720⟩
def resval6Tail72 : Box := ⟨861917397583579310330186099864625258244096306962200262010,671200937924424878999590954732839584956490195027129699⟩
def resval6Tail76 : Box := ⟨-407477163433243681921502705054613492236590105072159958,160521013483380982082824977674969284596696588417759490⟩
def resval6Tail80 : Box := ⟨-427119737929474114233257432910243785429012529777526669,158949991086813752278645818411141551511415071853840324⟩
def resval6Tail84 : Box := ⟨-447741568468962451734444914188739899577555256075002964,157006213060318093640226458535975052165740861945180605⟩
def resval6Tail88 : Box := ⟨-469359046384402082719294057412768011357871135922043039,154662059241802779303931488111902068165107081799067372⟩
def resval6Tail92 : Box := ⟨-492020240998894764760868309779465139677746251516060687,151888429956175096156975951036872786522167465264483652⟩
def resval6Tail96 : Box := ⟨-515775544154200821666612166617419045363962647612131898,148654509241279759402993120280619737836128360551158979⟩
def resval6Tail100 : Box := ⟨-540677780669107778494020014612618722973757175503384441,144927672042563410302487025685591278811346683570337771⟩
def resval6Tail104 : Box := ⟨-566782325805415692578629446912836193250818355986825376,140673386629359744798095806827431913717425214353897019⟩
def resval6Tail108 : Box := ⟨-594147228406256775041615174597151908980777426109340561,135855111973431518393580569758221142817133970116872632⟩
def resval6Tail112 : Box := ⟨-622833339979677227555268241907730634796749327517095132,130434189836125667212132131035221733327829408203048343⟩
def resval6Tail116 : Box := ⟨-652904450014522904170793015021369381638172345663390557,124369731297936444418787186692730140630727478975789571⟩
def resval6Tail120 : Box := ⟨-684427427829531573359706434860526599562749003853226840,117618497451076854596880420592035803059128085928149658⟩
def resval6Tail124 : Box := ⟨-717472371271062511348984122380156728141608535095758313,110134773961816039653924747944318420798097468037501736⟩
def resval6Tail128 : Box := ⟨-752112762590123688321296938069160291902505751987167578,101870239194818042642966268425460741454357120524674210⟩
def resval6Tail132 : Box := ⟨-788425631845359934998414799483975263274441989438189128,92773825576480184020352572208635456953244126410897597⟩
def resval6Tail136 : Box := ⟨-826491728234044010785749502600435145551587483582337974,82791573856565047582503771204974782590039056671300664⟩
def resval6Tail140 : Box := ⟨-866396041594506245300159122937625652887074391908725793,71866468093319881911927675002558663268790051685973826⟩
def resval6Tail144 : Box := ⟨-1056736808030184694198459268465364149457872521731223390,57024945101434416121728516786113243254811368474124018⟩
def resval6Tail148 : Box := ⟨276713358665031709892157977976942637547287807772,89067799285362306508317568803135321260220168772⟩
def resval6Tail152 : Box := ⟨289996690487762055029399293607081105907290138722,87365892381141653914922411893818538526160953353⟩
def resval6Tail156 : Box := ⟨303998062884877010989435672599649763174008323508,85391071808521018000848314695900523139419344066⟩
def resval6Tail160 : Box := ⟨318675439017978418021348319950458174530432189718,83123535317815133693762094821354289901563346260⟩
def resval6Tail164 : Box := ⟨334061455753088630963570345654852519130435443978,80542860067358490435771995138831689402016442548⟩
def resval6Tail168 : Box := ⟨350190327073110835825548987348198692038715311169,77627436725566592266334452815795987281675027786⟩
def resval6Tail172 : Box := ⟨367097918851832446889304399182904078838718419054,74354405780902415325866985231402927932866001006⟩
def resval6Tail176 : Box := ⟨384821828608680886561269681832477943084868248307,70699590589219158838245999048695154686976610389⟩
def resval6Tail180 : Box := ⟨403401469114566067160468638534203941667642346306,66637426978455710401574124660340912581807373358⟩
def resval6Tail184 : Box := ⟨422878156034309856433494760418433821757989527124,62140889237765993392549252179089989121670545185⟩
def resval6Tail188 : Box := ⟨443295199800552848287929104489852486524744920446,57181412309609070498951652988892104340080154884⟩
def resval6Tail192 : Box := ⟨464698001923439025529505064204559254431893992170,51728809994344961817123306564372090258580243943⟩
def resval6Tail196 : Box := ⟨487134155950242773188832039383075823729037485151,45751188967458526527438587674092799105132553094⟩
def resval6Tail200 : Box := ⟨510653553299442808468111842539613845551931706739,39214858399648971530408865794834385374518880672⟩
def resval6Tail204 : Box := ⟨535308494204587058008162058347414277257082527418,32084234959653034935026642088523806604599872149⟩
def resval6Tail208 : Box := ⟨561153804014714759761377929774044938568618621710,24321742968788784381415213011915774448654890187⟩
def resval6Tail212 : Box := ⟨588246955278476128779447370052721040133386025413,15887709457541009428517055355764382206365136087⟩
def resval6Tail216 : Box := ⟨616656228117459818185107042951062096169101579929,6739985193718063285042597802363937514451736628⟩
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
def polyval6Tail5 : Box := ⟨12555588682726270746918695239123563691601907424278689349139,3864148029148596015047466620548961022763394423441960622425⟩
def polyval6Tail9 : Box := ⟨13161784725158010343046418220464464421157502689209354835251,3781247134205308283181442376442510458303919980348279925734⟩
def polyval6Tail13 : Box := ⟨13797250830108511847657536578446102181449768337928423219330,3685755799017644745963236041542904189944689725045208082994⟩
def polyval6Tail17 : Box := ⟨14463397969733359462430280546244674994002032728363111873381,3576792436266424823353547375450615472192039213933030130186⟩
def polyval6Tail21 : Box := ⟨15161707459459466005469662934538913302522219037741405789105,3453424181716171641156176879909143024874880543918562234877⟩
def polyval6Tail25 : Box := ⟨15893732134542567472345004539629448385025281118302730151924,3314664130668256785608040978765509490677164616722442795653⟩
def polyval6Tail29 : Box := ⟨16661099802910781727619295105597203246493642586118053851595,3159468441970205637240456648432950682516879879521593289493⟩
def polyval6Tail33 : Box := ⟨17465516864931295462411482261849573498303651431999861215217,2986733293063492940749311144998020351861309965132299918137⟩
def polyval6Tail37 : Box := ⟨18308772107943718601242767654559207537169865195856752411936,2795291678584188658723254269253156508589899722809214146223⟩
def polyval6Tail41 : Box := ⟨19192740683997874083543812189633378464208753479726371463467,2583910044662361673742872066706200583826301439078864772484⟩
def polyval6Tail45 : Box := ⟨20119388279641343321270247580240547004148252200339841175065,2351284750677365625635635022950322216717616043642543930041⟩
def polyval6Tail49 : Box := ⟨21090775487029150425788742257513659431301051927750114292451,2096038349818268858591241093560953120917454678467496397950⟩
def polyval6Tail53 : Box := ⟨22109062386075649625053159491876627490255339370072485617427,1816715679370820972974875236159360093341863260584381697500⟩
def polyval6Tail57 : Box := ⟨23176513347837976284167987817159314247615933244602716152957,1511779751203495823975336342516725176703674582713408829864⟩
def polyval6Tail61 : Box := ⟨24295502069812399505505968249388813161476095136187939656022,1179607432454290230068119703298533409744050527707308526538⟩
def polyval6Tail65 : Box := ⟨25468516854364550384481940320423451830875854312959695318550,818484905924995826450135146743686460613688488461490633607⟩
def polyval6Tail69 : Box := ⟨26698166344337092964404149354782245289929482634064892760530,426602892704057587999586038681558354271880542024789679358⟩
def polyval6Tail73 : Box := ⟨28093750000000000000000000000000000000000000000000000000000,2⟩
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
def resval7 : Box := ⟨75792953451529435224800938213350306755439721486136150929,18880845841124058086711706395328436195214647227422090307⟩
def polyval7 : Box := ⟨24932760002130036327112751150736749947581851270418996560544,6877140558002348171894625768264949415350013538300034078500⟩
theorem cell7_lo : Holds Q cell7 (127/128:ℝ) := by norm_num [Holds,Q,cell7]
theorem cell7_hi : Holds Q cell7 (1/1:ℝ) := by norm_num [Holds,Q,cell7]
def resval7Tail4 : Box := ⟨-45403904068798385190918633425954521891399833209205225745,18032744690339872569570321464769835285093246374537493452⟩
def resval7Tail8 : Box := ⟨-46120385299901958098281704847448999250906374358171206957,17316324638375729088875976193587995862417408666352748315⟩
def resval7Tail12 : Box := ⟨-46848109098134374091101731721808409100394471801924493276,16588600847543392738744115013696924745532108315637016707⟩
def resval7Tail16 : Box := ⟨-47587315488413511432088118840357014237732315067515323159,15849394457270954706659589211462605653467489905678880931⟩
def resval7Tail20 : Box := ⟨-48338185659742063066356292107084427949922438306750261096,15098524285942429434501622464222979558277410337472323056⟩
def resval7Tail24 : Box := ⟨-49100903652457532887174663802931647258741995852596746302,14335806293226959957385941095688559717736611785151346429⟩
def resval7Tail28 : Box := ⟨-49875656410824051811389725177907516383060773990642757114,13561053534860441045483157554313976461323828399540325728⟩
def resval7Tail32 : Box := ⟨-50662633828859670054466948296056443523662974322832505414,12774076116824822803395268610941184025841899016029693510⟩
def resval7Tail36 : Box := ⟨-51462028796879925692186781794802682638669490905558799233,11974681148804567165756812409903848134106812566183780231⟩
def resval7Tail40 : Box := ⟨-52274037248775788376141869143253207363884992833393853001,11162672696908704481591560498457745076314010487677836439⟩
def resval7Tail44 : Box := ⟨-53098858210037591399299397608838443663589062323800692145,10337851735646901457143349304353668587614967114487894763⟩
def resval7Tail48 : Box := ⟨-53936693846536723195631411820356458167997750318191382054,9500016099147769646658336963846077789601518850730698038⟩
def resval7Tail52 : Box := ⟨-54787749514077034519478815722235995511545409895344265634,8648960431607457939230742302878269970571730420814889781⟩
def resval7Tail56 : Box := ⟨-55652233808728079867180083317889096000956281696151948541,7784476136956382147784462693021273959253865448999888146⟩
def resval7Tail60 : Box := ⟨-56530358617944239739407056138462527767599404343424558789,6906351327731364690701023309963655489616759849963772510⟩
def resval7Tail64 : Box := ⟨-57422339159457247522784834927553542441562645715935925103,6014370772696281153046474095330975608178849850285758083⟩
def resval7Tail68 : Box := ⟨-58328163015858827598303547071694583351210603374112402531,5108310404032176905723012629766136952927379885467838681⟩
def resval7Tail72 : Box := ⟨861757016703404827724682861216930143443884236733202419722,767689749374071390040064490183729914632837326851869482⟩
def resval7Tail76 : Box := ⟨-623942782714233317883693064772827845012583174260598317,250214244636740990404856345072295675104206711494516645⟩
def resval7Tail80 : Box := ⟨-633757923491724313997253131062977104186535973847335593,240369499688521402787715774214797804967628878799125971⟩
def resval7Tail84 : Box := ⟨-643757853900552426180773399614757388716575032553300668,230369567661347688734261076884043727907968202281544997⟩
def resval7Tail88 : Box := ⟨-653915572717999439845360305303113563387078125590442180,220211848842975571924180840954882375032375095378384455⟩
def resval7Tail92 : Box := ⟨-664233568030018717405412233369955582113415191679668768,209893853530953722806181308508263548334957319511810719⟩
def resval7Tail96 : Box := ⟨-674714368804550565740062453739878908110134017963080774,199413052756421849051398923297759743578554928465330856⟩
def resval7Tail100 : Box := ⟨-685360543914500643594899934572838109114720767625757577,188766877646471770458383256048767833405992858487110109⟩
def resval7Tail104 : Box := ⟨-696174702766478532525697458551625514649175770159961625,177952718794493881473433284171557176734579968072984022⟩
def resval7Tail108 : Box := ⟨-707159495940368015024311554122860500508950618472864138,166967925620604398966748292259235785028825999124379927⟩
def resval7Tail112 : Box := ⟨-718317615838991424672003498570702454973537363310981597,155809805721980989318846901827911239483594015750896227⟩
def resval7Tail116 : Box := ⟨-729651797348024934225147451653921251907577634532626421,144475624212947479777167922491133839192582352856332622⟩
def resval7Tail120 : Box := ⟨-741164818506326507856380784593361948196485322126531508,132962603054645906270110579340362732104766856439702702⟩
def resval7Tail124 : Box := ⟨-752859501186840818731650249241622937270442542436528045,121267920374131598198081279324085658813309493254613063⟩
def resval7Tail128 : Box := ⟨-764738711788248196599068536502353093458307328256132770,109388709772724395438270374969582850896913728608788578⟩
def resval7Tail132 : Box := ⟨-776805361937565533781370955218969605255988410519388077,97322059623444259562773615446290853858705155107112366⟩
def resval7Tail136 : Box := ⟨-789062409242288893329014049333729759361156851201976937,85065012355651812017562539767506058828620316687806783⟩
def resval7Tail140 : Box := ⟨-801513197467723061288230150178339383435326841086320807,72614552016173270230162065280082478921742306958152554⟩
def resval7Tail144 : Box := ⟨-961530667913268292307690051226942901790764860882437248,57081889822990289917625071213081124139483974107670568⟩
def resval7Tail148 : Box := ⟨480199192200147580974618553792409391648969160674,153209594896654881342274443449410175156921766544⟩
def resval7Tail152 : Box := ⟨487701846992155699815356068905206708853270477736,145633282227540368093183906445817663459244827081⟩
def resval7Tail156 : Box := ⟨495397189803534146079860302219034775926158665723,137937938092306808649265714955425151079682660293⟩
def resval7Tail160 : Box := ⟨503213957127881158370768581096440844091920339937,130121170767533771792341039847205484140517495969⟩
def resval7Tail164 : Box := ⟨511154063568545565024408632413892582845307188059,122181064326868612678905571668347557110357448847⟩
def resval7Tail168 : Box := ⟨519219455266894978650521523151417280190899399389,114115672628519194032001776094373277103645642620⟩
def resval7Tail172 : Box := ⟨527412109072472231788351549373741869440283449573,105923018822941940791725531386731312970465008835⟩
def resval7Tail176 : Box := ⟨535734033027111094999834585657328086562721114736,97601094868303077574743346927442844110098288791⟩
def resval7Tail180 : Box := ⟨544187266857112102805080668462184296738112022641,89147861038302069768835923483028096701003591473⟩
def resval7Tail184 : Box := ⟨552773882473185038919824591577605878812036359029,80561245422229133653982421190560054666272503076⟩
def resval7Tail188 : Box := ⟨561495984478279912539065373023454421959452479230,71839143417134260034914065757671357942436780281⟩
def resval7Tail192 : Box := ⟨570355710683430892107500314560762730218296439461,62979417211983280468205136088884647226654290816⟩
def resval7Tail196 : Box := ⟨579355232631739631282624782452952721647397105153,53979895263674541320082925954070858222785344528⟩
def resval7Tail200 : Box := ⟨588496756130626417828181544757597367022345454370,44838371764787755818282486767004808350697857572⟩
def resval7Tail204 : Box := ⟨597782521792479727904581392475633221749920190902,35552606102934569091303531708845331026006543127⟩
def resval7Tail208 : Box := ⟨607214805583896004112950455244148186988847693350,26120322311575106181696802111906709081903686906⟩
def resval7Tail212 : Box := ⟨616795919550975919173890344557941661245996062891,16539208504975334081607207477633765491820563011⟩
def resval7Tail216 : Box := ⟨626536184771712602978678705241353735499555977869,6806650037874376238814934571271528755317334414⟩
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
def polyval7Tail5 : Box := ⟨21447990967666526901254110287951239098181942350263878085610,6542048656863394133245989635026224692945548805980158391151⟩
def polyval7Tail9 : Box := ⟨21786412123579695879655846363839643615435097220617377291624,6203625374414795401693184358597744642597408030667453500649⟩
def polyval7Tail13 : Box := ⟨22130175305553379994579765173169423467603796064660294873460,5859862192232411878868266407629145386831117227221115016869⟩
def polyval7Tail17 : Box := ⟨22479362654170452232916322858324907915491423690649963148938,5510674843615173734669316608959053097518513388053924807219⟩
def polyval7Tail21 : Box := ⟨22834059755997989807721622989924533938676560604254408446014,5155977741787635575679922590657636677197266733645206814374⟩
def polyval7Tail25 : Box := ⟨23194353548264681220802640915715939549124472826515612578144,4795683949520944155677389893446531794019090006338162707491⟩
def polyval7Tail29 : Box := ⟨23560332339963495752874151405077794833331031595963849994547,4429705157822129623374151672329930665590171459125400442439⟩
def polyval7Tail33 : Box := ⟨23932085833496298032796024074890459649190922155884169040192,4057951664289327343433326061451384939737860260670990139495⟩
def polyval7Tail37 : Box := ⟨24309705146660151297894776784682762360194859023339214691587,3680332351125474078331584229288227896424722059727974000948⟩
def polyval7Tail41 : Box := ⟨24693282834980538423233466733309367725304687107438657430342,3296754662805086952993059317665811381111093452223307509001⟩
def polyval7Tail45 : Box := ⟨25082912914396974120778775536137144675379459898496789458765,2907124583388651255453861024410302805591438722654891933723⟩
def polyval7Tail49 : Box := ⟨25478690884306568608484956693942726543549988192385615136920,2511346613479056767815241574589942776453874832336605416259⟩
def polyval7Tail53 : Box := ⟨25880713750971190790969984009578179271361311686103640797601,2109323746814434586922017884541496856461161607102271171843⟩
def polyval7Tail57 : Box := ⟨26289080051293968213990227249008350214612638982685909010210,1700957446491657267606525864812079853036441582813079723216⟩
def polyval7Tail61 : Box := ⟨26703889876970974957144704242575740952390444237420646986810,1286147620814673294634536201533327549756802706438302237420⟩
def polyval7Tail65 : Box := ⟨27125244899047817094865169370193865032032779514457806897893,864792598760742114687331405196133464214056893723608127204⟩
def polyval7Tail69 : Box := ⟨27553248593723448567092728284722142310001482109334012555341,436789098649935424146603348304800263684954359172845249587⟩
def polyval7Tail73 : Box := ⟨28093750000000000000000000000000000000000000000000000000000,2⟩
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
def pend : Box := ⟨1031806158403849235423142856600520926756996004833333025955287,3742156283149075864520318480772605935859975386004683828⟩
def zend : Box := ⟨1003814145295197714477675781250000000000000000000000000000000,2025965811363357949218750000000000000000000000000000002⟩
def betaquot : Box := ⟨428763419310133320853864638150580570546109015870604356684828,394797854408017449536108431117501399799857903868615614⟩
def crit : Box := ⟨177944165040394199503371474115556763598873148435417412696,9173579167245775513818006238269233921574392281342280674⟩
def subsonic : Box := ⟨383822156510452084726328891549969872999936877388270072880,4444214215296933273013701552546602539659723189055200950⟩
def pendTail4 : Box := ⟨27988374283883054104242180110071274124499571441722826329949,1626604434395899182825151667495770937255678328227662764⟩
def pendTail8 : Box := ⟨27988411010767335244989293091698141401557033409620682187655,1626485393256748067149352934349080075796271358037266019⟩
def pendTail12 : Box := ⟨27988411012407055781656626262771709968085733437889160900141,1626485377746899397709351819790016769679942374498150666⟩
def pendTail16 : Box := ⟨27988411012407889609519029072243149321053731074989291424427,1626485377733725669734353479527018154123491976911335926⟩
def pendTail20 : Box := ⟨27988411012407891682267857597431085122269414520154680853077,1626485377733675884068687124298748474659338882845820469⟩
def pendTail24 : Box := ⟨27988411012407891700527110884230545630187544657338594872739,1626485377733675221818366182208381814154258860330509967⟩
def pendTail28 : Box := ⟨27988411012407891700995797486948748210344951182222727917013,1626485377733675195178168395553832182535132171889704664⟩
def pendTail32 : Box := ⟨27988411012407891701025732697436908536923415527081401424929,1626485377733675192223300956675058614188244914697057500⟩
def pendTail36 : Box := ⟨27988411012407891701029459912299400360096542433555316972426,1626485377733675191366291468632521731366635920300312407⟩
def pendTail40 : Box := ⟨27988411012407891701029306436583677178618927685927770174336,1626485377733675190732269129301221870054576982110959135⟩
def pendTail44 : Box := ⟨27988411012407891701024587144842122451219429115306066996553,1626485377733675189537800275515810308829304727408931587⟩
def pendTail48 : Box := ⟨27988411012407891700983729492303293639657004950823006354586,1626485377733675183686284728312924505102345248397514119⟩
def pendTail52 : Box := ⟨27988411012407891700243058764102221837274545769288490873463,1626485377733675105536853893576476040992279045702114379⟩
def pendTail56 : Box := ⟨27988411012407891664577782422233202417900378085298263012229,1626485377733672290267917510875483452879115586160733364⟩
def pendTail60 : Box := ⟨27988411012407886141358159958276384343326860070834398207307,1626485377733355195335578716200775450986380235870367709⟩
def pendTail64 : Box := ⟨27988411012404292852410003603020910684565237061979154005785,1626485377580517335735874434858436775679281825782349117⟩
def pendTail68 : Box := ⟨27988410996256352227539017106212532911604612689220515118392,1626484876305633214387738888440585134703156767105765221⟩
def pendTail72 : Box := ⟨27986484141564017978753999652402566237362330989573011143729,1588357430421297585304333086611390812551685244963231435⟩
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
end SepticProfile.ExteriorCertificates.C33

end
end

end OAI
