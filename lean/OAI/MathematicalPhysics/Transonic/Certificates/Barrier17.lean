import OAI.MathematicalPhysics.Transonic.Certificates.BarrierData17

namespace OAI

section
noncomputable section
namespace SepticProfile.ExteriorCertificates.C17
open SepticProfile.ExteriorJet SepticProfile.FixedInterval
def cell0 : Box := ⟨250000000000000000000000000000000000000000000000000000000000,250000000000000000000000000000000000000000000000000000000002⟩
def resval0 : Box := ⟨113299305788708754765946167425492695405149777299706317931,326025247486165556744583297156134176384879032669512359⟩
def polyval0 : Box := ⟨3798934697358570883419766407293061611034672425545430917647,15068236230863451609350494129489065306789429072052695598⟩
theorem cell0_lo : Holds Q cell0 (0/1:ℝ) := by norm_num [Holds,Q,cell0]
theorem cell0_hi : Holds Q cell0 (1/2:ℝ) := by norm_num [Holds,Q,cell0]
def resval0Tail4 : Box := ⟨57780009361829252952001224044213549278319098323742,1734826373055245358513669347435068756408941051704⟩
def resval0Tail8 : Box := ⟨6938426206651794430515790569528232081657656225,376474471429426545231506189791086413969135320⟩
def resval0Tail12 : Box := ⟨6265434800011630824917944138453966770393262,515399800372568346242249959785478309046129⟩
def resval0Tail16 : Box := ⟨24906630737431494077544069852463874897940,26578541853854770118932053577320530119984⟩
def resval0Tail20 : Box := ⟨336785182155445791582989027447192613086,378829747362307859747599825616845873275384⟩
def resval0Tail24 : Box := ⟨13294384140548991635441993109752413256,6060408881318059516002950041114978057220855⟩
def resval0Tail28 : Box := ⟨1394090205159253879717537740547745110,96966495275574985854042913043250369616109389⟩
def resval0Tail32 : Box := ⟨364873469773800403515490609903053223,1551463917656957943242551367092839897179959842⟩
def resval0Tail36 : Box := ⟨-313699394057324104383625833687032570,24823422679876350794551452122019584413181321523⟩
def resval0Tail40 : Box := ⟨-140267621041201949550257046346704867896,397174762745270528866459372632474340833017381278⟩
def resval0Tail44 : Box := ⟨-36000999727955576438492738276890785273266,6354796170170484344217629865757003941390759622774⟩
def resval0Tail48 : Box := ⟨-9216602014235627549234698255494102516733452,101676730082144381536043698547803192887986070190542⟩
def resval0Tail52 : Box := ⟨-2359453278446389572128919921062813135675230562,1626825469326484845816790822298447726648114159112144⟩
def resval0Tail56 : Box := ⟨-604020103659438282827696392021282674183213537877,26028641240351392927061044531215658746244248355609296⟩
def resval0Tail60 : Box := ⟨-154629144676094854454204104442717453425172638754342,416313295015842217602203005647725388855798182143945996⟩
def resval0Tail64 : Box := ⟨-39585046821130026320691293734867361365584506853728511,6623901729042761071468821465506627314027724703827211682⟩
def resval0Tail68 : Box := ⟨-10133437728438169386981862323173264806622020044217348445,96482154496143521110326997387556104914864402260288527110⟩
def resval0Tail72 : Box := ⟨784678909302189944357567267284254022562895371256946566038,2468490127588647266872090198661168137128171008011478354⟩
def resval0Tail76 : Box := ⟨-26634841871247168536931296998745674456996728422995,594045164046746654278549377146506889536475609678⟩
def resval0Tail80 : Box := ⟨-1428933498194658482675580165529637457049064849,66539642790151635831787312326000625114958974⟩
def resval0Tail84 : Box := ⟨-802326826706430868597005103560071233702088,58721181024018074652261230993239523269357⟩
def resval0Tail88 : Box := ⟨-2203752978793191635309025741745472105989,392978413293890778155069227918761821789⟩
def resval0Tail92 : Box := ⟨-21789290170422547753396065120653023419,2562510327209522289954202716614722348436⟩
def resval0Tail96 : Box := ⟨-651023509251182645797933757112711530,40948898974711983764290363949111781848991⟩
def resval0Tail100 : Box := ⟨-52800379605203695059184261396869865,655180282810147919256389926594623857045286⟩
def resval0Tail104 : Box := ⟨-10898322509950747064148482028521884,10482884291029747542376808122761662930425822⟩
def resval0Tail108 : Box := ⟨-7358161745732773263900911866699074,167726148588620934665344583937916609785496804⟩
def resval0Tail112 : Box := ⟨-478818936712449267005079543880817012,2683618376980985316022798732809081551304830962⟩
def resval0Tail116 : Box := ⟨-120864204056369669393982605424448121124,42937893918407756687658710906262771331583964489⟩
def resval0Tail120 : Box := ⟨-30936172977586029129676156429574766166729,687006273691981608177417116979550058951966572384⟩
def resval0Tail124 : Box := ⟨-7919623671340794201461376275682736478098645,10992092954426502611130736234396145938518482628146⟩
def resval0Tail128 : Box := ⟨-2027423037447809820412361135221687389028712835,175871586561835207114140116657269549076840919551439⟩
def resval0Tail132 : Box := ⟨-519020290338523185799387364183716893117014748295,2813458803489887457090904747781141521163615893406366⟩
def resval0Tail136 : Box := ⟨-132869229035934010990252072414069912978620115964531,44890775976611935967534086223394220151144229047078399⟩
def resval0Tail140 : Box := ⟨-34014956536222777457879358393886975392314774427352007,686363604111123368014128325018368685917620239966753619⟩
def resval0Tail144 : Box := ⟨-8985541851260769255463315953072040699415131292742882328,2680029604845743817072483980445558097650065597386299988⟩
def resval0Tail148 : Box := ⟨59555051058007373957860786801457548411362613,1102316436782947940070864725407409354244004⟩
def resval0Tail152 : Box := ⟨1053825366199197262633710642347033195011,43800576417410390622039788733737295249⟩
def resval0Tail156 : Box := ⟨332356280162778895161465646825872964,22174386946854441967023421540787952⟩
def resval0Tail160 : Box := ⟨577876085402612812090009120800374,57648429855192825420909068493589⟩
def resval0Tail164 : Box := ⟨3829654161172985211874035798324,28436740280901215974860467940980⟩
def resval0Tail168 : Box := ⟨79162764374026890056920342187,446754506296891176725784318150127⟩
def resval0Tail172 : Box := ⟨4516811040068963792347104702,7147839933869223582798454808870578⟩
def resval0Tail176 : Box := ⟨659669738864429147314074900,114365420923689936279460229187806557⟩
def resval0Tail180 : Box := ⟨242540228837438398786987383,1829846731159617022816836710752920156⟩
def resval0Tail184 : Box := ⟨1873399433881069853250636793,29277547695761421753828339765186085251⟩
def resval0Tail188 : Box := ⟨428070183107068611219058755593,468440762731395911662747723682616492054⟩
def resval0Tail192 : Box := ⟨109480630207685656975871155558905,7495052101066061492945724240529901412726⟩
def resval0Tail196 : Box := ⟨28026521541691673838324723382096112,119920807342211574610196440362741028078100⟩
def resval0Tail200 : Box := ⟨7174783331927185117319136316102885839,1918726191116604621929822779138641982018407⟩
def resval0Tail204 : Box := ⟨1836744389558609322137310259561189673769,30697897110066360696298158131947286366502584⟩
def resval0Tail208 : Box := ⟨470206591831329465926395538153743391968008,490725535111801987254795818475805608223457859⟩
def resval0Tail212 : Box := ⟨120373053102276845399981342099202106201615797,7738758912091236447367806159055592420957681180⟩
def resval0Tail216 : Box := ⟨30825209367921394621297562184910617991251363696,94925908147603062472407010000361968018160261746⟩
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
def polyval0Tail5 : Box := ⟨2078283954110591198310521226148082856203918531436544,52045222136620427710086500638102453114662949365599⟩
def polyval0Tail9 : Box := ⟨200035100919698000805034914795992391960087970530,9891321268870300183950256959339098581079767754⟩
def polyval0Tail13 : Box := ⟨156292343740030663952847979860576577409920585,11983340087360192416473999459684069344132188⟩
def polyval0Tail17 : Box := ⟨544433628175706622531255649375966086940260,434323158482629910801927596448179942103284⟩
def polyval0Tail21 : Box := ⟨6468725613588236141967804852126243100313,5993045036071798582618632343323346618848466⟩
def polyval0Tail25 : Box := ⟨224121714905714407057802564678164783459,95872969610649600727965602334174451186059203⟩
def polyval0Tail29 : Box := ⟨20554670302604415966523987902613488419,1533966767057244887161154396713971702706292255⟩
def polyval0Tail33 : Box := ⟨4728006579281599496770549172923961689,24543468179000192984227716312028879667856635377⟩
def polyval0Tail37 : Box := ⟨8298350642262389953027831375549059300,392695490832259733179150913904521267797244312416⟩
def polyval0Tail41 : Box := ⟨1460527531435272081545106154361982592052,6283127851952848086447571780857872315095892165088⟩
def polyval0Tail45 : Box := ⟨373019697025533367915434479152265481290994,100530045281551562461090096839247718137527925569565⟩
def polyval0Tail49 : Box := ⟨95490273775117126212072857541598554699922370,1608480634982762581405928374021374798121779630800361⟩
def polyval0Tail53 : Box := ⟨24445488867764987794165224736464118780360784994,25735667242079609362324743119053803067879267202756273⟩
def polyval0Tail57 : Box := ⟨6258044773347278720713535939349060252316214613727,411764808956368936726169200399073961344905594445088055⟩
def polyval0Tail61 : Box := ⟨1602059458424674789596355596215005289848821688285147,6586735012574900469968659757141985972663696850326293062⟩
def polyval0Tail65 : Box := ⟨410127245423080349827204169107899465044412075869258368,105003265924474279351199187918400785263549968984912166494⟩
def polyval0Tail69 : Box := ⟨104992869847890837483798375532110475169583767169200894809,1581621583001729299404012846678455505293511935287912394232⟩
def polyval0Tail73 : Box := ⟨27093750000000000000000000000000000000000000000000000000000,2⟩
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
def resval1 : Box := ⟨113074665184135145334793901348902774186385406526606666428,249621081161886894126928717041101153509509302468754688⟩
def polyval1 : Box := ⟨3780819860016680105285195795277868417263450663674745671018,8898492499274202567447084503486922603785646310320190612⟩
theorem cell1_lo : Holds Q cell1 (1/2:ℝ) := by norm_num [Holds,Q,cell1]
theorem cell1_hi : Holds Q cell1 (3/4:ℝ) := by norm_num [Holds,Q,cell1]
def resval1Tail4 : Box := ⟨56106635348528217418896557210219289640061757181402,3083603974691681147123511899320743873960121208746⟩
def resval1Tail8 : Box := ⟨6539851088211818103628038499191420525731528205,6206760282285867937586022273714396548669994590575⟩
def resval1Tail12 : Box := ⟨-320671051941551404662845365459814941940801360,19615578769571115078797744920017312960947905384995⟩
def resval1Tail16 : Box := ⟨-2139623330503939058379828637453364569374420603,61993806990796413304462946046525343007136320249095⟩
def resval1Tail20 : Box := ⟨-14022382813950655267766744270423826854607967446,195923784266696861973213473368554909103999099372483⟩
def resval1Tail24 : Box := ⟨-91897089940647180961874016254055532273930430848,619168331334056185859623894068796054200184098150398⟩
def resval1Tail28 : Box := ⟨-602256768708305614113008229002355660255349704916,1956565872571362179345577702293562720650280717909587⟩
def resval1Tail32 : Box := ⟨-3946949959414015985448002722834294391167250466342,6181670841535132618724843825137892313734618207854570⟩
def resval1Tail36 : Box := ⟨-25866731254017434894319368284897902274364543604147,19523740115938624372098467055997460171218956279297710⟩
def resval1Tail40 : Box := ⟨-169520209946329577876873154910711314437873615027262,61616891554020538534178857514996876483184577263251047⟩
def resval1Tail44 : Box := ⟨-1110967647904266303908957975271830162376359342527178,194164605334509538714891927326124098083891980725215420⟩
def resval1Tail48 : Box := ⟨-7280837577305396909088795544709422932757753290670052,609886405428841930293701683188398505178320272723971636⟩
def resval1Tail52 : Box := ⟨-47715697146628474398191268323776342392525881554617129,1902837564699960392877298498938497984210578863711464775⟩
def resval1Tail56 : Box := ⟨-312709592820127477091806272698072379687215500373024002,5852001950793765472287211072324959102874381896502711859⟩
def resval1Tail60 : Box := ⟨-2049373587500715442794031153700291273117349850405493626,17434159192310991892813973892155171534636788965526631106⟩
def resval1Tail64 : Box := ⟨-13430774734696435030837693833487399631731488898363158876,48146810339556456161813955049508491447819911062135846518⟩
def resval1Tail68 : Box := ⟨-88019772193470581949391798653622182009263130925924342950,106595670043462553119979705244778867396945196334582559423⟩
def resval1Tail72 : Box := ⟨787510536733108739080587791691071357717356027710277138690,1524785333132005723934995145626890739437251499904721585⟩
def resval1Tail76 : Box := ⟨-26041837433483222730626402074952088795147957107502,399513142087460724930926212114739404856973379220⟩
def resval1Tail80 : Box := ⟨-1365860229290325735131586547557650898893882642,62884693951109195486495614254571052249383300855⟩
def resval1Tail84 : Box := ⟨-3497855165817473725805175101984721172440874,198613704069244382862378374767724357840754958483⟩
def resval1Tail88 : Box := ⟨-18015186180075013882827711269263612598523806,627708064659535009993270619300333004446455237980⟩
def resval1Tail92 : Box := ⟨-118051186601173447441348316224843672051180522,1983806342997982084262323645501357051457384647257⟩
def resval1Tail96 : Box := ⟨-773660130430935829632280981809586410792662858,6269407141182470332195721119227957130273078213573⟩
def resval1Tail100 : Box := ⟨-5070259027160979157050733311767764593208475296,19811797458700758503402190814879105563663405918295⟩
def resval1Tail104 : Box := ⟨-33228449560122164224304669250739370002438865503,62597859645974896915364214075044716457851027372684⟩
def resval1Tail108 : Box := ⟨-217765967037163339610896090199676909691633285389,197727401347246328738784048562256056645162224674996⟩
def resval1Tail112 : Box := ⟨-1427151041574730643584412774847813196515537057664,624177328371469382350933830656046434368638911754534⟩
def resval1Tail116 : Box := ⟨-9352977066064136183376347967350504007657082681712,1967866118362816017776731433788805630396918508530067⟩
def resval1Tail120 : Box := ⟨-61295670500157933009925580724842840300059875508676,6187693075546673202736446250884361754689511819861188⟩
def resval1Tail124 : Box := ⟨-401707306189836386597147287588570233360050137338837,19348183051686569410497803444373387037163546909789111⟩
def resval1Tail128 : Box := ⟨-2632629001845816565575762495779760550834539890666874,59786777561319205097205144623289866664675174716792807⟩
def resval1Tail132 : Box := ⟨-17253197426520068458396746004382071558398323729005987,180022951711402897836826419010999147857571850513104380⟩
def resval1Tail136 : Box := ⟨-113070554677737102147700457680377713429769860716514310,510419496937415596572910063245345591214376374075783481⟩
def resval1Tail140 : Box := ⟨-741019393891655943483962246841185799862797639322569573,1229517232422532913301713724281147995465727894989078886⟩
def resval1Tail144 : Box := ⟨-4972163980939864660332638646894457199434573392858301235,1349921751621022774439408116732439714198521510597717449⟩
def resval1Tail148 : Box := ⟨58673617251837255509227181890406167822493568,792438614236471917907741044529618361402816⟩
def resval1Tail152 : Box := ⟨1013603240791412099515663499712334808483,2901038416786538696879304478994262448930⟩
def resval1Tail156 : Box := ⟨423862684303040372220609480944795940,9078183610578594238361998330006489912901⟩
def resval1Tail160 : Box := ⟨729447316365213164608874005917095340,28691165456079477969537417045921736640443⟩
def resval1Tail164 : Box := ⟨4777030655013136713718313892567507560,90675778025415540021623540657567606846084⟩
def resval1Tail168 : Box := ⟨31306725701932619499043354179001375118,286564027761693912308258683487446396371087⟩
def resval1Tail172 : Box := ⟨205171757112332522263597269467035195185,905577613783083166877693979520488413094340⟩
def resval1Tail176 : Box := ⟨1344613627386917289290919407062618804521,2861376288820626579398076853425902966548517⟩
def resval1Tail180 : Box := ⟨8812059868439553559924112222483673255257,9038799681201823726521486154835006876277981⟩
def resval1Tail184 : Box := ⟨57750715553804392234932827338887796959430,28537170342643570420975630863183938231545846⟩
def resval1Tail188 : Box := ⟨378475089453411761591716169307737753076778,89995596403121007121112823465968890907267638⟩
def resval1Tail192 : Box := ⟨2480374346241878804551025905242269318033119,283146320741400729116548705720359147050072693⟩
def resval1Tail196 : Box := ⟨16255381315530785751039032626414302117660106,886466025381216231046799172830502384645610312⟩
def resval1Tail200 : Box := ⟨106531266989463082772359705613016667669293160,2746514166521243970693195260843461672904794811⟩
def resval1Tail204 : Box := ⟨698163311342212965394172649239556205466364640,8318869169876865687660041971597045911381950031⟩
def resval1Tail208 : Box := ⟨4575483077243895993987347185886120923214883721,23922792418979890429848026747920149143507418467⟩
def resval1Tail212 : Box := ⟨29985885983030115614003543671194220826474395491,60082737878114252458210484696249173661165235530⟩
def resval1Tail216 : Box := ⟨196519787855885121673195901333525536190040527695,88144986080474244949839616098744443113778023956⟩
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
def polyval1Tail5 : Box := ⟨2022359776560198164053810438382346932883156878244714,117753123756234919108786962312786809710239912954448⟩
def polyval1Tail9 : Box := ⟨192661108927494818625500126622139586677379756104,272663086855779545647369522296477315603386074081252⟩
def polyval1Tail13 : Box := ⟨15429220542117046963557866797162323978386664200,861726148496904015927335051763732044596950351877851⟩
def polyval1Tail17 : Box := ⟨100164977588624424973958187739246964706112695900,2723428315196522802125045271046401199510207809569788⟩
def polyval1Tail21 : Box := ⟨656437966235673431751221439300428634814437762324,8607038510170378403626967736051502518718811351159388⟩
def polyval1Tail25 : Box := ⟨4302031818275212424283055231656706062475663441025,27200264717830204898758688712205451501076241112515518⟩
def polyval1Tail29 : Box := ⟨28193795723005444848021157631999922052257277054806,85951671487116040356827004764268660923832539266208992⟩
def polyval1Tail33 : Box := ⟨184770859650180280766321353339865423390723919224016,271554062626853419158413561148404556881205997518012885⟩
def polyval1Tail37 : Box := ⟨1210914305803398731613846466944099909061284076907566,857617991528084509882966843325682562032722793277022320⟩
def polyval1Tail41 : Box := ⟨7935847994513143280996970808788308973200099810003024,2706387607480490612685540432932663916629752060596010467⟩
def polyval1Tail45 : Box := ⟨52008373416841326879404075212518421492576569702788167,8526594152528849553760122730215713358387371686128363573⟩
def polyval1Tail49 : Box := ⟨340842076024611328997507769738359676988072640643093818,26771778252890164808036317926451582081050476414712798589⟩
def polyval1Tail53 : Box := ⟨2233742629434893659828045277553554730070698464496452322,83455526558246374894521608611987431261137467435047876076⟩
def polyval1Tail57 : Box := ⟨14639055696264586867952725869242181625493004439865917171,256181350625296020513290718361401880717694516783169565268⟩
def polyval1Tail61 : Box := ⟨95938515411055224714726573359364727947906622154050455765,759987707037346415008222313439945031419274975075811565042⟩
def polyval1Tail65 : Box := ⟨628742654613905624538428985199926247819932758624946744674,2076406887951989634831142757425580490938930227630273206931⟩
def polyval1Tail69 : Box := ⟨4120528002049172414446496330249308630590999340357986722657,4429080542777858851370812083228364385640464382462003442978⟩
def polyval1Tail73 : Box := ⟨27093750000000000000000000000000000000000000000000000000000,2⟩
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
def resval2 : Box := ⟨112964068541803447779944613402971800479664218021978306787,231648775807297034002568157436135264077799059287654280⟩
def polyval2 : Box := ⟨3771868992645563186008096173642788053682037786205023850323,7617684515380812165200761103353106171713396572458884426⟩
theorem cell2_lo : Holds Q cell2 (3/4:ℝ) := by norm_num [Holds,Q,cell2]
theorem cell2_hi : Holds Q cell2 (7/8:ℝ) := by norm_num [Holds,Q,cell2]
def resval2Tail4 : Box := ⟨-138134795828376225764730095659995087694027622837848,34148185390425127663323981854968095944145077996581907⟩
def resval2Tail8 : Box := ⟨-443875800036289327772810285256447678164421373436758,58140114946859043525240172614040235638155696337623493⟩
def resval2Tail12 : Box := ⟨-1018531060575393842832309288272305875693695242894886,98923181469239291728903428917895300214439778159387682⟩
def resval2Tail16 : Box := ⟨-2337118866742691279692113108755837201261907739304755,168159030464474726294479775593883828596371618894448314⟩
def resval2Tail20 : Box := ⟨-5362747174547487953650387880330764196397933287525040,285496156474244578353272470790246653538929244917338137⟩
def resval2Tail24 : Box := ⟨-12305346410530520728607936266516904497820072122675784,483887102296447134270402232479939090870223987067809585⟩
def resval2Tail28 : Box := ⟨-28235817455989946791547644166877177990890397854115125,818246593999145626676021626191205400642490809192568603⟩
def resval2Tail32 : Box := ⟨-64789836938333994430460842320015587848385243760964384,1379271786268761095993279943009560411438076278501015987⟩
def resval2Tail36 : Box := ⟨-148666599684557847127884567066157312067448871357724422,2314838776682065014550666664953672622424702299675854270⟩
def resval2Tail40 : Box := ⟨-341130012146885020594300568783675978888583110220154455,3861501400430244192799700952047397091524392933056297731⟩
def resval2Tail44 : Box := ⟨-782756082632199737429812833562699739422304492197334789,6386747568311540894218998470550425363165614794627840327⟩
def resval2Tail48 : Box := ⟨-1796110172311328098552214223074153229769967333612979513,10434746535004607598852832188817677958982441057249294993⟩
def resval2Tail52 : Box := ⟨-4121349961576807293589737381183130689357556654612520342,16743951609920932037461920005435730469583119538033207363⟩
def resval2Tail56 : Box := ⟨-9456839434259907516681294580757985825062705060222502652,26138443879715395499048988175104012388358023805609405905⟩
def resval2Tail60 : Box := ⟨-21699640389465796911899106129421111499054121047814809408,39024341473937851587334807569971335767795453981167358380⟩
def resval2Tail64 : Box := ⟨-49791941191573538521433824995414735430051917468440917685,53800491001893365289084910643714681507685050848117802336⟩
def resval2Tail68 : Box := ⟨-114252344879867975512250299947995732738319991183700913201,62471653896957418998459232184809442920441326259645230653⟩
def resval2Tail72 : Box := ⟨788924676390538855294703463455500729814786987910134390566,1053359467426707367213496757084874343066188149810769639⟩
def resval2Tail76 : Box := ⟨-27874779193779829216304951538565253042970832181336,403377712115223736944213704928515934061666331303464⟩
def resval2Tail80 : Box := ⟨-4859545238889651555617439302737329736982258097589,686772347111674805832476034101325427532591866916272⟩
def resval2Tail84 : Box := ⟨-11147635677330477197175592060519293247482251080173,1168743545860779639441391952014352501748626658872619⟩
def resval2Tail88 : Box := ⟨-25579335606632129754211672515109757118547134511224,1987262928692975979368019575543100115924622968784796⟩
def resval2Tail92 : Box := ⟨-58694280248967528777474363399359350668755078498400,3375125759135971887479018854654805926522054801954067⟩
def resval2Tail96 : Box := ⟨-134679750372716356703928000237597153120850014935904,5723265639598394136944457777857927253371404281028501⟩
def resval2Tail100 : Box := ⟨-309035822290056578101310332675394451900500965638400,9684360394836834901969217238476085335987823673720674⟩
def resval2Tail104 : Box := ⟨-709112833920421044854780051326526405059672913559415,16339179921328120122817122243472419503160406572516521⟩
def resval2Tail108 : Box := ⟨-1627128555856192471571374658720020159827804190722320,27456506231939736139596730775779501961171590621169831⟩
def resval2Tail112 : Box := ⟨-3733605162164890224158846519823232742612303863759440,45881791793608588985750277439327084965610751339322198⟩
def resval2Tail116 : Box := ⟨-8567121175996577353716309155915840744476641044062849,76074555596534939034647689548276384859666657430897189⟩
def resval2Tail120 : Box := ⟨-19658095073355684157096926437689373170197821280735936,124736868716852183917891676597335858535506939929568039⟩
def resval2Tail124 : Box := ⟨-45107416362432623526818585989808847139981818224591533,201224017075589629988814774074610444791472843575443170⟩
def resval2Tail128 : Box := ⟨-103503366084114250853681145890693533932864715451776078,316727184254136204041715920228253359171140832672247427⟩
def resval2Tail132 : Box := ⟨-237498567966425170241854532962245666195945910191237230,479396198458195568558152283758769749999309932123211082⟩
def resval2Tail136 : Box := ⟨-544963627001344605058286064272170862829303874015470436,678027194870798013798919913806755706235691816504483935⟩
def resval2Tail140 : Box := ⟨-1250472354689013119927513825513043657688218530207856439,835896139749084138673449142094797343777460016593660750⟩
def resval2Tail144 : Box := ⟨-2959023087885841912671296409218930717038188231576236694,681289016240324207551185782189106330127148047132137430⟩
def resval2Tail148 : Box := ⟨58492708713096041221527909713274135670073317,44573320490394862112087524991032611068883458⟩
def resval2Tail152 : Box := ⟨565393052768197900058095802944266966997446,74873795504620124165248714891768949620613329⟩
def resval2Tail156 : Box := ⟨1295067286270460023719117833191243958824225,127399148451199180638576189900341569649430386⟩
def resval2Tail160 : Box := ⟨2971657497443487316642645047524955690731547,216574992399990911879645616436379289889414004⟩
def resval2Tail164 : Box := ⟨6818757946819567397387405912520720934535686,367718134172203542496150335549302961650129024⟩
def resval2Tail168 : Box := ⟨15646305129461694130908131387168388755657297,623297097669166015754300410062619675367832662⟩
def resval2Tail172 : Box := ⟨35901973073925893473033871669016715074794616,1054107263853678784868448586560174859847568869⟩
def resval2Tail176 : Box := ⟨82380578669262530604997530658447205731574631,1777127057505443320404068224148429429716023127⟩
def resval2Tail180 : Box := ⟨189030272177752500897651889095901814466032554,2983207661088217996356268937118606739377862337⟩
def resval2Tail184 : Box := ⟨433748395274716847859358181036544383470052244,4977949470055318619141923091446955896668518557⟩
def resval2Tail188 : Box := ⟨995277995613733529637397469713707901790687272,8236839645532382785537878495300031629562091477⟩
def resval2Tail192 : Box := ⟨2283762428505361878696037357499691206173149270,13465822685253277200118148584591118707960083609⟩
def resval2Tail196 : Box := ⟨5240315623210930865516398894711000529734786795,21627781263900849930861165258985944895999581168⟩
def resval2Tail200 : Box := ⟨12024415275471852515326662373046382187488545604,33811371833903347466036637280327428976203598284⟩
def resval2Tail204 : Box := ⟨27591193567918664928317635389627309392751577491,50602635669899301707877225589449070814424117345⟩
def resval2Tail208 : Box := ⟨63310684558238740102430756193263724378008939448,70084535999094188909262854851404036363408010092⟩
def resval2Tail212 : Box := ⟨145272540359732039212941592868357586056639042187,82293816804526416886693941250358910330608887613⟩
def resval2Tail216 : Box := ⟨333345361051261874535126344370539606387356320056,54875776871619406137437099917443907079849392467⟩
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
def polyval2Tail5 : Box := ⟨21936740314445596233650769584951640764823781528242064,3059081542264169536556666360611404247520256564310299062⟩
def polyval2Tail9 : Box := ⟨45756787785771357182676633402193192229278528128428035,5206915794078989982662895605284815736949959903933727827⟩
def polyval2Tail13 : Box := ⟨104992985828731423378207309194472990849816504564793746,8855834224012290967945912017617577285432744876400796204⟩
def polyval2Tail17 : Box := ⟨240916645428413794555083601035131547293354433490435631,15045858969286193403839486062167599822955954155777973752⟩
def polyval2Tail21 : Box := ⟨552806739076563860283918300478007194709525466003865475,25525757574904728286096007521010339679905298770818453735⟩
def polyval2Tail25 : Box := ⟨1268468977000852225092714827746639164845403320434758709,43220410419112163358822168354494373682881175250645248472⟩
def polyval2Tail29 : Box := ⟨2910625779094844021672602927440557213200698088513170369,72985438363545268891530139014384287518128020914637384645⟩
def polyval2Tail33 : Box := ⟨6678714717928633341596357153066752360253204810286222548,122796620029365786663320864996897604850558382434982292875⟩
def polyval2Tail37 : Box := ⟨15324962282629141644232964121254625590286394757694155783,205554242684017232503507643406424005489443446726978522143⟩
def polyval2Tail41 : Box := ⟨35164620571912167877270782344443822091119851810641757500,341645551666065153449506160578684284490511069823764405346⟩
def polyval2Tail45 : Box := ⟨80688651440805148070907982029689200219954752137418695321,562132866879376071486715534703632782312325492690563070747⟩
def polyval2Tail49 : Box := ⟨185147980141612905186210638142509680090076968461227429324,911477150653665010424328176683435111846879578101545871757⟩
def polyval2Tail53 : Box := ⟨424840097565237329967492716074485756040409285086217499726,1445953961467440031229447911092958988344944751337394913962⟩
def polyval2Tail57 : Box := ⟨974837037710002989976037841021852821318166738397632598377,2216655034675605754416792212756268994653282739923525332641⟩
def polyval2Tail61 : Box := ⟨2236858657027524567633094620384744652475095390155561497236,3207685919603662692267304839311366508426608489689700321806⟩
def polyval2Tail65 : Box := ⟨5132690345132363323447524245944365423498003582246037696691,4155462335379396631789683641578440741955581460355526860045⟩
def polyval2Tail69 : Box := ⟨11777458689616741743528702002252710910779120068438397014467,4067719826675398648051381577631100193097597289599538332449⟩
def polyval2Tail73 : Box := ⟨27093750000000000000000000000000000000000000000000000000000,2⟩
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
def resval3 : Box := ⟨112781347881738696893449419829617612486948389887896936149,1748731863862163765642886430349775622767539919531378175⟩
def polyval3 : Box := ⟨3789984677217714013517588808068530396355788493570037687807,239486388134928673489529260430906013412866559858907171698⟩
theorem cell3_lo : Holds Q cell3 (7/8:ℝ) := by norm_num [Holds,Q,cell3]
theorem cell3_hi : Holds Q cell3 (15/16:ℝ) := by norm_num [Holds,Q,cell3]
def resval3Tail4 : Box := ⟨-189692513160283023650582113769440497048239702096623928,1991672714367487907943087578118063583548224541612022110⟩
def resval3Tail8 : Box := ⟨-281309132366901003887903523135706437322465169087053690,2542621904962830813877567003752196340806992124014833761⟩
def resval3Tail12 : Box := ⟨-417053492795195308706762509441330704887591291154064247,3238633319450334029644220334051034686133097578022749080⟩
def resval3Tail16 : Box := ⟨-618300623467878621879323218629361572592361845727570361,4114125863992321597920241790022129078289113589169612048⟩
def resval3Tail20 : Box := ⟨-916658576369895643855026586851755094277038955707669499,5209648629204286841073233071907846280058067928282570337⟩
def resval3Tail24 : Box := ⟨-1358987705559233137566166886283951071717133854173760768,6571751435665648632243868453611657937941706062799109440⟩
def resval3Tail28 : Box := ⟨-2014760600587996081443920588875464410824767766964067248,8251884739842894826807146529725727104193844016992861964⟩
def resval3Tail32 : Box := ⟨-2986973510559676535899305918562715769611665871631753897,10303591803622622063787146260832090472070956445738807488⟩
def resval3Tail36 : Box := ⟨-4428323022686348683854370624165529065378520246320199559,12776822427787747534118931952037183506977379180692134176⟩
def resval3Tail40 : Box := ⟨-6565188718255347955796211263641544634193380308159851724,15707530535912955643944171111599533840722523921996239629⟩
def resval3Tail44 : Box := ⟨-9733188542366216168342580789242390455747243154213635358,19099698944866849405566015708375624500469730009575699285⟩
def resval3Tail48 : Box := ⟨-14429891244074416647075701768728357426938464803156177150,22895385089027927749608788086175276442911959429045067009⟩
def resval3Tail52 : Box := ⟨-21392964947660937290132354239561095948651440584960175785,26926033763770079650339719765058627478307917914579867123⟩
def resval3Tail56 : Box := ⟨-31716035936153389092494125864879963059831449769419448110,30834757141423744150484586943098766812012195601566224435⟩
def resval3Tail60 : Box := ⟨-47020454526256382742016097193771323371381630863636586148,33953941031904256167693139653733603045816926115992246499⟩
def resval3Tail64 : Box := ⟨-69709945723139978482739092818330384291746021996480913541,35114508340712765594986924503439281359687685781651700127⟩
def resval3Tail68 : Box := ⟨-103348031682055103456677467851318716804235387746879921143,32351126150713871715505956359829442700133921324632016683⟩
def resval3Tail72 : Box := ⟨789629776610836308223618152274234607993494650360304586590,836940675978390653570042528058310781420613064642413287⟩
def resval3Tail76 : Box := ⟨-2341741873532074917983996335713460163899493554986038,25265879685720617150016136197316405074067043565851293⟩
def resval3Tail80 : Box := ⟨-3433759079402130310142312178393715937388744047605103,32272043525471931635834791477899646607757026705111631⟩
def resval3Tail84 : Box := ⟨-5090700831733393604041613141038086023147131072473168,41131825431092516822560551825099616277088323383728572⟩
def resval3Tail88 : Box := ⟨-7547193710262496459876076914836856732092384818615865,52289635546292608014223162448596015787839422294944768⟩
def resval3Tail92 : Box := ⟨-11189055257995401604059391077592426559843209676202937,66272010266102768243900778579216744846876691986378131⟩
def resval3Tail96 : Box := ⟨-16588279348954330600732731146967627997442250951376071,83688034531288562718715124122481212755099496130176381⟩
def resval3Tail100 : Box := ⟨-24592872714817923369377912929481940769111406932605475,105218653338625992154452288791381606257750518609440726⟩
def resval3Tail104 : Box := ⟨-36460043603338586473051959440758109359370129563260466,131585944968286113682212148954439452488535183053906200⟩
def resval3Tail108 : Box := ⟨-54053659975899764936586066094434280528012456665729412,163488303619754483932257571666399134862325728164050365⟩
def resval3Tail112 : Box := ⟨-80136990196101792522767506380744263366905160231028923,201479407358560861379096214506720529959867426867316122⟩
def resval3Tail116 : Box := ⟨-118806704311112037790295076720567595595683484332393760,245756500234910118976288023676141839060142893712063273⟩
def resval3Tail120 : Box := ⟨-176136300536460920320862517802342525345387572993144356,295804720167304177330738412837045209247948353760519357⟩
def resval3Tail124 : Box := ⟨-261130014055686561689846940666663230387674549825953469,349815699185635897641781452704089756706827685622253313⟩
def resval3Tail128 : Box := ⟨-387137029862891347065604003654546151359720591303287010,403755577800976556100403657974333880808960952049275876⟩
def resval3Tail132 : Box := ⟨-573948117121093143339567719800561099080069423493513403,449892632229229038636643643501716103301002630136926767⟩
def resval3Tail136 : Box := ⟨-850903984230470325717674710085789062713539772157025234,474497049847844067970492334959854438863865844726304742⟩
def resval3Tail140 : Box := ⟨-1261503703131020816034437478777494870217004483813114302,454278797117047431726025363052184237116718472384115878⟩
def resval3Tail144 : Box := ⟨-1950838328152855968544165538862435456084537116038501960,346077019800939257157240438238801167478917033129602070⟩
def resval3Tail148 : Box := ⟨572327990830847609338778444926273340796754212,5024876439904943196127364255552146663403203745⟩
def resval3Tail152 : Box := ⟨762461175720714515294731346425397335057591327,6407668934582888771381635196946808644392043773⟩
def resval3Tail156 : Box := ⟨1130381639723159586543183054210271186932979277,8151624910992506243264774558104116304457623682⟩
def resval3Tail160 : Box := ⟨1675841791226868762839719658160632630099899572,10340070925568673306634029484456736435422981383⟩
def resval3Tail164 : Box := ⟨2484511081277430859960397941223076610320145812,13070547798878207770043707040189527220252833500⟩
def resval3Tail168 : Box := ⟨3683399796631833812685336514661443514997017892,16453219240797889063365120769395035421997907704⟩
def resval3Tail172 : Box := ⟨5460806419447181118202663757724681579495146704,20606817585234188051981569405529472666339779987⟩
def resval3Tail176 : Box := ⟨8095891946875778346865774285821329649638024534,25649644976991840610546944979935824034388849233⟩
def resval3Tail180 : Box := ⟨12002525154906205815593888470405284255892973519,31682363888898007042994663502577385953927317168⟩
def resval3Tail184 : Box := ⟨17794285180615525751739038077463683357498523326,38757475577404284498024088740459388864137160687⟩
def resval3Tail188 : Box := ⟨26380830783732498866359922848668357113038991823,46827587844170440087308765384334409030748208682⟩
def resval3Tail192 : Box := ⟨39110772125764849800686517604039781169740285767,55660327591731387380543481373627075161314103301⟩
def resval3Tail196 : Box := ⟨57983484629936338108581039202660625754873584015,64701330996450494492943653074955381733114577684⟩
def resval3Tail200 : Box := ⟨85963132587076601816234320050792070985373027089,72857056586076731165681201999581230776192937928⟩
def resval3Tail204 : Box := ⟨127444223322309623754301973285577356920926770907,78154589865873669633522750278096149434952298091⟩
def resval3Tail208 : Box := ⟨188941812256275647284418654876628689316662055168,77213720012403046037866571419595655686039813800⟩
def resval3Tail212 : Box := ⟨280114763118952891388943506698682877620001435602,64433759660490866859040076708655771488458935956⟩
def resval3Tail216 : Box := ⟨415285796308204638225623617708233937068916307922,30748243734344690309874695632811775114000035202⟩
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
def polyval3Tail5 : Box := ⟨33478205114350513314934565434823224775068079936125446688,302244003670515202506857904620312775206431207035556027197⟩
def polyval3Tail9 : Box := ⟨49630010565215077134355124016171559369578007169503748495,384972661861875208795740031282703474293659061296381618426⟩
def polyval3Tail13 : Box := ⟨73578730046338674676937789324704331251060197657507867444,489031062112528301479460847786438430623228299505572751127⟩
def polyval3Tail17 : Box := ⟨109083787683997035324003184177170008171114908575150293382,619236120245175164907786220109591345644416099819316240280⟩
def polyval3Tail21 : Box := ⟨161721637870286908060997047939416987362078599414087076414,781116356915810842167067060860323390223389708047455875574⟩
def polyval3Tail25 : Box := ⟨239759626161983652209611467794965483174935334802681724318,980780242011877124304284235543917471885230438940926256247⟩
def polyval3Tail29 : Box := ⟨355454465428066313003930795159676449858922228171387002906,1224581105942642622074675706181271278838506755564319172668⟩
def polyval3Tail33 : Box := ⟨526977285606003925187897303542955419029963355632546209158,1518439232030554707274231581076195459349326356088731748946⟩
def polyval3Tail37 : Box := ⟨781267606837453815181784295700944228847155121241694993945,1866602356615968536163944135838785695879726320052551473709⟩
def polyval3Tail41 : Box := ⟨1158264483433302989487587957176612612979707453389793163319,2269504522490321449381755639275855273586833234634418956976⟩
def polyval3Tail45 : Box := ⟨1717179365740857050461249496542566464037137621745891272995,2720198798648489146592797389402509645142464906778007112762⟩
def polyval3Tail49 : Box := ⟨2545795900937654090202352343355687191969481816069766887077,3198559958448423783807989054576260703516601170033757949258⟩
def polyval3Tail53 : Box := ⟨3774257307380802786919515095480383237426868480837376945751,3662031198312550291414675682236810219751419471203164792899⟩
def polyval3Tail57 : Box := ⟨5595506779263309354328695308783035143880154543095141765862,4031053290052633161409750915033596434860563786774328183462⟩
def polyval3Tail61 : Box := ⟨8295591308932110971764808750754555655740843543018335101857,4166359124701274793759149094535373154897783271448233014882⟩
def polyval3Tail65 : Box := ⟨12298588471008188295735408477844603872794296743034412852392,3833883304184760093314322282813359127647150877286952037834⟩
def polyval3Tail69 : Box := ⟨18233212507807957280039575509810592988746226823013056690930,2650889713949554704166640008404882229750588397593666931539⟩
def polyval3Tail73 : Box := ⟨27093750000000000000000000000000000000000000000000000000000,2⟩
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
def resval4 : Box := ⟨109516086565831043782533462357824451957742184143478406266,8904650758651881080683828445509529669083417924954090418⟩
def polyval4 : Box := ⟨4617711897310663923357902312341049635769343628819807829659,1898670420176590157634718283348992137145855532812570856276⟩
theorem cell4_lo : Holds Q cell4 (15/16:ℝ) := by norm_num [Holds,Q,cell4]
theorem cell4_hi : Holds Q cell4 (31/32:ℝ) := by norm_num [Holds,Q,cell4]
def resval4Tail4 : Box := ⟨-4078516119172569553268304166650638498109974586879522795,9646203427385188676507799892789058354714821521249906921⟩
def resval4Tail8 : Box := ⟨-4942066290366905727295282827610419612087949813638951601,10641194190861226898246510772729989436529249435931740125⟩
def resval4Tail12 : Box := ⟨-5988376852346353808696905987099113971856175037760427532,11705030172352160082130746660286568962289520678343577592⟩
def resval4Tail16 : Box := ⟨-7256207256843869385949977374006444676857405872781634552,12833083581519121022862949591665507553439339851309741231⟩
def resval4Tail20 : Box := ⟨-8792456629311099293975086745131498025285268575958407170,14017147299703326734873980325949312691011461631311308924⟩
def resval4Tail24 : Box := ⟨-10653953345310281146339860771852314376853740931774346968,15244324278555587679605681820737345803564433985840817863⟩
def resval4Tail28 : Box := ⟨-12909557211309386982572929244619179187925754481204883282,16495634828419841999573700875879649838188253643683279317⟩
def resval4Tail32 : Box := ⟨-15642706701492182977371050760769337104395848870477849208,17744274913707813568323878979643948466808609700257352712⟩
def resval4Tail36 : Box := ⟨-18954505483313139023117174490926803720029026599396662567,18953444237526941037835819337638648544028218776855223224⟩
def resval4Tail40 : Box := ⟨-22967462407428261600602746488962641423037691260931340863,20073644710308755521800889787768669074217412187573309895⟩
def resval4Tail44 : Box := ⟨-27830023310343080595149892434786982016650249976548266771,21039327724542114723113769530981116951843680418421782288⟩
def resval4Tail48 : Box := ⟨-33722062268565766222825806242097266904754250595800336978,21764741638173526721645485186618493379522694273247529056⟩
def resval4Tail52 : Box := ⟨-40861535434732918555279145566392785830355928632779146741,22138797955967521027556829211369309859560032679844300665⟩
def resval4Tail56 : Box := ⟨-49512543591983173272966112679977972156663325730156794438,22018734619868090198502338670460403165447273508715009564⟩
def resval4Tail60 : Box := ⟨-59995101673640788541869661872561030522633606639060828828,21222306032590446404864715753678828829518740587935004921⟩
def resval4Tail64 : Box := ⟨-72696976632895673710694180657085317765957359232207337402,19518170069076232466757958315308384621701138245538759923⟩
def resval4Tail68 : Box := ⟨-88087927956795737491672589828115647802464835385459835749,16614067340092617253979304114451727783032696021392592228⟩
def resval4Tail72 : Box := ⟨789941377720794297478175337708551721377879839107576929969,812560700496215943109357031657683559861381394556804926⟩
def resval4Tail76 : Box := ⟨-52360631039624008802329665117037187859208135949218732,126753861515566893604725173574482649976923047553170942⟩
def resval4Tail80 : Box := ⟨-63415215318052487013086685010404180541912168585015261,139924196115025575049206535198317716166702415087132605⟩
def resval4Tail84 : Box := ⟨-76841178735819302887334054722654658086437149867479343,154032645777495057695932336552117106922643284416345385⟩
def resval4Tail88 : Box := ⟨-93109624278769652745098118538289519830261546230503772,169027080151468208382832978145478264190501938698011746⟩
def resval4Tail92 : Box := ⟨-112822347028521536032768887485433691632991091641288927,184810578464931349381365467788855357550039496648211580⟩
def resval4Tail96 : Box := ⟨-136708552822790878673492073432058212336087048397442889,201227176285938466963460224169118224473867934381563965⟩
def resval4Tail100 : Box := ⟨-165651831460102155330887559688883622483262459112663037,218044148475291822508322705829612364915193922873451230⟩
def resval4Tail104 : Box := ⟨-200722842130119018520384454726242263036025283381706925,234929834806015271516648763641702758347672281425233891⟩
def resval4Tail108 : Box := ⟨-243218918847248562174589973882457495489979175701018102,251425968893240229421968588159128475067724292556996016⟩
def resval4Tail112 : Box := ⟨-294712060956554400219500194639120129377696505254922993,266913238097144189348232577851821253464013573201999413⟩
def resval4Tail116 : Box := ⟨-357107083959239441527923177736885070809835451871297769,280568517982168552723195525901132922663568280928814234⟩
def resval4Tail120 : Box := ⟨-432712081751790686255630433575169157925955363140649352,291311878700991469246301555784679480232928088715649594⟩
def resval4Tail124 : Box := ⟨-524323806792194908947731980345497345083666727017463243,297741038897005989186869742349261552762495653431034945⟩
def resval4Tail128 : Box := ⟨-635331126545142493703321563267392473803902927634109444,298050429080987925499080486350749375243486695382202729⟩
def resval4Tail132 : Box := ⟨-769840383229262048664863911909392765828686864420735065,289931401139734238406826920316401628135462606720702014⟩
def resval4Tail136 : Box := ⟨-932827294144703258443779227139249749364453943969954782,270449359640712288312203804413862052195871150762484390⟩
def resval4Tail140 : Box := ⟨-1130321152544765246411624272870941100067097061111065685,235892656099362968016105987142283692851798575596703576⟩
def resval4Tail144 : Box := ⟨-1446342190673905913509619691630738478688590620216477125,178247025182266813515923478326011276751250213756547695⟩
def resval4Tail148 : Box := ⟨17621291968844896084935502386765663112474413660,37443320392846802120585248279988741524513506789⟩
def resval4Tail152 : Box := ⟨21281790808671162541104765997089493153408759908,41172895342523449935338452175781401390566443179⟩
def resval4Tail156 : Box := ⟨25787468222968907221180575509148626637667733864,45124274925599915859154828641807625005703902849⟩
def resval4Tail160 : Box := ⟨31247067221478549456708926352188932635028244594,49266913493022054862905813133000446830450252871⟩
def resval4Tail164 : Box := ⟨37862546315623383871438971960086908044705992233,53553921573777781941979296339742396085140947289⟩
def resval4Tail168 : Box := ⟨45878622890961815464493613857893381515643895323,57916650019558587939134607332140616469038365676⟩
def resval4Tail172 : Box := ⟨55591824723699400044160725387708674355349807327,62258480886483630394362517907301255116072393829⟩
def resval4Tail176 : Box := ⟨67361459027562511627955443589922270573240622886,66447086804641933448758518114089067992925957178⟩
def resval4Tail180 : Box := ⟨81622903814984312695710419411317195183835668122,70304805197100532370453485594766004608961801362⟩
def resval4Tail184 : Box := ⟨98903713241486439914093897687676247479383649701,73596694875985581296048570797830128073391348935⟩
def resval4Tail188 : Box := ⟨119843132696271621457378565137934502013509476604,76015746465313596542521551871359413067259033068⟩
def resval4Tail192 : Box := ⟨145215745534129085251862517848940719405973909770,77164601069508927906563357140004373823632783200⟩
def resval4Tail196 : Box := ⟨175960126179920673314887304560138688800499251139,76532989104145778119938780825992520635871490697⟩
def resval4Tail200 : Box := ⟨213213559530821132898576497652582206284941142179,73469927744622808012890493514117248743985786328⟩
def resval4Tail204 : Box := ⟨258354110983756459750574933800780605581442056781,67149504368071975753980407876288004065211326325⟩
def resval4Tail208 : Box := ⟨313051603327148520773793041538731631528727078213,56528816577951661479189916476863720188307863084⟩
def resval4Tail212 : Box := ⟨379329386276351937737557768198185467381300915160,40296327090949280552921299382721682000990557312⟩
def resval4Tail216 : Box := ⟨459642060810415325001447359013566756656474548413,16808339846367422177180526768705378074672763268⟩
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
def polyval4Tail5 : Box := ⟨1033024902876987191775691299221114126677024533936830287103,2088432370033705457426017715391085067136118619445815684739⟩
def polyval4Tail9 : Box := ⟨1251729582534859467298164456679602104954006511683776778692,2292405417884050334021267099775011322634797403522006007644⟩
def polyval4Tail13 : Box := ⟨1516739761543902718460107887747522990437703518818433985207,2507310478792555564402918766040467590612158088605949606260⟩
def polyval4Tail17 : Box := ⟨1837856623892203959474852351928267643462980333020784329782,2731094709982062318350500430482245808131863966250490474374⟩
def polyval4Tail21 : Box := ⟨2226958807057675943821959309188764468458925955829505782675,2960679280076825760991659123485912391365000313147955308317⟩
def polyval4Tail25 : Box := ⟨2698439836851293733825649601876236572009709476978610853401,3191662061053731982016757092956989734686140023199523055062⟩
def polyval4Tail29 : Box := ⟨3269740567283627975301304478491078915490601506489066256124,3417946542914905945246364095039649670692607090117471037867⟩
def polyval4Tail33 : Box := ⟨3961994346264698533304496019110914007383068768019518018356,3631279871932329909208447700292608319660479854311383088687⟩
def polyval4Tail37 : Box := ⟨4800808772689332520003796645390185458253272932791442258981,3820679105355852479724499792524131089189780984214021384973⟩
def polyval4Tail41 : Box := ⟨5817212963380399398196818255303067817561194046302836236611,3971720123370316510022679069063989117949207494878933086284⟩
def polyval4Tail45 : Box := ⟨7048805370842627101515206051618652053042919949055712637603,4065657971488211811925498651969748771629314306163861400943⟩
def polyval4Tail49 : Box := ⟨8541144611482022427538203057078651916728481129454385414243,4078340504338735026304726516615668408718924731748793507146⟩
def polyval4Tail53 : Box := ⟨10349434753300284930042596232409354869775312805800740072176,3978868798873262361936682357663347441250376612254342333582⟩
def polyval4Tail57 : Box := ⟨12540567404610929296168872860244772244948070154674622335578,3727947578290303670176622104274742715887047245090864117190⟩
def polyval4Tail61 : Box := ⟨15195596143976889302786273233379790740373870393020018593691,3275856445309822072346120894405851094426910602619155329207⟩
def polyval4Tail65 : Box := ⟨18412734824589118822081484675811983295180705093321559541460,2559957588765404850146396140607430680362246544225197093357⟩
def polyval4Tail69 : Box := ⟨22310990761242448470511481524965451779354753442329368935061,1501637217482109613191828265252435380196128925639288871306⟩
def polyval4Tail73 : Box := ⟨27093750000000000000000000000000000000000000000000000000000,2⟩
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
def resval5 : Box := ⟨97404900935168496527197137975856215339247634609336976407,14312766979360061068860421597307824413802313471961022226⟩
def polyval5 : Box := ⟨8665753033588130061964742897239991516854196989038460444786,3801043175201603992047891742633551296189037107532998123811⟩
theorem cell5_lo : Holds Q cell5 (31/32:ℝ) := by norm_num [Holds,Q,cell5]
theorem cell5_hi : Holds Q cell5 (63/64:ℝ) := by norm_num [Holds,Q,cell5]
def resval5Tail4 : Box := ⟨-17002255087489215214879195157595101155525082999822952577,14520229126250391732635040435682150671452520791580305521⟩
def resval5Tail8 : Box := ⟨-18694237235590492361316811779493893068437845540202363947,14877891451974483745289701696482370126048334661436131434⟩
def resval5Tail12 : Box := ⟨-20554531219851655745770375208663704482119307456842852712,15200451902034595704866122198951454917231413703105221514⟩
def resval5Tail16 : Box := ⟨-22599946079717674081936535253682783582567763962264570616,15479820315458992552410934829169614290079744751393537814⟩
def resval5Tail20 : Box := ⟨-24848903501760232177443563443115736466137327015775444004,15706803202612401263175569251353148240475594120252773811⟩
def resval5Tail24 : Box := ⟨-27321658337669139645934308646503261961738401728954438129,15870973918064104395807439351372344239171272320217265053⟩
def resval5Tail28 : Box := ⟨-30040481032390317999829213026405808549991379673541049654,15960529251517823066962009130180449586629496175445950904⟩
def resval5Tail32 : Box := ⟨-33029858199097531525020206185859527379237397098499250182,15962130402369088423240271500962197929010943303979339239⟩
def resval5Tail36 : Box := ⟨-36316713153700186781380906642763333591273077713546484977,15860726696264743599825871495884535489564106226341566062⟩
def resval5Tail40 : Box := ⟨-39930648395098962845418188492905407622055426780193874944,15639360233111900460136393455106278426706623234497392866⟩
def resval5Tail44 : Box := ⟨-43904212215046382618239476640915652162404700408718168258,15278949469754166765019292138336600238206669300003905112⟩
def resval5Tail48 : Box := ⟨-48273191838788590705734451615744193673953233211096366242,14758049535377366653547404430160864779700677407475320574⟩
def resval5Tail52 : Box := ⟨-53076935736609561775651384098214120941848538275723162048,14052586851716473153061975300467520686136748422112726383⟩
def resval5Tail56 : Box := ⟨-58358708009121711721574822887501599865723150363448827209,13135565381209460934880592177172262016661535982686888900⟩
def resval5Tail60 : Box := ⟨-64166078038009925444204758279587294714354977325951984125,11976741552070623892831721671523653345699656771208172573⟩
def resval5Tail64 : Box := ⟨-70551348905858417506913723172653765065570701809001486918,10542264607014310113986986805219461032229205906423342697⟩
def resval5Tail68 : Box := ⟨-77571927172964581965191784929811960236492722752871236378,8794275286014576474703927323458193848797910037169196695⟩
def resval5Tail72 : Box := ⟨789958265911582029013565608766186010852853293570239649753,825666596897186973844341868153020845573322647370736708⟩
def resval5Tail76 : Box := ⟨-223108161874199060057347607331738845872383907357294177,193657668473038143992475359941586777365490369769051977⟩
def resval5Tail80 : Box := ⟨-245281965455625893203599305147094961830979878839387828,198554572494659261089444140790155570425284100057838932⟩
def resval5Tail84 : Box := ⟨-269690371661092653717457513966255417401710321998953417,203004345453405564700155054201045979349387344065656476⟩
def resval5Tail88 : Box := ⟨-296527699539828102133081931849423641086778663604901204,206901552337122369983348449558561889647294924116200511⟩
def resval5Tail92 : Box := ⟨-326035653601707021350079747890140592492406366345915545,210126487563879036679907257223798498193054756461896130⟩
def resval5Tail96 : Box := ⟨-358479992204624945486943129804012920360368770239917607,212543325466099229066133448113690047688677306239229107⟩
def resval5Tail100 : Box := ⟨-394152919754034964179802177939919289509344502489328557,213998242532112785732517005083709626582732398234973611⟩
def resval5Tail104 : Box := ⟨-433375718391422088974790406634279401430877850970418843,214317335017759499655002996103389242133227150730832243⟩
def resval5Tail108 : Box := ⟨-476501641567145881359515370507008406184906219424227193,213304310389783098251075591409128069993305031106238554⟩
def resval5Tail112 : Box := ⟨-523919095557428671616236099208702854936788373047195238,210737928862743522523928878146646672143216317869861407⟩
def resval5Tail116 : Box := ⟨-576055137579278088824742388328443074737580322783701848,206369168848859685296580274060703941588832385708561659⟩
def resval5Tail120 : Box := ⟨-633379322008519679758989590517262157144254463181074051,199918087449616851847830985578746192064750642806606352⟩
def resval5Tail124 : Box := ⟨-696407929341246736275484936719791273168834864301122036,191070344154104364253293427004055150544626705512317361⟩
def resval5Tail128 : Box := ⟨-765708615986107874846835533977404859054345982994066087,179473352644334464911013006093421107316025451766722421⟩
def resval5Tail132 : Box := ⟨-841905526765010536267438104893120124539073515999179790,164732022011908263861539450885119654649946610854964802⟩
def resval5Tail136 : Box := ⟨-925684916183111338938528041871604268377857498319601147,146404044728901373537713344574642760472576061436463551⟩
def resval5Tail140 : Box := ⟨-1017801466886131317751071720409508988525709342485845425,123994676924472562094718016528331904394582520390616968⟩
def resval5Tail144 : Box := ⟨-1193993099407343411399539776755314168251055824782975716,94276029076184114913541048667405886398428570229936625⟩
def resval5Tail148 : Box := ⟨96274085811180623444186429325830173029030432139,72406110406378108762938372444100990195998015332⟩
def resval5Tail152 : Box := ⟨105790837597498780772759052701727133120180815222,73794777695444283614500699266089946912754158107⟩
def resval5Tail156 : Box := ⟨116318254974624333551878724813566398806417859734,74943987192128837825131692604230125157408403105⟩
def resval5Tail160 : Box := ⟨127893273866887704948726251220258264200428448859,75804808637782959239038613124429973821662260969⟩
def resval5Tail164 : Box := ⟨140620141730982922947196546143875465245733371631,76322357458005881327041298001330548133501341974⟩
def resval5Tail168 : Box := ⟨154613480932724856528475206375126114393187601751,76434584791140640071000672129627513717970549860⟩
def resval5Tail172 : Box := ⟨169999320096453845684444301712905657662401143657,76071453838140913380334196636021026343422291973⟩
def resval5Tail176 : Box := ⟨186916229160065237190553097580036001472065050260,75154027065914510061013016410774920458923947809⟩
def resval5Tail180 : Box := ⟨205516567381535166197385235280912245991861927934,73593454910693388882418971695982691498544360286⟩
def resval5Tail184 : Box := ⟨225967855536607716631428290890560468714151671290,71289855681082315733947957261820342485570147839⟩
def resval5Tail188 : Box := ⟨248454284666107564470689159751846322874526402534,68131075303031487802831737043324380991725258443⟩
def resval5Tail192 : Box := ⟨273178374961153604869959200389700608015133908323,63991314384233539428750704883190966064367783199⟩
def resval5Tail196 : Box := ⟨300362799726740480870112442717163280927373928002,58729608792550509800914332867797671931980305905⟩
def resval5Tail200 : Box := ⟨330252390850905114577908862106445349291206423238,52188148530128401831346775939903496036334380592⟩
def resval5Tail204 : Box := ⟨363116343841394503359065242201665946915912069892,44190418128758684369366978526452616238425698868⟩
def resval5Tail208 : Box := ⟨399250642289143665454328421803471308423402572991,34539140078385110226636754555441143009576155540⟩
def resval5Tail212 : Box := ⟨438980723653599817132332466001448215127650378389,23014000909749507566888526003522436375794818536⟩
def resval5Tail216 : Box := ⟨482667221618571208136464517285565683805829820752,9368990424277799791908615634542738657260812361⟩
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
def polyval5Tail5 : Box := ⟨5389456297279347337224343019799356643648981118690390036384,3876577323497858392824783798285665251585803491723017626728⟩
def polyval5Tail9 : Box := ⟨5925767696986836705288064691698841932875386604779298352301,3942739832975981386353034027530923443373772296302974896876⟩
def polyval5Tail13 : Box := ⟨6515450486136327098949836325182358678281750192252449050483,3994705821920465106422425564888863392114121254200806257793⟩
def polyval5Tail17 : Box := ⟨7163813569705533957731064761063893779622150449365709005993,4029711417376514711008522162661847442260700269369680404761⟩
def polyval5Tail21 : Box := ⟨7876696319110728388114129844589929467982717211456515783557,4044629869005444340692339561272421373494293241921207303262⟩
def polyval5Tail25 : Box := ⟨8660519191322664501303807192615554390394960791157160284790,4035929715297599643125079240076391458189286222316214630716⟩
def polyval5Tail29 : Box := ⟨9522341553436470020098088853881949797219936570116386786336,3999628426641053280145648711177331918754664131104178140239⟩
def polyval5Tail33 : Box := ⟨10469925261657977638388425813138894571520565076336265437814,3931241039793305403129847933517329995388462645332983376184⟩
def polyval5Tail37 : Box := ⟨11511804567138625713758818643370294014401652777333427490342,3825723259621644248482098201247009588232009615982126066525⟩
def polyval5Tail41 : Box := ⟨12657362978253781437178811018345095798549560815754536688589,3677408450150543906788228611166724392493917898485091105257⟩
def polyval5Tail45 : Box := ⟨13916917771571494518023765727635031815769637667316094798323,3479937877659650130277869396601500610842222488250467494081⟩
def polyval5Tail49 : Box := ⟨15301812912645316475113415540912693422315010880665439908622,3226183503264755776847599376723139656197782546705481725110⟩
def polyval5Tail53 : Box := ⟨16824521223506467612581294168747031853813725578712731742722,2908162550480474826932058863772664653801028954789886666638⟩
def polyval5Tail57 : Box := ⟨18498756717009455373465591782769789543082850303257689781753,2516942994040049240239874949877689429569391793302494433403⟩
def polyval5Tail61 : Box := ⟨20339598109751291415510116917792558699069356524201910079439,2042539029000927255199840656827559372671732772348879339345⟩
def polyval5Tail65 : Box := ⟨22363624625973361051539399778723896365416329015063061810636,1473795483086190099956876493950251592091000957571993114807⟩
def polyval5Tail69 : Box := ⟨24589065409385414281962154049025844677209849018044191755259,798260024622382153524209760909197313309652784479516420202⟩
def polyval5Tail73 : Box := ⟨27093750000000000000000000000000000000000000000000000000000,2⟩
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
def resval6 : Box := ⟨80726173964067202934131626003756174955981261324178748609,12918376103489254087733422277978279758774846433852016241⟩
def polyval6 : Box := ⟨15334033610216409023519449244221350812110376469514389775935,3804102318035512853631433002009385176302736101295651911251⟩
theorem cell6_lo : Holds Q cell6 (63/64:ℝ) := by norm_num [Holds,Q,cell6]
theorem cell6_hi : Holds Q cell6 (127/128:ℝ) := by norm_num [Holds,Q,cell6]
def resval6Tail4 : Box := ⟨-33686913611761190080562119273242299942362983153043001647,12621125535813834449821878888937092719283347262626803426⟩
def resval6Tail8 : Box := ⟨-35313413767165607883602195547305257797799297105988056074,12470519305159195531067518182092913270607576334261102854⟩
def resval6Tail12 : Box := ⟨-37018386007788125656054653673706240247143900977727151073,12288421989843367371383036512884311200852867642692325747⟩
def resval6Tail16 : Box := ⟨-38805676262661841267137921052446098539098112833748660471,12072540708757811669645583877973770359758702043687288165⟩
def resval6Tail20 : Box := ⟨-40679258946769909200916499310448553268262016009996741612,11820447834389494990486855195416829166852391789348327908⟩
def resval6Tail24 : Box := ⟨-42643300357854635846924548228511224800993378549612000891,11529573146261933433826103472061046623159705060672279097⟩
def resval6Tail28 : Box := ⟨-44702167947299771644302251860094908254371181456259486109,11197196137266741314296695386625055365802161967813125339⟩
def resval6Tail32 : Box := ⟨-46860440032065280498868675681373244870282063658963351628,10820437922866854614921514489863626135934911639206272003⟩
def resval6Tail36 : Box := ⟨-49122915975519916533006893966935210217983603904827757901,10396252733062303072809678423306087756036700338349273891⟩
def resval6Tail40 : Box := ⟨-51494626859816087482369248186016544696348842171229213169,9921418966125793954849755943829039894085634795171681316⟩
def resval6Tail44 : Box := ⟨-53980846673539251595388223131397634540263799943456433265,9392529782074937177850139782758546601851392930541654050⟩
def resval6Tail48 : Box := ⟨-56587104039509895397802678024801099245437582283245371100,8805983212756271874699454103756960481509562044069299617⟩
def resval6Tail52 : Box := ⟨-59319194508817280078274021304337412743427155729040224710,8157971764270988523634128120255036486027973756013254679⟩
def resval6Tail56 : Box := ⟨-62183193448423265445165473670628260479733860210167969211,7444471486270761918183276328518837421889347164825959759⟩
def resval6Tail60 : Box := ⟨-65185469550990793574749441316351636101006703638719797808,6661230481391420879778085067343817362122089215220567404⟩
def resval6Tail64 : Box := ⟨-68332698991344938379695517690647824084646462960005536792,5803756826474105609377072135683160129705828788328644760⟩
def resval6Tail68 : Box := ⟨-71631780119984927210915610097829420092337966897740556169,4867302023217198466585527963787833847489091730777676548⟩
def resval6Tail72 : Box := ⟨789824162227424127897573841231146687642982243562667015817,778435087560758648379416041587815941235175790892520954⟩
def resval6Tail76 : Box := ⟨-445843529313896486645118554438800938859366932625826123,169216505879862175844232412221527775097422090780342203⟩
def resval6Tail80 : Box := ⟨-467342640016353269687213528806279597181246833085385605,167292893769712559186035426304294137100511940451366574⟩
def resval6Tail84 : Box := ⟨-489906478840001207826310508200822566513341548407561953,164954900947554187283427413248642902024237867058095673⟩
def resval6Tail88 : Box := ⟨-513559727126297690263598025944272397938680787086907753,162172098154196827189844397049629532923775971917482271⟩
def resval6Tail92 : Box := ⟨-538354981446470931844607468647105182428252933169267067,158912430850065156216419763373326092289563037641549831⟩
def resval6Tail96 : Box := ⟨-564347379164634761344347662437980867053902285810641407,155141959744178921475179100607098870691327234487156616⟩
def resval6Tail100 : Box := ⟨-591594719740992230400084816883402238488693791226553341,150824759033225314348727468475677712503170720995282041⟩
def resval6Tail104 : Box := ⟨-620157593260167591036863984470609087607097248698083585,145922809403362224510964994838667319617161522703787255⟩
def resval6Tail108 : Box := ⟨-650099515165761264053275728763953752715097372126447622,140395885512695305055021663557471115258072105515137340⟩
def resval6Tail112 : Box := ⟨-681487067500045929599435646162291719680323191480172281,134201437676673042307494800973803615143578162243845841⟩
def resval6Tail116 : Box := ⟨-714390046962877614050825937087672990640579577740528325,127294467464889967019534789862851371767852559717461571⟩
def resval6Tail120 : Box := ⟨-748881620119061301371051254207472549659009292520980487,119627396903343437311632371907308239433951683798505752⟩
def resval6Tail124 : Box := ⟨-785038486099306676307365840044544137425700030604271670,111149930961035453012459089657254263965049490193155791⟩
def resval6Tail128 : Box := ⟨-822941047156573226139834111674114055936246469099342737,101808912983913152059560175269805750013529491963108300⟩
def resval6Tail132 : Box := ⟨-862673587457088264401534013743597527717259301273413179,91548172722462368326287235773148778578418249924572836⟩
def resval6Tail136 : Box := ⟨-904324460519456548198353345831839835443590490340997720,80308366580759996873167725681436375319231082870471791⟩
def resval6Tail140 : Box := ⟨-947986421995636396842267387644287661055055015459903786,68026802837838222940322380111880269324105493853535505⟩
def resval6Tail144 : Box := ⟨-1067793224480227842988625962801875468092286027563374187,52276507429752080891376471723676457826196113760773770⟩
def resval6Tail148 : Box := ⟨221850152635188842044531957491617991942053403321,71484082047954772348995281361355808384831619996⟩
def resval6Tail152 : Box := ⟨232500686377605890279034645375285167050224627366,70121927922722390281136977678768381255766468172⟩
def resval6Tail156 : Box := ⟨243726085912679444036710446175102490711295221388,68541116238229047554881582212112724173199306157⟩
def resval6Tail160 : Box := ⟨255493461673085522615473279709901244166881925075,66725702561561644204408712725865216243300875206⟩
def resval6Tail164 : Box := ⟨267828979870305590748906570077899698849848486396,64659315682422200330639591198650306621643936878⟩
def resval6Tail168 : Box := ⟨280760071074355811949763636232734703485195286036,62324633220434007629256486449584331087185445264⟩
def resval6Tail172 : Box := ⟨294315490235031330862147162941039491336250223652,59703330563960502401073425207270083983554240807⟩
def resval6Tail176 : Box := ⟨308525380624177743226880044765893413120086301060,56776027194404447368505972244523113056306000971⟩
def resval6Tail180 : Box := ⟨323421340865476034070896046364308018103115437696,53522230250498158170296085303999727482881848773⟩
def resval6Tail184 : Box := ⟨339036495200503127676340518459720962228996747495,49920275193952013832712460779264634999084320150⟩
def resval6Tail188 : Box := ⟨355405567147318663594427538837039893908921403890,45947263430970534308142474268663828331410252225⟩
def resval6Tail192 : Box := ⟨372564956715373064091086395713445336354243085900,41578996736944274012490764440806158302756722852⟩
def resval6Tail196 : Box := ⟨390552821348440175404531327953849211487270079499,36789908324071429066064061843542643632015986154⟩
def resval6Tail200 : Box := ⟨409409160775567797590166515580034063299830254920,31552990383738164494848278356234283061903689265⟩
def resval6Tail204 : Box := ⟨429175905958729749680577057998350213945974963421,25839717927173156310289236991558356941143711161⟩
def resval6Tail208 : Box := ⟨449897012334994697494245734157885760153069488946,19619968739169106395564536354037681171145304344⟩
def resval6Tail212 : Box := ⟨471618557619439483643924100287625166641970623167,12861939246932917214076448892478477578866710287⟩
def resval6Tail216 : Box := ⟨494391623766738748830057107258924664693636693752,5531920950174490174016880264226326457411799844⟩
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
def polyval6Tail5 : Box := ⟨12129154883657523495939761923530314557407913338446397518843,3732800241393052293911245154909740380267386937116096099664⟩
def polyval6Tail9 : Box := ⟨12714762365840009550827987579959165468991278789580643242845,3652711546439407194531497022133068750024761830741536263462⟩
def polyval6Tail13 : Box := ⟨13328645717145371896193705924312440682548625398072426319120,3560459921442183134154748379115910026729638163430752074000⟩
def polyval6Tail17 : Box := ⟨13972168062928503184260549745129825510173083691921781576915,3455193715884324083053389147844098780658609191482647962173⟩
def polyval6Tail21 : Box := ⟨14646760407743231446838416395205420657606759262406476721840,3336011745432094974899480577070741253948037928431776179111⟩
def polyval6Tail25 : Box := ⟨15353922846879259937376053731080111237598277549533207566407,3201960620586520357403298416819506025162675139697322846844⟩
def polyval6Tail29 : Box := ⟨16095227901952423789232216110181693652435355372751370581453,3052031949047304849345391253971842489066085223105784065710⟩
def polyval6Tail33 : Box := ⟨16872324017730879715088278315129356121022250192211331221079,2885159394174592567807212252521739586674080491056064203745⟩
def polyval6Tail37 : Box := ⟨17686939227792226174288082159070915524934889378795244004632,2700215582316974888031101329676769183793459461626337337594⟩
def polyval6Tail41 : Box := ⟨18540884997162765972905031445586833615082247137297814593399,2496008851418403903891682732565892770786635384809691614864⟩
def polyval6Tail45 : Box := ⟨19436060250483812256259096841650334348026208504621293081970,2271279832941090157518288838516935112217414879170036619952⟩
def polyval6Tail49 : Box := ⟨20374455594662496937028119313166047010217706167245340170993,2024697858747453265276849839148338373633344925798121946961⟩
def polyval6Tail53 : Box := ⟨21358157745397017032487399947338857337507794093626681066839,1754857184170856470980427515827505396574004374295832059532⟩
def polyval6Tail57 : Box := ⟨22389354167419611317847430918666697006816896367698458794813,1460273018071248051322273934698468570503013422455962158022⟩
def polyval6Tail61 : Box := ⟨23470337938775816066484276598328916027864076773474233761468,1139377350216964328416798067097359382900155874769955015710⟩
def polyval6Tail65 : Box := ⟨24603512849967614883343634808542043445013601667643219395146,790514565856112338305432796171858327734889831221899185852⟩
def polyval6Tail69 : Box := ⟨25791398842113694108550782895128725322355678491859447476973,411936832434758526648048342297856784946727156517143985521⟩
def polyval6Tail73 : Box := ⟨27093750000000000000000000000000000000000000000000000000000,2⟩
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
def resval7 : Box := ⟨61150849996127624600218210019778801560946241028150901010,20959327977354304348759738272909806004863646642449416202⟩
def polyval7 : Box := ⟨24160569026532046195671487829221657196535281484747166641791,6644013432177298564097791838171855391834107643284324979520⟩
theorem cell7_lo : Holds Q cell7 (127/128:ℝ) := by norm_num [Holds,Q,cell7]
theorem cell7_hi : Holds Q cell7 (1/1:ℝ) := by norm_num [Holds,Q,cell7]
def resval7Tail4 : Box := ⟨-52522029281478747850759503164731382733414824667531377636,19967453599521556786789917385205952060516179189060967076⟩
def resval7Tail8 : Box := ⟨-53350818669793071216610630267695609515578584740753749024,19138718231599436440753567036517302757398083659470888014⟩
def resval7Tail12 : Box := ⟨-54192629943391344223498262730282414899681804212165713817,18296906964166662578310900822990482268116589396000015511⟩
def resval7Tail16 : Box := ⟨-55047723972398013759447998302678557688715788719528575614,17441812935165260060515160212099850237282513072898825275⟩
def resval7Tail20 : Box := ⟨-55916310348960159655175188165501418490763859181388815302,16573226558603133726371284632945455449852465335017179529⟩
def resval7Tail24 : Box := ⟨-56798601965977415168738058326264926041704390077955090043,15690934941585878453587081483503932101746004468579608067⟩
def resval7Tail28 : Box := ⟨-57694815075535950015465969597729513146312233271951637852,14794721832027343615005993516431406205213058865210276004⟩
def resval7Tail32 : Box := ⟨-58605169341917775981388925707498282215894210068969238193,13884367565645517649701948569985216504073558437046377274⟩
def resval7Tail36 : Box := ⟨-59529887895441082034144339393703554314304099388113885852,12959649012122211596994940257431239220625111663044437948⟩
def resval7Tail40 : Box := ⟨-60469197387150085227322395366007772565046041349296699749,12020339520413208403699640090906099996780865969494827818⟩
def resval7Tail44 : Box := ⟨-61423328044367820957313658961263672358723425721625630815,11066208863195472673024150915729928736062872517199466953⟩
def resval7Tail48 : Box := ⟨-62392513727125488920221813156361276077265338604914240780,10097023180437804702975344414484130811830717980998476231⟩
def resval7Tail52 : Box := ⟨-63376991985482185626378643793190363621725264273093745242,9112544922081107811687820681856141215679861558819314482⟩
def resval7Tail56 : Box := ⟨-64377004117749060645829315591749661290280302003806084701,8112532789814218590947605042210708799267757118638968373⟩
def resval7Tail60 : Box := ⟨-65392795229628526754423969625218329086887915483281442298,7096741677930773874959487298525462393078856468661809970⟩
def resval7Tail64 : Box := ⟨-66424614288688091727436221850086498100555903282881128223,6064922612959165189603320241200585448698242766978393517⟩
def resval7Tail68 : Box := ⟨-67472614772244007469937190295208403243842617758161785541,5016818869153244893086984432262532311357506045878043071⟩
def resval7Tail72 : Box := ⟨789621639616498236972980081076524286799466227533318055536,883945138065192041579382273669694759399881606311793572⟩
def resval7Tail76 : Box := ⟨-697524385151055504347271079354019311459059592424784888,267366194406260889753357249215460017057832735980182436⟩
def resval7Tail80 : Box := ⟨-708504587285897628170432736436680107261150447001598325,256360344109630184637053914665074660187876579791317187⟩
def resval7Tail84 : Box := ⟨-719683929767543396554940763981172106923482694413181924,245181000302669849912895695414694035877298503553966879⟩
def resval7Tail88 : Box := ⟨-731039670053935222555002223025227494891776790572303631,233825260015561283942817158137401805816292164722789543⟩
def resval7Tail92 : Box := ⟨-742574590161687608037752439574452058288732242351802820,222290339907807011194784847201040726868852254476507146⟩
def resval7Tail96 : Box := ⟨-754291517330539401520610643504706478412458503751733378,210573412738955200003358807166384735574697354113313617⟩
def resval7Tail100 : Box := ⟨-766193323411353826645525005881019420600779474402621600,198671606658140774388353906992122362988931290208483554⟩
def resval7Tail104 : Box := ⟨-778282925569322381497977153794630305534845061673440497,186582004500172219501308804526988569169994163295665388⟩
def resval7Tail108 : Box := ⟨-790563286998968233913001681191215263551440306238239301,174301643070526367081147738987166166772905392261726968⟩
def resval7Tail112 : Box := ⟨-803037417650433280643387766274181329299455751946047692,161827512419061320350260126666595029452452560351262649⟩
def resval7Tail116 : Box := ⟨-815708374967225151329302609158380129769666161975373213,149156555102269449669469804797864003260379897384777440⟩
def resval7Tail120 : Box := ⟨-828579264635604966561603671756546272643203489696451618,136285665433889634493732778462139273140652394757085664⟩
def resval7Tail124 : Box := ⟨-841653241345799527814179674554191478798339712025626382,123211688723695074484587817320080289660930710484665742⟩
def resval7Tail128 : Box := ⟨-854933509565224590090551243325735241495388889331348955,109931420504270086522370569590630992212543888743721189⟩
def resval7Tail132 : Box := ⟨-868423324323924965741497626525123262736890897687219476,96441605745585035083191857312933475141574978428409726⟩
def resval7Tail136 : Box := ⟨-882125992028155869406511209972482256465499741475231653,82738938056172760615792007013108274970368118632702004⟩
def resval7Tail140 : Box := ⟨-896045006588227628182195995280648595138625843973098260,68820052072713392759448763976169157722195592803637418⟩
def resval7Tail144 : Box := ⟨-983650540592858366526055746643767277395930457103524963,52341764712094160066941639611998659937009322099387627⟩
def resval7Tail148 : Box := ⟨384971764015660498991054564292499612148318269177,122957760389326682971834647045095058468229423723⟩
def resval7Tail152 : Box := ⟨390987403077197525564951133190370957528565987089,116883808987014438781841352695882396318818044048⟩
def resval7Tail156 : Box := ⟨397156709500751307931188684011221618515502591169,110714501573272196265080795292360519492849764972⟩
def resval7Tail160 : Box := ⟨403423361095448888347380923458306511787837002223,104447849978273304050382426633968577497301947001⟩
def resval7Tail164 : Box := ⟨409788892858580163220556874606138042175956612736,98082318215141525419493043225703071883521552236⟩
def resval7Tail168 : Box := ⟨416254864999079788684970478405394316979477893715,91616346074641896767995226678341084597075355557⟩
def resval7Tail172 : Box := ⟨422822862344386873294163327835708557623931953642,85048348729334812096955712650704675759863693719⟩
def resval7Tail176 : Box := ⟨429494494728597482311692072629164561796611024722,78376716345124203076248985146284486380066244801⟩
def resval7Tail180 : Box := ⟨436271397387038896842909701996772460379694116639,71599813686682788544658470122441221487944816742⟩
def resval7Tail184 : Box := ⟨443155231357070257920219297822029319889870439607,64715979716651427467280493244136256861462897483⟩
def resval7Tail188 : Box := ⟨450147683885207361884351134197628347105052570496,57723527188514323503210170895664510335395135801⟩
def resval7Tail192 : Box := ⟨457250468840671391723735619123538191486261436921,50620742233050293664524216159158899880824502572⟩
def resval7Tail196 : Box := ⟨464465327135462946260414692332023171132433395091,43405883938258739138592656772708241501668282084⟩
def resval7Tail200 : Box := ⟨471794027151064328864687974378297667589590569796,36077183922657356934168614567803322773356582110⟩
def resval7Tail204 : Box := ⟨479238365171874729395751335116582051585572143531,28632845901847001766108250072582927995080479654⟩
def resval7Tail208 : Box := ⟨486800165825506159023569261101092861859329071925,21071045248235812602414599963556308092886712272⟩
def resval7Tail212 : Box := ⟨494481282588517021576117116357145725469923939404,13389928540263451757332225568403980971285367430⟩
def resval7Tail216 : Box := ⟨502286356896892385971996237890940707177788386164,5587479133360565658343373802695290431124668899⟩
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
def polyval7Tail5 : Box := ⟨20719268556463875376890794606492091854456599741143059790492,6319594479736132974493162544812948550462495752994506761895⟩
def polyval7Tail9 : Box := ⟨21046191504985473863207682513323251768326485744337796634583,5992669550200394437126200020095978021726448065759267895538⟩
def polyval7Tail13 : Box := ⟨21378274902634434288745358495627123555267074837219420280716,5660586152367600476914620488035874866133259428778062118751⟩
def polyval7Tail17 : Box := ⟨21715598174058543978077109498823366108051873175236033052048,5323262880943352490355507749166795522318548668203769622341⟩
def polyval7Tail21 : Box := ⟨22058243997932066775890381407960417833757010940405484953911,4980617057069829231087497191087894650512181354684747332888⟩
def polyval7Tail25 : Box := ⟨22406296357682562492575923281134437350285602835808125342105,4632564697319333509209385399884105014827554986689852157835⟩
def polyval7Tail29 : Box := ⟨22759840561894441688736688894261625666123068995858150537978,4279020493107454312882793734595876881609037307003859444397⟩
def polyval7Tail33 : Box := ⟨23118963265218199041182311913695334122466513583215047057179,3919897789783696960424095783701934899621558259287945631326⟩
def polyval7Tail37 : Box := ⟨23483752489609704530201531067466547767879215420930216254776,3555108565392191471402805292436522166830763193737540901792⟩
def polyval7Tail41 : Box := ⟨23854297645904625334606368326365272693637235749318759377611,3184563409097270666997877787204591837610939649892265800598⟩
def polyval7Tail45 : Box := ⟨24230689555733265964404526885928702506624779307622671625388,2808171499268630037202711341959801859408451139301251310819⟩
def polyval7Tail49 : Box := ⟨24613020473781198014144835982931604307759810758991943690188,2425840581220697987495819648644906693863660809042936057635⟩
def polyval7Tail53 : Box := ⟨25001384110401135678698273476557844675288952078212466013273,2037476944600760323709316486273556620057487497985278687209⟩
def polyval7Tail57 : Box := ⟨25395875654581599312775083515089015979381356748481082952302,1642985400420296737535531598820723165484864193552201399378⟩
def polyval7Tail61 : Box := ⟨25796591797278007582585227029480855263996991220973223269210,1242269257723898743006327443259577042432220604585591308186⟩
def polyval7Tail65 : Box := ⟨26203630755122728693471606109586649098596239291617549883024,835230299889382684482721244644251564753862603131760457820⟩
def polyval7Tail69 : Box := ⟨26617092386659546503940070732817425998651667545284700578078,421768756186720050596482565219423925799637144511903300042⟩
def polyval7Tail73 : Box := ⟨27093750000000000000000000000000000000000000000000000000000,2⟩
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
def pend : Box := ⟨1030800259838324484154737198486608612534724648315474669491234,4322620384860605032081180784900053644740812556822130147⟩
def zend : Box := ⟨1003758709275718370234570312500000000000000000000000000000000,2643113038841356132812500000000000000000000000000000002⟩
def betaquot : Box := ⟨428750786186702858758273990711161992124758693233236025918053,394772360413912572860303906585280802176864521260533979⟩
def crit : Box := ⟨122741216930754577454336119244179843896142755318993019646,10896604712685524857079870241919876834394990429656029755⟩
def subsonic : Box := ⟨507320673773053130605779821387344394082827407612394907517,5672916224250268224862863390719432909215070503756623126⟩
def pendTail4 : Box := ⟨27037260848231316512291077887693188223238509200984518552297,1565673847911317209274025470322677610887834052593010759⟩
def pendTail8 : Box := ⟨27037295519092601256023736370117963108698282610147113113580,1565534462981960004637984076344199410312448688284759721⟩
def pendTail12 : Box := ⟨27037295520554649518780759243265218534835984977692407993302,1565534446555596389947152548782575842708761881504691472⟩
def pendTail16 : Box := ⟨27037295520555352043364742081080311697878404597836919599744,1565534446542340996095800409419757617133731428579194270⟩
def pendTail20 : Box := ⟨27037295520555353694758469716172502472991849762967640617134,1565534446542293338680732950382478679509142778527527186⟩
def pendTail24 : Box := ⟨27037295520555353708531724746491573075171955529461781469653,1565534446542292736881303255787177387917671108751365308⟩
def pendTail28 : Box := ⟨27037295520555353708867224049753602601031825099835424629804,1565534446542292713934462151473556198899768950178298639⟩
def pendTail32 : Box := ⟨27037295520555353708887671992074409809504894155168720920104,1565534446542292711523774359442876540603661303610008116⟩
def pendTail36 : Box := ⟨27037295520555353708890153989093648757650560004411051507416,1565534446542292710861644427167222770468127836705873162⟩
def pendTail40 : Box := ⟨27037295520555353708890153934812545128699422540903449050434,1565534446542292710397523388821914268811795658769476736⟩
def pendTail44 : Box := ⟨27037295520555353708887644642320213343550292614997111073584,1565534446542292709568082880577848246035989156068481792⟩
def pendTail48 : Box := ⟨27037295520555353708866405265663513505348972045972523502755,1565534446542292705706080443835745396583417560579606768⟩
def pendTail52 : Box := ⟨27037295520555353708495627960715993494025479666380149644416,1565534446542292656541612522080788843015691644858152369⟩
def pendTail56 : Box := ⟨27037295520555353691294546245545324721814542512614679846068,1565534446542290793652185103169442375081904501650626746⟩
def pendTail60 : Box := ⟨27037295520555351115284652894536223508775303896149714573553,1565534446542075973553684808942629942182117358355520061⟩
def pendTail64 : Box := ⟨27037295520553712905549041318792543268770600911222192088724,1565534446439043291647239196367464711221734506221326556⟩
def pendTail68 : Box := ⟨27037295513196725461383829674756751187508667699833613941001,1565534097632548330356128649704409554705470419000618493⟩
def pendTail72 : Box := ⟨27036345528903203188894580816618534634089977616189685533811,1534159800668576119403475552837296915074960858987827107⟩
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
end SepticProfile.ExteriorCertificates.C17

end
end

end OAI
