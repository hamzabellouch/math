import OAI.MathematicalPhysics.Transonic.Certificates.BarrierData14

namespace OAI

section
noncomputable section
namespace SepticProfile.ExteriorCertificates.C14
open SepticProfile.ExteriorJet SepticProfile.FixedInterval
def cell0 : Box := ⟨250000000000000000000000000000000000000000000000000000000000,250000000000000000000000000000000000000000000000000000000002⟩
def resval0 : Box := ⟨111722702913271729798614184495682106616198664407439153099,337330221333125368133725295469718248651165872125552441⟩
def polyval0 : Box := ⟨3785569907349671246113670870362521328707972246089896799041,15234892746413564002333020105953517521855852532439568499⟩
theorem cell0_lo : Holds Q cell0 (0/1:ℝ) := by norm_num [Holds,Q,cell0]
theorem cell0_hi : Holds Q cell0 (1/2:ℝ) := by norm_num [Holds,Q,cell0]
def resval0Tail4 : Box := ⟨56182970542234567277031273563740441300099341380756,1718026773153242404048093459874538388537224807783⟩
def resval0Tail8 : Box := ⟨6653177487992407896694724286789092890976974863,366137147618994157749328415130029431231294788⟩
def resval0Tail12 : Box := ⟨5925148262809458083555984214485298251948713,493698313792640699906632687373646777251261⟩
def resval0Tail16 : Box := ⟨23232120708685484242299059484714344155618,26111359299729478811155080645546116807607⟩
def resval0Tail20 : Box := ⟨309888541628935840109283562552993018155,373969953956896171018409470242120691397975⟩
def resval0Tail24 : Box := ⟨12068699213912584197774806434202095704,5982712965253975268444118203303571852422539⟩
def resval0Tail28 : Box := ⟨1248803096347684246564038794676904290,95723364530515936605146242215899035806757815⟩
def resval0Tail32 : Box := ⟨322355716897061901464644292235027662,1531573826388966955646895789772226798975101625⟩
def resval0Tail36 : Box := ⟨-338203587334418494663236416906406859,24505181219835380317614484639618013105503171965⟩
def resval0Tail40 : Box := ⟨-138915609696712982560390685371863509138,392082899386023577441476318095984902655556078146⟩
def resval0Tail44 : Box := ⟨-35642120206767118443088507578694196881909,6273326356759348300297099753782639450757765389176⟩
def resval0Tail48 : Box := ⟨-9124677544442168383043615256065941855842982,100373213153748037175391512474013183703955173521958⟩
def resval0Tail52 : Box := ⟨-2335920115939104313844951375769724090935083519,1605969220534540618298520052918846942509905639893025⟩
def resval0Tail56 : Box := ⟨-597995603533581556477044871611737937032851859334,25694946907653241740963559766327155396178043821717428⟩
def resval0Tail60 : Box := ⟨-153086873045226172964033127867115079434715778877696,410975631573466976830694740655049397085691188908668648⟩
def resval0Tail64 : Box := ⟨-39190227994263032466057418247565392951653641260422714,6538869258394249459636852231744172224007288887476582091⟩
def resval0Tail68 : Box := ⟨-10032428218779670759466247501262038588156918778670395172,95216363974146981263742594059469191824578405722704662166⟩
def resval0Tail72 : Box := ⟨771118769453892625082198111064875039806280103935682956420,2474259443420412960359397008966028449640340440776472004⟩
def resval0Tail76 : Box := ⟨-25808903272684999346180961354432696396303845555957,586890936543486555258185482255123538303094948786⟩
def resval0Tail80 : Box := ⟨-1365386846191556945907082818854096204843859731,64460167459159797854314085372895530659493526⟩
def resval0Tail84 : Box := ⟨-756056684057608991074083274227146911389913,56031398956968865619220719718031932184240⟩
def resval0Tail88 : Box := ⟨-2048179296031444516219743459307821933531,375945767308296950791182601828057929896⟩
def resval0Tail92 : Box := ⟨-19975572564396127910761455370643429732,2512803071139466831380326547346361600525⟩
def resval0Tail96 : Box := ⟨-588789896155383274672539593719103093,40157350836509584944991249472825513153219⟩
def resval0Tail100 : Box := ⟨-47116590315505386968324179492242186,642515695145935828116468865460461593163230⟩
def resval0Tail104 : Box := ⟨-9597995197237781726573970309500452,10280250911799852575010838817107180871538611⟩
def resval0Tail108 : Box := ⟨-6608192190788256390343336924383832,164484014528545672173653579344547127968367033⟩
def resval0Tail112 : Box := ⟨-470482008135445798720446914577209865,2631744232025486276296929284119172564306258639⟩
def resval0Tail116 : Box := ⟨-118972718353894891613560259205173747804,42107907600888915305145267294128593188887829982⟩
def resval0Tail120 : Box := ⟨-30452722861849545598173778314536657257914,673726493064891705415041640379974959760738605716⟩
def resval0Tail124 : Box := ⟨-7795866363439079203860335259524710040554596,10779616580415152864740924931232186008366702379599⟩
def resval0Tail128 : Box := ⟨-1995741272198054948099797642227352202244657721,172471994279286996595005487307077865964939908637537⟩
def resval0Tail132 : Box := ⟨-510909759387194358445764330013022792322376867793,2759072930587214027902770274657980854895685079131316⟩
def resval0Tail136 : Box := ⟨-130792926211522186393367545550581826363952195674907,44022548539310957120433399443450457204877758767551807⟩
def resval0Tail140 : Box := ⟨-33483334803535709606111034406878210215005891764401765,672970316324911907772266529070296493932062023557671549⟩
def resval0Tail144 : Box := ⟨-8802717220994613222878245758944834959297746655246312247,2615841116461829962546874425990802219326441771460706910⟩
def resval0Tail148 : Box := ⟨56749189777069255236071300574743555139455929,1074247169093031330139717857641049190179836⟩
def resval0Tail152 : Box := ⟨990164121377553740863303159249153149503,41726420911382508569829222876288767795⟩
def resval0Tail156 : Box := ⟨307944575743787620703215700081665068,20806055740440749115933419578941448⟩
def resval0Tail160 : Box := ⟨528046069257524988953875238622701,53358548334988916556341409838346⟩
def resval0Tail164 : Box := ⟨3451509842623394451724420089384,27241705607104276705352024810835⟩
def resval0Tail168 : Box := ⟨70377414284413650644218528698,428365888256137618209310904072864⟩
def resval0Tail172 : Box := ⟨3961548987966097765218937553,6853645748347228782672957248913260⟩
def resval0Tail176 : Box := ⟨570886410722616413827288866,109658316028204357121601158168566199⟩
def resval0Tail180 : Box := ⟨207842126351867863097994097,1754533053294034431580930791666200148⟩
def resval0Tail184 : Box := ⟨1776453719133317620479257907,28072528850160760980560378493080336510⟩
def resval0Tail188 : Box := ⟨411333927754949424207460320666,449160461217367869672159300646940899556⟩
def resval0Tail192 : Box := ⟨105213782291058858736055705186246,7186567280841400573919653351752055694364⟩
def resval0Tail196 : Box := ⟨26934300650300320462091649955651447,114985051242570122044736067971595551036409⟩
def resval0Tail200 : Box := ⟨6895175934305057456331247766745331232,1839754355654148280784768864317827181668207⟩
def resval0Tail204 : Box := ⟨1765164923084502024855393701910279795630,29434414848402089704111485770461019597497999⟩
def resval0Tail208 : Box := ⟨451882242143646024895850837811487521798448,470526997996078732610076997700754653776061936⟩
def resval0Tail212 : Box := ⟨115681982601655763698282400633600971090600212,7419980176625348413638767688049339901614771864⟩
def resval0Tail216 : Box := ⟨29622085725543691923512111680726997199829252593,90952348494986935459437242976523324398594759600⟩
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
def polyval0Tail5 : Box := ⟨2042113289153763019713608879045822526124300935965116,51737595012874455890781826621405302739318203074382⟩
def polyval0Tail9 : Box := ⟨193830911428693830487765906106901961035894877232,9690885013272696516717072380200116227510567647⟩
def polyval0Tail13 : Box := ⟨149359920613642731581603712423896700480972069,11576269819753047163059011601160800170074739⟩
def polyval0Tail17 : Box := ⟨513176449702990628522544493256025008824522,429110156295746275332576000012635519730761⟩
def polyval0Tail21 : Box := ⟨6014765951212019562150618706996372286906,5955239849763380879796138603896915964678868⟩
def polyval0Tail25 : Box := ⟨205600078638438737529463562073998841375,95269050773600680857376884438306974585440233⟩
def polyval0Tail29 : Box := ⟨18606340053000916058739088944217162781,1524304121309551109094082373124130917726885443⟩
def polyval0Tail33 : Box := ⟨4226246462298018587549833213592056488,24388865855263069303439633957059248226843995945⟩
def polyval0Tail37 : Box := ⟨7958118736681171123259722243927466093,390221853655484844855529820613364657221966685510⟩
def polyval0Tail41 : Box := ⟨1451756409216435915517826324661618267340,6243549657131707211598416040940612202057967087184⟩
def polyval0Tail45 : Box := ⟨370887177216499064266830779544723175115948,99896794166410487745101676043641439690849335825530⟩
def polyval0Tail49 : Box := ⟨94944734557669613876046082465656559576290251,1598348617651936080414262288554097511377598030045076⟩
def polyval0Tail53 : Box := ⟨24305833987237288663721008088961684189419735448,25573555095712614312604408848091027643018519161274205⟩
def polyval0Tail57 : Box := ⟨6222293182958097081593019946572773317522818750981,409171048131600059763987913781108866530756192612039551⟩
def polyval0Tail61 : Box := ⟨1592907051669091464551935806895864376168016346872373,6545243419757011206342587628473567489032047994003897688⟩
def polyval0Tail65 : Box := ⟨407784224917458992863068010434632114021085122815609486,104341597018087691466278690232589201777033599618068033198⟩
def polyval0Tail69 : Box := ⟨104393003220133985422200255432900715961541230617655571277,1571597228425227662433169328439945809908974621361876959271⟩
def polyval0Tail73 : Box := ⟨26906250000000000000000000000000000000000000000000000000000,2⟩
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
def resval1 : Box := ⟨111501949826179174391755632604226625562964481957880672869,262377286330908881204813032174489505852068368142470130⟩
def polyval1 : Box := ⟨3767581588699063426037587844248935877011840123509886455925,9110500132213823325102549558928425885971626969448978153⟩
theorem cell1_lo : Holds Q cell1 (1/2:ℝ) := by norm_num [Holds,Q,cell1]
theorem cell1_hi : Holds Q cell1 (3/4:ℝ) := by norm_num [Holds,Q,cell1]
def resval1Tail4 : Box := ⟨54561204870640545320564424300015800286862041284517,3067785837653940071524690326254859832173980744108⟩
def resval1Tail8 : Box := ⟨6270359522086735697163634127713987053936901506,6146442083835417427910120043079908844415570525793⟩
def resval1Tail12 : Box := ⟨-318590898128691499907749129525505948659981986,19424956472319009905748142912202595459832471151495⟩
def resval1Tail16 : Box := ⟨-2123931700714095445267829604831698532698742023,61391354542349635683778920744157939507491652131300⟩
def resval1Tail20 : Box := ⟨-13919536287046901155704099217903650745208929556,194019790270861886398406803475297876077744162121942⟩
def resval1Tail24 : Box := ⟨-91223074788492858043500982074007499875021710323,613151119032537807258163864768429215350365391980632⟩
def resval1Tail28 : Box := ⟨-597839543000433176183792263063456976364100209928,1937550797240676259300016248860500206765530806385107⟩
def resval1Tail32 : Box := ⟨-3918001229014152695406677583530375150459153661623,6121588801445324626219529454052612173019326517610365⟩
def resval1Tail36 : Box := ⟨-25677012854468692067906789352990252087763031580267,19333949425227392658027167165706988434093569328325978⟩
def resval1Tail40 : Box := ⟨-168276871443046823686236989863946977642302054607639,61017702982247774385866061640894459113129532021959143⟩
def resval1Tail44 : Box := ⟨-1102819304689152348720420299354634226102285315513945,192275092331667022998538144129487341926412211615667155⟩
def resval1Tail48 : Box := ⟨-7227436595210826590223327098814278826323430983304947,603942259440680289360755638144511860170169376079399180⟩
def resval1Tail52 : Box := ⟨-47365728470373528193690468857740169165730606844238096,1884232323198615495762378818309019345483254933494854314⟩
def resval1Tail56 : Box := ⟨-310416038103426050654860125626278795900120244274678221,5794387680751635749694639506346366142511041433172274560⟩
def resval1Tail60 : Box := ⟨-2034342547310309438233467753808510746652599448153011142,17259851922153383140929664295345977820517041875672371379⟩
def resval1Tail64 : Box := ⟨-13332267311286339111715397990481759908809101902506030219,47646915203263145956775256682255501097794273151931923712⟩
def resval1Tail68 : Box := ⟨-87374223311261272074825058704789066608136779922209716838,105349996626396214937878115166582313822084649246990007961⟩
def resval1Tail72 : Box := ⟨773891672226423827185954560304029445952775003787121513946,1550396477670305549208694165659198288861308117325692261⟩
def resval1Tail76 : Box := ⟨-25236204495565027881113045098819610464055607995325,399677071970613513326526367728405934522101629807⟩
def resval1Tail80 : Box := ⟨-1305325262723155463741144284438164226378353865,61857129138300901640375418423940504618197743593⟩
def resval1Tail84 : Box := ⟨-3417143837982221063822398232340353150914410,195368807532383309434629077378357935096624799790⟩
def resval1Tail88 : Box := ⟨-17768276516805867415596053262498224281794850,617452713625315362974705344089880167113142902925⟩
def resval1Tail92 : Box := ⟨-116433963178412646294510616224409193740233721,1951395206658402044776505343915386553772144758926⟩
def resval1Tail96 : Box := ⟨-763061505454969845833734861975608670945876634,6166977432255167818202670090709192499179395579057⟩
def resval1Tail100 : Box := ⟨-5000799878863724799220887820002784590245353442,19488104958177816619084513958858748114555135180417⟩
def resval1Tail104 : Box := ⟨-32773242085871201552504477831918483547881217689,61575067178438825435113094791130993512530093102976⟩
def resval1Tail108 : Box := ⟨-214782719333918517488332027869495171817530750739,194496416634423125126546664142979897250605325530108⟩
def resval1Tail112 : Box := ⟨-1407600029426748320716306790687548365206156040010,613975943607138713963938702122303578256987131178829⟩
def resval1Tail116 : Box := ⟨-9224847552851121700885157901014017660129752630258,1935691043446664408196148779597751115473398622125741⟩
def resval1Tail120 : Box := ⟨-60455960922365118691744077266077516033245491076591,6086438706927955593204700989348629240029254484179355⟩
def resval1Tail124 : Box := ⟨-396204185500813159104598855799836198193523527780187,19031018468445880448264137279946864991388669825136670⟩
def resval1Tail128 : Box := ⟨-2596563750098214948078034200443057507107470029977855,58803053526572885235069779394069353707952991600111426⟩
def resval1Tail132 : Box := ⟨-17016840192662575176356850717724417202616651209801519,177036271200288214874537326342665399766783132857186532⟩
def resval1Tail136 : Box := ⟨-111521563905357046679651625918892233126380011344181604,501782096808285747090764419957659506235151983614647315⟩
def resval1Tail140 : Box := ⟨-730867886005594622225749432706312567574095266670371553,1207474679947489884495573319070998428523459728749033317⟩
def resval1Tail144 : Box := ⟨-4886023002830128601559447188098968405210533316992847747,1317941289067930278724816752159131302586129270711717478⟩
def resval1Tail148 : Box := ⟨55912130726070547391804103816695833652166438,780343131648806000474633620311359113627412⟩
def resval1Tail152 : Box := ⟨952494834755366946999123307212983347116,2779491248026270740582980674583956231442⟩
def resval1Tail156 : Box := ⟨396317085156257023250176464089387689,8697454156839603627196717119306461701965⟩
def resval1Tail160 : Box := ⟨699000359242433060393450140196469057,27487887027432921874386008640659774892901⟩
def resval1Tail164 : Box := ⟨4577792273361187597229924254737552333,86872927131638785336601938157821740536771⟩
def resval1Tail168 : Box := ⟨30000999248159583932941894463942162067,274545817022117825117816885958244141496533⟩
def resval1Tail172 : Box := ⟨196614548274386119515248864043278313972,867598563395603030285407879508674836928900⟩
def resval1Tail176 : Box := ⟨1288533103549543317168969824640440486688,2741372770027706956111082677475269024399715⟩
def resval1Tail180 : Box := ⟨8444530547419386469756818701741720245982,8659719587990871364157691491980728211819766⟩
def resval1Tail184 : Box := ⟨55342075395566778559666526209215723705089,27340337114058783809072627369831424099746024⟩
def resval1Tail188 : Box := ⟨362689825312385843405143521940214775348249,86221185143827289842447184968118029691408253⟩
def resval1Tail192 : Box := ⟨2376924039167251418190347798457300702235320,271270878332434686596274183331639738234709933⟩
def resval1Tail196 : Box := ⟨15577409383086505966425556563474440571029363,849284780828396169425326959478101968235457918⟩
def resval1Tail200 : Box := ⟨102088110132996146457559271696805140254519352,2631303503374900058012986314563291817212674706⟩
def resval1Tail204 : Box := ⟨669044638567657332771956049211707751349033629,7969822683136353076618338793183545918051842259⟩
def resval1Tail208 : Box := ⟨4384650943341826690292428030999015140964718126,22918435900581819706397310835427370253018795860⟩
def resval1Tail212 : Box := ⟨28735248490736798452329712880874427178698191477,57555988996386650162741049367486589029057391735⟩
def resval1Tail216 : Box := ⟨188322634124486911547686432399213780808221782690,84402932086712247112017770722071893050140578355⟩
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
def polyval1Tail5 : Box := ⟨1987343817833571726122864061680320793844592898449218,117335414338638592465225843794133381896770724915912⟩
def polyval1Tail9 : Box := ⟨186772722416882064516639081906174926866637505060,270890227850620138112019309807257512408988604718853⟩
def polyval1Tail13 : Box := ⟨15324678986673027868165009072036796516222362361,856123253386377947358707815170653513436882485332430⟩
def polyval1Tail17 : Box := ⟨99521865519306418770734020936671776539350137956,2705720732087913348100573334082770563405901477082799⟩
def polyval1Tail21 : Box := ⟨652223451506165807737681777300692391572004565189,8551075985110388867658697490906951397266418642239768⟩
def polyval1Tail25 : Box := ⟨4274411577143054521269098434850776511018687026872,27023409803120338894840647709916124331980443642261312⟩
def polyval1Tail29 : Box := ⟨28012783710823772211606131285591693610932379191234,85392816339283138713782400828575020517523994721700307⟩
def polyval1Tail33 : Box := ⟨183584579327156636119233864296536674795958653411918,269788418574826554414124204132262649568098539957644817⟩
def polyval1Tail37 : Box := ⟨1203139899078433366100996352952313944610275952692271,852041709575777730251125103290077240696771872226729106⟩
def polyval1Tail41 : Box := ⟨7884897642600411484641270087901311361394979309327449,2688790182179167212593118719130548756974071649744930752⟩
def polyval1Tail45 : Box := ⟨51674465190546048842649975949142725734545423833856272,8471150478443682489138578093099911384304465243385581375⟩
def polyval1Tail49 : Box := ⟨338653775072762592965833093597338771513727087243612955,26597681849252700456987112423408339825458259726129926758⟩
def polyval1Tail53 : Box := ⟨2219401380316857644075590927227228184459316526107182472,82912721086687075586325289110949345270636432112508206995⟩
def polyval1Tail57 : Box := ⟨14545068886044614682094332345460154380983890766812266668,254514478663992552741150704017669077815459450932386495551⟩
def polyval1Tail61 : Box := ⟨95322563451594881609984129582881030560399320702791865445,755038475718903187499387932822318246387706212565008132077⟩
def polyval1Tail65 : Box := ⟨624705951849502337928043998717337248434318701317244320054,2062854863317137848595532193804300770080732367298214746399⟩
def polyval1Tail69 : Box := ⟨4094073041333910119205850578069102029039386974397430915494,4399946417842857795744395607146144109896678982633327129466⟩
def polyval1Tail73 : Box := ⟨26906250000000000000000000000000000000000000000000000000000,2⟩
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
def resval2 : Box := ⟨111393259831566300948927529952761840464138408130731303644,245039321473827595653068993780601543352679456049616313⟩
def polyval2 : Box := ⟨3758692912564989657338908986310231161323786522473990349398,7840502112162734732933729001810545297244444341432621861⟩
theorem cell2_lo : Holds Q cell2 (3/4:ℝ) := by norm_num [Holds,Q,cell2]
theorem cell2_hi : Holds Q cell2 (7/8:ℝ) := by norm_num [Holds,Q,cell2]
def resval2Tail4 : Box := ⟨-139404550984561936101545639881534125563223328987372,33998355620476813130573686127055355300580335909403172⟩
def resval2Tail8 : Box := ⟨-443299447931857877729485639946506615623586341186692,57884634608658456806989570267070219484574941742455690⟩
def resval2Tail12 : Box := ⟨-1017207961699726688406155108241207997782982875781761,98487682710783074997715202600074288285083841073457648⟩
def resval2Tail16 : Box := ⟨-2334082886639320036037443569103723480636559730629136,167416867640388300426906170046038990038047514036331428⟩
def resval2Tail20 : Box := ⟨-5355780822103661695398425656642344545680063053923591,284231846565977388900089341438838939326361359121143197⟩
def resval2Tail24 : Box := ⟨-12289361435433009244811453570836786825343315972979668,481734346095421194464269599620968514526708040980505271⟩
def resval2Tail28 : Box := ⟨-28199138371644490642133889890879396258124430932198830,814583496383198846243285272381296062040452970510753729⟩
def resval2Tail32 : Box := ⟨-64705673202062021441302884465472181606692238176234508,1373044294293080965112960100872238549481466056270202042⟩
def resval2Tail36 : Box := ⟨-148473477783352706438020443413478850302259891983165343,2304264492587370189595012561108985489068392193431428995⟩
def resval2Tail40 : Box := ⟨-340686875109758165769190356757422471802413924803446331,3843575818200729540220150933000909327906824851246113171⟩
def resval2Tail44 : Box := ⟨-781739261482199893014976972890268813870673205838768232,6356428165339856601136047201261907515175643009244633505⟩
def resval2Tail48 : Box := ⟨-1793776977014020939270615311744487370397158853657945237,10383621515390453606714701678134012134451399689611129002⟩
def resval2Tail52 : Box := ⟨-4115996217415037008121016321442761841111193261725255913,16658107999531538308273688535601174817843289681471024776⟩
def resval2Tail56 : Box := ⟨-9444554746140244246300489309798261310194816067231352206,25995149907176349281699540639220540565478756892429213975⟩
def resval2Tail60 : Box := ⟨-21671451974473766760602060310909095870619322572190647586,38787119562375864679497568342253582776702258182142796546⟩
def resval2Tail64 : Box := ⟨-49727260125481819167626033876650762629569113837094795572,53412393769513145346535218537512037882808661841679991969⟩
def resval2Tail68 : Box := ⟨-114103950940509273186533757068929015836072953542967524548,61847649962648229614402430753825744310418861673976946684⟩
def resval2Tail72 : Box := ⟨775276489718544334087120676173775923407695435038554585963,1088884994420835955333362776004343882597770829857588775⟩
def resval2Tail76 : Box := ⟨-27062301089971804785441732049862873986521548625341,398927937556508131186476517550662029970460313313079⟩
def resval2Tail80 : Box := ⟨-4821528678031351827746543467528351169280166683580,679171990259126352454127389042026946850696699033322⟩
def resval2Tail84 : Box := ⟨-11060538622156327909130225720918941264963459321986,1155800014604857702990821537293717587920399123478313⟩
def resval2Tail88 : Box := ⟨-25379483014499025844274981350817966652559853660755,1965233104736046086084462515463378219848713772466373⟩
def resval2Tail92 : Box := ⟨-58235698985383252879384051473510880247653533545194,3337661493608877638877112218962667994030367673872636⟩
def resval2Tail96 : Box := ⟨-133627490938867357664969692616143033818374362070595,5659623196635486283857892532400434740301785477680847⟩
def resval2Tail100 : Box := ⟨-306621310394229231155321139540694349711663945013145,9576408600603084626038649623251140789343390378821102⟩
def resval2Tail104 : Box := ⟨-703572500892692997837794621377697383500113698205756,16156440208580442119246484590132161030557711139710756⟩
def resval2Tail108 : Box := ⟨-1614415721385929342084712576153121527141663005642074,27148021620555745549659931967245796820691795410794914⟩
def resval2Tail112 : Box := ⟨-3704434323614308506459131360600975398345187902930910,45363013969843875728857783781025588056415291369599346⟩
def resval2Tail116 : Box := ⟨-8500185841965873825662090875112539255186593710149212,75206714703642090618798817657130783385066369933161508⟩
def resval2Tail120 : Box := ⟨-19504505421346434246114102795123477820021878627874535,123295771394484562198347848960714210667467801937349095⟩
def resval2Tail124 : Box := ⟨-44754989926590803922895340511876702604209058721794231,198855977935818094006236345188169160762900128893218787⟩
def resval2Tail128 : Box := ⟨-102694689255595292231222844758910084826569983795444043,312894866914511747053568367638697678213591123082574180⟩
def resval2Tail132 : Box := ⟨-235642980114671947264001840327394524582435652116283924,473334455150963590323583333454720540998365354304016416⟩
def resval2Tail136 : Box := ⟨-540705799699850228624344676739258052308156758407134512,668778404748185014313319560217257620741256258682896902⟩
def resval2Tail140 : Box := ⟨-1240702321559386248185842827744507074730598646078758010,822624449591605746487749887651818177809297741783431008⟩
def resval2Tail144 : Box := ⟨-2921401546439641210482779544707691812876024968561529361,665511462373283833400124336226742056584521090742174272⟩
def resval2Tail148 : Box := ⟨55742302995242102926542876606381525896465617,42716628470406497271731036514745832731838120⟩
def resval2Tail152 : Box := ⟨541545642273937525980592310361468587291992,71716687443173328888885750109030858728462112⟩
def resval2Tail156 : Box := ⟨1240484536077900653077917232629059538398672,122027263315668763092202218890745871250385068⟩
def resval2Tail160 : Box := ⟨2846412104732472259569241569978682079362974,207442923186544889500006888858006306030548555⟩
def resval2Tail164 : Box := ⟨6531370178399463754504548109361631538609905,352212951917033034692690464085303224762941123⟩
def resval2Tail168 : Box := ⟨14986865866440122129045530856413185963615054,597015109686612473843200107469898345186070325⟩
def resval2Tail172 : Box := ⟨34388825371066004598271411321575433193315322,1009659526093033618313088914402041617013654496⟩
def resval2Tail176 : Box := ⟨78908513690633433207270860878327773725210200,1702191880976985076949629875808878517974908771⟩
def resval2Tail180 : Box := ⟨181063280460395387231640146006825211934416014,2857415360338673923889588680893542261615091986⟩
def resval2Tail184 : Box := ⟨415467355773693921483364572592477881681946960,4768043061849374757371102347404435742516801894⟩
def resval2Tail188 : Box := ⟨953330367563628893845594293830664278713774457,7889509561875808552420864984782229416375867387⟩
def resval2Tail192 : Box := ⟨2187509504872027702202931211754980349738351552,12897985018653143385221066352488233343914020060⟩
def resval2Tail196 : Box := ⟨5019453902569700213219463827808399037430481798,20715733756055497951801721193494478154867590836⟩
def resval2Tail200 : Box := ⟨11517626517237067497898111205995434415401584854,32385467464324287140817308742023876418613623255⟩
def resval2Tail204 : Box := ⟨26428317336005384159951151435016331000964333950,48468422750823187986886786145413647221359797584⟩
def resval2Tail208 : Box := ⟨60642351631001372202263102860244705377286797500,67128180395525847823867574338677833254607949069⟩
def resval2Tail212 : Box := ⟨139149790205155718090668864351383800105582736362,78821096631709947130839898548950281664760500347⟩
def resval2Tail216 : Box := ⟨319295351001678408062692284983777366816800428982,52555645194088130330566287187607321751521429819⟩
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
def polyval2Tail5 : Box := ⟨21771985470383466907488770121200035802661592072814681,3039012209505595174564241327858764581847903664179416646⟩
def polyval2Tail9 : Box := ⟨45457831201793627653310211039762182510074964195484756,5172753797003895819058949080072860084069872414545487557⟩
def polyval2Tail13 : Box := ⟨104307013913602016038985096773060254200069951859481351,8797731339926550647928716740743914287549375821051582696⟩
def polyval2Tail17 : Box := ⟨239342615981779723784143080590688318806611795919490595,14947141805832033458264059221893839549781547139020981568⟩
def polyval2Tail21 : Box := ⟨549194974999225634561120291001487358483497157108216614,25358276991576175214425428540624171987086036120230780685⟩
def polyval2Tail25 : Box := ⟨1260181432076920510028902019906564957361767301883619046,42936821972793059142519570599103609730524191377701743474⟩
def polyval2Tail29 : Box := ⟨2891609198998391238003015510709171435100343474217132946,72506527388401623749954989345912937653400256418887383186⟩
def polyval2Tail33 : Box := ⟨6635079320246439806928217417411847197212345745583698924,121990813000449295859566442336406084965388822348251403670⟩
def polyval2Tail37 : Box := ⟨15224836606970017822581958064060080057510786631200916028,204205257081313919403401249938769673815332132954505764976⟩
def polyval2Tail41 : Box := ⟨34934872444045624732068115508426699745658291825354685007,339403179928803607618756558208006950903239391654621762888⟩
def polyval2Tail45 : Box := ⟨80161471954517491071072201653771319609350856823744451000,558442719015574327217779709104120702643969915304647256611⟩
def polyval2Tail49 : Box := ⟨183938315395513402742245398076572105559682230041713320601,905492241128225076129660302526829483170851158370787582031⟩
def polyval2Tail53 : Box := ⟨422064403829010412266167472547313053337198025209762988658,1436456029124439321606383275325563021542899421622636770615⟩
def polyval2Tail57 : Box := ⟨968467937724100270578519027867771120476250474954570600449,2202085870429723224606002699291244828449742357096322305471⟩
def polyval2Tail61 : Box := ⟨2222244135943662454647467524676776272547375096609158283487,3186580686296272249079070406408855206682650368956343997605⟩
def polyval2Tail65 : Box := ⟨5099155901176671213492024765547532940925747004213027693131,4128060455306894440479163243172776066576146867243298059406⟩
def polyval2Tail69 : Box := ⟨11700510617284984633817455471817992058040184701195025358129,4040713201946699315879932931950404556011471790615433678266⟩
def polyval2Tail73 : Box := ⟨26906250000000000000000000000000000000000000000000000000000,2⟩
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
def resval3 : Box := ⟨111210614069588840368730221648437813144486031665172532210,1767135163522820864877413214891340327918446720522901262⟩
def polyval3 : Box := ⟨3776691116247223214275337933602063782405415672778259296307,238183386864115125709113447444251829075558756548298968892⟩
theorem cell3_lo : Holds Q cell3 (7/8:ℝ) := by norm_num [Holds,Q,cell3]
theorem cell3_hi : Holds Q cell3 (15/16:ℝ) := by norm_num [Holds,Q,cell3]
def resval3Tail4 : Box := ⟨-190982752758507538291673873759611137780614459363439518,1997390570102817108757302212681409264119078057865458429⟩
def resval3Tail8 : Box := ⟨-283219733619193531425955302230498602599860877087130441,2549781573335478066544986722871519455657118312812803575⟩
def resval3Tail12 : Box := ⟨-419886044987158359123215753169487254872631089851348569,3247542578084481716079370248227480196507098787701295750⟩
def resval3Tail16 : Box := ⟨-622500009916728185301343547381810563342889337903758391,4125126701035434237263126651609772282962157778483721613⟩
def resval3Tail20 : Box := ⟨-922884356286205317131273697105492605870367311269461000,5223100120335268915714619958182821518416127879104942383⟩
def resval3Tail24 : Box := ⟨-1368217705236199308002125208918542381269749182567671733,6587994416440145388227255126305069011896375355609734255⟩
def resval3Tail28 : Box := ⟨-2028444491631689434187344307600477185985269490604633715,8271176596885464669947676960322773788113300723003966563⟩
def resval3Tail32 : Box := ⟨-3007260496545489530955164694960859710119327501810477575,10325993185569280077133624802264358389330764008572454634⟩
def resval3Tail36 : Box := ⟨-4458399394902002500494039270252049567597585098788232491,12802007781613030408953578254138594223961999124155140347⟩
def resval3Tail40 : Box := ⟨-6609778297322792742858525927218874651866705042941103291,15734479376160450649730027691964326332335955407721638413⟩
def resval3Tail44 : Box := ⟨-9799294605529548684118843820189275712507666944075969101,19126202103396828381516142823573957671270734687184063572⟩
def resval3Tail48 : Box := ⟨-14527896465885202680861380158023389161556943007925666495,22917266049002679730180300642026655750526193135245004281⟩
def resval3Tail52 : Box := ⟨-21538262111681272626085694556403971743374337834621830273,26935933850307710158774508231186646613556557548686632890⟩
def resval3Tail56 : Box := ⟨-31931445538644886628781885553960202195463015338584394285,30820256319427396765049432858391187239326439738081760409⟩
def resval3Tail60 : Box := ⟨-47339808982749127094982998016149854235785443515857376342,33894670680864699402571521546763418686174508759098495810⟩
def resval3Tail64 : Box := ⟨-70183403117568343182661240556180914220022449212661462913,34977739775779838773924153404765262117114200660315291724⟩
def resval3Tail68 : Box := ⟨-104049974477220922128158460366375124884072980014272615839,32085060471995280557249917684673120442585433484995248991⟩
def resval3Tail72 : Box := ⟨775966938331607639290794965941634284641790092551189924018,877352213401111709527341840072757331863883960207468489⟩
def resval3Tail76 : Box := ⟨-2341383993143125729865014959414738346675639189543225,25168652387882588918545040178559030567168632493101794⟩
def resval3Tail80 : Box := ⟨-3434401428836255328633757050633948995453882487137877,32146085237398276955295721973657540446344016758158979⟩
def resval3Tail84 : Box := ⟨-5091653230393283032426176060515309171481925298826702,40968646828749624714169718191678519967745973115810955⟩
def resval3Tail88 : Box := ⟨-7548605684315286819244977524579065873659897154497808,52078215542967465736722375958679533884450469297028785⟩
def resval3Tail92 : Box := ⟨-11191148573247071308377201933447551942012448561488887,65998053519613877638330535180328338516512788702289664⟩
def resval3Tail96 : Box := ⟨-16591382783280060153604095408372681940748998154732469,83332993480576415098781367712519955494347311727273374⟩
def resval3Tail100 : Box := ⟨-24597473696254631324649076145915895062016456547711391,104758455643559648812463792516854787876856013111626268⟩
def resval3Tail104 : Box := ⟨-36466864765947192507520563008290114808093571758974520,130989336423466509436059935682444783186395192792877720⟩
def resval3Tail108 : Box := ⟨-54063772657285920766894857231369541624763653203946603,162714688599986501360982006318756709300504300155870470⟩
def resval3Tail112 : Box := ⟨-80151982702612174868680077053116955841681802946934491,200476031854555340321267797035840080100667313280892377⟩
def resval3Tail116 : Box := ⟨-118828931378581163467491437917454696174852141556486223,244454773550179928397058965130094825769175812202897438⟩
def resval3Tail120 : Box := ⟨-176169253167025725424185472073889664183758342368100478,294115406313691053216652485415958251535753621546006102⟩
def resval3Tail124 : Box := ⟨-261178867817553656797353998629490064728593472228367109,347622622428930389765862074633491901704902590890436789⟩
def resval3Tail128 : Box := ⟨-387209457769485105150950648526814178486972573324788422,400907371164709100098048376057844174203182192614766964⟩
def resval3Tail132 : Box := ⟨-574055494761072239003246003355955179418197137846878876,446191902790177223390960736899925286251950271224400116⟩
def resval3Tail136 : Box := ⟨-851063176424007367139433992947092369752778521757466303,469686126223892361883571697578979012088773523724390585⟩
def resval3Tail140 : Box := ⟨-1261739682768335709291013648380623595643974556647182580,448020944711978877868811484625122195156709677415539436⟩
def resval3Tail144 : Box := ⟨-1937520948663750691717647216175619834729342978336404815,338425672934709640444416989974042174528416519475267944⟩
def resval3Tail148 : Box := ⟨547844216396476233258397332106626857626864411,4812588123980316532893351672713053603738979197⟩
def resval3Tail152 : Box := ⟨730209409805360986255104536390462001800693627,6136934169070728217575758072893795759070171029⟩
def resval3Tail156 : Box := ⟨1082567029276490887644696259068195152029873974,7807211937414911269382822253936386045872197610⟩
def resval3Tail160 : Box := ⟨1604954473540136364427153907399686117489444886,9903204624585186768651972891558624177869308650⟩
def resval3Tail164 : Box := ⟨2379417433871890085873637368768538597827761324,12518334954369305935259370075627964150602229875⟩
def resval3Tail168 : Box := ⟨3527593721787589445980612055425293254987561213,15758116905684505963770789145627772407228406619⟩
def resval3Tail172 : Box := ⟨5229816882423171744166341919133139763971304417,19736273619937544128467871343454444877162711253⟩
def resval3Tail176 : Box := ⟨7753439534362947303764401726908267829323197339,24566120113295558873737023755228915165511698773⟩
def resval3Tail180 : Box := ⟨11494823999491237332344770905050498598407116413,30344082885821313004940198420921735139700572185⟩
def resval3Tail184 : Box := ⟨17041595306661035256050139775157800713025463274,37120470898491424969111437082146373495367255201⟩
def resval3Tail188 : Box := ⟨25264934078926765606147912214733726594903155322,44849933492843538261836730650435639299658189448⟩
def resval3Tail192 : Box := ⟨37456404903771926819344198346291480812948925705,53309974576396737562241629155571127102420874466⟩
def resval3Tail196 : Box := ⟨55530810566631299220486061921989683544048473691,61969741445464179087572451344258937394662225413⟩
def resval3Tail200 : Box := ⟨82326932606299308881567832672264093592588742508,69782028908064923867928477303323734339911607371⟩
def resval3Tail204 : Box := ⟨122053392759854901310250682008150197244885375028,74857479374572283652371028854910363571030181869⟩
def resval3Tail208 : Box := ⟨180949662675189631196810260636167073106830645329,73958997397949333888942517834299849593242834722⟩
def resval3Tail212 : Box := ⟨268266040688756212715122207117196479739282105394,61722975584429337500478006224036707909045597401⟩
def resval3Tail216 : Box := ⟨397718843017830810525206407762788016791876845906,29466709574774582687246310533393933319558799688⟩
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
def polyval3Tail5 : Box := ⟨33258137065146824323704510005072724979777107903501411839,300253578804156762440042868704687323054502245510199033833⟩
def polyval3Tail9 : Box := ⟨49303800455507611523329195741639635933471273374219246828,382437347698397309780284375181676674686938133906906198881⟩
def polyval3Tail13 : Box := ⟨73095108846169171539344526839182544745218606573496112762,485810330633115526410822103855843232571533840204435847092⟩
def polyval3Tail17 : Box := ⟨108366797430360103124945180739658061725098906489990121406,615157684183578258342105718520030592513672906053777608862⟩
def polyval3Tail21 : Box := ⟨160658667463620289725215203413622049578942914958941423235,775971464428745842315414113158265157442441111264300405528⟩
def polyval3Tail25 : Box := ⟨238183724565389292097720408888171215027684614321178925150,974319827507659725277416649486447041369471790744979881751⟩
def polyval3Tail29 : Box := ⟨353118120195336283871609001276023947052262288705876517015,1216514132420156859680059437470814578855372964269696920874⟩
def polyval3Tail33 : Box := ⟨523513548366130207349864138342885870113676446128366075236,1508435474990096136451891753234029814728678349481307833430⟩
def polyval3Tail37 : Box := ⟨776132460071122154136866444829964865525132862945454013598,1854303316613789444228471028219705244879482257012759827147⟩
def polyval3Tail41 : Box := ⟨1150651396618228093071850349907886528231963100682551416649,2254548387299250751578787164209605193259023969283118046662⟩
def polyval3Tail45 : Box := ⟨1705892620981413527187786249060953009255674371186903532024,2702268821760628814799794694650737640083166911253653549728⟩
def polyval3Tail49 : Box := ⟨2529062792494364574629009572496299862838684892286362590003,3177470902548449981931243818657626485846369262696907620804⟩
def polyval3Tail53 : Box := ⟨3749449718997924203746935271949648825152540366500539455345,3637876547438142854258943481849100841249954518867552219011⟩
def polyval3Tail57 : Box := ⟨5558728409992587675176287780655951298157569603494217337283,4004448166741320330531683245173447564208816623438933580381⟩
def polyval3Tail61 : Box := ⟨8241065716789217635901025093711117475219395902427974935162,4138832359908734769330736228641758947312458192174056909843⟩
def polyval3Tail65 : Box := ⟨12217751820075491460525544987050744455485687181234334635561,3808500038787136280810148856313269951218172532517613977619⟩
def polyval3Tail69 : Box := ⟨18113368506670104817685007014380410530112703038860916584467,2633227950822495588045663479056410308761786016530250013793⟩
def polyval3Tail73 : Box := ⟨26906250000000000000000000000000000000000000000000000000000,2⟩
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
def resval4 : Box := ⟨107895090812333015474211536258012857473352465749979188134,9011349048460707785841715906025500412053592617601675549⟩
def polyval4 : Box := ⟨4598964257862661526243750784978486353232662844759480047102,1886419708728398450498360302058423231110988018945689357182⟩
theorem cell4_lo : Holds Q cell4 (15/16:ℝ) := by norm_num [Holds,Q,cell4]
theorem cell4_hi : Holds Q cell4 (31/32:ℝ) := by norm_num [Holds,Q,cell4]
def resval4Tail4 : Box := ⟨-4141043505333375782040940909771887491262192775198731422,9747483122465454833213592604941491188732236954674507634⟩
def resval4Tail8 : Box := ⟨-5017829853254470670038161215194360002493236414412402956,10751417276765655397896889965315139244354826798042665837⟩
def resval4Tail12 : Box := ⟨-6080180712810534684610034062863301760803503252695923981,11824397618194807154739429631087645828557215637557729539⟩
def resval4Tail16 : Box := ⟨-7367447390009958236856921355642674556481502248744432248,12961609694796458871681032035900687892370616225406062418⟩
def resval4Tail20 : Box := ⟨-8927247989546726260833816102055343751182753214044394406,14154589198517208296172847029614378543491881482891433432⟩
def resval4Tail24 : Box := ⟨-10817282085370702479648281489806864243855866188114413581,15390092204235412029138212440275856879404872945612973815⟩
def resval4Tail28 : Box := ⟨-13107465128278933415026613822255762621095723837649376264,16648678698551231935957736800301435868647557900743021896⟩
def resval4Tail32 : Box := ⟨-15882514732734788314089923142689082044577040831431401018,17902941439200952685508618017859654140634622176935742088⟩
def resval4Tail36 : Box := ⟨-19245084519912789281752038402627698302619906176239033816,19115297638093029269702616339889319742944688187671079169⟩
def resval4Tail40 : Box := ⟨-23319561442951220293662366856191781515172127176940611338,20235242488646555169295922365659758493987153026867141141⟩
def resval4Tail44 : Box := ⟨-28256667063681021638502938884240726753646837562598886643,21195941038765018032829745370042326294132813400882922108⟩
def resval4Tail48 : Box := ⟨-34239032989578766292180878965022991452646215609105358293,21910007469306801538687121763626743157403089771389867517⟩
def resval4Tail52 : Box := ⟨-41487956715470639100003772276408034597934954298176967659,22264287411318457225063858990520539145382054658282941979⟩
def resval4Tail56 : Box := ⟨-50271587779615647855687643955646800345141124908508161307,22113418232691589642932552627521935338281496784099565779⟩
def resval4Tail60 : Box := ⟨-60914847053460211226044811554700297641433494557677872434,21271892678888013626260177581097749590214721518446675064⟩
def resval4Tail64 : Box := ⟨-73811446091092048542081786877475762390708020890265707446,19504290959826424152352415941473461599425698003449268274⟩
def resval4Tail68 : Box := ⟨-89438367419920487744840477172562637758175464683463146403,16513270299400565947454405138139158236090381355546820474⟩
def resval4Tail72 : Box := ⟨776270842619868222824283508417358703956600829160183999870,855955001269854961699710619491280845638737472726444807⟩
def resval4Tail76 : Box := ⟨-52812869981388280591636184625004648555365811077469995,127226933679043667812009540707948618810140935784703054⟩
def resval4Tail80 : Box := ⟨-63964155921189593066970336414825384586226544091590914,140426749659727431030046204022390505238583448667372803⟩
def resval4Tail84 : Box := ⟨-77506338479081029629555572323498730359592458120103356,154561364233019867071072330209164725935381382528975127⟩
def resval4Tail88 : Box := ⟨-93915608450326013723071073563362301364172641595450396,169576638546039797202263928160651701681898483946970313⟩
def resval4Tail92 : Box := ⟨-113798970300360660674627816419459392152466673873371733,185373053277294226351327645205027971562128627060778796⟩
def resval4Tail96 : Box := ⟨-137891942086200138907270155460873977734292988614010666,201791296080515110172730942183676805858790321489416170⟩
def resval4Tail100 : Box := ⟨-167085762218392536975670555515281863275337555451119494,218594358909228392644421847389209848366945483288870994⟩
def resval4Tail104 : Box := ⟨-202460357826051213873037585599666588998590005886044400,235445135055557589677226329410332024502541866540478194⟩
def resval4Tail108 : Box := ⟨-245324293026689504967026341728409145250115622978853865,251878466958005843364272528128527615956007380754358037⟩
def resval4Tail112 : Box := ⟨-297263174852005276513118115777597442477412037672002743,267266360755427483078587824844133557496965893327386158⟩
def resval4Tail116 : Box := ⟨-360198307443936454078674664644295408556819813036369994,280774796934956298035260252733724021775293032712768022⟩
def resval4Tail120 : Box := ⟨-436457764235580184774651936516374487592436454828258667,291310217106697734712641280192586126266118965690459954⟩
def resval4Tail124 : Box := ⟨-528862507193127789204585324477127801632487675181526865,297453341395004383914942290932989475852546324317399914⟩
def resval4Tail128 : Box := ⟨-640830738810351759026914894071597748142538188366149313,297377452718751897820646498876971236644993158561916878⟩
def resval4Tail132 : Box := ⟨-776504347006516165796483045861803955709192447019465755,288747653371204559361838506781347474495959204433260031⟩
def resval4Tail136 : Box := ⟨-940902120344319283889153811675916141942994212435307046,268596831557449956805873146890078213468109173447915295⟩
def resval4Tail140 : Box := ⟨-1140105513579185769914544078441894469212026497562696253,233173133893271286037673176034452860880023359750522663⟩
def resval4Tail144 : Box := ⟨-1445188008778614681505062316674682428689212330547691762,174664972445457542407630158349819444914747376986326102⟩
def resval4Tail148 : Box := ⟨16874496792507557660558216420748414631072440750,35860740502718353393102266800341601685191250274⟩
def resval4Tail152 : Box := ⟨20380188710573260356822824011873544297925849174,39432785984912591607009378413020041520727122046⟩
def resval4Tail156 : Box := ⟨24694983327658090868328001563516999723077402852,43217331362368035866123120054498741023650984038⟩
def resval4Tail160 : Box := ⟨29923286667808842433378460609615173246656110344,47185109663313332309407429386614349438224726709⟩
def resval4Tail164 : Box := ⟨36258501296941199245935599732768740990213408000,51291228261241320204234478267389644223106030285⟩
def resval4Tail168 : Box := ⟨43934977159932906369775507733169606682650476963,55469958105427372892780697997237644377850754413⟩
def resval4Tail172 : Box := ⟨53236679647502879369297427654236990960596851366,59628787841390627252907837567646845377114897965⟩
def resval4Tail176 : Box := ⟨64507693939931829908830431254392539884936007716,63641011327879078123434695922001690191519693623⟩
def resval4Tail180 : Box := ⟨78164953280348036327356757615441067810266582365,67336509896883548769764135992824844186067850090⟩
def resval4Tail184 : Box := ⟨94713662016941228823813661763140922660069163748,70490315209920733789620944278316080334566812095⟩
def resval4Tail188 : Box := ⟨114765983937647316279566486946498662842270232451,72808446556769171606873202692788699637996348693⟩
def resval4Tail192 : Box := ⟨139063687209353303786493296041786324331905197380,73910404370711755050832414257461743329078653732⟩
def resval4Tail196 : Box := ⟨168505583594940718883318258133646394522790950465,73307565269739455301515776395402834366835715412⟩
def resval4Tail200 : Box := ⟨204180776969660199991481377441194447395365198047,70376557821785667101753951786013668472617644074⟩
def resval4Tail204 : Box := ⟨247408951053808518714033912943183855516013707370,64326496094957102348725121652348930736767675667⟩
def resval4Tail208 : Box := ⟨299789186670814779531620839425748544970490161554,54158702147608403216049246054468792601590332917⟩
def resval4Tail212 : Box := ⟨363259114408233852269041201945725001986297840724,38617249535872142596750851853841661485778336104⟩
def resval4Tail216 : Box := ⟨440168812783812010623876458702775407074573265120,16128150284257462039855413730145539798344840483⟩
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
def polyval4Tail5 : Box := ⟨1026217605948737516583172384818447039196584139898809506790,2074653953749522606132101789304483403194898429061443967958⟩
def polyval4Tail9 : Box := ⟨1243481118656168761670808750866136357404492346435773245220,2277280672325319623067644936716444981518216460690964719707⟩
def polyval4Tail13 : Box := ⟨1506744972490143513937752528482176055875918893649108178883,2490767066275087513373430875535645859830532452184615509282⟩
def polyval4Tail17 : Box := ⟨1825745786072438943416929658513925415980135629540479169390,2713073779005292146966894625664844284467733624654818329896⟩
def polyval4Tail21 : Box := ⟨2212283920783655729951035981353777835717521003324825228226,2941142221416626120671690276005927861966438071595468716249⟩
def polyval4Tail25 : Box := ⟨2680658054091064701106403970417967218540025749952893983186,3170599221578684808279633063547623768679750079578808698102⟩
def polyval4Tail29 : Box := ⟨3248194110825443984080709474103090360938631811169533081238,3395388383879801767115503141049889435391172968483769859288⟩
def polyval4Tail33 : Box := ⟨3935886177462706094677530185140252482704033470267567014224,3607311170478540253584524990112402638796311273536797051704⟩
def polyval4Tail37 : Box := ⟨4769173107701161099198924493823289911218186797438231974249,3795456935703201477150779744571911530786422774938134673124⟩
def polyval4Tail41 : Box := ⟨5778879547244088908146365519175365605425918497863688905295,3945496522593817206449982378575120841860246158902881875276⟩
def polyval4Tail45 : Box := ⟨7002356187832597841851604250253468541409077800675314565909,4038808400526900471690845153720739092109967278300118183191⟩
def polyval4Tail49 : Box := ⟨8484861430389390274982077474390370622267167139601017852757,4051399466118268244582184866150331991830529156113083957953⟩
def polyval4Tail53 : Box := ⟨10281235567251694191931889518037717066737917723817044193281,3952574282027764034145054476730165283312374361031035456760⟩
def polyval4Tail57 : Box := ⟨12457929414230901572594484994143517019199706413984522780369,3703296368959797097000011475255448801871622139374469559917⟩
def polyval4Tail61 : Box := ⟨15095462434914964124475095010708867782684139369148605808869,3254172805469367127800081920383172006135876375018213897345⟩
def polyval4Tail65 : Box := ⟨18291401287258938657751899023974203258377768367448772752719,2542978355249583477860658043210279954272941492315935789599⟩
def polyval4Tail69 : Box := ⟨22163969052374357775497863548656147644849073421328156612939,1491617053381088653764036359828017718268007918104494908738⟩
def polyval4Tail73 : Box := ⟨26906250000000000000000000000000000000000000000000000000000,2⟩
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
def resval5 : Box := ⟨95488226591698228858964757448127309791050664439483552480,14568384928757134860435226977958679991815838538857303400⟩
def polyval5 : Box := ⟨8620292282752792095034632365002370733655956709284705829832,3776219318230789377076850556276320433398289352506901348918⟩
theorem cell5_lo : Holds Q cell5 (31/32:ℝ) := by norm_num [Holds,Q,cell5]
theorem cell5_hi : Holds Q cell5 (63/64:ℝ) := by norm_num [Holds,Q,cell5]
def resval5Tail4 : Box := ⟨-17384352429087126864987719577693440914653241447736401433,14765449228515853924988013714226954053702484817998600715⟩
def resval5Tail8 : Box := ⟨-19114356056138048994448111851094191400031422648651064075,15125876533809022618408872366914994117035882377757048296⟩
def resval5Tail12 : Box := ⟨-21016456747808974514683068396488368380081416653359784615,15450070284861148496920724107665541077337972770256377684⟩
def resval5Tail16 : Box := ⟨-23107838568872992286243675666945913796863905766220303691,15729736208150161571193427984793591126972964375669021582⟩
def resval5Tail20 : Box := ⟨-25407337199246599026049930368267211372003383953862480697,15955450466530621921306143640355042391992713778206414756⟩
def resval5Tail24 : Box := ⟨-27935662681397345196880177867553728196094288725291004781,16116526810526125409592576219903175005011598066441497543⟩
def resval5Tail28 : Box := ⟨-30715585947824451900769138853335652305220166653214981228,16200869846037433617753086990194451940350797079016696779⟩
def resval5Tail32 : Box := ⟨-33772143903586094916070756961133146531206794681073776262,16194812328202476611597535930766673893479598628005667945⟩
def resval5Tail36 : Box := ⟨-37132864916917262025038244235434569020328176307157462738,16082934802466473569304586802334777629992115744876931097⟩
def resval5Tail40 : Box := ⟨-40828016748786021769018831944088835864546175766314346607,15847865741168744128747862490977522486281356832540709301⟩
def resval5Tail44 : Box := ⟨-44890879154323510066715341009490393307958865608673718745,15470060133508722723489627773534704795425982260744500745⟩
def resval5Tail48 : Box := ⟨-49358043611265948856358620463869339974854221539051861695,14927554276956306070019746116778578565772070214584528956⟩
def resval5Tail52 : Box := ⟨-54269742874861820659976508122080051583644135929259427861,14195694287069109305027330605121379160582033534441863204⟩
def resval5Tail56 : Box := ⟨-59670213327324287476148999113127269340591243142410015052,13246835588123544881601121216582232109795184849045572167⟩
def resval5Tail60 : Box := ⟨-65608093385264413003534172252125628613979347194551110540,12050010366594155263662808724778329458782950192385178841⟩
def resval5Tail64 : Box := ⟨-72136861548678622777388380315214821458103046665100702041,10570559660466652812854454230841238475920022366774271432⟩
def resval5Tail68 : Box := ⟨-79315236191799228957267807821408017772459859828943441079,8769723100429211482596501030121175879762564330630104160⟩
def resval5Tail72 : Box := ⟨776281246429682546917579350358950447885225290659580376830,871752506385106979082217171544429850972423930926666523⟩
def resval5Tail76 : Box := ⟨-226622769167564046641243624545313014803818344845790510,195606371768350685285625583985457905793795828463149214⟩
def resval5Tail80 : Box := ⟨-249147183051386863958438484055373644871419200131207662,200508718964246415243112321655174636403175253851803915⟩
def resval5Tail84 : Box := ⟨-273940223415217961952938976542161687690278809261394426,204952231944961861397501691853851684439097961984206581⟩
def resval5Tail88 : Box := ⟨-301200460959857453480394133519209196081000295638427998,208829505110439625799228255838313382739993415977494903⟩
def resval5Tail92 : Box := ⟨-331173409116852528234170824234393978886654555222218155,212018623621247671909080758487120099232553151212908385⟩
def resval5Tail96 : Box := ⟨-364129014134197704725094285108221674540524299378373093,214381277532631040201045652427878008924780413280603889⟩
def resval5Tail100 : Box := ⟨-400364085051161829169761459211834179544786432093531460,215760853080620880194280579606663038933956001152881632⟩
def resval5Tail104 : Box := ⟨-440204966857651850999489480434128255362037860710268740,215980316024947488866421285013117088759445703911633438⟩
def resval5Tail108 : Box := ⟨-484010479664736918369419338337479161638705034929670310,214839865165195166545078046141850214112241406704981214⟩
def resval5Tail112 : Box := ⟨-532175150356817435863274998349838143715360101982187173,212114331911706802464279865624253432618631763244151617⟩
def resval5Tail116 : Box := ⟨-585132765830761886130746197338845591560260545605422679,207550299311543814220993190816115447318198712840189459⟩
def resval5Tail120 : Box := ⟨-643360279823654034411021003398266527287965400828125024,200862911196404573844221237903591558620585351928720664⟩
def resval5Tail124 : Box := ⟨-707382108515328698798731845798166053240668873912744997,191732339108377321894889279883471236573043545746028540⟩
def resval5Tail128 : Box := ⟨-777774853593308197513633242732025427864404830322409904,179799871342759605128159365459399340000068139435783535⟩
def resval5Tail132 : Box := ⟨-855172495317632147163244894708012393980384630040236110,164663584794112667780124446356313831160397039337809973⟩
def resval5Tail136 : Box := ⟨-940272102368899358287114576478738428056717343202266448,145873556267380606491908044073943358717489368033113375⟩
def resval5Tail140 : Box := ⟨-1033840219738660406385632962680431720052982337411702549,122926558875734605299999857271642922763120366339738232⟩
def resval5Tail144 : Box := ⟨-1198923298751009955040664419378764509809853557895384192,92730170888683037279878698467208901348704544490320804⟩
def resval5Tail148 : Box := ⟨92192242748287318145090925350149325062504983206,69349541972457464710604378467401712143288492623⟩
def resval5Tail152 : Box := ⟨101305796119974934771853209351432187344136911948,70680162942888794195237173680359222068437946131⟩
def resval5Tail156 : Box := ⟨111386899783783682520249038686014963735538793031,71781557785352542619505959897487595756017131827⟩
def resval5Tail160 : Box := ⟨122471191493888653612802868190548473871726746595,72606849835581480157487990263866350975116299288⟩
def resval5Tail164 : Box := ⟨134658499115111225470116273943866303246630719987,73103485202722090638151410132233905373425937822⟩
def resval5Tail168 : Box := ⟨148058585555928996072904779614213657956407566853,73212049690924096990609124469447358293818522949⟩
def resval5Tail172 : Box := ⟨162792136410811652302741003081855458735799386831,72865480083869421411632066267595826089980548280⟩
def resval5Tail176 : Box := ⟨178991846894184158065916080285456679294641996065,71988190063720278107714458736822034160632266015⟩
def resval5Tail180 : Box := ⟨196803616937256993662261407446465427826734749560,70495101807158461504393012222188822093485497801⟩
def resval5Tail184 : Box := ⟨216387865210887800761992930755202774093791853531,68290573394927758932983805811605747482930160411⟩
def resval5Tail188 : Box := ⟨237920973908996927334005547125639094246272158504,65267211158718691409932666699983105281059172936⟩
def resval5Tail192 : Box := ⟨261596877304732437265120305823615266295118475873,61304554973874712352614255360942130249509665094⟩
def resval5Tail196 : Box := ⟨287628808386444913695893840992975227126978037395,56267623277898337608837917452653994103695251509⟩
def resval5Tail200 : Box := ⟨316251219304251247482483081487910277387754157306,50005303241695906854102297071119654355527427604⟩
def resval5Tail204 : Box := ⟨347721892923362083944126372251109381271339233014,42348570030378860372938555038272473305212016815⟩
def resval5Tail208 : Box := ⟨382324264501535349465055606679498216799035410229,33108517449436369660034898135826394112151362447⟩
def resval5Tail212 : Box := ⟨420369974446749905807539858406819528783747722609,22074180461723678770408570012229718455893225180⟩
def resval5Tail216 : Box := ⟨462203846151718339804584755363989599921268707079,9010001714082568195654444490186365260233527324⟩
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
def polyval5Tail5 : Box := ⟨5353899531207518166865196000492880105740828515572211953781,3850978414770581134251361540170117794779869350020160318352⟩
def polyval5Tail9 : Box := ⟨5886672656631952295139075534270882087186177795696320152947,3916702901922902159128401551360174182273971318450833492014⟩
def polyval5Tail13 : Box := ⟨6472465034683906881707678811737992917017835910463646073622,3968324431626450523306799938507079803874654086015307986969⟩
def polyval5Tail17 : Box := ⟨7116550566008403751011675513409601410236122768997942501252,4003097358392054154834403961862866505706680554447858442575⟩
def polyval5Tail21 : Box := ⟨7824730096982113676521450072676096857389946851275443152623,4017915553674810151289065024725805724011978621459921476658⟩
def polyval5Tail25 : Box := ⟨8603381725840662148513061614401172309468978460731946292379,4009270847382349885409971222430473316011002986925011371564⟩
def polyval5Tail29 : Box := ⟨9459518245757358600763196972724809459274964980949424169136,3973206976752764357145033461952179706484011137878943219902⟩
def polyval5Tail33 : Box := ⟨10400850304369445361043438880670931300911927393777902631691,3905268559677789635042740480279217667424130571427702378349⟩
def polyval5Tail37 : Box := ⟨11435855848411753914197492294568461494193199274695194820951,3800444571794650185454856120469416323454910342719274372455⟩
def polyval5Tail41 : Box := ⟨12573856478898897050490615360944110581093363685894437860566,3653105753197888192813749316928406213450855126087702435605⟩
def polyval5Tail45 : Box := ⟨13825101404535930092119366376624618354475394589678898308967,3456935311718867906337369818000403552040557043810726709864⟩
def polyval5Tail49 : Box := ⟨15200859749469564365498315944239749351980819926065216095428,3204852224840373750701764740764176212032721927230899159194⟩
def polyval5Tail53 : Box := ⟨16713522046733960268824359682877144642871111390571677480603,2888926370854598652397701733956944601527794105142238004767⟩
def polyval5Tail57 : Box := ⟨18376711831474519844841303666022316286512460676627588639080,2500284641172206873924609467393471610969391772729188895151⟩
def polyval5Tail61 : Box := ⟨20205408338995036874300610289556191200016856607967004600073,2029007099018956787341107603338207168955921159642833593591⟩
def polyval5Tail65 : Box := ⟨22216081412696271482570110615024294451233653849018483982214,1464012154311726209460354502653753872870042361281888654575⟩
def polyval5Tail69 : Box := ⟨24426839913789072274835746690723589986180671584103790345256,792929615006795687312853064726927012642364482687813533245⟩
def polyval5Tail73 : Box := ⟨26906250000000000000000000000000000000000000000000000000000,2⟩
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
def resval6 : Box := ⟨78277016460081944975130981714630138783073873116189619141,13209792837901412868613949323029094374080092821738237805⟩
def polyval6 : Box := ⟨15244535686478705063493368098462092854786220058371265576240,3779246918109401357889839009000482384875926801600140124038⟩
theorem cell6_lo : Holds Q cell6 (63/64:ℝ) := by norm_num [Holds,Q,cell6]
theorem cell6_hi : Holds Q cell6 (127/128:ℝ) := by norm_num [Holds,Q,cell6]
def resval6Tail4 : Box := ⟨-34609522419962666200032835530315082741202882535995187248,12892778751992478197999730241201835515678717680369982785⟩
def resval6Tail8 : Box := ⟨-36280565618712071506975452506718940775388408585855933333,12735689063286928611633114329298354364718510280997861958⟩
def resval6Tail12 : Box := ⟨-38032233062873102638946722753481740552493907379844906069,12546170658931531106059361383595051032115128195726199291⟩
def resval6Tail16 : Box := ⟨-39868473019689185203694420098470466975294341366596092485,12321865457496902627229931382392932530777307042447495524⟩
def resval6Tail20 : Box := ⟨-41793368753651469904192538727135369611255043020510495115,12060276872351634976247948627586990015197698448349081070⟩
def resval6Tail24 : Box := ⟨-43811200667657458340502827145259760206768558424970870055,11758761739827034009753837436616335972947614925868752881⟩
def resval6Tail28 : Box := ⟨-45926455827374533949644610963893501915298021175043360419,11414522412326961646262215928363480250397810486954571976⟩
def resval6Tail32 : Box := ⟨-48143837939161488709182163816974812829434403791289738841,11024598443352146366312167245103970518735195823942655436⟩
def resval6Tail36 : Box := ⟨-50468277809730302678753287792698032727817165032683257016,10585857843777309102956719766383632088651537085168190978⟩
def resval6Tail40 : Box := ⟨-52904944310812406132214635066270377987313479606775858931,10094987887810796596256077189959025785412115967759813108⟩
def resval6Tail44 : Box := ⟨-55459255873211640133659631675985034911971204791457754194,9548485445997399411553728844742382810137588857776008561⟩
def resval6Tail48 : Box := ⟨-58136892535803314458248040523143648901286331672613120218,8942646821503377429580210943582182783998244767684764172⟩
def resval6Tail52 : Box := ⟨-60943808576272798627458414261393223168964840456850596005,8273557064745994176006874846621563794722301859831256180⟩
def resval6Tail56 : Box := ⟨-63886245751680689854949284467003862120459403386896019970,7537078740195384802098933793151874419887504933550020473⟩
def resval6Tail60 : Box := ⟨-66970747178294695121375069855306525294484681627641400858,6728840117881297253164747751680924057116991649818821673⟩
def resval6Tail64 : Box := ⟨-70204171876986003305921311038464410456311064780099004992,5844222760505402757137695524670026761076076651188561290⟩
def resval6Tail68 : Box := ⟨-73593629084505449696527148761506573557659872721202086666,4878344880943225891130740246681293914738840597863029400⟩
def resval6Tail72 : Box := ⟨776139723530627428771090878206137842291437648068714892789,825721423615391286036174038126905178369547539247161486⟩
def resval6Tail76 : Box := ⟨-455053031443199095278960605912295169611954279779894941,171685550252997947506050117004493561450429698463837669⟩
def resval6Tail80 : Box := ⟨-476997612548021035122500701233962949487622092054015359,169689466915832008302127497486554840969240070051573718⟩
def resval6Tail84 : Box := ⟨-500027604611258702324585115115874112551217617630465536,167269403919284673914481129587749609301726319049004802⟩
def resval6Tail88 : Box := ⟨-524169512491115483413165396970638170566745762381862609,164394265273387564336287916391503469763874276624205072⟩
def resval6Tail92 : Box := ⟨-549477019452038536677486539120989171077877495165857286,161031299915172887914668730143019596286695944626233269⟩
def resval6Tail96 : Box := ⟨-576006401957638557258714715241905798771165272680502842,157145831999512325664968646304515064034492599778339349⟩
def resval6Tail100 : Box := ⟨-603816653564607571380459482005470346583989423622077461,152701157001040335232151801730603702707367415059768696⟩
def resval6Tail104 : Box := ⟨-632969616106410608494547506400860038334624143427762430,147658432469501872972062032978057176686483462465110359⟩
def resval6Tail108 : Box := ⟨-663530117211362655155507396612099921850768782291337297,141976563150602662351490338972867487979062050194008470⟩
def resval6Tail112 : Box := ⟨-695566114460238246521101986723380870159886246065157648,135612080188831634034327940545631796311149016112684972⟩
def resval6Tail116 : Box := ⟨-729148846503976272879062480236070750658162099214243684,128519014114685609776493673769085609490041548745406882⟩
def resval6Tail120 : Box := ⟨-764352991477521389621535657569314536456014179920524833,120648761303981976394421706646894677582620437950402811⟩
def resval6Tail124 : Box := ⟨-801256833062067898483575994489610505843382118795328215,111949943581476815886501876189904835549749874170001721⟩
def resval6Tail128 : Box := ⟨-839942434564979830820183138580553252327788344653983165,102368260624778433769665829225862789187584332569837025⟩
def resval6Tail132 : Box := ⟨-880495821404503105799568680185727336871706076339538278,91846334807521204885044310174307368174884056050811466⟩
def resval6Tail136 : Box := ⟨-923007172417795236935587008073951736003379058658940172,80323548101993102240466461946139090574903772981635264⟩
def resval6Tail140 : Box := ⟨-967571129045345758252252770406483619627769654282356652,67735864494587994219615610918806285426814099025038668⟩
def resval6Tail144 : Box := ⟨-1075766313149967983009323543257719032339341441708198229,51749134385016544872694652944492916215416307075014566⟩
def resval6Tail148 : Box := ⟨212441210463866286746844307767903562633866046277,68476716577949291795003417085383304736797522385⟩
def resval6Tail152 : Box := ⟨222640321294822681082733186150166775406728108171,67173080061972891008183594932254049014349056183⟩
def resval6Tail156 : Box := ⟨233389651124006486610844479650042640913636346275,65660108267106935871517205403822167201437417846⟩
def resval6Tail160 : Box := ⟨244657971923908621759964296431998811477849453450,63922509381369019705620735221400833143353729703⟩
def resval6Tail164 : Box := ⟨256470340213097842612430294519319108353210097452,61944607307891278297054779685597412943386707390⟩
def resval6Tail168 : Box := ⟨268853023229832335097737996083666918828607596778,59709815145196053308460760988833025990676100249⟩
def resval6Tail172 : Box := ⟨281833556425131432797742544829582492639058775526,57200586291862089432335054972601993947500163617⟩
def resval6Tail176 : Box := ⟨295440804693261318155359850376436695699129433198,54398363048061614144126570116110701754077368971⟩
def resval6Tail180 : Box := ⟨309705026558783643320160342218144010628096124061,51283522574167788014457758441805158543797492228⟩
def resval6Tail184 : Box := ⟨324657941462629141200209478640373685728097938605,47835320073679892727356520850639545558635848705⟩
def resval6Tail188 : Box := ⟨340332800296820265293890957376967837417146039005,44031829061146697705268922990836566568754725411⟩
def resval6Tail192 : Box := ⟨356764459344691367396254022988004241304142441357,39849878568872836856405443332327480450220561655⟩
def resval6Tail196 : Box := ⟨373989457791027751264669101762728340950983604111,35264987138959085389324747998517264715979068776⟩
def resval6Tail200 : Box := ⟨392046098974483391996706514010621707906006474027,30251293439638660412592033866343903549417925598⟩
def resval6Tail204 : Box := ⟨410974535562958877656740334347508607759350448360,24781483336910765604569519682584900494414101907⟩
def resval6Tail208 : Box := ⟨430816858841361725073557232681589601440353503050,18826713244119960962638511885944744525525539512⟩
def resval6Tail212 : Box := ⟨451617192356107189242841777069953425770796582591,12356529560259072680484237135204284925408967275⟩
def resval6Tail216 : Box := ⟨473423936525080371604597224467851818443647946104,5338666940928382041668480445710589427902265790⟩
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
def polyval6Tail5 : Box := ⟨12049087485766955673779644978680757682610824495398999604842,3708139619976916936300603580292949533664330008535612809807⟩
def polyval6Tail9 : Box := ⟨12630829257497002047156214895665001559341596625576174539806,3628578985807420037408285520256220039102107655718183955698⟩
def polyval6Tail13 : Box := ⟨13240660221797861420725191319785767125644126586944477416939,3536935692752096201861436696201170933063940895322895552864⟩
def polyval6Tail17 : Box := ⟨13879934526665026601815916557937516527410272805297698283488,3432363710937028473929623595749035170101706667631157696967⟩
def polyval6Tail21 : Box := ⟨14550073730262278586041893308192859546243563923530292398788,3313967804303501239057111691245592568346219613535295173829⟩
def polyval6Tail25 : Box := ⟨15252568025400864296011011957145380005041332072081414425243,3180800876225307845819927664949678538918603671279576736221⟩
def polyval6Tail29 : Box := ⟨15988979553115106698156462673515192126192313148438168061684,3031861190339764856878111229575983701076222365739006918427⟩
def polyval6Tail33 : Box := ⟨16760945876405235198318960078076376254764614127858335113144,2866089448426566588802573968589300240694722428698299286382⟩
def polyval6Tail37 : Box := ⟨17570183621696649248681327740164861840089546708046243244116,2682365718150535364385756870783320838372533947583078976465⟩
def polyval6Tail41 : Box := ⟨18418492296113024015392987526194408047111300566410887541385,2479506203131009890824585044772973764681147816466988704258⟩
def polyval6Tail45 : Box := ⟨19307758289051752205580289803599238907345748855824284577840,2256259847427514714608177686273114517247982131351371160264⟩
def polyval6Tail49 : Box := ⟨20239959066960050823312993405827533625450230107327464298821,2011304766139944691388952823491196451405673501233171904983⟩
def polyval6Tail53 : Box := ⟨21217167570639683176472561120729006259583282343166830727809,1743244493410889326972686168729550205081372988240791077694⟩
def polyval6Tail57 : Box := ⟨22241556824858610667382620076321361174835351141381122772707,1450604038686976063929097811282438367635433348423175891082⟩
def polyval6Tail61 : Box := ⟨23315404770520006154489324787051505316024816323742394055960,1131825741644246142753422027768203849141103881972187039438⟩
def polyval6Tail65 : Box := ⟨24441099330142880288941779344385210641865226503281445778425,785264915707942684967072509075425018861750830518857319442⟩
def polyval6Tail69 : Box := ⟨25621143793932175421494128456515252017123372054393790655218,409185265520899926034099167437160176777164095508770264159⟩
def polyval6Tail73 : Box := ⟨26906250000000000000000000000000000000000000000000000000000,2⟩
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
def resval7 : Box := ⟨57957963510529558402398467980157239245800321512791634969,21483774769821450012892582181456891840821749779312740885⟩
def polyval7 : Box := ⟨24012754942643634187491605220234944542781457994794697675610,6600380961712754973685461675374858660658782158132427493636⟩
theorem cell7_lo : Holds Q cell7 (127/128:ℝ) := by norm_num [Holds,Q,cell7]
theorem cell7_hi : Holds Q cell7 (1/1:ℝ) := by norm_num [Holds,Q,cell7]
def resval7Tail4 : Box := ⟨-54171575644142103139757951075980681592789302795560756821,20452117628523477466282778484472327688311977609995276087⟩
def resval7Tail8 : Box := ⟨-55026391353715061678512305128876323326849401912672077962,19597354419065381161179472800941713313912430685436934755⟩
def resval7Tail12 : Box := ⟨-55894641133519488008042034129492208323894956287739723309,18729104645168230511582624229962329462981732009294241810⟩
def resval7Tail16 : Box := ⟨-56776590836581393273202726565981681337329608257829968640,17847154942111299859902204419013602407129422186809692474⟩
def resval7Tail20 : Box := ⟨-57672456637191520808839996877985164801696738018912238073,16951289141501190535093562997492211678557219132572164811⟩
def resval7Tail24 : Box := ⟨-58582458114510589157235490936673392841600807025158023807,16041287664182122407595225683473385453094599653688057187⟩
def resval7Tail28 : Box := ⟨-59506818312387242539829718161268653024465484976587240653,15116927466305469032363221516386724554066412928330087031⟩
def resval7Tail32 : Box := ⟨-60445763794031750045344140052068112276324005148065918865,14177981984660961527398861832626262824519099407237581821⟩
def resval7Tail36 : Box := ⟨-61399524697547285629688705639931081707374600933159212699,13224221081145425943095782170440529524983859758250813437⟩
def resval7Tail40 : Box := ⟨-62368334792337406251280194543025161207909910277368564735,12255410986355305321401158947139832190842416763730880450⟩
def resval7Tail44 : Box := ⟨-63352431536403571452142374783828209506922874003365678221,11271314242289140119948705987593689951982235562277500034⟩
def resval7Tail48 : Box := ⟨-64352056134546748354732177697489046416064902754814118470,10271689644145963211286468191040867689229715950351201452⟩
def resval7Tail52 : Box := ⟨-65367453597487367339934033325010421704009494445582171407,9256292181205344070642740356183031449850448798342651387⟩
def resval7Tail56 : Box := ⟨-66398872801918108946686544617007471921963742400018373625,8224872976774590648921035128319192655081343550124906373⟩
def resval7Tail60 : Box := ⟨-67446566551501268704196322330880908054625814605871296116,7177179227188153906148266150351874526874463557602768358⟩
def resval7Tail64 : Box := ⟨-68510791634290410479368672625852708815723429559879397982,6112954139573204722244119489156110498984544403038129676⟩
def resval7Tail68 : Box := ⟨-69591728541915992365450087281643367872199080521897103859,5031933301693076165849283427455196637043831287873435298⟩
def resval7Tail72 : Box := ⟨775927820363263259085967934782945045485758520243656109622,933542024856765657115597953649897019561186308857110939⟩
def resval7Tail76 : Box := ⟨-714737450753197187611066318328963262482434584534640642,271998875803833752939128805147643497665368500376144926⟩
def resval7Tail80 : Box := ⟨-725990053275238201062147588362365530540387873848037265,260721403566660037394191308951350575513511551986971515⟩
def resval7Tail84 : Box := ⟨-737445295279735628349557053161186914786991921358007987,249266160294282213257213404958041262179246829539216570⟩
def resval7Tail88 : Box := ⟨-749081288390440648349086126732408278950811956960080727,237630167182900523821878848634698940061926523240168408⟩
def resval7Tail92 : Box := ⟨-760900883372418293311976942396320579388238395839790281,225810572200921119894370721999708801003308760887771166⟩
def resval7Tail96 : Box := ⟨-772906977240036874957319613598530858861151014986990238,213804478333302521945602232524875245157732596513880316⟩
def resval7Tail100 : Box := ⟨-785102512719707743908765862841795454007500665790847271,201608942853631652547930375633385708931614383835524737⟩
def resval7Tail104 : Box := ⟨-797490478970500660577123356228820445660325449212813459,189220976602838735848336094651897970419766783545489987⟩
def resval7Tail108 : Box := ⟨-810073912316793209463575625556187554398501411876123117,176637543256546186957238242593649609032147750735525479⟩
def resval7Tail112 : Box := ⟨-822855896992482186706345852444256930775078169062934276,163855558580857209713925465648811663973664795208633938⟩
def resval7Tail116 : Box := ⟨-835839565896937755384832722682023673751981732487862772,150871889676401641039594639927405250284673573504256008⟩
def resval7Tail120 : Box := ⟨-849028101362885641663548161408642647676320029673309743,137683354210453754807373231826218743007039961670940746⟩
def resval7Tail124 : Box := ⟨-862424735936405582424659279919846902247229560467114727,124286719636933815063551993817946595149963844715541316⟩
def resval7Tail128 : Box := ⟨-876032753169237266111454507847161019536388331100316060,110678702404102191684260505171265711065833828949680190⟩
def resval7Tail132 : Box := ⟨-889855488423601125530757127734885117328675629016218984,96855967149750630459184130102732498985630733521992796⟩
def resval7Tail136 : Box := ⟨-903896329702377471373872911501335329126910832880459748,82815125882788332839083391521977409362601181267092419⟩
def resval7Tail140 : Box := ⟨-918158826342646363534296344995490102831103362262172933,68552731056960474814956875183303435560766971829382646⟩
def resval7Tail144 : Box := ⟨-993652483159000693279716165547020754240448843909162388,51818632007601756956700342127813251901013120148535764⟩
def resval7Tail148 : Box := ⟨368641131900735932208253159223412245650256943763,117784026411505758806772491849063148359062915402⟩
def resval7Tail152 : Box := ⟨374401855718777795056998105569899030476191213055,111967705497300395112491880347781202614003757024⟩
def resval7Tail156 : Box := ⟨380309462363353209268268302067440710236951081294,106060097921398838266531539598971314892473004155⟩
def resval7Tail160 : Box := ⟨386310284814011135944490684186003799061009777749,100059275470461270276362589997081432600981364816⟩
def resval7Tail164 : Box := ⟨392405792971324010189030222410690781712028176654,93963767313147934570089709412407032462285977244⟩
def resval7Tail168 : Box := ⟨398597480860724351638879103022201757756182861002,87772079423747590237235073009276665572994942340⟩
def resval7Tail172 : Box := ⟨404886866081831897308209876628418972950298861195,81482694202640044512608629061176401726006192745⟩
def resval7Tail176 : Box := ⟨411275490180149777355636978482664609197068073029,75094070104322164462367799604403245233896850118⟩
def resval7Tail180 : Box := ⟨417764919024901094202049111332975657839409522792,68604641259570847615626933516144775074562751215⟩
def resval7Tail184 : Box := ⟨424356743192827745217277368369729873848096494951,62012817091644196600336678664366151613030238473⟩
def resval7Tail188 : Box := ⟨431052578358045128289911300375275691792803849300,55316981926426813527749098752003492415730262899⟩
def resval7Tail192 : Box := ⟨437854065688048282261034026655233518052646134931,48515494596423659557186022702564107339368546512⟩
def resval7Tail196 : Box := ⟨444762872245966524376432063731754993353921389297,41606688038505417450393477418663468538048137535⟩
def resval7Tail200 : Box := ⟨451780691399165178780650856946040408282160466463,34588868885306763364021145001016505597897240187⟩
def resval7Tail204 : Box := ⟨458909243234294583432652098849809390739339754217,27460317050177394330674288102186555219622744769⟩
def resval7Tail208 : Box := ⟨466150274978905113918158344342212314693494096445,20219285305582635169493559266313712544186432986⟩
def resval7Tail212 : Box := ⟨473505561475216732886797452039673434003127092246,12863998851767001964010061217443497314105924541⟩
def resval7Tail216 : Box := ⟨480979036010806126413032164522425000077250043522,5392538832054664512082283972758398004869302551⟩
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
def polyval7Tail5 : Box := ⟨20582444765084396126249389114997862675125759461690542871671,6277829012683430342314477831071036167762418781114817445103⟩
def polyval7Tail9 : Box := ⟨20907208834468037531482711435749997716634095309293725854099,5953062995637053280380489832946382588107461911321920056355⟩
def polyval7Tail13 : Box := ⟨21237099254003344790064894645618832841614568547279790569620,5623172575923411993953303542985050843821763465308701090106⟩
def polyval7Tail17 : Box := ⟨21572194944770996482583850395011408111729807608509567214547,5288076885155627896366976531484426817907093270177316849844⟩
def polyval7Tail21 : Box := ⟨21912578039464714627376274376425736818440409150723734407057,4947693790461909315395799436066293919129916644017648010454⟩
def polyval7Tail25 : Box := ⟨22258331966910960168243526934519352092400648273268467623409,4601939863015663769679656530793792457716526834852379449370⟩
def polyval7Tail29 : Box := ⟨22609541472342105564273480665209492957274255531229251220478,4250730357584518373496526941177906020876865198672258783645⟩
def polyval7Tail33 : Box := ⟨22966292638167594883827197874470189592397979542057361659400,3893979191759029053930825816542136602710330223595233153094⟩
def polyval7Tail37 : Box := ⟨23328672905072977170791223977262389579745151860708207584288,3531598924853646766964894017863717230408663333159478538143⟩
def polyval7Tail41 : Box := ⟨23696771093451857395966026009782079754166249940842581268437,3163500736474766541789959549739385717925633318718625221735⟩
def polyval7Tail45 : Box := ⟨24070677425176017626945794739937323657790717452605338208984,2789594404750606310812666981464141922315464279635913812760⟩
def polyval7Tail49 : Box := ⟨24450483545709044328798638064266811634328118593235483631571,2409788284217579608987743332965862845960504591346577689342⟩
def polyval7Tail53 : Box := ⟨24836282546568881906504244693596769962788456459821900170765,2023989283357742031919724710260463327694254485779063994972⟩
def polyval7Tail57 : Box := ⟨25228168988144818163059527050829204704310955686491382583538,1632102841781805814882460227550500364948191501944686755076⟩
def polyval7Tail61 : Box := ⟨25626238922874503145683456215868071604227527635974289986694,1234032907052129224239064759222203250075765150048621741593⟩
def polyval7Tail65 : Box := ⟨26030589918795547634757270156561208863704822905552385384624,829681911139384570548082912774722034399359064008128310999⟩
def polyval7Tail69 : Box := ⟨26441321158938696741040692945477728367742340952984466919654,418950742464143208728699339192125095129513501782201477934⟩
def polyval7Tail73 : Box := ⟨26906250000000000000000000000000000000000000000000000000000,2⟩
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
def pend : Box := ⟨1030608566380107312162245886476200543799915634055897563839448,4569524249076998931180419409259403524606097029561329869⟩
def zend : Box := ⟨1003745442031863888114980468750000000000000000000000000000000,2890406884916067441406250000000000000000000000000000002⟩
def betaquot : Box := ⟨428748417566879945318694859330570039066798756337342920478555,394767580570348188260357399916071796727888847161491589⟩
def crit : Box := ⟨114877698824600404318147313795529691881682574352827429931,11615021619658446579701497102661699340649826255023490550⟩
def subsonic : Box := ⟨536197019450707803235630926056631139387745668733327859901,6165296957038753293388276282716793892436571890319190476⟩
def pendTail4 : Box := ⟨26858682296429227040839424452441652914985632649037099649693,1555488749585183461186107287471080511795055972433072148⟩
def pendTail8 : Box := ⟨26858716487870191591541939421805736181555120869880322865187,1555340650720302363537831798238950543801622315105416782⟩
def pendTail12 : Box := ⟨26858716489292232690915569087332493120887841686727521680022,1555340633729293925780892041991250090206343566999338259⟩
def pendTail16 : Box := ⟨26858716489292906665814493320675681314125511269955738370955,1555340633715744629783327648903810463618963660961180334⟩
def pendTail20 : Box := ⟨26858716489292908228713685414545602757051895519075410177910,1555340633715696473006408250776818801923147914032813228⟩
def pendTail24 : Box := ⟨26858716489292908241576275374691245095753651206028465089450,1555340633715695872297793803817058148459903690747833356⟩
def pendTail28 : Box := ⟨26858716489292908241885603264078247041070550154931570418491,1555340633715695849683024871221649322211724168813026436⟩
def pendTail32 : Box := ⟨26858716489292908241904239741109187866206480945056073423827,1555340633715695847338108200954475697129698883731943605⟩
def pendTail36 : Box := ⟨26858716489292908241906486893646356424674671637630042924453,1555340633715695846702516122785278614273656970220897447⟩
def pendTail40 : Box := ⟨26858716489292908241906506744654037622962408855174304003170,1555340633715695846262859773340631251174132360942919271⟩
def pendTail44 : Box := ⟨26858716489292908241904358502195360307395794527366400533809,1555340633715695845487363259823302116009425022562292903⟩
def pendTail48 : Box := ⟨26858716489292908241886274285070771531692646659176092906403,1555340633715695841922384568237264677009784241634325556⟩
def pendTail52 : Box := ⟨26858716489292908241573630914273262380564431835836838806183,1555340633715695797093017116469535745712226175911161428⟩
def pendTail56 : Box := ⟨26858716489292908227214382257874038202391110339668319118490,1555340633715694117966914603971593838491548445604199846⟩
def pendTail60 : Box := ⟨26858716489292906096529282707834311758170681373272493038508,1555340633715494384941928676413244420845137025059671074⟩
def pendTail64 : Box := ⟨26858716489291560966816876339750737606708224229047294308545,1555340633619950079441056001563918196640878656895584925⟩
def pendTail68 : Box := ⟨26858716483269739452039952718412064403951706496340581626489,1555340308730682135991934482170218717743096090848860191⟩
def pendTail72 : Box := ⟨26857929298676433788103983773246010085565312383386600515560,1525158423173541499795454082369305329435777068837154990⟩
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
end SepticProfile.ExteriorCertificates.C14

end
end

end OAI
