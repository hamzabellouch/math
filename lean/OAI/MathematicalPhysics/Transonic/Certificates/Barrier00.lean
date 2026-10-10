import OAI.MathematicalPhysics.Transonic.Certificates.BarrierData00

namespace OAI

section
noncomputable section
namespace SepticProfile.ExteriorCertificates.C00
open SepticProfile.ExteriorJet SepticProfile.FixedInterval
def cell0 : Box := ⟨250000000000000000000000000000000000000000000000000000000000,250000000000000000000000000000000000000000000000000000000002⟩
def resval0 : Box := ⟨101220585042696322703151617556453404957046072565695914100,884777692186651092315221970793925082933540414769411190⟩
def polyval0 : Box := ⟨3663631517932671403915651893894520245565285231405904929672,24367476388687532934378571638503217910366318961861704566⟩
theorem cell0_lo : Holds Q cell0 (0/1:ℝ) := by norm_num [Holds,Q,cell0]
theorem cell0_hi : Holds Q cell0 (1/2:ℝ) := by norm_num [Holds,Q,cell0]
def resval0Tail4 : Box := ⟨44674348863426538674406928235130741566483168790509,2454518751591645911915147665606530729031965301885⟩
def resval0Tail8 : Box := ⟨4644282373658520276248299887471792116073572493,420352446939452373464372302199891351548151628⟩
def resval0Tail12 : Box := ⟨3632574732095636385177876975011470957452876,484022883891916655266614609670472800660774⟩
def resval0Tail16 : Box := ⟨12515775242351594678476184209178564482640,24311905049096484323559410401151526664681⟩
def resval0Tail20 : Box := ⟨146787528608404392555761752096520662106,352054102973901152333610074292350970872459⟩
def resval0Tail24 : Box := ⟨5029914777626069667241239922918843172,5632280133517616771154740069932247361937913⟩
def resval0Tail28 : Box := ⟨458310043308169790454632289062861131,90116455278464301730993069757072430312267178⟩
def resval0Tail32 : Box := ⟨102931168255467912963468734425181416,1441863281165907705746592013142192581319779985⟩
def resval0Tail36 : Box := ⟨-462141342837199975022143093833395761,23069812497323734372332599772549711399447260227⟩
def resval0Tail40 : Box := ⟨-133258676484579240645557808338720075289,369116999831683039754521386811065949443340468722⟩
def resval0Tail44 : Box := ⟨-34134368007825803660773687184473087867058,5905871965304840974957667866836366040374001568837⟩
def resval0Tail48 : Box := ⟨-8738464336286435670046911930577910815408054,94493943252561104409185709099667433229284530093871⟩
def resval0Tail52 : Box := ⟨-2237047404928438714500669711837992009861640699,1511900994808938464823242696058855083870022929005120⟩
def resval0Tail56 : Box := ⟨-572684145639591630625249656630849759420194252189,24189879025551221029472494792116195481678586989304914⟩
def resval0Tail60 : Box := ⟨-146607141181212236738787011503580438734877167438415,386900620212804661723482929146390506403668930722906184⟩
def resval0Tail64 : Box := ⟨-37531426666806108792000840863169905038447094038722888,6155224209453687203939968365847328352483050472523320683⟩
def resval0Tail68 : Box := ⟨-9608012416787879564289858104580396036307175002294250120,89476053449508915811887970793383143292863985901946215681⟩
def resval0Tail72 : Box := ⟨698407082196866728657788996878321556418174882088055524070,4142285635259473898444369828948063625658170039124180113⟩
def resval0Tail76 : Box := ⟨-20510206999742869637429110248528117007575087393011,857040626762504702091382154013678422247993236710⟩
def resval0Tail80 : Box := ⟨-952394012865358271705440441303144296628783671,73207423355658230203985955738254363844670688⟩
def resval0Tail84 : Box := ⟨-463065625731934785008910816578425889153711,54524360760929790039030615944649624400046⟩
def resval0Tail88 : Box := ⟨-1102033359379391354325093154566531992865,326929786983594177299309804710138549468⟩
def resval0Tail92 : Box := ⟨-9447303544538308770155523003831829008,2291797176682229528379105836887342034796⟩
def resval0Tail96 : Box := ⟨-244923525156514567589622378711342573,36634353748047159457438241675923365486979⟩
def resval0Tail100 : Box := ⟨-17251670643984499592903725556514776,586148460911818587043134404690842938600035⟩
def resval0Tail104 : Box := ⟨-3100364685838110787004464688288913,9378375261054604298497627092463530568110866⟩
def resval0Tail108 : Box := ⟨-3055101626941573574095970389865566,150054004148598105803915784365629516499541658⟩
def resval0Tail112 : Box := ⟨-434500011728175694531938974661808177,2400864065967293298360636730782140173694001090⟩
def resval0Tail116 : Box := ⟨-110862055225531952024821408809218129339,38413824951539304181271916354125862661414127297⟩
def resval0Tail120 : Box := ⟨-28379729030621730436042004566960452875876,614621172618619117286241154448971218649790318369⟩
def resval0Tail124 : Box := ⟨-7265204531204032981966087623662990038622796,9833931950768571144146139244716005072105411188494⟩
def resval0Tail128 : Box := ⟨-1859892266508879427763616191200253365995349036,157341167563298104551584762359271812787852006172762⟩
def resval0Tail132 : Box := ⟨-476132418673681229864818497486442616622918766492,2517012306871077820001113804139514624239430330710212⟩
def resval0Tail136 : Box := ⟨-121889902586019403300352464166928047103448122534668,40157925127414831356084364949596612118885742628334836⟩
def resval0Tail140 : Box := ⟨-31203854883306385459190244659242489537911203348944562,613273200552740059817161963045277169564080859462312416⟩
def resval0Tail144 : Box := ⟨-8019093681690834442639805462192468506249838621775040893,2304680130833718414227232729997419672961385850955926408⟩
def resval0Tail148 : Box := ⟨42258212139137451290750666652361362956636082,1485877712418046440217277359073564066423800⟩
def resval0Tail152 : Box := ⟨646991053200469433264480915705430790567,43510981673696851770574899813653825234⟩
def resval0Tail156 : Box := ⟨176624129087260084912739379772527387,18723650729535863431681931637489781⟩
def resval0Tail160 : Box := ⟨265965309793759870615919526917703,41692516542813554230294440015968⟩
def resval0Tail164 : Box := ⟨1527414233968972904724019430146,21910998130141781703119094562597⟩
def resval0Tail168 : Box := ⟨27379501378866422300695757839,345502356175715651594215891758536⟩
def resval0Tail172 : Box := ⟨1355781972753858891936457323,5527915664829520917011865581348912⟩
def resval0Tail176 : Box := ⟨172018161690218525002111296,88446642566671741784080263132627690⟩
def resval0Tail180 : Box := ⟨58617300138308321977978444,1415146279685904026142471464805636083⟩
def resval0Tail184 : Box := ⟨1345969299964975169542262681,22642340473401624047493868042790754636⟩
def resval0Tail188 : Box := ⟨334385252995501741126817108386,362277447260830788424813520020454177455⟩
def resval0Tail192 : Box := ⟨85584439652201183982930726367076,5796439075937623833594231245357689698583⟩
def resval0Tail196 : Box := ⟨21909537811144638032054497493410989,92743004674808968706962573731217294913072⟩
def resval0Tail200 : Box := ⟨5608840848009009063274462229192719734,1483882816508639508746357312778214435164055⟩
def resval0Tail204 : Box := ⟨1435863238797218312520610290999760956483,23740778942353127408854505947567139320154729⟩
def resval0Tail208 : Box := ⟨367580991297593104203785865630216771666359,379507855899407699310502754788048027845289882⟩
def resval0Tail212 : Box := ⟨94100747052574082106841870795758736879797875,5983906248043844723347556815872352219763452970⟩
def resval0Tail216 : Box := ⟨24090494203635958468693991433369287355839746017,73157883375648366639915492276153814474981071216⟩
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
def polyval0Tail5 : Box := ⟨1734320097034234367257111917213236683185380358942243,67866410486383898687780807027909163408738316875675⟩
def polyval0Tail9 : Box := ⟨144515148671330842398101008168802543772591672404,11027268266416905049854630168829404214127926644⟩
def polyval0Tail13 : Box := ⟨97801690196711059739832002892815634822638277,11541646476376834086783336987762372817943611⟩
def polyval0Tail17 : Box := ⟨295275372721279840831414341945681016088444,410644732193714026918920034607707185512299⟩
def polyval0Tail21 : Box := ⟨3042902865391709569109959888096362477375,5778542995374926102384788057818396806028399⟩
def polyval0Tail25 : Box := ⟨91517247606712413692392913372777891821,92445508554116934691797127359911794193757584⟩
def polyval0Tail29 : Box := ⟨7293016062755366500097053383607448407,1479127683528600376571393309000890633554208886⟩
def polyval0Tail33 : Box := ⟨1473969366353074351369845545698149980,23666042887758181990909138528234427037701822263⟩
def polyval0Tail37 : Box := ⟨6207746745668474130707486010086877501,378656686187954009442237150695328475787459092061⟩
def polyval0Tail41 : Box := ⟨1410567587152011294209165141246319863284,6058506977683424980766253979574400992965671336372⟩
def polyval0Tail45 : Box := ⟨360899583100647406898571691532007547550595,96936111304589203919300403030889912987051217707005⟩
def polyval0Tail49 : Box := ⟨92389722857563469700890507619583458483636645,1550977694258054315566702875231166004439339546572736⟩
def polyval0Tail53 : Box := ⟨23651765190614634946293818322295124547110153327,24815620934598954156086707992968795109734121832645379⟩
def polyval0Tail57 : Box := ⟨6054851826813142968547969296616165131098138100259,397044258529996486832736203842584366957811600330231287⟩
def polyval0Tail61 : Box := ⟨1550042066728231549601993163847319343165536050059384,6351254972043018069549339744174426186205567289588420336⟩
def polyval0Tail65 : Box := ⟨396810771751853839896548873737122034214834095774067193,101248069455077420226882373940649723347027983295974585233⟩
def polyval0Tail69 : Box := ⟨101583589349063413534542330615381758388510351396930124156,1524734506316960832337685739388207786940518076697080185430⟩
def polyval0Tail73 : Box := ⟨26031250000000000000000000000000000000000000000000000000000,2⟩
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
def resval1 : Box := ⟨101026889260219606716413084008817673431748369935260721368,823211162634113231750348196187913139377728675542339967⟩
def polyval1 : Box := ⟨3646777460129420490410093164893370718140847019962546715926,18697672082364555448129794511338894339918994657207702040⟩
theorem cell1_lo : Holds Q cell1 (1/2:ℝ) := by norm_num [Holds,Q,cell1]
theorem cell1_hi : Holds Q cell1 (3/4:ℝ) := by norm_num [Holds,Q,cell1]
def resval1Tail4 : Box := ⟨43423876330374285082285840691471842998771278943810,3909073546729778739424850430631367072209988524863⟩
def resval1Tail8 : Box := ⟨4369657049283868285171806083320499886966148374,5959011572051799414736489580323627495066167665293⟩
def resval1Tail12 : Box := ⟨-315761526096367316000576549118777254585665363,18832239096147644031449553678369052120311431552005⟩
def resval1Tail16 : Box := ⟨-2091503674841110994233704239970222652774632710,59518091409493574511046259214721770201956277307674⟩
def resval1Tail20 : Box := ⟨-13706952779453339423335869938566373631168360083,188099463766245688418441868534748272704798109729157⟩
def resval1Tail24 : Box := ⟨-89829886580950545976431988016291475102448349880,594440684978809914417835957459658788508962221468470⟩
def resval1Tail28 : Box := ⟨-588709144724823858115066620161885660315321877334,1878421313145902789485794585994069973005428220734609⟩
def resval1Tail32 : Box := ⟨-3858164250871018559604904490710342911560168344375,5934741412371360136035323559544388913234483669909097⟩
def resval1Tail36 : Box := ⟨-25284865234508814312016331375130854445840671393718,18743622438657974916351536709899860432056346113222842⟩
def resval1Tail40 : Box := ⟨-165706892800877203852685996196149325806054755405847,59153308783698824437309455158562483846011143721231403⟩
def resval1Tail44 : Box := ⟨-1085976692659829041470136490654162045986548528768244,186391406186154042585128834227047355276461111210894097⟩
def resval1Tail48 : Box := ⟨-7117056853015455298420932321885217472722251567952020,585404054467680235577949904206485903065759980861578872⟩
def resval1Tail52 : Box := ⟨-46642343791922063227569102302925641623036656878138502,1826016970999412417361320248838908933810463038015443443⟩
def resval1Tail56 : Box := ⟨-305675264274738250741401781579418540270968203917167891,5612852940497871210648652698906624513568300571956554260⟩
def resval1Tail60 : Box := ⟨-2003273411950312293254562692315974656059939228835871273,16702198445108006633684679377927168858477444146263250207⟩
def resval1Tail64 : Box := ⟨-13128652631673128803736840092846777904073319356145994624,45989875705634354734577972644439469182755474132706483240⟩
def resval1Tail68 : Box := ⟨-86039922822820413337547263523088345712089913055103677560,100803804575840470573663848901342378417998479199028603191⟩
def resval1Tail72 : Box := ⟨700837656152536897942423895661806419200350615633132719459,3341568186484032349440261035745841486890058214433880002⟩
def resval1Tail76 : Box := ⟨-20069041247267809697641288376425065632137223392771,723697757884800798014838226010482684648955216999⟩
def resval1Tail80 : Box := ⟨-911849490423419770433745916579934997682624600,58107800827444890250361620817567981996689111029⟩
def resval1Tail84 : Box := ⟨-3022503175553684046074441269235079984863436,183463773443001407143657496965723334650157199483⟩
def resval1Tail88 : Box := ⟨-16968984249093614449446960873448453546529407,579827267861724722435444059393258594447646071916⟩
def resval1Tail92 : Box := ⟨-111201345068367700065126965470751584079835763,1832482926505058932458136405281297470074804633095⟩
def resval1Tail96 : Box := ⟨-728769080146296237115276505109006322861932640,5791173659651436435099558112352390246241245475611⟩
def resval1Tail100 : Box := ⟨-4776061042272625038934850685194179721528535699,18300495812479002725529166532268190787821910651325⟩
def resval1Tail104 : Box := ⟨-31300393646545553267867076037536838891592164780,57822398367111998807059716847175817135468089176754⟩
def resval1Tail108 : Box := ⟨-205130259801985562255211344949227731053738329852,182641127551978095442582579523562186393900004655695⟩
def resval1Tail112 : Box := ⟨-1344341670638286693528240937471523918001820438876,576540127462888878605523288510789587309513937631023⟩
def resval1Tail116 : Box := ⟨-8810277572695071249108747450415085400024318480263,1817590019935736459218922135008293351917256801311392⟩
def resval1Tail120 : Box := ⟨-57739035100414418377549813971370532230020196078268,5714587831099072879531222473455541945931416937415806⟩
def resval1Tail124 : Box := ⟨-378398540434076116215702915077153237395277586709718,17865004888542081284063375520684252760637070849078512⟩
def resval1Tail128 : Box := ⟨-2479872674588774490613974795698104752906601699225293,55178291249088962166220256834595841732347349367582404⟩
def resval1Tail132 : Box := ⟨-16252093560187639618569798758592734571922584690782505,165976177606004920060895774062652400705526374546524272⟩
def resval1Tail136 : Box := ⟨-106509720358423343370038869605358106264280174876624760,469421605797682005014307473250638695586630155836669025⟩
def resval1Tail140 : Box := ⟨-698022122432827304205716396657879460971951111117222594,1122205289853372125375828479337096248718631872221039785⟩
def resval1Tail144 : Box := ⟨-4587358625396672802362854541506462324388732872129623040,1173690878666396222978482581665488796221658598909080115⟩
def resval1Tail148 : Box := ⟨41654264099015389579955338104272321000034593,1282125871695694924573386243981433751368847⟩
def resval1Tail152 : Box := ⟨623115281164102493020608629880310340422,2246131961068136487111427426953779310106⟩
def resval1Tail156 : Box := ⟨252007403890403208886709255646309947,6987846279958350782737922085640734292875⟩
def resval1Tail160 : Box := ⟨560771036505530977856376189013914193,22084730063834827532028870639532146378502⟩
def resval1Tail164 : Box := ⟨3673465071879568561670718663327364627,69796751062910916536271440030073613710291⟩
def resval1Tail168 : Box := ⟨24074411727763307373237637164936683627,220579736437395021458803380117000477723323⟩
def resval1Tail172 : Box := ⟨157774064543370903611255263714640462168,697059208372104863224270233861624410665689⟩
def resval1Tail176 : Box := ⟨1033988109384036099520102733698406294415,2202515981073104876929435306995804358596886⟩
def resval1Tail180 : Box := ⟨6776344473658335113957613984413755650639,6957529730967293731044311625254845309624050⟩
def resval1Tail184 : Box := ⟨44409451142567017341190660345960689990734,21966236910744886254986799997084601194709846⟩
def resval1Tail188 : Box := ⟨291041779007927057354713256057894597551404,69273470179549949826566112520599281301991840⟩
def resval1Tail192 : Box := ⟨1907371402906350641229456747750687538467539,217950839231548173636691913335812054954823085⟩
def resval1Tail196 : Box := ⟨12500149226087060550504880267056153735279352,682360368334658102220218634001723099645893961⟩
def resval1Tail200 : Box := ⟨81920977968084219323548201604219277686822781,2114181398520196803707752854364192172714117530⟩
def resval1Tail204 : Box := ⟨536877321211643645920578652250351374402563083,6403890683492062103355574261732995243631985384⟩
def resval1Tail208 : Box := ⟨3518479212295493188276559521635799255656704466,18417775222324986746287523757092478762944522275⟩
def resval1Tail212 : Box := ⟨23058705372861071769191961919681366323295074489,46270691362657382280955616827888705284726947991⟩
def resval1Tail216 : Box := ⟨151117842315849273153475481464311323521526634332,67997475462262675159495259148360095093897188423⟩
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
def polyval1Tail5 : Box := ⟨1689219502380027026337250715245394998983757938022012,135058673445835815648984914332641482593721317229154⟩
def polyval1Tail9 : Box := ⟨139976602376694292827434129594267819414879977381,262609137821974323495543392475875589128188381719922⟩
def polyval1Tail13 : Box := ⟨14818266747653252911083539895897132306620542863,829942932096465191400683754301214502869248098459454⟩
def polyval1Tail17 : Box := ⟨96515861392353870952449406583380199581630919203,2622979529816409985979477163334045476428318117010954⟩
def polyval1Tail21 : Box := ⟨632524591236118948361209867190917503749640032067,8289583125039050596248664408622008439819488411313077⟩
def polyval1Tail25 : Box := ⟨4145313143527234376987258425763423241809904737775,26197030073332961064268482120993886839192825866996186⟩
def polyval1Tail29 : Box := ⟨27166724216909393731737219018709545887650198383666,82781486349091215279432953104083353188440843667553091⟩
def polyval1Tail33 : Box := ⟨178039843827898644758187173498434813390803010355414,261538197029837262794208443236406643159801606961721378⟩
def polyval1Tail37 : Box := ⟨1166801920510509414679401758575617547527461715188529,825985749186381848113945212636352817983454349819499188⟩
def polyval1Tail41 : Box := ⟨7646753066257671531500014750271055499505673221727452,2606563778827130517994526718349105234825236774558866906⟩
def polyval1Tail45 : Box := ⟨50113760895026273806169813051558152777047549316403113,8212082488051978372252580666736122858986761452112973903⟩
def polyval1Tail49 : Box := ⟨328425543401644188357958137004283002700676615234877301,25784194700183950737872270569317402322185498282929202520⟩
def polyval1Tail53 : Box := ⟨2152369641237015480388061276246787576576920237919849680,80376405449601408005609010719470057361441240193170571976⟩
def polyval1Tail57 : Box := ⟨14105769680810914076229507427605076627803332287094802899,246725914556900649986892312228232951894004601919934409626⟩
def polyval1Tail61 : Box := ⟨92443572180164366541614807232921726376709093538496976901,731913355780999005283067690254682552692200556556329574820⟩
def polyval1Tail65 : Box := ⟨605838194641758571729128014400157591051361285611174927163,1999536787557440223938193597283668321916120591043371604111⟩
def polyval1Tail69 : Box := ⟨3970421207614090983521561489486785897228204220834613423173,4263850349978881692686308999342357883318319050206434601956⟩
def polyval1Tail73 : Box := ⟨26031250000000000000000000000000000000000000000000000000000,2⟩
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
def resval2 : Box := ⟨100931460273492237401021983340788848043551165495013558274,812879099779432118549413764635448739307682739871594627⟩
def polyval2 : Box := ⟨3638446731894053603328098642694179225251745478363304817326,17599397496958902590657006153164387491104020168884069715⟩
theorem cell2_lo : Holds Q cell2 (3/4:ℝ) := by norm_num [Holds,Q,cell2]
theorem cell2_hi : Holds Q cell2 (7/8:ℝ) := by norm_num [Holds,Q,cell2]
def resval2Tail4 : Box := ⟨-157126196496121394034271219080374996010576886183819,34545857390230335197872734216012493334502096189564934⟩
def resval2Tail8 : Box := ⟨-458812279099630138408949129683477038256313271055315,58812973716975046386341524126997613590401440182244160⟩
def resval2Tail12 : Box := ⟨-1052799417531116698070421277675691006062972575307068,100062257606020006606471747091909023617901044074592395⟩
def resval2Tail16 : Box := ⟨-2415750948530536656122477170025779584375838827360448,170082072283652815541438160317241013893231187559189355⟩
def resval2Tail20 : Box := ⟨-5543176155022768982280043672647983017755103603003340,288730494798355328662395115945072347991681102276852386⟩
def resval2Tail24 : Box := ⟨-12719358303125944703306800358472426007664216796848875,489298532669400951860414968640475258604636457120167106⟩
def resval2Tail28 : Box := ⟨-29185808121342465820880371396298630941987374437764275,827234550655613044065862362225979970904017931423325526⟩
def resval2Tail32 : Box := ⟨-66969683170767825387380087679341939555870659952223691,1394045639424155027235844602109291972145352057842578125⟩
def resval2Tail36 : Box := ⟨-153668469461133721104136714019597794970291448921470535,2338759169584598892124632031680797464578225644110084400⟩
def resval2Tail40 : Box := ⟨-352607290172082894417500781537885643430584650562291405,3899364225667700855544169845464631120865595998073528871⟩
def resval2Tail44 : Box := ⟨-809091816418109469810614987291788360224501338639349551,6444583872411442483247153635502919803533408685457192096⟩
def resval2Tail48 : Box := ⟨-1856540081957117124271801004397346123032055728430793439,10517910405942026896982111290699210915987960947162400023⟩
def resval2Tail52 : Box := ⟨-4260012282873205668692285637571677381342890405505108231,16850253938882268637473283962944789865627891275795895485⟩
def resval2Tail56 : Box := ⟨-9775013653946932928145115745779388188192873651137267843,26238168538602178303318355011246179336533992360075211799⟩
def resval2Tail60 : Box := ⟨-22429722167467934299010066652352142020892864208954580868,39007176733273221365287172731364364267700296334071097567⟩
def resval2Tail64 : Box := ⟨-51467185040680342371871319247410033170047501467996733301,53341452150181340473341754674985598206840594911628411318⟩
def resval2Tail68 : Box := ⟨-118096463733007662679210168488046644485887829821721476576,60702429989921810963304900913158344352165598138518486310⟩
def resval2Tail72 : Box := ⟨702051554540735186970530392028307267673678124580525373478,2941619039901845658112469210214595924734523354941021448⟩
def resval2Tail76 : Box := ⟨-21964841321632710923921287344474628817189482783215,392984219256369854509398151841719087822576213144068⟩
def resval2Tail80 : Box := ⟨-4836986055226561886556124812252115169516595125575,668351006433603605775488419564147853591591641996795⟩
def resval2Tail84 : Box := ⟨-11096888935831419896265370759010187054621042846505,1137330520055055972218747776422387705576706728557024⟩
def resval2Tail88 : Box := ⟨-25462892958879604160934995482479665922123595674978,1933703564930990129215507847027843973754169190889350⟩
def resval2Tail92 : Box := ⟨-58427091239455473841411004900384855493913212230326,3283824392106056752251807491870808433421281152687278⟩
def resval2Tail96 : Box := ⟨-134066659131978469062637059767845938862789371238594,5567666816829363085120542886237339983021729545295255⟩
def resval2Tail100 : Box := ⟨-307629024644561756096471704090715453730141717530891,9419276563667664002626348965993529281167058130050481⟩
def resval2Tail104 : Box := ⟨-705884799520534940476677269931248485732111028969626,15887786708070833922578849879222159793062726964417638⟩
def resval2Tail108 : Box := ⟨-1619721516101599304513800315299330024901749519469262,26688349493933488930019078083169342567757403656478723⟩
def resval2Tail112 : Box := ⟨-3716608987053478939303648266797303411265641476586853,44575710403660274248399001955144474929812455874261142⟩
def resval2Tail116 : Box := ⟨-8528121794598816419987374859195027286119502833099926,73856443063528435996747472475599556824736779084696950⟩
def resval2Tail120 : Box := ⟨-19568607189203040270758056312324372740871008121735244,120975823322620877220436758707424970083085875192942664⟩
def resval2Tail124 : Box := ⟨-44902077684661267232912794176000729354334649745977951,194860515974826765337023384627990156332878943803580199⟩
def resval2Tail128 : Box := ⟨-103032196461677152612631822109878176496887043194681183,305992203217316181185647884742847215761048149090943764⟩
def resval2Tail132 : Box := ⟨-236417423315448949178851902786087951572368559603014478,461360144816645808915511114302180903367771982640792043⟩
def resval2Tail136 : Box := ⟨-542482835140794159794387627747874813957668706052046892,647894890420121188989346705890913667806117338087149945⟩
def resval2Tail140 : Box := ⟨-1244779787636295167546817535482830491119828266508987803,785952068845446885595298721512018886325578368725901006⟩
def resval2Tail144 : Box := ⟨-2866170853150286424756214143281008554776885210870858384,605258239883682369769502516389743671183407040345297269⟩
def resval2Tail148 : Box := ⟨41550103297537501284874766270576927921558729,34953726921607687992864232619586996071242555⟩
def resval2Tail152 : Box := ⟨433477791029496391670919827967867019928627,57555528484949001266867488868944189992145143⟩
def resval2Tail156 : Box := ⟨993253194257589807058921237594704482155269,97932348635128980301568066800745461191376761⟩
def resval2Tail160 : Box := ⟨2279115953144973595384397574036526797839152,166483593080891766115215459807326799646373296⟩
def resval2Tail164 : Box := ⟨5229653831795039802578053442644941944065682,282672077197927852306723388673698768136062050⟩
def resval2Tail168 : Box := ⟨11999950755240880284401195942262351659756898,479147692017661643860444176293685485751678935⟩
def resval2Tail172 : Box := ⟨27535057340270469681660719029376101325007600,810341137910795182650615177065513710079218561⟩
def resval2Tail176 : Box := ⟨63181874509014580533702373573116364207640124,1366197923803507246460070785083836242530076883⟩
def resval2Tail180 : Box := ⟨144976973068967457107439837778279264167100265,2293481858204705763505183463564551392214376254⟩
def resval2Tail184 : Box := ⟨332663804035147623236262081522631277245264310,3827239308375083743454680749702278255317770699⟩
def resval2Tail188 : Box := ⟨763329542426645938025655560664352666896711793,6333281514812965756197609123835263335764008310⟩
def resval2Tail192 : Box := ⟨1751534081176172689925712167064673486284144946,10354971079362540137808289200520536299236549589⟩
def resval2Tail196 : Box := ⟨4019065773045819595053047436645792486769996233,16634097549555832942649213114476419985135248982⟩
def resval2Tail200 : Box := ⟨9222138388093233243140888508300434357259375582,26011246438802380604379005832277837758752904123⟩
def resval2Tail204 : Box := ⟨21161095949094160030031621364969446523495876143,38945503072548672655398065373685666307938199835⟩
def resval2Tail208 : Box := ⟨48556198456633245433881963061521035471475788179,53983005871834947037796358379459112655540663788⟩
def resval2Tail212 : Box := ⟨111416932958134783161765657720549371909193480259,63510422701074981348433955817563380600768393976⟩
def resval2Tail216 : Box := ⟨255657261879857014117709145869050021257874146849,42761247267582240702518658962616838415097080076⟩
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
def polyval2Tail5 : Box := ⟨20869689338401701258242782870656263974692746072950501,2945273920763896286029309531431847686040280861682691813⟩
def polyval2Tail9 : Box := ⟨44060958848816118429225859669731372559634883145923488,5013154878111547002151854545156766619296961987022802953⟩
def polyval2Tail13 : Box := ⟨101101858513152689866520820491205831780208106713298391,8526284853904420383614138021314966724651595440595101135⟩
def polyval2Tail17 : Box := ⟨231988074428283793335570577447222657870338376350299516,14485952772585170380548671768276525649150846681809094538⟩
def polyval2Tail21 : Box := ⟨532319262130710640660083198544641904537695913227911403,24575838051224541276249574011959954921449579247332750981⟩
def polyval2Tail25 : Box := ⟨1221458463043944095726202444686405724878647273457323477,41611949431792832272078868002055746661325964917462578113⟩
def polyval2Tail29 : Box := ⟨2802755569974717817390683822978624389793554640640512631,70269147277693518604189726508238957117284947611348564596⟩
def polyval2Tail33 : Box := ⟨6431196002726203793351933702083043605496341199777333705,118226244257185956287711791532088230924415261123895636579⟩
def polyval2Tail37 : Box := ⟨14757006450567714426839152600075852062197580494457645518,197903083222318669449264981840055616784562173547801345693⟩
def polyval2Tail41 : Box := ⟨33861390523595312932338700905663874864490987323668460250,328927333882961383591628581310517291925661135329988378500⟩
def polyval2Tail45 : Box := ⟨77698262993394574011391047007548790711731056864170411972,541203284349069494693301648458508269396257506950095913409⟩
def polyval2Tail49 : Box := ⟨178286242202132516459134867233163300155657697284108254243,877532474130534216324613574754345191738728478480157731126⟩
def polyval2Tail53 : Box := ⟨409095170650851041731491944292898386583988157740781948437,1392084946841278461640351849974481555178510688071356246604⟩
def polyval2Tail57 : Box := ⟨938708767332172336956165601941903836304835379432491152899,2134024994120456757276475802444446981095645625783455882180⟩
def polyval2Tail61 : Box := ⟨2153958817124095559101573839899389050434371080853790403126,3087989324029578276160360773784864202210831783243446500631⟩
def polyval2Tail65 : Box := ⟨4942468577398798390236037409604886097176742262093082309652,4000063528460237486759228098526687086892638431315764384686⟩
def polyval2Tail69 : Box := ⟨11340976192417056091614199686363332726039486908098988881640,3914588790702401665666405884427219812944597681154201672427⟩
def polyval2Tail73 : Box := ⟨26031250000000000000000000000000000000000000000000000000000,2⟩
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
def resval3 : Box := ⟨100742422890642113324460807580371080566635207680952134818,2462606272240001870782881817851654394490826747343431138⟩
def polyval3 : Box := ⟨3656028762810131863272968870329347299609017720114526944096,240875169983425899624704726766972308904192758523239047135⟩
theorem cell3_lo : Holds Q cell3 (7/8:ℝ) := by norm_num [Holds,Q,cell3]
theorem cell3_hi : Holds Q cell3 (15/16:ℝ) := by norm_num [Holds,Q,cell3]
def resval3Tail4 : Box := ⟨-210211290108015354418303351733491771831065456522226269,2156070909188834658040312529174402428087557653077297896⟩
def resval3Tail8 : Box := ⟨-311710784900672946958862564597788590884258220533761695,2751584961072613218472000521907295283217332094640570213⟩
def resval3Tail12 : Box := ⟨-462125311519680636067797622678240230431372275377553001,3503428274046525055950648822150640664460577280804482243⟩
def resval3Tail16 : Box := ⟨-685121628681415656435450613453347721993036530799443671,4448439255937965816080661922674536910865620957243778863⟩
def resval3Tail20 : Box := ⟨-1015723732033315132021936251382287549028921648830143770,5629867302720588576392002041053327410713093561409357319⟩
def resval3Tail24 : Box := ⟨-1505856269347777715285784725653825978320776867609458256,7097115662575814175031403490469335376083580444795588447⟩
def resval3Tail28 : Box := ⟨-2232499874148486060615630233925120177505575770555420036,8904376541269677263544851374612090533855920699066790513⟩
def resval3Tail32 : Box := ⟨-3309781809542632871233848220865039350440395200386962860,11107330936350596790408492057407266188335726179911260007⟩
def resval3Tail36 : Box := ⟨-4906900893312524732937180413437406389495821543375414885,13756603322289622409874662060134399780095820729529757505⟩
def resval3Tail40 : Box := ⟨-7274702008262732823828146570089212703392600302723365428,16885918481094349944535050148291308400314638519514945555⟩
def resval3Tail44 : Box := ⟨-10785074013038811071441921526250351612931362514956675635,20491773876156364756629303099879047370656454498965496340⟩
def resval3Tail48 : Box := ⟨-15989358922827255867655771140502358202638078111086399182,24499717684902028931843259740448118273961320445775286224⟩
def resval3Tail52 : Box := ⟨-23704946155576797101392090605314337270538507982224584269,28709713095073008461071654904345713708593666432823006821⟩
def resval3Tail56 : Box := ⟨-35143652409763720950580479678901704809186100429543834100,32709129983334264729732629597830618478931557224310116742⟩
def resval3Tail60 : Box := ⟨-52102050626582748361458674680297637151565615041801272882,35735973016163663362207003320813505511050045061955064102⟩
def resval3Tail64 : Box := ⟨-77243641264733316619747548847522789050197071925293044924,36466042042092276770282931081974102684244953073807199668⟩
def resval3Tail68 : Box := ⟨-114517173257175855165483555833806255116708432786181459626,32684350348132768743195999144993427358108394046280583194⟩
def resval3Tail72 : Box := ⟨702656499073905149674369926808950565660863578128738635603,2761769158308516480037677319346815348354990921938856419⟩
def resval3Tail76 : Box := ⟨-2490820563986256548040002233773198986076011679263492,26313088004727577941866544981135656610397333175060006⟩
def resval3Tail80 : Box := ⟨-3663469439482659841565845955194044609856140532178389,33598049375160087033984463679183103649711798911932447⟩
def resval3Tail84 : Box := ⟨-5431257456577133348114009095479484536753782038584273,42805203510878264458359398042207900752392160768466437⟩
def resval3Tail88 : Box := ⟨-8052084275351257672338255371097539596793324737793825,54391860533223098199701137289466312199417723878643406⟩
def resval3Tail92 : Box := ⟨-11937578304959038628774497653185085340129937100961405,68898498079725611710844254851283369191181193452397277⟩
def resval3Tail96 : Box := ⟨-17697998544709557975877159308943908111759729973932457,86947396061644864943248843393178230666002436935357394⟩
def resval3Tail100 : Box := ⟨-26238081500870756136980854979389481698918879002649080,109229386764256027968335288834544533551419236715877213⟩
def resval3Tail104 : Box := ⟨-38899139872069310465143573576846782579944218600399314,136468682354564742316490629899892614788881859614266674⟩
def resval3Tail108 : Box := ⟨-57669730263494918269598912543179548169819037539052391,169350627216894005837325597706175059880457295401034668⟩
def resval3Tail112 : Box := ⟨-85497977580020454980630267516394124219608542626018749,208388563611777441912169289733551285425973623108618303⟩
def resval3Tail116 : Box := ⟨-126754610033278892833836496894087570328554142962853111,253692765049104652266660347942800777196131377030435259⟩
def resval3Tail120 : Box := ⟨-187919429435055442376850638182237503773158223746077689,304584257940729012176267721731528210913609125579105892⟩
def resval3Tail124 : Box := ⟨-278599034385615753424465528323849134856463599106279833,358965837828891111119936066474602269341241255909511779⟩
def resval3Tail128 : Box := ⟨-413035640827240421166703080200747870518211034598459191,412316486885350633791502114768224352436492963723568938⟩
def resval3Tail132 : Box := ⟨-612343976603451673841879403447687670532461614476052100,456105940271065375109490860120042021518405907839216392⟩
def resval3Tail136 : Box := ⟨-907827578589248912569066586345264138263937055820993095,475321730099004229217617932970639280094784594279161975⟩
def resval3Tail140 : Box := ⟨-1345895366486744679732742770786157614693489914998676038,444644358199512758733086203434796554985509566669492346⟩
def resval3Tail144 : Box := ⟨-2004245853394961151269230996451002446661807619379393497,320306683017381420385698516632626538430615045575261485⟩
def resval3Tail148 : Box := ⟨435289315035132808893153983367630008956146442,3862180930049435868422726161439551929307950322⟩
def resval3Tail152 : Box := ⟨584230234003175086005680471443023585631655404,4924320569421737269463591748572491620993145700⟩
def resval3Tail156 : Box := ⟨866146787565317835363149924194298860907391106,6264882231302209447138778118086977281440577922⟩
def resval3Tail160 : Box := ⟨1284101698972321114939592535571510820902999105,7947288281656820859776400944585727868672102309⟩
def resval3Tail164 : Box := ⟨1903738716438528502038964787742629878491859250,10046648913595937039983718036614868032558111777⟩
def resval3Tail168 : Box := ⟨2822378557218764735141965008773653978972591139,12647855590375084920797595797277213532340015993⟩
def resval3Tail172 : Box := ⟨4184303576674933200098822956506796627468310690,15842506598074904416784128927629993295582983752⟩
def resval3Tail176 : Box := ⟨6203418877667426036088276965975402294246748016,19722053351713420541220288544872480495628853939⟩
def resval3Tail180 : Box := ⟨9196848428091520800237040034506071476388354282,24364667582272986089244540846890462218032554478⟩
def resval3Tail184 : Box := ⟨13634742821218857165128358385177930343470648593,29811924107279875151039022980888337908291299153⟩
def resval3Tail188 : Box := ⟨20214121528080613463086852398613319483013558397,36029251584533567693860151511956269189601484600⟩
def resval3Tail192 : Box := ⟨29968347368908054002232755861527008879105903772,42840851649527165282713402270117539072762229581⟩
def resval3Tail196 : Box := ⟨44429427357302305073432333264602758626371297274,49824867296962791836792779256355610792491420987⟩
def resval3Tail200 : Box := ⟨65868631025873198748811652378963283014962136590,56147160667201712704544831277083103187696040991⟩
def resval3Tail204 : Box := ⟨97653217952392357746158484429073377498876023677,60300894134469025828633410186978987254079474663⟩
def resval3Tail208 : Box := ⟨144775302415375635959258214781660464138614859115,59702340838443833037820434357014214052827220048⟩
def resval3Tail212 : Box := ⟨214635919117267323282929599012303584054627594559,50068215765690243727623013566343542056295722712⟩
def resval3Tail216 : Box := ⟨318207654995566716505836797239622965948066989912,24462131474963312924017377847514871427987361669⟩
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
def polyval3Tail5 : Box := ⟨32229878662945846550785086882735347310483074646363351010,290955402296618430576131248652474413590130435148835651713⟩
def polyval3Tail9 : Box := ⟨47779792827613174329323191034016080239915495016569260875,370593734708234755345396115183745291893485871613990872445⟩
def polyval3Tail13 : Box := ⟨70835698830482461508793585490447148491034786307642697168,470764844211576043880636045698288412170381897111789222720⟩
def polyval3Tail17 : Box := ⟨105017120121678893254192598654899169800891966253545248436,596105510768163535871683933600917894420145294571955496062⟩
def polyval3Tail21 : Box := ⟨155692619692469195295445200497225644673140108814435426045,751937459082774168057538831801121643086448684995146825397⟩
def polyval3Tail25 : Box := ⟨230821334641607192005253298294918151612973439336037276069,944140538792750316629837745998060952797119945942478666349⟩
def polyval3Tail29 : Box := ⟨342203044890443689131994429227375622163082090258908947328,1178830067946969716899429391779412926744059543530516833789⟩
def polyval3Tail33 : Box := ⟨507331456661555848057990341877921908446650058272987256704,1461704120284868349023218423940718247598344336530180506672⟩
def polyval3Tail37 : Box := ⟨752141778869144774046680374509812266495848053689690545460,1796850133639711644320325181458616786160190030725048112809⟩
def polyval3Tail41 : Box := ⟨1115084129107797820937706925383610688510409329987274755861,2184683455646383200969727967932457698368369268932374182803⟩
def polyval3Tail45 : Box := ⟨1653162541851595345962914359583633904630030271029415842969,2618512884014083813576817903541405929530983557354020963114⟩
def polyval3Tail49 : Box := ⟨2450888070631868297739251646377173772688239328124546136828,3078959252025576628673417255170333859849295805348244679298⟩
def polyval3Tail53 : Box := ⟨3633552166042749532749542255609308352541670395860909834476,3525046829269414629229487659312104122474421062175941169250⟩
def polyval3Tail57 : Box := ⟨5386905057622701782946862653665771393738627402930552863384,3880175312881554823926391377763194789910136159151678985150⟩
def polyval3Tail61 : Box := ⟨7986329843021066898854370346894509897877215124905634691058,4010260362635565288276071876855178213043479736993601450379⟩
def polyval3Tail65 : Box := ⟨11840094391729192377715054422967673219359163247560626664446,3689950758255111083788639598655917221213722704148574918313⟩
def polyval3Tail69 : Box := ⟨17553474255060725673790386977894297212447098934649393964417,2550763558764582863179112775550669997871162316935092182541⟩
def polyval3Tail73 : Box := ⟨26031250000000000000000000000000000000000000000000000000000,2⟩
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
def resval4 : Box := ⟨96867181313784932034244867963515722595685789447550975523,10903181309223190324852888652014912352628093081616835499⟩
def polyval4 : Box := ⟨4452888684975207728682800225299001380810915936196215915721,1838047913212630306237217231211295554477115955918774809291⟩
theorem cell4_lo : Holds Q cell4 (15/16:ℝ) := by norm_num [Holds,Q,cell4]
theorem cell4_hi : Holds Q cell4 (31/32:ℝ) := by norm_num [Holds,Q,cell4]
def resval4Tail4 : Box := ⟨-4838940792000770530354149532459112792728593372461415269,11201398869883657882491067268385054898380082145358291217⟩
def resval4Tail8 : Box := ⟨-5863469477358130702715437000916911569489811978366342526,12348956581854236788942761718751084524082261547855954943⟩
def resval4Tail12 : Box := ⟨-7104855097074092907147431257572569244466608407081040844,13573735721786117469564084529829624162548098129458790958⟩
def resval4Tail16 : Box := ⟨-8609060916730613601753002220003165404166683341408526437,14869640754893714512195055703316734504738590673931667932⟩
def resval4Tail20 : Box := ⟨-10431729972715105781335796910691445118291853473418369206,16226248659092033225396218792520630106651122741674752746⟩
def resval4Tail24 : Box := ⟨-12640285772884105637139627235807950308079721390579000133,17627479228481107157566778692023945257069624165742357012⟩
def resval4Tail28 : Box := ⟨-15316426406558011413029557292146335407874976705230674193,19049930128996165886570696185454587307507840389561758884⟩
def resval4Tail32 : Box := ⟨-18559146690398046172236333891124004310407784345727325780,20460796191924344998320967384088032780361702157799036641⟩
def resval4Tail36 : Box := ⟨-22488400148498971395833962169390045351342354323729533910,21815276354551943141076931163812569448034005926795051927⟩
def resval4Tail40 : Box := ⟨-27249536289330443624601470134962518159077712110966919276,23053350047702624125239784570554211140192115503764828329⟩
def resval4Tail44 : Box := ⟨-33018677321654592744816474564232999304905523470431723161,24095778487948855415705888888856366895796551023924530670⟩
def resval4Tail48 : Box := ⟨-40009233202930799209500676520664397015645489482008024714,24839154234940938690017183357850475149481698665447760333⟩
def resval4Tail52 : Box := ⟨-48479796022498153130999912299995676511418868781092968693,25149783278951186303566596632981388463268821706166978002⟩
def resval4Tail56 : Box := ⟨-58743705745674267851525995746652284370040155051171471823,24856136321367564664190242801247639006289553196801617107⟩
def resval4Tail60 : Box := ⟨-71180641171281111678295868193486722580594117288487986220,23739547969290550276842190322415132882451534727103271359⟩
def resval4Tail64 : Box := ⟨-86250664870447341123928327592920834874282995892640165223,21522772060065400925971881548090628459671082208335208678⟩
def resval4Tail68 : Box := ⟨-104511231453730494313406721834875866428558197809416730572,17855912894011303242263556824825983356334795537089723959⟩
def resval4Tail72 : Box := ⟨702912051426411688777285154572429293518669431877133685150,2767713159378970238054428220268262972583569817743322741⟩
def resval4Tail76 : Box := ⟨-59800555679980672539452316322432517732565244562226078,141585992318237995462977591401121003566893254343345613⟩
def resval4Tail80 : Box := ⟨-72437369953504098900880243076926237109739972595995037,156196173331390683784062242988577400659132322314005431⟩
def resval4Tail84 : Box := ⟨-87773461174759967746331450197623036185486934811765632,171819602023053560948600807753193150873923305165558104⟩
def resval4Tail88 : Box := ⟨-106356437083864116723794223649780598537549139285981445,188388409904181853521672028451456100084547233607480796⟩
def resval4Tail92 : Box := ⟨-128873711459374897607823197907137847573048692098307497,205782861239390154998990018336083147510164903060039365⟩
def resval4Tail96 : Box := ⟨-156158235088472253579710568401336457923377050953371232,223814554240823186928777338726613147877899486117013109⟩
def resval4Tail100 : Box := ⟨-189219307101538874042148135451087313568392258922425517,242206017870773932691152615584292633214417814296809947⟩
def resval4Tail104 : Box := ⟨-229279910596463705022956212674137591966739062231384358,260565194775442157016450910198875123861847825807734899⟩
def resval4Tail108 : Box := ⟨-277821952782612512689309420134229485307426570028501700,278353620063539942090767529930735930605925649683988731⟩
def resval4Tail112 : Box := ⟨-336641083150939778211285324270892660600041071862809269,294846839129904031969917528130423244493904093769625992⟩
def resval4Tail116 : Box := ⟨-407913117483963398254993386388724301589661855898724734,309085282762006188905268689725830043269179650088034515⟩
def resval4Tail120 : Box := ⟨-494274524838312852846609292604691690438174720787193443,319813421766385693074577104393945301478552180241945917⟩
def resval4Tail124 : Box := ⟨-598919954844905398719432339146730411887390011305848508,325404540969448993400123828687277344903331291573968550⟩
def resval4Tail128 : Box := ⟨-725720413021009307181321209208469178173328665540727412,323767885050212111994053543254511996889233128907876156⟩
def resval4Tail132 : Box := ⟨-879366455592167570059774204038084338400744055962253242,312234213627406343728625616798586192663916157539415877⟩
def resval4Tail136 : Box := ⟨-1065541700836192337335565582311664965115739743789821703,287414932882538966050817842121545242260894536234808979⟩
def resval4Tail140 : Box := ⟨-1291133088442931818521414610931283187702944802456778383,245028908375113066409846835985023192134112254469489387⟩
def resval4Tail144 : Box := ⟨-1572950432929586786720268011344876092835077688336350304,177647023892940467666095570658667374602019421610929055⟩
def resval4Tail148 : Box := ⟨13493618030501458911939781986862426115265779782,28797324255253121329593178124937923176101813713⟩
def resval4Tail152 : Box := ⟨16300565839303241352739359687790702903002534950,31669125676190978824529422584295825253390364955⟩
def resval4Tail156 : Box := ⟨19751642668787232232766898950558713474872054985,34713677113158452261170075749966348152494426108⟩
def resval4Tail160 : Box := ⟨23933365651562988111032249629033291789315080141,37907163319078431625811704137396240883377791993⟩
def resval4Tail164 : Box := ⟨29000422953235499401532110791214383321460436734,41214000439323015857698767099734198943064394645⟩
def resval4Tail168 : Box := ⟨35140253306230358378006736092274357611955391846,44581982813224896225605283268259118192455787899⟩
def resval4Tail172 : Box := ⟨42579979071935093571945468993782703750064216429,47937533211157454431068056528980268673578399261⟩
def resval4Tail176 : Box := ⟨51594807867960826852003406670651717394113564077,51179780863379393471607060513007497766551505165⟩
def resval4Tail180 : Box := ⟨62518212947792645577332976715268602068060686401,54173196509657485893294253508417373014299369104⟩
def resval4Tail184 : Box := ⟨75754268921556584252419709768188163733089620612,56738453348164655499460932028287283390473949457⟩
def resval4Tail188 : Box := ⟨91792599136379066481061853852737436550859334046,58641109189360379285780518672588615093304824524⟩
def resval4Tail192 : Box := ⟨111226487644372418853638261759374137257198087190,59577615501490604385034349459849130666297161872⟩
def resval4Tail196 : Box := ⟨134774825749549431888846087689111864598120546944,59158049908152412959266526855103826407167430722⟩
def resval4Tail200 : Box := ⟨163308704972312821029144442125587208386857290786,56884835862871619483008937294735951687949161582⟩
def resval4Tail204 : Box := ⟨197883640148746926398321417831171172373750513171,52126551579209841834204942641634786221221012396⟩
def resval4Tail208 : Box := ⟨239778614649830803925374182382838393996989870501,44085733644723543807730817915944649470168693949⟩
def resval4Tail212 : Box := ⟨290543392072013959702279713748739400707747980176,31759341574854630766118167423338029016749481287⟩
def resval4Tail216 : Box := ⟨352056053256439345801472088882071171737248566861,13890198700361444725910822019810210847424446096⟩
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
def polyval4Tail5 : Box := ⟨994416411435082814643174227173485439467551687937791914196,2010291874899486350051273530316257481590902046561213233443⟩
def polyval4Tail9 : Box := ⟨1204947479503222995992143301112996304642963762039676038115,2206629764221798747475390610802545218860981286820167272378⟩
def polyval4Tail13 : Box := ⟨1460053176261524156019834839774124116006047175775501846935,2413489514994369578628281468953546866026642406136099376230⟩
def polyval4Tail17 : Box := ⟨1769168626855112842840013535147650137351411089489526916252,2628894764260241652195764736124176900978211717915794257145⟩
def polyval4Tail21 : Box := ⟨2143728516972831388290340173095229716922571701812096010984,2849881502076192581925405608307740028076234054634592801361⟩
def polyval4Tail25 : Box := ⟨2597588429233938067951687006999442198085164381678462068472,3072211845296201859172013513855190405382247371376972658129⟩
def polyval4Tail29 : Box := ⟨3147537383706666391412459155503289311691214474004949672890,3290016816647972002446901777389949999092299978941972101987⟩
def polyval4Tail33 : Box := ⟨3813918891205064588607642663341432530548621098523861464901,3495351643185669686490100467137290319173943846351373884186⟩
def polyval4Tail37 : Box := ⟨4621383493009046463628393863742101764092828421513585395740,3677643448305009830969750683872952121528262143782213579996⟩
def polyval4Tail41 : Box := ⟨5599800624681972187484236307934936300860327737757798361276,3823006733261515717137311301703764681663389229973823650304⟩
def polyval4Tail45 : Box := ⟨6785363535318972585011292593070278451419489803923877532968,3913396588341399808335577208100144462562278549580724110095⟩
def polyval4Tail49 : Box := ⟨8221928134995196893920039853912554308694506567017060051286,3925562929558071134340631767290477071303838189435087108953⟩
def polyval4Tail53 : Box := ⟨9962635296569675850950066084705268488740513346413589874645,3829760967841212018470763147116006389128648015852326524471⟩
def polyval4Tail57 : Box := ⟨12071876623440462078777547130745413668533184620037771957736,3588163273162767476691074985896744150942418968793011391902⟩
def polyval4Tail61 : Box := ⟨14627676400213704290812073951861286613951503475827027523721,3152906818381897560974041455151054758811950891524494914144⟩
def polyval4Tail65 : Box := ⟨17724577838536908031425610993641377401353210183200560762341,2463693818548157902993675034956087833879459558907510827075⟩
def polyval4Tail69 : Box := ⟨21477140395422208011167735770524512208920661586751880081852,1444847461662329227292317506358158957832061062934630994983⟩
def polyval4Tail73 : Box := ⟨26031250000000000000000000000000000000000000000000000000000,2⟩
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
def resval5 : Box := ⟨81488968164653805917978458227131951921800312511330897861,18266853807945037354475687119815303748343069180859001094⟩
def polyval5 : Box := ⟨8349460036708582015486443855606277028187154052404803739440,3669113743247237855294786287642519551224574947778227518662⟩
theorem cell5_lo : Holds Q cell5 (31/32:ℝ) := by norm_num [Holds,Q,cell5]
theorem cell5_hi : Holds Q cell5 (63/64:ℝ) := by norm_num [Holds,Q,cell5]
def resval5Tail4 : Box := ⟨-21286451317355905008191206468851334434949538942470180184,17971297783585651142508347626650814632511004126782667744⟩
def resval5Tail8 : Box := ⟨-23404747268803061628083769174027491751000963744804087246,18405577730048567532077865435471637404398315514157922962⟩
def resval5Tail12 : Box := ⟨-25733791771852372308129791693725161230169521019816693858,18795033863045151649817915451712627728313235703395573280⟩
def resval5Tail16 : Box := ⟨-28294603279921514463609636578113314620537787216528390056,19129479462558507885135891154068689006725687228443910522⟩
def resval5Tail20 : Box := ⟨-31110245309582664326048578746777972582422253466726574428,19397343693682173267434348607971099374924673487731275070⟩
def resval5Tail24 : Box := ⟨-34206076460849904429205636606730561368353706909605558715,19585507886181671856875195330516898748948333194380903484⟩
def resval5Tail28 : Box := ⟨-37609978809299395559233966326858364162090424720797751813,19679125732530404832635044274923360651069840246954528448⟩
def resval5Tail32 : Box := ⟨-41352609021233644697757234837604970700322361362296064731,19661423918025177590511644395599882165124344101973320932⟩
def resval5Tail36 : Box := ⟨-45467674457721106829289157556419819347452617566785537296,19513481126493196845784316591810553603230256291669184210⟩
def resval5Tail40 : Box := ⟨-49992236754198192261297665987029999214008272949509407900,19213983153663546433120491400328866454084790470936879174⟩
def resval5Tail44 : Box := ⟨-54967045609771629174839647444768502999641855479040145719,18738951627046038831090438974022004879637796872341329204⟩
def resval5Tail48 : Box := ⟨-60436905792437638484629088774297057203841711163533455413,18061443574230200579005251591992013122899974821760217089⟩
def resval5Tail52 : Box := ⟨-66451080665587871056580778035126357196711590195164911468,17151218798496978491540309744823693748537445462605288186⟩
def resval5Tail56 : Box := ⟨-73063735870094799893510469506548412387658212169289015336,15974371708895316559580807723369150297056226253046913533⟩
def resval5Tail60 : Box := ⟨-80334427157923212613417800362554784168322592367043018045,14492923908580702975028365516386126425671334915336699572⟩
def resval5Tail64 : Box := ⟨-88328636770254238965667861760141770968413478097176301054,12664373466856023823636429527564433536325849954841091267⟩
def resval5Tail68 : Box := ⟨-97118353222567301466455374847449644565635251522605820210,10441193683173510894007759092243703614126189728963131828⟩
def resval5Tail72 : Box := ⟨702868408505929978410318365702752152732470594339855533382,2811726794003966406052265877206340276449956283415586813⟩
def resval5Tail76 : Box := ⟨-268925528751807783200193041613047274347749078449340567,230471909703802036604032621933676465733604548429197703⟩
def resval5Tail80 : Box := ⟨-295665112278775234026712450823361793895236423384189895,236181529861233927350442782125941235368307332425845379⟩
def resval5Tail84 : Box := ⟨-325087227914942144837700325191688756092374164029102094,241339996695415465759300393385480057146222982902923955⟩
def resval5Tail88 : Box := ⟨-357437187133496717525694366507546507361538111766259416,245819044857497739867212726374557440937742380069982204⟩
def resval5Tail92 : Box := ⟨-393006343452824682076212405635028682162762149668466005,249473512077764561097268526239470794814007691939906972⟩
def resval5Tail96 : Box := ⟨-432115044416108978254330054579143190483867432959650924,252138748371512992743789478375885803283218159045726920⟩
def resval5Tail100 : Box := ⟨-475115515872454521962170180551455311981280253110902062,253628348878888157675398199193360343571390908960951680⟩
def resval5Tail104 : Box := ⟨-522395034238556436231453117303843580097010205390258053,253731639826596294485845324909152633761059321759182618⟩
def resval5Tail108 : Box := ⟨-574379414437734439899825797730460934493610760831273948,252210891610294590083069417667164679145604529899326992⟩
def resval5Tail112 : Box := ⟨-631536844929459109811788198367813956882100078640806855,248798230366790872034549879670141038165343223787664689⟩
def resval5Tail116 : Box := ⟨-694382104368908877725592609945664793965316257322963719,243192216460137162280567089307532440290078757853969644⟩
def resval5Tail120 : Box := ⟨-763481197873183321364171591106567452477620372754396925,235054055061309723286868111204906892205710622977315185⟩
def resval5Tail124 : Box := ⟨-839456454649914143101371818811782305473407278674688216,224003400427275704696136822624707966205650781648260719⟩
def resval5Tail128 : Box := ⟨-922992132899197034567804152949601783355794039776126844,209613711548631588772482407877317125052483284835819762⟩
def resval5Tail132 : Box := ⟨-1014840582468440190977832915886981091153219946118085964,191407112499105233456192133374335063517847425227459536⟩
def resval5Tail136 : Box := ⟨-1115829020764665538164710995827942884232813556781663223,168848706044220465763845932204463071836313919585478932⟩
def resval5Tail140 : Box := ⟨-1226866995686997062809270120119118104290441444701454971,141340279936691467802497263559723782492536936322787119⟩
def resval5Tail144 : Box := ⟨-1357219428289463750240268692177735321327723596831693347,106271224168524628078045283020866462394030331787990127⟩
def resval5Tail148 : Box := ⟨73723345071364354722233322117337094637169754855,55817119937226642752547045325577873221167941354⟩
def resval5Tail152 : Box := ⟨81014474800969474365344929345230122476733953293,56903771450655625151347475298757792523859113836⟩
def resval5Tail156 : Box := ⟨89076356399600625116927332005054357280951298641,57809311453914847631826553843047236480638868483⟩
def resval5Tail160 : Box := ⟨97940489621106454916723884152087819265669440159,58495660819426408475845816906975603739664220514⟩
def resval5Tail164 : Box := ⟨107686707168480942056354028768459711656275154669,58920896706708666954010393087150993508373091850⟩
def resval5Tail168 : Box := ⟨118402786688653927124828165264832097168968720610,59037616893662634646696417154123236718218037802⟩
def resval5Tail172 : Box := ⟨130185240725256384300802292537397482610382314347,58792309465320405471528637882766234784994944741⟩
def resval5Tail176 : Box := ⟨143140185942237053896523325250303231133960813418,58124654280381917011604420818047323532396229628⟩
def resval5Tail180 : Box := ⟨157384298845508375440531276718640807497110631527,56966749038147691544003123788322611891333068684⟩
def resval5Tail184 : Box := ⟨173045866610009351426845780186059373582387703284,55242252059899163265042949580033511385363925034⟩
def resval5Tail188 : Box := ⟨190265942476279948961927972256674132487387191605,52865433089157421905972008822315007105824043176⟩
def resval5Tail192 : Box := ⟨209199616122429346952328351604334931495988593408,49740122523433161405483651237717214623869032210⟩
def resval5Tail196 : Box := ⟨230017410452886624572784781802229695919405841982,45758548507792755578609952948189553165338552202⟩
def resval5Tail200 : Box := ⟨252906817383873689995760065325483348225997052113,40800050238692852760126709513541483404345412308⟩
def resval5Tail204 : Box := ⟨278073986457390540002932163685488826577609467785,34729654635049503963458352913183030883957394490⟩
def resval5Tail208 : Box := ⟨305745581491928882323091852272130067154845625116,27396502221371854423900864035949831796226924693⟩
def resval5Tail212 : Box := ⟨336170821996372122231952156310833939156283279282,18632106621195506892458103475191909716460899649⟩
def resval5Tail216 : Box := ⟨369623931671329019990316196338224562303933192152,8248373036678318715724481536594949732255894178⟩
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
def polyval5Tail5 : Box := ⟨5187795968917196642921697120125400720429332801340745201259,3731406379345810671770425780967249600334272311182063003957⟩
def polyval5Tail9 : Box := ⟨5704040176940021124222814889651050874745634605924522515401,3795085484510752690944565668723121474494130035532441603111⟩
def polyval5Tail13 : Box := ⟨6271658499702005863322419496063339564843825751178984935921,3845098789990287455335860226102738744490954783959443328303⟩
def polyval5Tail17 : Box := ⟨6895761445862444448765458596691115658728056448190066503161,3878785781718493152180866139777519232314441208389404816736⟩
def polyval5Tail21 : Box := ⟨7581969892095199325913080662583104363060475288139670266882,3893136669733179669183436790796837862752144010455285281967⟩
def polyval5Tail25 : Box := ⟨8336464057806215683377070236984477743360654705272823692438,3884752093926278879611699618543162916928183860055758606157⟩
def polyval5Tail29 : Box := ⟨9166039166094630365528916945337137341311115279138823162934,3849798501522577313756429703856270608287309055566191079424⟩
def polyval5Tail33 : Box := ⟨10078166643771276662050921358421660780719355247298631318896,3783958703365055266411219835831316702466119221541470672153⟩
def polyval5Tail37 : Box := ⟨11081061411490743134124606247664758211635163581347839130753,3682377104479760583334294309597207420319842554486420313854⟩
def polyval5Tail41 : Box := ⟨12183755870034007134157236027891638079928696420085762998577,3539599052583816302122613010469779519018342614026573107121⟩
def polyval5Tail45 : Box := ⟨13396181249086486284553972528744142620728081017409439168784,3349503691123961087233740187718879680407711698984090174676⟩
def polyval5Tail49 : Box := ⟨14729257051165411447741343923329178795723638128414048661982,3105229640565607312042221941625427856121901944601709469530⟩
def polyval5Tail53 : Box := ⟨16194989396258007258875638580564908868434112096033546885522,2799092762410240293688004841619544065556092734466398573566⟩
def polyval5Tail57 : Box := ⟨17806579152894701052150535466152279524206320137425378900760,2422495184159993718853819859821081463930933762190237282759⟩
def polyval5Tail61 : Box := ⟨19578540829521441367438906499331276210421748132470751964812,1965824679465944004950638974074142036778696879783339541042⟩
def polyval5Tail65 : Box := ⟨21526833296947266109952726199331580020340583339465063163275,1418343405213302461435564024680592007610190202235559482141⟩
def polyval5Tail69 : Box := ⟨23669003529340781728497535112364122893633540068522160189290,768064892426459552071783224476533037495572055215716517259⟩
def polyval5Tail73 : Box := ⟨26031250000000000000000000000000000000000000000000000000000,2⟩
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
def resval6 : Box := ⟨59160920152370344789944413417272268953663973894407638259,17516082749703640838712087144920631180316744331483571668⟩
def polyval6 : Box := ⟨14768004471199336955143297405423010009620113051027184001788,3671999121708745665123639666681542501552777872732929803819⟩
theorem cell6_lo : Holds Q cell6 (63/64:ℝ) := by norm_num [Holds,Q,cell6]
theorem cell6_hi : Holds Q cell6 (127/128:ℝ) := by norm_num [Holds,Q,cell6]
def resval6Tail4 : Box := ⟨-43694546166135491770288467994606119066709668178573903100,16601994658540973743622104192163323167546628512580305284⟩
def resval6Tail8 : Box := ⟨-45804213438095953622925353265992595998304809287392855781,16414021336139873747823291897046747841586793628939294465⟩
def resval6Tail12 : Box := ⟨-48015693551147705300941103882311601346424121825157275664,16185437634938729139147580207374704450693553842783309428⟩
def resval6Tail16 : Box := ⟨-50333946463275316133114914339076339001837001694300740610,15913276079562683288847817079102686497019406619802898048⟩
def resval6Tail20 : Box := ⟨-52764127292443160874908026068452436396279389748200085867,15594395580300545885808296707352162995920630551311813407⟩
def resval6Tail24 : Box := ⟨-55311640047228308970834184263178659441693929870355847435,15225470339878942334006265261146454694846271985605869606⟩
def resval6Tail28 : Box := ⟨-57982149647954325591481561799649768840467505645856614336,14802979881911605898284756562605504248347148062846053851⟩
def resval6Tail32 : Box := ⟨-60781594523813757773534645284721072636381472416592719801,14323198564615178720864276989811813576108507661909709839⟩
def resval6Tail36 : Box := ⟨-63716199818190928127363520289916436747904738754172695538,13782184553594266138712246631349801471617451060264669792⟩
def resval6Tail40 : Box := ⟨-66792491231552891480495396666724621567975685657720745887,13175768226474660802801631423012566053949696135484792483⟩
def resval6Tail44 : Box := ⟨-70017309532691088847712935768749556280402431788139120458,12499539980814510745530263381989174849932774784746883306⟩
def resval6Tail48 : Box := ⟨-73397825770582439228564867465680008847277174672257748182,11748837415307497227612631555740078241714905714071673019⟩
def resval6Tail52 : Box := ⟨-76941557220696581523430822441461690823209879589559085058,10918731852806869383960777012575251187517059097236622455⟩
def resval6Tail56 : Box := ⟨-80656384101209169880962359732829703838383515725756971039,10004014172141061144018868351948326984576770099495889714⟩
def resval6Tail60 : Box := ⟨-84550567096292745873472507911588932783977153525163015238,8999179914056868139388479851339933607158775143716246633⟩
def resval6Tail64 : Box := ⟨-88632765724854312422648849965914439664154966570855359815,7898413624708261224823226379812439163760005746511888574⟩
def resval6Tail68 : Box := ⟨-92912047738296490071769106863820119327130704519487727918,6695569683231375599007192058426505233134389416136053554⟩
def resval6Tail72 : Box := ⟨702657601710513417493158769872335427521983997102989073950,2777789371957308785594433416038728452898032695849993332⟩
def resval6Tail76 : Box := ⟨-556829860373112368783929351858724832842816090636214093,213824674617077486301608204801303613175247861480827761⟩
def resval6Tail80 : Box := ⟨-583693634312279874131043402893508620152581439630398450,211500817487007297720728055271050431569874340103494347⟩
def resval6Tail84 : Box := ⟨-611875033421959765428544102230382363640161408721308356,208662280781948813783663090971423806621183918568480310⟩
def resval6Tail88 : Box := ⟨-641417063811567694162974278629171063407995584311152774,205270791285256084484261529583042767588957625201711097⟩
def resval6Tail92 : Box := ⟨-672385417407947174169963717274414352097466336204101559,201286396852403232035951166409618269570905487519930574⟩
def resval6Tail96 : Box := ⟨-704848958735647716772232487841231310421861755083333251,196666794015624455863723080622030811873310117852442461⟩
def resval6Tail100 : Box := ⟨-738879877178096004427855304335256371663944823564967210,191367200950148044930579910256282610055210180451445215⟩
def resval6Tail104 : Box := ⟨-774553847505183468565707307571938057870216177587845046,185340223924190384515468611562080794510902051633104204⟩
def resval6Tail108 : Box := ⟨-811950198151732749400972237502379863502658363445676102,178535716858296390678825643439225644616806880853705695⟩
def resval6Tail112 : Box := ⟨-851152087620642999609751593505580573472814591743828928,170900633647193598993612703846917647109609642183503121⟩
def resval6Tail116 : Box := ⟨-892246689402981948480006955686467776265999208892071654,162378872880165815764816551851932284895545880206774367⟩
def resval6Tail120 : Box := ⟨-935325385826232705479482301603620072987007076227653661,152911114577914275241881969371499279658253072580816444⟩
def resval6Tail124 : Box := ⟨-980483971261756883213346984912506059349937744650064513,142434648544950490333387082804336838412640262275321194⟩
def resval6Tail128 : Box := ⟨-1027822865143347778278778631196711611228557314060422942,130883193916712302458118651585809267815263300116145792⟩
def resval6Tail132 : Box := ⟨-1077447335270566180313388130004626709793504528018754496,118186709459766942494815733285587214727802491196388149⟩
def resval6Tail136 : Box := ⟨-1129467731895038664377385197395421388634176460957502702,104271194161027900288657070745828236917269056102273362⟩
def resval6Tail140 : Box := ⟨-1183999745707229097729555521065304894977388741364468932,89058473828621966154954427925444198931939178395917569⟩
def resval6Tail144 : Box := ⟨-1249333045893903702052512067570005962815594532670421994,70571813529841599840869518662768247348470951516256982⟩
def resval6Tail148 : Box := ⟨169874228418736929409450922565324847620315967210,55385002655225635997987138582028477584135959498⟩
def resval6Tail152 : Box := ⟨178032875949965019105157605197648094041520854699,54361862374909220436710009250969781228521480365⟩
def resval6Tail156 : Box := ⟨186628507342917597801997968711838060336785887824,53172655370870521394857968457109247379445417545⟩
def resval6Tail160 : Box := ⟨195639146336694212187134537949422016692663645669,51804484310152516357079025196008186456398604805⟩
def resval6Tail164 : Box := ⟨205084829345259266993190388333864671381944463409,50244834843294242390717571982915495120146643555⟩
def resval6Tail168 : Box := ⟨214986560793868085634264540424302155554479927647,48480464985768216338036233265245030638821107991⟩
def resval6Tail172 : Box := ⟨225366359225750991850891165728171176158885762413,46497366024389472227436018706622875245475969020⟩
def resval6Tail176 : Box := ⟨236247306264731350848608909188664334288320481965,44280721438826722979175398806143375373777439115⟩
def resval6Tail180 : Box := ⟨247653597941979120330413683296444531725814144369,41814863710418494773259581416897290684133949787⟩
def resval6Tail184 : Box := ⟨259610598500879330023074477328462223231237664927,39083228912155356721270557863307402716575546492⟩
def resval6Tail188 : Box := ⟨272144896799661498748149826444679069623382040128,36068308968445277205112161650556064740439004042⟩
def resval6Tail192 : Box := ⟨285284365437212873864562003424276356045756217340,32751601467765855486634464348544590712010227810⟩
def resval6Tail196 : Box := ⟨299058222733553940207112817401594694005712609697,29113556905523360192971560288614386573128606194⟩
def resval6Tail200 : Box := ⟨313497097702802576358708610807305352670539288638,25133523228370980119250562121587889595746278660⟩
def resval6Tail204 : Box := ⟨328633098163107657018847240036615506943150896074,20789687544873615578024321524067938407726777787⟩
def resval6Tail208 : Box := ⟨344499882135010574044530829943986840418730442964,16059014860728614950137416848147014716314354144⟩
def resval6Tail212 : Box := ⟨361132732691801932428075753924467431390962473840,10917183688110104322010375472260940328040560000⟩
def resval6Tail216 : Box := ⟨378568838057224561346949064868238436294183032498,5338462191140071378608160183668522524307959681⟩
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
def polyval6Tail5 : Box := ⟨11675056916977573644074953339435441944403524328742081874696,3592959460675238478485322548811481639856959055011638194553⟩
def polyval6Tail9 : Box := ⟨12238740365973720407628310433459461378247288470313037105499,3515866266591996393274385876187698174444084857508741553879⟩
def polyval6Tail13 : Box := ⟨12829640827659215640108549086306583655767191491588871612190,3427065438592134416405402699864226357675339672007715409576⟩
def polyval6Tail17 : Box := ⟨13449070643424411581136212076610423186995024616022443706238,3325737182192929828121577605724159547427025504528837519363⟩
def polyval6Tail21 : Box := ⟨14098407243160746157561380310514747275633729064544865067589,3211014049057837153701944580020063696497742616680570845945⟩
def polyval6Tail25 : Box := ⟨14779094560796930400183235366832857648885383793809176294029,3081978340077489926931413671860804460056706641419849526442⟩
def polyval6Tail29 : Box := ⟨15492646245052649722644688234263097531811602372675185234569,2937659412466037426564178519584952704630941916080968698688⟩
def polyval6Tail33 : Box := ⟨16240649025348769414372115239675643807414282681371035782252,2777030848346605357608935576380567479589493796535539554811⟩
def polyval6Tail37 : Box := ⟨17024766240227644512610635580063130341736579793247673843864,2599007477861133383864651416024287938988523974397400237969⟩
def polyval6Tail41 : Box := ⟨17846741536129620856213613766510564704638212486430354421135,2402442249501298764086889223588980554967942522826085737835⟩
def polyval6Tail45 : Box := ⟨18708402744750719931677379937809956836689208605993202400083,2186122939995721398915469226192876758994098276922230595798⟩
def polyval6Tail49 : Box := ⟨19611665947603612466207320677919954440473694000239656940361,1948768695709386716256560689544929907513576824352500816989⟩
def polyval6Tail53 : Box := ⟨20558539736820270869118391995207642553277941292966438781980,1689026397113359869359835114945498264287176166862221408892⟩
def polyval6Tail57 : Box := ⟨21551129681671074499687731136341531265705432534177223971997,1405466837465490155016789100321954845698708283356040417303⟩
def polyval6Tail61 : Box := ⟨22591643010732596092476997821064155594377306663270568044201,1096580706404966152643643050038374645620915948379351481950⟩
def polyval6Tail65 : Box := ⟨23682393520117083128656938984573939240980721947056035283479,760774368703835967065177799527461222724264449782681953640⟩
def polyval6Tail69 : Box := ⟨24825806728711018873544549454921367469878835847838586524527,396365424968781862412594625468877618849175145208343648249⟩
def polyval6Tail73 : Box := ⟨26031250000000000000000000000000000000000000000000000000000,2⟩
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
def resval7 : Box := ⟨31864634787273250767850236891559758815590419065050558462,28743323442972670487143228349390545259271137689890810097⟩
def polyval7 : Box := ⟨23263818828274130696148333772242682349882804212609685497210,6405435267528764401031647416534333509695013810380417068578⟩
theorem cell7_lo : Holds Q cell7 (127/128:ℝ) := by norm_num [Holds,Q,cell7]
theorem cell7_hi : Holds Q cell7 (1/1:ℝ) := by norm_num [Holds,Q,cell7]
def resval7Tail4 : Box := ⟨-70062790708465091876625513307924019134009651170438350022,26890891168518045612422582804845973539736506143070433442⟩
def resval7Tail8 : Box := ⟨-71168339569874646794747141438361736778938145037442229368,25785382952966133818687937610684004825672102364234097467⟩
def resval7Tail12 : Box := ⟨-72291289729622845061649261128476510977363388702957071312,24662432797167114414266205062105389837155675311587216770⟩
def resval7Tail16 : Box := ⟨-73431958677805277070483960777948797342296133520021552926,23521763848987529216955339953375191961662432500579319098⟩
def resval7Tail20 : Box := ⟨-74590625999705755450247808589175684293978413348902728746,22363096527087059644489654966629405513321300336994971453⟩
def resval7Tail24 : Box := ⟨-75767575687854010727101035591309514623030400621373425508,21186146838938804455643440773076598633742957769976775893⟩
def resval7Tail28 : Box := ⟨-76963096215834575915240473683308444387305539309715667656,19990626310958239269766422275923119113200670628370641203⟩
def resval7Tail32 : Box := ⟨-78177480608995560877636686482615964858379215783404305046,18776241917797254307466651679576462472936423106765220431⟩
def resval7Tail36 : Box := ⟨-79411026516269975689715202503099346058371720672332572629,17542696010522839495365908599661505317290841309413989553⟩
def resval7Tail40 : Box := ⟨-80664036283130297531500254901318967219658676341089765090,16289686243662517653520719933133781508245011533693972489⟩
def resval7Tail44 : Box := ⟨-81936817025694172138654626603936428335184214320565168333,15016905501098643046149411266068019270731945710413958230⟩
def resval7Tail48 : Box := ⟨-83229680705999413416747831300725859850475431879430521613,13724041820793401766297297826210133412731989886310131331⟩
def resval7Tail52 : Box := ⟨-84542944208466751309719322546277818964696721403513971058,12410778318326063835691653495007429319583446803778195870⟩
def resval7Tail56 : Box := ⟨-85876929417569067587323696766838775164207456197010777301,11076793109223745098185417648184092350779413699451427051⟩
def resval7Tail60 : Box := ⟨-87231963296725732768487716386898192817105768011107402161,9721759230066475928292790238709366659967838273820679690⟩
def resval7Tail64 : Box := ⟨-88608377967847985729707582519138626599085724183449507214,8345344558145790352616229473276680508531504978582976190⟩
def resval7Tail68 : Box := ⟨-90006501006975297979487006887675277908129746489800630307,6947209036944356390057625057756222910847732040206114366⟩
def resval7Tail72 : Box := ⟨702357146511968160889199903585217288552792997998755744526,2919630817502020640189245421314893608762719325991717096⟩
def resval7Tail76 : Box := ⟨-896083513019410289964343602718843158799615099779694496,345944268061296717192193000493151444124870008674310471⟩
def resval7Tail80 : Box := ⟨-910202660526383832498184252112528847686033322874389164,331804914090826139915117630179415774346793477353094511⟩
def resval7Tail84 : Box := ⟨-924564554623189683471143509012348083217395573366700094,317443019075569437579941312704587489626952110348609717⟩
def resval7Tail88 : Box := ⟨-939153062892448053748519350802953293104084315615863761,302854510805871073342199847744064312509046952670058634⟩
def resval7Tail92 : Box := ⟨-953971760144017385762964448203186187184582613837143913,288035813554300706274640447699677911359451499076464394⟩
def resval7Tail96 : Box := ⟨-969024278480680385424712044342384530048373711406745976,272983295217637697813559579336573403789766130048394681⟩
def resval7Tail100 : Box := ⟨-984314307315810737325165268721949073100183699979871902,257693266382507345686712316682651680049422008068915152⟩
def resval7Tail104 : Box := ⟨-999845594277255185291319003522134715707105667087274924,242161979421062897704858150331292440127888339238949638⟩
def resval7Tail108 : Box := ⟨-1015621946125886465745453519817288889373599756282445901,226385627572431617248040534221436342325405329878469561⟩
def resval7Tail112 : Box := ⟨-1031647229688650792639733388014276311264947915129533768,210360344009667290352750557771538748661314667674971607⟩
def resval7Tail116 : Box := ⟨-1047925372806337707750580998241414264587516316252081694,194082200891980375241338482086925590318419638261167280⟩
def resval7Tail120 : Box := ⟨-1064460365296304590830019515988658397739494000109128090,177547208402013492164174489438198042158600539757445629⟩
def resval7Tail124 : Box := ⟨-1081256259930391796051016712970008900395214849220038274,160751313767926287030193920717144313817003893193060219⟩
def resval7Tail128 : Box := ⟨-1098317173428268114040281461229544267667804367813463670,143690400270049974676105205131522861779847669168399222⟩
def resval7Tail132 : Box := ⟨-1115647287466451877472866325956569635152189289376274182,126360286231867333463971040592713253366324997375578324⟩
def resval7Tail136 : Box := ⟨-1133250849704862820131896851440587942432014134133985226,108756723994487326110736907295862975486807213230296235⟩
def resval7Tail140 : Box := ⟨-1151132187336706023926508690930709951036811666837808342,90875395116148844477565856648506146105600376557228382⟩
def resval7Tail144 : Box := ⟨-1177401017231343407157234277119966242307566025672013976,70833041799893654909372164669048779659835848024925007⟩
def resval7Tail148 : Box := ⟨294764297971964132815588659211966252801076458754,95267992593615463397277998218381152257954722163⟩
def resval7Tail152 : Box := ⟨299373593419474239076207872339340857036347327239,90616543410296735946820464322487054880446442660⟩
def resval7Tail156 : Box := ⟨304097345327203551954106944574979106073522091334,85892790874611516323698749452380296087991550254⟩
def resval7Tail160 : Box := ⟨308895632926225071875214360449295307901370882051,81094503275421137214298915401603398594730778980⟩
def resval7Tail164 : Box := ⟨313769631689076257918381627030466418895028463522,76220504512569699908701449569873610411762883947⟩
def resval7Tail168 : Box := ⟨318720536246014925603314062169414051585937999107,71269599955631030792766311250062135946627032261⟩
def resval7Tail172 : Box := ⟨323749560077275862924241292694004486464857035188,66240576124370093446339046624586940701967732608⟩
def resval7Tail176 : Box := ⟨328857935810341673875114780626408108799809138613,61132200391304282494213847562963845863811455454⟩
def resval7Tail180 : Box := ⟨334046915522062921206130732035276479767117942850,55943220679583035163043320130780580174920542107⟩
def resval7Tail184 : Box := ⟨339317771045545582585826412473946888453350039833,50672365156100373783303650756977303504328873324⟩
def resval7Tail188 : Box := ⟨344671794281880820081109042269027325098004950518,45318341919765136287996944236804477605406276926⟩
def resval7Tail192 : Box := ⟨350110297516793467657460759484711725656704352560,39879838684852488711645901357486081105091797853⟩
def resval7Tail196 : Box := ⟨355634613742286848093894223864769087733868591280,34355522459359108275763427972904734088619323717⟩
def resval7Tail200 : Box := ⟨361246096983362755380404577065065950900111954659,28744039218283201014365334471947200930857078810⟩
def resval7Tail204 : Box := ⟨366946122629896687450065563619698012669338864932,23044013571749271808143634730392214028891120383⟩
def resval7Tail208 : Box := ⟨372736087773751639560703960759603580859377481210,17254048427895521899118579196986344562777532253⟩
def resval7Tail212 : Box := ⟨378617411555977583980564431645525027524152485462,11372724648817807260331109351805339643608048853⟩
def resval7Tail216 : Box := ⟨384591735642145677060064509922920246071153522803,5398544985073683170930300547144240079618024569⟩
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
def polyval7Tail5 : Box := ⟨19943284758716004212660708862199627076185690730436769942190,6082760190584475265676917234262981772174608600626335033400⟩
def polyval7Tail9 : Box := ⟨20257963951489206218027107567105745260974545780256571311322,5768079314716535232746710253235744812930193676454538123995⟩
def polyval7Tail13 : Box := ⟨20577610073581653307312473362508686425169039992188307024956,5448433192486386989649078986430320032234348654024956907316⟩
def polyval7Tail17 : Box := ⟨20902299824261951955840544065690470834489854749720951556232,5123743441805996509670071909570647638698771258504530898346⟩
def polyval7Tail21 : Box := ⟨21232112785743780251319695465959190436257267192454253458966,4793930480324167940160852410328984332540858536167407164463⟩
def polyval7Tail25 : Box := ⟨21567129796085110542542213193134102934953177952916445139620,4458913469982837646139655933841820548526335757630897049603⟩
def polyval7Tail29 : Box := ⟨21907432968870594943148046047804183348703397423324546402362,4118610297197353245450445423414590539175394782181617030978⟩
def polyval7Tail33 : Box := ⟨22253105713337745048371032997367341156687889675318647773970,3772937552730203140220945657327928933068473365184808802424⟩
def polyval7Tail37 : Box := ⟨22604232754820763725456122838012421437488872305576247542846,3421810511247184463134632502864567967215875660886424604960⟩
def polyval7Tail41 : Box := ⟨22960900155516956032514582317720336700223627466580354472460,3065143110550992156075682901685214849153615199650095044899⟩
def polyval7Tail45 : Box := ⟨23323195335580808938714071962198574478144556687600393099873,2702847930487139249875941007000233334220890066363703368239⟩
def polyval7Tail49 : Box := ⟨23691207094550910060358952232697375725330355447894734282832,2334836171517038128232767779058471726151614835640560766051⟩
def polyval7Tail53 : Box := ⟨24065025633114957209252254886842225764891263536918751945241,1961017632952990979400218463216105478468326327927245066744⟩
def polyval7Tail57 : Box := ⟨24444742575218193423475737109081735419245162594333887589295,1581300690849754769222862381784153599731142578826822808429⟩
def polyval7Tail61 : Box := ⟨24830450990520687684253257364323320716015120158881925547035,1195592275547261345596510753484532123271008334164712207838⟩
def polyval7Tail65 : Box := ⟨25222245417210204651069826481463123689286422802970146010651,803797848858544932543229674742435463129166937158101774789⟩
def polyval7Tail69 : Box := ⟨25620221895136326845731919636407419765138206615206041984784,405821377954450781857224698345503218651425788113439178057⟩
def polyval7Tail73 : Box := ⟨26031250000000000000000000000000000000000000000000000000000,2⟩
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
def pend : Box := ⟨1029654660433728275117466539132862941916503185059287680901925,14593662074619979713442055914073943074632963702421663933⟩
def zend : Box := ⟨1003624415055616193178027343750000000000000000000000000000000,12547255979467269980468750000000000000000000000000000002⟩
def betaquot : Box := ⟨428737364386895177824076895854138710263752435149342415616995,394745275804109877389111432986020503489424360846923238⟩
def crit : Box := ⟨131563720124778911506385289292246672837983238579580633187,40420298416449621836506743398320383293832461489782257474⟩
def subsonic : Box := ⟨788656485344360441592204510782020057584615939431450510649,25393341847945269144622380118128041523631144401765799018⟩
def pendTail4 : Box := ⟨26024473955444973214402966586911075615391696074792837103310,1539771115596764617564394418871865182462678311491413034⟩
def pendTail8 : Box := ⟨26024503993069476924360506896135528930514089601728386322811,1539271944221675781954516803991996921908734800720831024⟩
def pendTail12 : Box := ⟨26024503994167600446279579723113869709897636116478502538882,1539271899921105944233296006945155897429341458203837813⟩
def pendTail16 : Box := ⟨26024503994168058094469808427156386085195713090065912228491,1539271899889256621255430722425291135732641999258648661⟩
def pendTail20 : Box := ⟨26024503994168059028553574017670993627085811188123499430548,1539271899889154291156978297172536498152766008177543671⟩
def pendTail24 : Box := ⟨26024503994168059035332465962861808544034633354443788330650,1539271899889153147205169268672001751540682591765969676⟩
def pendTail28 : Box := ⟨26024503994168059035476805877583727051955394065815921076726,1539271899889153108850320699437539338765375367589120932⟩
def pendTail32 : Box := ⟨26024503994168059035484587324853096423274356979514177003960,1539271899889153105323172870347158159560982616011222042⟩
def pendTail36 : Box := ⟨26024503994168059035485461875841985449676082934840800848720,1539271899889153104477552420378066761589654177591911269⟩
def pendTail40 : Box := ⟨26024503994168059035485525818476451041465955077455220516858,1539271899889153103960915530203262068565314244529297482⟩
def pendTail44 : Box := ⟨26024503994168059035485042899145021254790744510441199111495,1539271899889153103156265719998131864895531578186722921⟩
def pendTail48 : Box := ⟨26024503994168059035481165851667390900082638046222623290100,1539271899889153099887340881461347011141546822315819966⟩
def pendTail52 : Box := ⟨26024503994168059035420497032692224620690841125385272473869,1539271899889153063490195411564955064099119636848730315⟩
def pendTail56 : Box := ⟨26024503994168059032919044180736160010750434818304236831052,1539271899889151852692304398981378468704972710668494470⟩
def pendTail60 : Box := ⟨26024503994168058698952635686201204217914815439592768656685,1539271899889012696184591356352354109049168820090258944⟩
def pendTail64 : Box := ⟨26024503994167867453950525425984162331459396043248223239433,1539271899817811875037958559469156857715278042630467827⟩
def pendTail68 : Box := ⟨26024503993362265245577869967309774902938423136126571219386,1539271650074635033665101708826819279981798769629782355⟩
def pendTail72 : Box := ⟨26024399183053169839385289801033334706218577871271839996221,1513590061126393096487284953263212636498269212360476672⟩
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
end SepticProfile.ExteriorCertificates.C00

end
end

end OAI
