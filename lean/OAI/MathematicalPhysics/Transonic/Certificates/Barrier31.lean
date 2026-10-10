import OAI.MathematicalPhysics.Transonic.Certificates.BarrierData31

namespace OAI

section
noncomputable section
namespace SepticProfile.ExteriorCertificates.C31
open SepticProfile.ExteriorJet SepticProfile.FixedInterval
def cell0 : Box := ⟨250000000000000000000000000000000000000000000000000000000000,250000000000000000000000000000000000000000000000000000000002⟩
def resval0 : Box := ⟨120051860004356110036324606241973116483718833977276907858,306714231952901854061797439972754380431054413752751966⟩
def polyval0 : Box := ⟨3848698757271195197576566774077707225782524809199032058336,14808832609716461995202871802129884036278989994521425021⟩
theorem cell0_lo : Holds Q cell0 (0/1:ℝ) := by norm_num [Holds,Q,cell0]
theorem cell0_hi : Holds Q cell0 (1/2:ℝ) := by norm_num [Holds,Q,cell0]
def resval0Tail4 : Box := ⟨64472148718369938319309582414698053342609823976416,1860020513621876444806662549338605199497829807215⟩
def resval0Tail8 : Box := ⟨8150280473534215222959194523544962448223159520,429403514470989136040274698755813003561786290⟩
def resval0Tail12 : Box := ⟨7744627391774696428947627689569014293040859,620684385459915556817308148204656316076913⟩
def resval0Tail16 : Box := ⟨32380997569849258037164788021482297738700,28807367893621882336722577231696188261126⟩
def resval0Tail20 : Box := ⟨460268193594088151362425015267283833511,401915489128279122013360936708736712945000⟩
def resval0Tail24 : Box := ⟨19086571467489024520565851567210458763,6429486119169476571886297751670628549081810⟩
def resval0Tail28 : Box := ⟨2100991187772132987114078583268420204,102871711805686226804925246805628145164605373⟩
def resval0Tail32 : Box := ⟨577853598341031822286784899618469004,1645947378853610393519109364951891379279018426⟩
def resval0Tail36 : Box := ⟨-185382388303680467091217971242626243,26335158057752621035268085047115134093392190380⟩
def resval0Tail40 : Box := ⟨-146717205358256198410282825366159894937,421362528784492081709499139504442039819907343271⟩
def resval0Tail44 : Box := ⟨-37719729806576418770950363794220629647471,6741800425184723243331129127992185104859018693442⟩
def resval0Tail48 : Box := ⟨-9656876040515067641925331441929161678702436,107868797749600534837424047629093980676643885453995⟩
def resval0Tail52 : Box := ⟨-2472166204646973577352891359808871513998741516,1725898446337087542063575683151869186705248146223754⟩
def resval0Tail56 : Box := ⟨-632874672353831542880267875705829136314816126012,27613781821339415813757806047204458685626461387670126⟩
def resval0Tail60 : Box := ⟨-162015911763238741694556339871436024244910476892894,441668619210756764234675141671705764307758163044010600⟩
def resval0Tail64 : Box := ⟨-41476043019808140055819046395442585783694552196154838,7027814096631012385988888452388319495681671752081233000⟩
def resval0Tail68 : Box := ⟨-10617156409369523163552713574160021143040269034221723480,102491074808611714969074330703157081166775492230483367443⟩
def resval0Tail72 : Box := ⟨847193011206268986842736646097016706131605643596092764940,2551589127799250721468728067573550916316594694704971690⟩
def resval0Tail76 : Box := ⟨-30289927934364273061030674409082149772735115967391,647393605076529091803190336172427119118893282892⟩
def resval0Tail80 : Box := ⟨-1711023742745532448256143444689051044375011210,77439096551284408303374345792706760557499346⟩
def resval0Tail84 : Box := ⟨-1011179440416245618083316954665784916645577,72163267234128801705292660543134128217585⟩
def resval0Tail88 : Box := ⟨-2921973300839628755790466847688974842842,477002813230170685701087323145077144029⟩
def resval0Tail92 : Box := ⟨-30378539783512478053539101833110573857,2803077537689297320190292669723226457666⟩
def resval0Tail96 : Box := ⟨-953830531539135636231022596100725215,44779175684728215042180105646792322923214⟩
def resval0Tail100 : Box := ⟨-81238229542461727488560741792053821,716463785423958331633881592698837691825017⟩
def resval0Tail104 : Box := ⟨-17590625966978873295447086584816941,11463420211929286382017904439261075425375892⟩
def resval0Tail108 : Box := ⟨-11315237297520739147041983000438506,183414723282814251438797669311371372674320402⟩
def resval0Tail112 : Box := ⟨-519717662929163447833453756550866252,2934635572050962974098276315463255747918475623⟩
def resval0Tail116 : Box := ⟨-130013262490287607527045734586847523899,46954169030972419698816725323715916549417977113⟩
def resval0Tail120 : Box := ⟨-33274027749185515064424005812863373362706,751266673301406114317723925477356095369468243748⟩
def resval0Tail124 : Box := ⟨-8518080577809881083352868336900314257015030,12020258787126198674713855347593469815028462691057⟩
def resval0Tail128 : Box := ⟨-2180627390817599745587815223124221645557665041,192322096256081778505252153168226719113000589522094⟩
def resval0Tail132 : Box := ⟨-558240599946184951832439547762595841514399577433,3076630189586164213895590687801590001169628793088788⟩
def resval0Tail136 : Box := ⟨-142909671425034730523834414071262818133338462270538,49092105269025602881998225263891764328370166956163334⟩
def resval0Tail140 : Box := ⟨-36585864160064562464921698802593778782673021547361998,751174924896657339421267151473737943236994233183173923⟩
def resval0Tail144 : Box := ⟨-9881525219491607010041375525164942783831004645233981559,2986088056919597026846935701375385074892428314681912083⟩
def resval0Tail148 : Box := ⟨73279040380755757231664639044710616734059189,1282199267455078156457627582517844120598312⟩
def resval0Tail152 : Box := ⟨1365688516078095815376240183592511978019,55051759320613533644439099616118295332⟩
def resval0Tail156 : Box := ⟨453476882056107189118603580450524630,29457702097256094558897084386123856⟩
def resval0Tail160 : Box := ⟨829808404769434170216788107605738,80479113810771208138574167468056⟩
def resval0Tail164 : Box := ⟨5784846493916124768176768777924,34468196685414947517907008239263⟩
def resval0Tail168 : Box := ⟨125721872720141024875959373376,539317672262908348828104195966849⟩
def resval0Tail172 : Box := ⟨7537248355251824239933058677,8628720872210625127852310303783484⟩
def resval0Tail176 : Box := ⟨1155801119511101776611276335,138059504360043857785854195242518768⟩
def resval0Tail180 : Box := ⟨441621971025448278852023151,2208952063500054196004925464198296252⟩
def resval0Tail184 : Box := ⟨2386139473554334587181128790,35343233011798087030170098609827358450⟩
def resval0Tail188 : Box := ⟨511638110891984089824682373219,565491727710270712822412368870298988315⟩
def resval0Tail192 : Box := ⟨130767130690166896347626732520056,9047867520774299131514856998763541936571⟩
def resval0Tail196 : Box := ⟨33475292411724072263653508226356324,144765848949345782503039489595158246234886⟩
def resval0Tail200 : Box := ⟨8569661356429814929194021847187074368,2316245549133450571646091427493465583413821⟩
def resval0Tail204 : Box := ⟨2193832990395310960028464736883153197318,37057872067872424100709918488077031418728720⟩
def resval0Tail208 : Box := ⟨561621317415542036547563906297940624567764,592399433178921408907339102876040770693727615⟩
def resval0Tail212 : Box := ⟨143775482288993413739743916966492210402097415,9343601645631183814410732842580970442407720614⟩
def resval0Tail216 : Box := ⟨36831521598927577132393769189041386768046083328,114979628188383090999125608111754203194469528855⟩
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
def polyval0Tail5 : Box := ⟨2217377339443205022492795141806697664443019685004144,54248770399075677549326753067296763180516231280462⟩
def polyval0Tail9 : Box := ⟨224674764710788460806148903125994727427280595452,10870395684605968994667765073093340202449106090⟩
def polyval0Tail13 : Box := ⟨184724528051216926208201435946736968950401638,13867755594518854881563941691096598359326262⟩
def polyval0Tail17 : Box := ⟨676798228978650949056815107114221446358203,458423173509437786267024976847797907585393⟩
def polyval0Tail21 : Box := ⟨8453119388983604344038218104321827378374,6169052300417611623124623236554745580837613⟩
def polyval0Tail25 : Box := ⟨307669641673877597408210220446663143038,98684611871964773487006234727598571581203639⟩
def polyval0Tail29 : Box := ⟨29619886389911275111989363374812653825,1578952780461005459076651514300907891031240685⟩
def polyval0Tail33 : Box := ⟨7134722348201281869720454226076781697,25263244353759080420416172422361407129227622259⟩
def polyval0Tail37 : Box := ⟨9969896626203597153406348027695555576,404211909613477460073325627734579447252608465630⟩
def polyval0Tail41 : Box := ⟨1501472510017916206704451475430661478990,6467390552418596764120584964379476543455658458601⟩
def polyval0Tail45 : Box := ⟨382927766706575268093306635000726353785023,103478248479725068301464894476988197173155299112391⟩
def polyval0Tail49 : Box := ⟨98024724639802553335014070366843929422273719,1655651883777555453351183225195516301703619060074351⟩
def polyval0Tail53 : Box := ⟨25094291385856942675696261122071194233691093821,26490406614545134540601739336658117076025365220599227⟩
def polyval0Tail57 : Box := ⟨6424137897718635039436596967399896835671426311051,423840483203587739582479413381854413753199975948734868⟩
def polyval0Tail61 : Box := ⟨1644579296508565260059323449917967632599295231641637,6779905938198739422030392520250099473782143456183463397⟩
def polyval0Tail65 : Box := ⟨421012348922792020025098627602911665469724055828717252,108083795967156342297063184971156399786704220019772574571⟩
def polyval0Tail69 : Box := ⟨107779753783983978365217161006810128560068055123933922459,1628297511018721018129316754230944066431418110658354072723⟩
def polyval0Tail73 : Box := ⟨27968750000000000000000000000000000000000000000000000000000,2⟩
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
def resval1 : Box := ⟨119810786596563746438912900421723394154924111650471111606,224378896076481746113168886399876151543353818104178879⟩
def polyval1 : Box := ⟨3830109011773521661114001810300812344866084916229042734402,8471156269110720124941838042540699556160960971735478389⟩
theorem cell1_lo : Holds Q cell1 (1/2:ℝ) := by norm_num [Holds,Q,cell1]
theorem cell1_hi : Holds Q cell1 (3/4:ℝ) := by norm_num [Holds,Q,cell1]
def resval1Tail4 : Box := ⟨62582144756108253460147387805872651678826818381299,3220975050905311630548504252545227474703147010962⟩
def resval1Tail8 : Box := ⟨7684110929630330389020334063005348754107913923,6507498179845391597610058374935514094545540618445⟩
def resval1Tail12 : Box := ⟨-331747992046344358929123358830392447294040663,20565973950764921219623404601468120563373252899485⟩
def resval1Tail16 : Box := ⟨-2221163779389629376307104447842151878007025308,64997482750390148997545208230732545100568102061933⟩
def resval1Tail20 : Box := ⟨-14556810288809978811476064286496639826507187645,205416606264583508614462469087529730288273394103700⟩
def resval1Tail24 : Box := ⟨-95399514543621080816003093304527282386348895250,649168523291160714720712309056255842045385475796004⟩
def resval1Tail28 : Box := ⟨-625210258618036100129747723283081468716318253584,2051369409966862868279409988492724400770987351110953⟩
def resval1Tail32 : Box := ⟨-4097377950890068382121206324991554958551391515629,6481218952638288530200914634012451312562578466629621⟩
def resval1Tail36 : Box := ⟨-26852576138955882996450017519231378815828920368842,20469949653871288536480846533003128445982412562572327⟩
def resval1Tail40 : Box := ⟨-175981042984262768722928820896979777188186975821375,64604035881492559404397569570302863069864243576618423⟩
def resval1Tail44 : Box := ⟨-1153309363301665757539964993868156836042645315937481,203583534249859648123323421128937383947878962287933537⟩
def resval1Tail48 : Box := ⟨-7558328243333791057041706980089224118371098960632243,639511202188385903911089993003514770517329275994142227⟩
def resval1Tail52 : Box := ⟨-49534259975511986962969472869436703558580245671736393,1995524996697577007283471924044605458928121237192875104⟩
def resval1Tail56 : Box := ⟨-324627726175481032576265126915669429358814578391286678,6138769430717210215450418043272007542975901293994714290⟩
def resval1Tail60 : Box := ⟨-2127480266252629833300293843576760147232763274810252097,18300046550583138308026992227498390538735911857850812371⟩
def resval1Tail64 : Box := ⟨-13942654655137887638232598191013549148887151890171200802,50618417737689148498283314366554689667346685721563410823⟩
def resval1Tail68 : Box := ⟨-91374255836124963296382607415715124411028998440763405406,112670331114543987763460136784674192674032199546426809324⟩
def resval1Tail72 : Box := ⟨850290295617364091607163060207437920570957529417568313348,1518632255383140482689542805420686019422959219248356605⟩
def resval1Tail76 : Box := ⟨-29607187011220338303353043907255758237375093778849,421083402073481915825656226132071131652264114881⟩
def resval1Tail80 : Box := ⟨-1634544506583475162574854770241490350528717753,67990707164756610378108834143325851745449404986⟩
def resval1Tail84 : Box := ⟨-3882129145422266291496321290515019418384965,214733757580840878910540049905452033317544744758⟩
def resval1Tail88 : Box := ⟨-19260949163062734187281443451465894177217146,678654760559686070782168356083470818567857471786⟩
def resval1Tail92 : Box := ⟨-126211156751417956026486999945417706699708952,2144818836151000474480454033402147093875923675333⟩
def resval1Tail96 : Box := ⟨-827137261372993865587631942888132754981729671,6778258444269454091560969379484885601223097216445⟩
def resval1Tail100 : Box := ⟨-5420726750825150262741310564277901796976465165,21419837407467535229758643378500849890785777506581⟩
def resval1Tail104 : Box := ⟨-35525274833778260044062229272222286779390738793,67678870803683306510972378486518865297394683129539⟩
def resval1Tail108 : Box := ⟨-232818441150563691942800713970936485399108573838,213778112374903393408327155075287609239915737042329⟩
def resval1Tail112 : Box := ⟨-1525798935924295736350597556156912014797294871616,674854426853085725398436307203725987853472225122466⟩
def resval1Tail116 : Box := ⟨-9999475906473432884519717291572032910264578592256,2127696052513113786695974633588620523702963546959276⟩
def resval1Tail120 : Box := ⟨-65532565300664316933851889006345486732358520739070,6690640956618031165817095477030404041405857090082827⟩
def resval1Tail124 : Box := ⟨-429474219954436447387869583048530234519871136585698,20923370491294776556689862885220638144194620050961785⟩
def resval1Tail128 : Box := ⟨-2814602247893614323266583817075711363979772811203765,64670931654326305379214520631412273581048388773283503⟩
def resval1Tail132 : Box := ⟨-18445777291845934725706129156065030527862739561213370,194841836028791918579458831384337670809728996096388135⟩
def resval1Tail136 : Box := ⟨-120886246111562862529074745803203871829031443213357052,553207939240637148417647827757137767922849543386455969⟩
def resval1Tail140 : Box := ⟨-792240572907317053145077355798717017357091422791205312,1338230324661518887638672845249805047194145361069276527⟩
def resval1Tail144 : Box := ⟨-5408327965494373770205461590862813866660996706691516599,1503180382648842712925707375006626890629973037704312219⟩
def resval1Tail148 : Box := ⟨72180805578898104152194851709673059287018803,894761754578410218466950712660141602793688⟩
def resval1Tail152 : Box := ⟨1312933325459156144771300201798881142506,3515558741040792304458398628691458554977⟩
def resval1Tail156 : Box := ⟨560863513303808429770837164319318992,11000101107262816085374804382771857437540⟩
def resval1Tail160 : Box := ⟨882870857294783361772107444156909045,34765298361640797702677731390108212486896⟩
def resval1Tail164 : Box := ⟨5780997172496180756054991088181345799,109872517788684958988801103328979203115522⟩
def resval1Tail168 : Box := ⟨37886309281651983088811558690800364724,347231798726120321635718247498749624263630⟩
def resval1Tail172 : Box := ⟨248291715798309101958614495113263056578,1097295404198218965711024295194071091970532⟩
def resval1Tail176 : Box := ⟨1627204588615085766306025162115030269838,3467152871386531252289971410050490427937185⟩
def resval1Tail180 : Box := ⟨10664047991941987563584918039995515294019,10952393969904814075072048566183213035605903⟩
def resval1Tail184 : Box := ⟨69887904919989067794616268681505868629602,34578789287445066265023898886542288694726893⟩
def resval1Tail188 : Box := ⟨458017373683639030013500557984320964566281,109048913012062708207819446431911691456265750⟩
def resval1Tail192 : Box := ⟨3001662660173095843199053485608906611054234,343094314855272150171844512989075801321110508⟩
def resval1Tail196 : Box := ⟨19671696409710421149706183109734350890015132,1074162504132931365618521629534642439533812488⟩
def resval1Tail200 : Box := ⟨128920429590679426300379582102226802382310521,3328135809161374662400293468296211691526788294⟩
def resval1Tail204 : Box := ⟨844892927365637654908806250059599338425212688,10081111975357036415065062101682431637236064101⟩
def resval1Tail208 : Box := ⟨5537090288861048381485001878132500273287367907,28994480761782822544862858420344611506274707189⟩
def resval1Tail212 : Box := ⟨36287875141834158336883389700988037040539181900,72848942189608062896057006314050638092311786395⟩
def resval1Tail216 : Box := ⟨237827269577289297831905989257423191285666377125,107107986115107291643036420473218026274230893068⟩
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
def polyval1Tail5 : Box := ⟨2156979137310019248301489780843139166750779894903361,120846208139610647385229698204308135138680100450639⟩
def polyval1Tail9 : Box := ⟨216047257426824228554445389011220170981909372213,280923299010203786969150901045114253761398326222851⟩
def polyval1Tail13 : Box := ⟨15912560164055480785180847647839112488397773246,887831036311701508005012969141740253089827162834649⟩
def polyval1Tail17 : Box := ⟨103160389852501968838173459428114945817624188862,2805931103210124109674930447089144622474124956701049⟩
def polyval1Tail21 : Box := ⟨676067919240780352828934120000010112561622833683,8867777899074175851211324472190840512048930979343635⟩
def polyval1Tail25 : Box := ⟨4430678666939823929564914270752560215992731095749,28024263340449603481493725236571758554398928896831915⟩
def polyval1Tail29 : Box := ⟨29036895709954257941336819382066562899917860026496,88555477535077325933207178837546999978060054163147635⟩
def polyval1Tail33 : Box := ⟨190296199724600836548349734410815240188962896049417,279780514840788211830713277453360100839372285352062407⟩
def polyval1Tail37 : Box := ⟨1247125174515109860709581464284163148768501466971979,883598894904142652906495927602034694168366947099499715⟩
def polyval1Tail41 : Box := ⟨8173159543702207348726281180762613131321978887839612,2788377224902426023714838162311780271457853998683729790⟩
def polyval1Tail45 : Box := ⟨53563618385606771907093837318144564943171236488768939,8784916608999687387576494718680941697732873017772312042⟩
def polyval1Tail49 : Box := ⟨351034529451912560638537386157383648175183564828360405,27582927670679387541499726577466750896785091226962266697⟩
def polyval1Tail53 : Box := ⟨2300539892216055782808527784209741804859481520024271818,85984575209433486784079114968274133851615645238706595119⟩
def polyval1Tail57 : Box := ⟨15076818237627274965198161711310365436113725966278810826,263947743071289908852467379240752215457099276600764299090⟩
def polyval1Tail61 : Box := ⟨98807436002145253830429240506486649183621294117650520699,783047967640878025594584031776559330493008342938547402060⟩
def polyval1Tail65 : Box := ⟨647544412616102743709245424497466182744041104115624841625,2139554147072531910792982505880250207350218656590672100185⟩
def polyval1Tail69 : Box := ⟨4243747345519163314942086853492112685502475777267124885501,4564860680926890848896630169830386540292816887302081944049⟩
def polyval1Tail73 : Box := ⟨27968750000000000000000000000000000000000000000000000000000,2⟩
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
def resval2 : Box := ⟨119692128743344345922742896850951690206902449821301403254,203993251754613673936997759773259495436558274822384993⟩
def polyval2 : Box := ⟨3820924780267152357141924556708846429108582524254207976084,7161603972783486767868309803180558422048102989984778793⟩
theorem cell2_lo : Holds Q cell2 (3/4:ℝ) := by norm_num [Holds,Q,cell2]
theorem cell2_hi : Holds Q cell2 (7/8:ℝ) := by norm_num [Holds,Q,cell2]
def resval2Tail4 : Box := ⟨-134392751221990811287185234821189682226509902504167,35063736588285194189487890371808344297389711097678234⟩
def resval2Tail8 : Box := ⟨-449912072455934775372604409526365798307498080749129,59700465726842539073566090120867674718087097712544319⟩
def resval2Tail12 : Box := ⟨-1032384436109383957264470120949479041199435117906516,101581517138962139211436268617990357915724307722821264⟩
def resval2Tail16 : Box := ⟨-2368906791012699050346070876828897225167342781382048,172685879081087988811967327736128133919501233645746099⟩
def resval2Tail20 : Box := ⟨-5435687667015416146906314254593852165936075017666321,293200048664610145975237295820561429088081525671928917⟩
def resval2Tail24 : Box := ⟨-12472715484245890856109098854594741425872264671556568,496986666445924762739485763021840710419988681701851845⟩
def resval2Tail28 : Box := ⟨-28619862118817256118130527836640184587548267799979202,840495351702914959897926724539812389189367253231624807⟩
def resval2Tail32 : Box := ⟨-65671064872336675522880754016489542394219613747751838,1417001119973067390136461164158610401641160786069044357⟩
def resval2Tail36 : Box := ⟨-150688663123611091591233570805166048041920814957899897,2378684626808406840006384807216228110892059427910949497⟩
def resval2Tail40 : Box := ⟨-345769833915793442257344489500990328547851352141791664,3969229331249365011595026388219337190057374306164884305⟩
def resval2Tail44 : Box := ⟨-793402606193951157678375315508517904367025086359735438,6567795469822912242738193097197344652018501196508562126⟩
def resval2Tail48 : Box := ⟨-1820539658958957415587812363882867240000060815671358619,10737339274554192295165308983738103897867932135296672443⟩
def resval2Tail52 : Box := ⟨-4177405801251154479119910372432569083751480591415747249,17245781250672985584378361236022410045144885731618120959⟩
def resval2Tail56 : Box := ⟨-9585465025412093418490995765270538932021357424611845378,26961546288490948358586727135300178925938544701495695433⟩
def resval2Tail60 : Box := ⟨-21994784352968976843971012036004661610170425016002014422,40352803461160578975544495256865545323238541865407260784⟩
def resval2Tail64 : Box := ⟨-50469177793092240854606859813291133369774034305248507976,55893054465638772383906220353743954213035310823721890662⟩
def resval2Tail68 : Box := ⟨-115806194668826662322810860950961425011672116802466665086,65642832045743709867675768681438042225716702938755549964⟩
def resval2Tail72 : Box := ⟨851837084067923535853404037682016763521521120854699655735,1002612976408764973177168179061803145155101188812867250⟩
def resval2Tail76 : Box := ⟨-31491315196247336269550230063561568299335194043220,427122738719045991744654735592443357871414540449975⟩
def resval2Tail80 : Box := ⟨-5075590746987807659405553365713499558792029098069,727270748229512279678500220522530023110441422900839⟩
def resval2Tail84 : Box := ⟨-11642771129507176467371159289953632000803041998584,1237705014301394666158892811207236482739970492379213⟩
def resval2Tail88 : Box := ⟨-26715471760999034915947286972243595513348752185725,2104616692072851685556873878561739616191884731147341⟩
def resval2Tail92 : Box := ⟨-61301255458938390545005914898063899384799877933357,3574657321406106788515071524132975001388047913534059⟩
def resval2Tail96 : Box := ⟨-140661709245311422627563270695024306831047436313550,6062123101599803411009362972855563016096740571147539⟩
def resval2Tail100 : Box := ⟨-322762010332295119254823269218612229317766850822841,10258915034741252265326398278419770756952698636716008⟩
def resval2Tail104 : Box := ⟨-740608911072346528726341298069304224830665512469408,17311264965071447660623205123461023902754713236033586⟩
def resval2Tail108 : Box := ⟨-1699399376633776879199363296454177211362099705793398,29096300497037602111784893604138824623139965608064703⟩
def resval2Tail112 : Box := ⟨-3899437608874731324354593746730344976708206122759181,48636666798687937703017425260089842605664549394382730⟩
def resval2Tail116 : Box := ⟨-8947639898295381542101614660450358465584845712554542,80676634842802782701394944806679901278511758197367706⟩
def resval2Tail120 : Box := ⟨-20531232392937436651325639273473005091157150776463585,132363823558556974424358581049837876470870680293055873⟩
def resval2Tail124 : Box := ⟨-47110915097634814482376127376085744183170972525726998,213721300303165316353016517366124126574988964923485182⟩
def resval2Tail128 : Box := ⟨-108100589329456281102941017550963820120981991686830446,336867654852833494121145030910002977240540862673394330⟩
def resval2Tail132 : Box := ⟨-248047345061323110208530045023260836561786960234554469,511048834934823771784864693251870051315626727599417636⟩
def resval2Tail136 : Box := ⟨-569168824870711510590200859843319365851670000936409606,725815745455925907059994649214061517133400775550917765⟩
def resval2Tail140 : Box := ⟨-1306013750029236796649554077793017316194919227411681457,903173091241776413176540140333200433406649179201683665⟩
def resval2Tail144 : Box := ⟨-3164443817366905583624927096715558075133256236654479052,757684360543013496176697921834053346132947695299353881⟩
def resval2Tail148 : Box := ⟨71947432720092633267395026380894792435073943,53996423955657164976419419856218684148188270⟩
def resval2Tail152 : Box := ⟨685744310649913177637495495309723025726112,90824044388575840776537559345025208801373140⟩
def resval2Tail156 : Box := ⟨1570551693223420958853823275802457033952899,154538898277237498902810954087816322720573203⟩
def resval2Tail160 : Box := ⟨3603783083931425729838434612742931401306671,262712045891903241289135058026712545588443435⟩
def resval2Tail164 : Box := ⟨8269231754515755631466590894433401902865052,446053815093463058735401178093554664647902861⟩
def resval2Tail168 : Box := ⟨18974558743168146642186612242007391462418327,756080501602230005988095479221625863617563372⟩
def resval2Tail172 : Box := ⟨43538975588819057453247799083256009845292354,1278670740019156958551933622195091541157660602⟩
def resval2Tail176 : Box := ⟨99904425762012723203591947620624205470698123,2155726975791618987874494737761896766198802564⟩
def resval2Tail180 : Box := ⟨229240448399540134451240260743223527539309494,3618767140423315128141179148332338604834852712⟩
def resval2Tail184 : Box := ⟨526014566237605904509442998074744317803375200,6038516497410213818422653427278684602564445002⟩
def resval2Tail188 : Box := ⟨1206991723432223681105346414035615804536441260,9991808458450937328908128776978119544595136012⟩
def resval2Tail192 : Box := ⟨2769560225022030433342727502251318712686369596,16335098477599138871128054600378199958103502494⟩
def resval2Tail196 : Box := ⟨6355026046253415051772773900559948985234227346,26236678262757959179536907841807626898698038586⟩
def resval2Tail200 : Box := ⟨14582227056729940897931351227672820485199088227,41017781627031238297241500684800937144409019176⟩
def resval2Tail204 : Box := ⟨33460342158532871793770580172618752856264527440,61390818011682072329250047856684146334074699328⟩
def resval2Tail208 : Box := ⟨76778018406338214651893295853451253701728595155,85033873329328641218326064207235123147883005642⟩
def resval2Tail212 : Box := ⟨176174651426696686838279235091539811853315166307,99869292319821029489132483345534852655625595517⟩
def resval2Tail216 : Box := ⟨404258557872206148266317394634912569849808298700,66668022879819024024559483345327840779619168166⟩
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
def polyval2Tail5 : Box := ⟨22676332519727475817086729399889273464060532388874033,3152610554445103105693792207420384334930884524998960590⟩
def polyval2Tail9 : Box := ⟨47149829948870133050222083241131541699181995378691051,5366118026033565559202644002841684285220026771139550732⟩
def polyval2Tail13 : Box := ⟨108189404845396233333586934355552992931159481694066604,9126606214418919205448504468127825024954047360311013633⟩
def polyval2Tail17 : Box := ⟨248251140544767276061624791624177499066040463031912489,15505902485371622143432537605724132138148966544403157606⟩
def polyval2Tail21 : Box := ⟨569636453440133961979237395897225437278218054122992361,26306254113719851212229606523636333101748006905370139420⟩
def polyval2Tail25 : Box := ⟨1307086397978087769387976016092460131546387319697323779,44541996385481833314203127802573000622505674473599692751⟩
def polyval2Tail29 : Box := ⟨2999237217810718972639499218801608442849014545196153008,75217273853014702008112728748729581376468523167462390633⟩
def polyval2Tail33 : Box := ⟨6882042306167265755877832604744753306340189164391006003,126551872456890178747182606135738951271532038837398788864⟩
def polyval2Tail37 : Box := ⟨15791517263995585880002510353939499843204799350532258878,211840850445077005818497652734450868423838865988853228912⟩
def polyval2Tail41 : Box := ⟨36235176478877305281739690658448564257887278043889755298,352095593257216545443892791108298171326198426255249643806⟩
def polyval2Tail45 : Box := ⟨83145146378617803264540274928876063925144377815795737045,579330002658883409804960196929858305004048052049278498152⟩
def polyval2Tail49 : Box := ⟨190784647353702473886174652622537679195058886777163921410,939368709771497429850906873244930411991455085354561843180⟩
def polyval2Tail53 : Box := ⟨437773980216807723089348326944131716589835560126816658798,1490217752721475829336603077075107758898622095087450012048⟩
def polyval2Tail57 : Box := ⟨1004515092871002916994445535972688633847562195392107027591,2284553686019130227153907744921279516165169139503110194578⟩
def polyval2Tail61 : Box := ⟨2304957849038716792287756614237390857222897502197708399707,3306048281046264855565254906575023809355791823723488753709⟩
def polyval2Tail65 : Box := ⟨5288950582799970656745193243284623129679022637248838600652,4283178158926257382296358521094890097067023655284254053546⟩
def polyval2Tail69 : Box := ⟨12136013157076369400953276256489820711441993096378167748622,4193616085962159077319063038889044847884725826174237383295⟩
def polyval2Tail73 : Box := ⟨27968750000000000000000000000000000000000000000000000000000,2⟩
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
def resval3 : Box := ⟨119507905734025027531277303677122065525069002048646250339,1714545354996748097582483386734070592808147252131995212⟩
def polyval3 : Box := ⟨3839615991807405859253202760664680643081353993123783836794,246152447417240153866036493768529581694435932716645229925⟩
theorem cell3_lo : Holds Q cell3 (7/8:ℝ) := by norm_num [Holds,Q,cell3]
theorem cell3_hi : Holds Q cell3 (15/16:ℝ) := by norm_num [Holds,Q,cell3]
def resval3Tail4 : Box := ⟨-185996488758713011199022148273278295960857077935643748,1986402605561875589169859429868126255054651578121464521⟩
def resval3Tail8 : Box := ⟨-275838983021611779421349608518636905741717525327941787,2536493265908402635232709325674920772619995692846776527⟩
def resval3Tail12 : Box := ⟨-408943751171244043476422610312772403793292951778419399,3231727987006077133077667969884904002604868826040709158⟩
def resval3Tail16 : Box := ⟨-606277565543623320810914540552680795530561749736920931,4106711333885948540648799725696050090986222118334127534⟩
def resval3Tail20 : Box := ⟨-898833850432146109902033331374739041451532606128109303,5202310653528705766368369631942414927684671128031143504⟩
def resval3Tail24 : Box := ⟨-1332561744979348262033794395956687564697231246914915274,6565603315990101829882375129525839984211857241654034394⟩
def resval3Tail28 : Box := ⟨-1975582921502861094125161179928888553166829824378828381,8248894025375042748624259510447400098092600097966741647⟩
def resval3Tail32 : Box := ⟨-2928890833343160746520471344931551021970559709588265166,10307085881532697155867661956676907744391459393239691717⟩
def resval3Tail36 : Box := ⟨-4342212832613399940312763195255797590876881695529309623,12792265586865202005371823006170904233725685003666767636⟩
def resval3Tail40 : Box := ⟨-6437526475573963468274824662081754522592614647830445998,15743711602429980375780533126482366505718884296762901192⟩
def resval3Tail44 : Box := ⟨-9543923506571566770613713272947826391656593799301808937,19170538096985301648255537666042969284373668683851652583⟩
def resval3Tail48 : Box := ⟨-14149297287537466989457930692514134330396273086658308336,23022672206797405662790017236363011894019603119899285638⟩
def resval3Tail52 : Box := ⟨-20976971744719406778656407591927345215269312437836706549,27143565396628350168330996957884073445490472849698300244⟩
def resval3Tail56 : Box := ⟨-31099307240249457926282303138376185237903658217964332868,31194569739412075083099094069451299270471336187105775859⟩
def resval3Tail60 : Box := ⟨-46106126403432162513342385299086043760542414859480719673,34535681433380953619205611828081541334737329500072072044⟩
def resval3Tail64 : Box := ⟨-68354413013241663706279327673573301382732604369489536577,36039493509811076600755466317012731679789270842485471078⟩
def resval3Tail68 : Box := ⟨-101338270743355389365545044101907675558639441775509297731,33803406186577696862859533282414744979438708654996958695⟩
def resval3Tail72 : Box := ⟨852608448520495137417282081226157379196562382323247663628,764435745415933580761299225637732014317438686924627002⟩
def resval3Tail76 : Box := ⟨-2369660859111314193850360642219562543303122807205503,25987607256183335813091896251462630172501406492559262⟩
def resval3Tail80 : Box := ⟨-3469959299466330466180819144073823505680193305935549,33201782462079636739987529952371621572546913286587022⟩
def resval3Tail84 : Box := ⟨-5144368907098213917170977779678202909721972137795000,42328602227298882639904797398379007624815901923143409⟩
def resval3Tail88 : Box := ⟨-7626759053599151737739210728770296865271626018299463,53828818945498503681344636385333597230687280206519879⟩
def resval3Tail92 : Box := ⟨-11307014470039755324891179377796378839620891071594486,68249583253391330606736446980491308761090552256257671⟩
def resval3Tail96 : Box := ⟨-16763159203960492365483542543486545737350292961588801,86225901307699320229727106805885779678551792336420371⟩
def resval3Tail100 : Box := ⟨-24852139991675269809278633472093040476661107423171771,108471140397305222642817910584973544280721639701347776⟩
def resval3Tail104 : Box := ⟨-36844419041245117090842023697503565331967452212692168,135747669918206251792802066617726703202596600568856620⟩
def resval3Tail108 : Box := ⟨-54623513908323056734267346480874640686058823277263277,168803550625930867425029330348507853782901290920463512⟩
def resval3Tail112 : Box := ⟨-80981824366742154160785205380488251308895576201163299,208253061585195923342233481189937619067392995219698629⟩
def resval3Tail116 : Box := ⟨-120059209093954200733585044601968079519643527758423708,254366420254119159220300005567510291372900581782303567⟩
def resval3Tail120 : Box := ⟨-177993195398861442737610677375246524469510487426751010,306715111661984695011743395759586624951043841562848093⟩
def resval3Tail124 : Box := ⟨-263882944485369376950100083143670200150842191909939631,363590509569734082135786267735714002638187103147888553⟩
def resval3Tail128 : Box := ⟨-391218373456505703751860561699365846412359736059334763,421070027233968739805606433472987882990818782624838081⟩
def resval3Tail132 : Box := ⟨-579998893177614480106564742477624404356967793526255789,471539529097007389190194865175736687618557049454919734⟩
def resval3Tail136 : Box := ⟨-859874532808826314248563918871256229019785946761009561,501382198924143593414325170596628830014908829373715748⟩
def resval3Tail140 : Box := ⟨-1274803134530694628259271382522497047007523234291763781,487396117289085046246245636484475764283442098236666872⟩
def resval3Tail144 : Box := ⟨-2040678848633945288541619011575422445676946719121550379,383924743313058662563604293359225022940229801377414001⟩
def resval3Tail148 : Box := ⟨695535860913012964336719515310907508670816328,6097868324145922136715363459462490960686829132⟩
def resval3Tail152 : Box := ⟨925329428325386104043518014702112811990509889,7776033475629471264542223726885633252279159366⟩
def resval3Tail156 : Box := ⟨1371840743192422282865243555327008321363197784,9892404884554898038015850749736937510886763025⟩
def resval3Tail160 : Box := ⟨2033815808294533173938527452982667945371746483,12548181257048164526722558125106798512709289967⟩
def resval3Tail164 : Box := ⟨3015223715888733606028520354307065800167891598,15861729561627341825460483267096156703542054512⟩
def resval3Tail168 : Box := ⟨4470205226934895426693728326103476919936767381,19966733242107933238520910842417425176135731046⟩
def resval3Tail172 : Box := ⟨6627280976073844492509353744553543512580230151,25007271112957085144638352387108903087312754908⟩
def resval3Tail176 : Box := ⟨9825243116622117032967788838299202290781247742,31126895267708371941731001922999876693116627863⟩
def resval3Tail180 : Box := ⟨14566366304559507450786802892653991311394320828,38447744138017933050953324863608132559506476633⟩
def resval3Tail184 : Box := ⟨21595295383545988206362453818748214061088222759,47033499519461520745971163770446946928717477446⟩
def resval3Tail188 : Box := ⟨32015999937927242679461484185326000212505535080,56826601598141895230743048806293663146682045830⟩
def resval3Tail192 : Box := ⟨47465164695378493726138070585733900204974185253,67544983142010682020164935719441056224196443439⟩
def resval3Tail196 : Box := ⟨70369248623420110900190318400452888997618625208,78515789375022101898846710799405142776358734505⟩
def resval3Tail200 : Box := ⟨104325586640318864759272318814044104226415314235,88411793118020076615584733129683378870556612693⟩
def resval3Tail204 : Box := ⟨154667390099492400416821530411436776794429161736,94838524366532423707879216584131662981484913135⟩
def resval3Tail208 : Box := ⟨229301385504497514767166499706077383378721348671,93693569763613345894885068453525119734858267818⟩
def resval3Tail212 : Box := ⟨339949651866635690827737574679925595489682133556,78179679414609161990315893823861197873576643619⟩
def resval3Tail216 : Box := ⟨503998487944564666291276948141239105073842336093,37293239838182782279445850041807998365425581698⟩
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
def polyval3Tail5 : Box := ⟨34503780311058326712730366436325380471426863740001379718,311520682866099438507896801664016056758148403160872440929⟩
def polyval3Tail9 : Box := ⟨51150277176880808732852126711457176582004962037852359684,396788889667104601225632471219346713503272974268723889899⟩
def polyval3Tail13 : Box := ⟨75832593870054537913373414709810881350677704264897714185,504041800691781602126375096346340004700297599667914235777⟩
def polyval3Tail17 : Box := ⟨112425242512828365823632488338930079920465337092984942048,638244353970998061399583828974883238448253185014005062942⟩
def polyval3Tail21 : Box := ⟨166675495444004462507166140968038713567872226027187337413,805095026534543899438704681904948773939779200731837791537⟩
def polyval3Tail25 : Box := ⟨247103943567962968408917177869816708149347010898569591853,1010890188350775698229007011017140681886916346364055301403⟩
def polyval3Tail29 : Box := ⟨366342747409756995208492811142066534542945118905301569443,1262178801813481666353550853678193723510292348422718060256⟩
def polyval3Tail33 : Box := ⟨543119654999828004694561771503705842065244303654351739431,1565063816603019776497486813066696071285138196903842387706⟩
def polyval3Tail37 : Box := ⟨805199397921193485824334505559978775367085433173837547182,1923924789633655545049232927611850719350449248639764126659⟩
def polyval3Tail41 : Box := ⟨1193744443685908967710712335379000426407549034639448388019,2339211265066576683396307946110894279231094912964430546902⟩
def polyval3Tail45 : Box := ⟨1769780007921032350268761757117752105630616853841526663239,2803766368944210111581865998282394911691440290889756270050⟩
def polyval3Tail49 : Box := ⟨2623778726681198021389190975233672349285503174619240360139,3296852095130960595557961352578264502768334633950470852183⟩
def polyval3Tail53 : Box := ⟨3889870365679926221246035221260678680415645681965016932386,3774612825199710859178227249617570420588448894672268786466⟩
def polyval3Tail57 : Box := ⟨5766908355467196765493159006762862051226637188285681712952,4155058467199230903431890670023459601912262833831272677268⟩
def polyval3Tail61 : Box := ⟨8549701880500661346313707556113192855631569982709100718722,4294663901035498999755824061780164336294214422044503681677⟩
def polyval3Tail65 : Box := ⟨12675318860629318059514066703906306157159814169744268870520,3952204218084360655336372981120736114181201763582627895218⟩
def polyval3Tail69 : Box := ⟨18791732412839824431049007855878173906368496876342243615192,2733232764773695005309518407054200344417523335626131943249⟩
def polyval3Tail73 : Box := ⟨27968750000000000000000000000000000000000000000000000000000,2⟩
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
def resval4 : Box := ⟨116421146792457328669693657942452263411037468793894566169,8578457917168847483824749804297139814635930432357553860⟩
def polyval4 : Box := ⟨4692776984822410796159162460411810947756503974928373805292,1956377617397635191825985705730258186744747771317629869125⟩
theorem cell4_lo : Holds Q cell4 (15/16:ℝ) := by norm_num [Holds,Q,cell4]
theorem cell4_hi : Holds Q cell4 (31/32:ℝ) := by norm_num [Holds,Q,cell4]
def resval4Tail4 : Box := ⟨-3856792624737148521720025698065325708149667842497481300,9324369723442507903446992826979330930539214192688774659⟩
def resval4Tail8 : Box := ⟨-4673408193215193787855472143240605249465724172326539358,10292698594187550537661555136241611280523262565237805374⟩
def resval4Tail12 : Box := ⟨-5662839753681505256000588286052539900387602783461191902,11329844114194467016082774310616975837468117409342931092⟩
def resval4Tail16 : Box := ⟨-6861749006146633678511117824782514248969456593789106768,12431932977748482597413851524572324102196673314966517201⟩
def resval4Tail20 : Box := ⟨-8314485571075664442892522042390184842334352887613592066,13591775228564876986888870504472770052530513422513538263⟩
def resval4Tail24 : Box := ⟨-10074788548764916529402890530180407895596224995258975267,14797823253504745689886484465926724032600817340952558335⟩
def resval4Tail28 : Box := ⟨-12207774423883355157492372817219552802004385742358860630,16032865250987831684990506441462198803819641167700631214⟩
def resval4Tail32 : Box := ⟨-14792345830691440722293868918104016675738901738935269162,17272390095960719451213976088962568313875502177555438070⟩
def resval4Tail36 : Box := ⟨-17924110290462654478862686975506040517732808796624711681,18482546990774280584024588977683192275785647655909381918⟩
def resval4Tail40 : Box := ⟨-21718916889982681017654705837515884685983388165187699548,19617606118514473265078188586944975725105789911047145300⟩
def resval4Tail44 : Box := ⟨-26317141728645278800980499018949299704440356004008222551,20616805577542574044894455536339263811200959291201087141⟩
def resval4Tail48 : Box := ⟨-31888880659838230820497938284835882736106677958542658695,21400444358795058485806782976677212520139344964690713552⟩
def resval4Tail52 : Box := ⟨-38640241414611688733581869428686005130964846933088461685,21865050041390307575577771347619343611120401844185681297⟩
def resval4Tail56 : Box := ⟨-46820967863568957863358091671253042815567575046193050052,21877412025755402658792594877163110548156155855518981831⟩
def resval4Tail60 : Box := ⟨-56733678450882382218273767096926593932816693848003242122,21267225037853090238718307823863935327998451885766456496⟩
def resval4Tail64 : Box := ⟨-68745060532827923711247181398809366354130805328511336220,19818031551533819031866834632465418511214444481383535929⟩
def resval4Tail68 : Box := ⟨-83299214274087695553114838241167017047765243446420938142,17256080678674361769953791636586025824527078294107772157⟩
def resval4Tail72 : Box := ⟨852954291913572146844029855719331603456455167423711374105,727964169480963595361825560763855501166867296138708221⟩
def resval4Tail76 : Box := ⟨-51035741601764296325221426062431086731770557119301060,126358349465572021183406735382608241988090754484934872⟩
def resval4Tail80 : Box := ⟨-61805596588515368885815636490856781927189445085306884,139576506764436076785359778194296125181818348223721412⟩
def resval4Tail84 : Box := ⟨-74890778942181385733495744872458526613619230329184603,153760695946634800577084746465353371494833502983016649⟩
def resval4Tail88 : Box := ⟨-90746295202024936673730160889234841300840899085489404,168867128782993090614562266594797423948702879871009590⟩
def resval4Tail92 : Box := ⟨-109958665263026995171050165658690991780206865206304157,184809299589436174511405234203633354107927217310321798⟩
def resval4Tail96 : Box := ⟨-133238586098850933736436906134584075918147660194182543,201444234879920956379149538765063207113071716399472881⟩
def resval4Tail100 : Box := ⟨-161447220036328559286558219355076848041814647328468492,218555371881599362977374641605697263896983920853202534⟩
def resval4Tail104 : Box := ⟨-195628050556770952757207284214735407384163418561481929,235831112605661941524493669323244986919999740551191987⟩
def resval4Tail108 : Box := ⟨-237045482455696734984474712600154952065354709788816656,252838043173077526288992402445510690793045450115930826⟩
def resval4Tail112 : Box := ⟨-287231614243109866228336939680283920200144121927093826,268987581389385333976119935491691748205152477652958201⟩
def resval4Tail116 : Box := ⟨-348042912971868645437880585438909071973473257123903562,283494539105062238709269565082028660839862440166726662⟩
def resval4Tail120 : Box := ⟨-421728887988692213782575841828232979410278132359623286,295325748937831253339232318447655595389643643212390401⟩
def resval4Tail124 : Box := ⟨-511015303962113595612790313756127926753165357910100340,303136494394248927230919158166647916952778846457986023⟩
def resval4Tail128 : Box := ⟨-619205011373309724468237517855505540556779595743127956,305191982429019988913056369766841466656391365593156496⟩
def resval4Tail132 : Box := ⟨-750300124354525670647162709289407419293842441430876665,299270488737438348980833830039905996216184522952658887⟩
def resval4Tail136 : Box := ⟨-909150065469333449894090466552615164380244014196557720,282544065173408990187939281824456445290484428796129649⟩
def resval4Tail140 : Box := ⟨-1101631274416550779859931300607014284764952231505214710,251431782205551619961854020456953243582093780555148781⟩
def resval4Tail144 : Box := ⟨-1478340434494585765650603580733679104429921666565970101,196791932957628485058463960424101231292495389189714031⟩
def resval4Tail148 : Box := ⟨21392994719306754687309066990284281921568078354,45445164758893738183815724348188435005118240664⟩
def resval4Tail152 : Box := ⟨25835874168459958465511028049986658403010382499,49971479599474157451465791412792633937471341215⟩
def resval4Tail156 : Box := ⟨31305719902870632716047686358761739916219242740,54766790022438500814972630643073131760960501487⟩
def resval4Tail160 : Box := ⟨37933616660712166691767090563509742096652706051,59794067027054297084132693739073971793405343383⟩
def resval4Tail164 : Box := ⟨45964739908392337856279890209409341857590922772,64996357511788306686116049157158674467043854831⟩
def resval4Tail168 : Box := ⟨55696174022720496850760315696035056590404370595,70290288319189794832696944291119440789369704518⟩
def resval4Tail172 : Box := ⟨67487900659322224032678744024983874164465855765,75558527886028586516683745803480340855323902918⟩
def resval4Tail176 : Box := ⟨81776115062132474734760722593425239752447299511,80640388578141835775827194399325181537719983543⟩
def resval4Tail180 : Box := ⟨99089361638505739682405025334534354565760810193,85320140388090596965340162076863988534390772020⟩
def resval4Tail184 : Box := ⟨120068085680842695787856146402730404384929203061,89312510967246822800903178451008727212675247237⟩
def resval4Tail188 : Box := ⟨145488324484876358847245947238396797787606244859,92244730324778337736630583148257536521701264049⟩
def resval4Tail192 : Box := ⟨176290414237810430272849590162165361025271696315,93634336450141964016543511193042353113261598411⟩
def resval4Tail196 : Box := ⟨213613774591028523015134593325305717970372065470,92861785117273042208645945981580622096526526995⟩
def resval4Tail200 : Box := ⟨258839057655580271909724723571683177919652295099,89136696546751914297312236451513808123553311961⟩
def resval4Tail204 : Box := ⟨313639220580687408973003889373781190989607142003,81456315350238665257153033726635057446561845353⟩
def resval4Tail208 : Box := ⟨380041410973490967676354975539244236610838874756,68554448443192445467396528508946753861516148894⟩
def resval4Tail212 : Box := ⟨460501954558157645168542659792882305137668994298,48838766464416510007978933614713963028111460622⟩
def resval4Tail216 : Box := ⟨558004641005527210416518940971517487529553890557,20313552227075444929074357341101986565573779677⟩
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
def polyval4Tail5 : Box := ⟨1064751573367310965355344835250139415400468672053347280896,2152651865084970314814980790884766716109303272326306269758⟩
def polyval4Tail9 : Box := ⟨1290173112745282331898063754069695926702508536770647890167,2362900082488707686990764069726110374115569326016138115810⟩
def polyval4Tail13 : Box := ⟨1563322371424324899544766265386668315054706207629510609912,2584417505144806067252050936539728069548068131755851278407⟩
def polyval4Tail17 : Box := ⟨1894301480351783734030179336497249415848693747561591520765,2815088440194886618919230392299403737766899506131728548765⟩
def polyval4Tail21 : Box := ⟨2295353897605903626210556780045007653643831121584447351031,3051739720543705110558210739726047185285845447468585725681⟩
def polyval4Tail25 : Box := ⟨2781315207691329685346601302212229446021237971586375971157,3289834271037193135086074046208749775988701517193953882739⟩
def polyval4Tail29 : Box := ⟨3370161913857186389373956989465968757920864740161518685367,3523088630318029490632204032355387965540143864724169151188⟩
def polyval4Tail33 : Box := ⟨4083676418337853887423303235565662860867165991870900801705,3742996805778404613004431136765736919167801117614583688333⟩
def polyval4Tail37 : Box := ⟨4948252789018777237561492365700170426371324460879153788128,3938238912470338736348333223198841868744860438657805677360⟩
def polyval4Tail41 : Box := ⟨5995873119153286085724650188713947869798576146587068863099,4093948251861180582015690071344034050451783855116292656148⟩
def polyval4Tail45 : Box := ⟨7265290597272380765465230629425855910732511931676896525911,4190804644668912827855701189848497290321687845942618959093⟩
def polyval4Tail49 : Box := ⟨8803463050977383240025509274824624554514402956372147381241,4203914717815999770179515987052949335243233172664592179989⟩
def polyval4Tail53 : Box := ⟨10667289993743722014136641309671433335081862736457507004945,4101431184540572966362514898977082629968110412611163909595⟩
def polyval4Tail57 : Box := ⟨12925717430936631032708337828137593468125952571297314609830,3842852615917347364705855249320210118985391954965212396867⟩
def polyval4Tail61 : Box := ⟨15662288285253980601490376717283949694873897073781104858715,3376932377243111587359723303421896445203020816656142804399⟩
def polyval4Tail65 : Box := ⟨18978232786025243776559879648918362850275259740133314619875,2639109803280828664553311616793490959960983361117048510827⟩
def polyval4Tail69 : Box := ⟨22996213333905022870645686568632317173707143390913756730931,1548357708221838229472213779960871187752075431903313928863⟩
def polyval4Tail73 : Box := ⟨27968750000000000000000000000000000000000000000000000000000,2⟩
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
def resval5 : Box := ⟨105418443653449592969542424179097239571259245009794441935,13442717089005571407670788197353101623577765712431614722⟩
def polyval5 : Box := ⟨8865331104443694220281879135692912986122429079575274813486,3917353396818108422770385527679020643220091474524318857854⟩
theorem cell5_lo : Holds Q cell5 (31/32:ℝ) := by norm_num [Holds,Q,cell5]
theorem cell5_hi : Holds Q cell5 (63/64:ℝ) := by norm_num [Holds,Q,cell5]
def resval5Tail4 : Box := ⟨-15581183253823073673828621170210667214134218610800720835,13670978418400261590349381317867318757778571345873381181⟩
def resval5Tail8 : Box := ⟨-17131759141720824611287016283294035582185805280469460925,14022437728254048944522615042143279075466029193377483642⟩
def resval5Tail12 : Box := ⟨-18836568388695215619144040150596373226285898522599607266,14343269377425475982528079532358944292394221347575802614⟩
def resval5Tail16 : Box := ⟨-20711025970775587606006320217401353067338754760300512615,14626159530240643604210115325975584114233745692412408470⟩
def resval5Tail20 : Box := ⟨-22772013878038506097159318813760376896050861256002555832,14862789761900547947013316584140711824630960915551861887⟩
def resval5Tail24 : Box := ⟨-25038094046779780562415643392846366129931633265122776070,15043718495309528369808652185001976770417758473670306001⟩
def resval5Tail28 : Box := ⟨-27529675541783411631443520916810829543943672444773065260,15158250029170609485418207204481065572593151047737998893⟩
def resval5Tail32 : Box := ⟨-30269198367091413626175915728069263983077410353502604614,15194289284266254202906582259038721713431603153330379632⟩
def resval5Tail36 : Box := ⟨-33281335568075321386891392151894205784656813681913333967,15138180765403843985660088254131647748947729603671642704⟩
def resval5Tail40 : Box := ⟨-36593215445013782277371014144568687765732818448117962851,14974530081830852769469102345599484664475439735449669490⟩
def resval5Tail44 : Box := ⟨-40234665879504967973562357580387944849451610094023936144,14686006198392402597161863897052027616224173754316741647⟩
def resval5Tail48 : Box := ⟨-44238482974197994001994804343435785423124180841625567184,14253122401835947279834381667795673672316944508878201557⟩
def resval5Tail52 : Box := ⟨-48640726425301297866181405484149748361859145135280192713,13653993759715515834645687368877550546296761873300309805⟩
def resval5Tail56 : Box := ⟨-53481044288090101073392834663906536094793007334703853638,12864068621386828379951225673585965882729094574019018084⟩
def resval5Tail60 : Box := ⟨-58803030060350421510726027599438584264927353639910494090,11855831459496745688711254417894452356727395555171198916⟩
def resval5Tail64 : Box := ⟨-64654615287650361407197837954553711418168502347419085234,10598474073439581168532956967775508146661455570016574165⟩
def resval5Tail68 : Box := ⟨-71088285754054852288229926556084779895582185381193011846,9057527385736550624049866523179202148301117660230847617⟩
def resval5Tail72 : Box := ⟨852997911253875131517785529036970915222801543091483406828,730431536683078919649494787965386325680117856324879653⟩
def resval5Tail76 : Box := ⟨-210725267707188983499287584647012750982694771901148197,188048225366315859122898619426971888104490966141041722⟩
def resval5Tail80 : Box := ⟨-231662996662195622779038428554744238450999442860096911,193007648264178803970101384882920127735006443816091932⟩
def resval5Tail84 : Box := ⟨-254716156831699258355491307207199407130010125956250755,197566503691721468072144150321890529748818317647106545⟩
def resval5Tail88 : Box := ⟨-280063376217894225857519025739506395745502171173094635,201626630419015650446050947305105390594014897099126766⟩
def resval5Tail92 : Box := ⟨-307932938665776492730663113638866817062310128117142658,205076475017709979301638173162318229647387968019574117⟩
def resval5Tail96 : Box := ⟨-338575846638255055125291307552487622523886012688413536,207789356919425800080255768465967626196489328832081037⟩
def resval5Tail100 : Box := ⟨-372268080262865152353307458068206520090716317831685169,209621701281771449927982765416011132416306599288578124⟩
def resval5Tail104 : Box := ⟨-409313082898869481577107862211538598126249870858191127,210411079001054089432804276687227988225119466682713291⟩
def resval5Tail108 : Box := ⟨-450044494048148812471824037982538217418095577097604814,209974033555264167106418124482318174524958502053822278⟩
def resval5Tail112 : Box := ⟨-494829154222506444521005123517243571484724705773167373,208103672285755836809912239244127470399704561378959108⟩
def resval5Tail116 : Box := ⟨-544070408830209404523152635629008677186606663881518684,204566997421202128756251104796788394285400164574770227⟩
def resval5Tail120 : Box := ⟨-598211740837657346502863540303669623549532250580801521,199101949608201155940583524371938357374119270128478505⟩
def resval5Tail124 : Box := ⟨-657740764923127285715435763197408715619028546265484698,191414133915719864457317195139166430543228644174461172⟩
def resval5Tail128 : Box := ⟨-723193619095259221539164333833559171557844173528348405,181173195199367063091663033866497645384706198474937182⟩
def resval5Tail132 : Box := ⟨-795159793328681558181032055725033792015575763296763116,168008806317656197530640514618455347415169501154969414⟩
def resval5Tail136 : Box := ⟨-874287438740580760564371919397461254127001769082218148,151506228952698804591461882610867692985392733078574973⟩
def resval5Tail140 : Box := ⟨-961289518562587871815459676698278472541314074962375161,131201390331853254996055335520767223801497137009055676⟩
def resval5Tail144 : Box := ⟨-1197057145501687122811574008870794148405299537795036373,103162278713694142802834020938207138442609448327873527⟩
def resval5Tail148 : Box := ⟨116893724974162026977929382374979402902264996049,87870105704009611383839279677993013619200442074⟩
def resval5Tail152 : Box := ⟨128447733563892400384245245366350616339105737975,89553467953157541140798648797425540102779355217⟩
def resval5Tail156 : Box := ⟨141229775221821151699368841156158403600978771837,90945828120949176743052787106119774836170652770⟩
def resval5Tail160 : Box := ⟨155283780044139930709437308651338464650732147720,91987843824229768546431085001498594058462732610⟩
def resval5Tail164 : Box := ⟨170736321763541867260512671749087113040552587617,92612863466484533250391597070294900294901023747⟩
def resval5Tail168 : Box := ⟨187726571062718808362211436456398510467310412452,92745535992466723216031906464208086860740199067⟩
def resval5Tail172 : Box := ⟨206407547725976895068882554463857051617760810191,92300810787700094401740828850318962615251081822⟩
def resval5Tail176 : Box := ⟨226947498785441263091657623041349340979369825181,91182829334421269830917292289684337627781943007⟩
def resval5Tail180 : Box := ⟨249531413809272306151745534015602924142341456515,89283697268436043734885019518863171823540887203⟩
def resval5Tail184 : Box := ⟨274362690978679638138870920648935476049843060504,86482124330309305022329755387927242028999537255⟩
def resval5Tail188 : Box := ⟨301664968958971719441519787565810675239932287581,82641918420424080562642694434240833253031960075⟩
def resval5Tail192 : Box := ⟨331684141063075507404178015336799072208495831457,77610318553233914436384508807520815731700939205⟩
def resval5Tail196 : Box := ⟨364690569847746554262876388967863253008657534538,71216149948366715708390435796957653321807974557⟩
def resval5Tail200 : Box := ⟨400981522087852839417598223717063309833474158647,63267782780664787566947136209939236228253278610⟩
def resval5Tail204 : Box := ⟨440883846058913294712340477796895975862318210932,53550874221862718810481554329529997263346443623⟩
def resval5Tail208 : Box := ⟨484756915240433878913536707302555116170355063415,41825871325911996346684360519479151618017237009⟩
def resval5Tail212 : Box := ⟨532995865103933254667210633601606875311826308715,27825250011435974031162815559197051019672616346⟩
def resval5Tail216 : Box := ⟨586042404110149086496183460577525414138108772560,11250184932163073447704206370505907620454991747⟩
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
def polyval5Tail5 : Box := ⟨5555180262354732226852705456046239831111784387475366052173,3995894091538352095940647815902965083891582657676035845240⟩
def polyval5Tail9 : Box := ⟨6107982979884447669408953627864210126044821860802058927433,4064098448172911690365619529472634687245679356975578175562⟩
def polyval5Tail13 : Box := ⟨6715798308416349690121845423052288631521083273812061305351,4117670223921578127933922454003636543982930243826343043807⟩
def polyval5Tail17 : Box := ⟨7384098329901991442577329290724431979345728525235337198165,4153760590477082899931348899233786412204913272866438364951⟩
def polyval5Tail21 : Box := ⟨8118901974368581052041682188063220929652791896050850399801,4169146684212273844578433932587164964577531623261333305330⟩
def polyval5Tail25 : Box := ⟨8926827125591778775166455939294027029709332582536427933219,4160188487759974965100980425523389251352224335189592582675⟩
def polyval5Tail29 : Box := ⟨9815150223734367868132065892292333218748025387259194233955,4122781047762772033089638088276986123798093905314515796564⟩
def polyval5Tail33 : Box := ⟨10791871799364145404105754350147275183482516353269247545175,4052301530022130579482595448315934359094972598519046510817⟩
def polyval5Tail37 : Box := ⟨11865788528868781595036802669401582117048840944162594817278,3943550571796337782343957625573085053063007851883170459327⟩
def polyval5Tail41 : Box := ⟨13046572460222302419469278307223376903547964127791978919420,3790687335514159535848304176413602863118618863766165178577⟩
def polyval5Tail45 : Box := ⟨14344858122636556744056202737342833501066557194012726806752,3587157607053023602155005562637359849766595629031868076239⟩
def polyval5Tail49 : Box := ⟨15772338304635895938573499697834693249065296934012352204240,3325614214411139245397641137171597301191468552581081978749⟩
def polyval5Tail53 : Box := ⟨17341869363163970112081227403582826721579133061544433607623,2997828968457381801659939964069551778203712157131689397171⟩
def polyval5Tail57 : Box := ⟨19067587012171161376632970991969801071121388579831891629322,2594595245783457617878799761155868745515728223070486535586⟩
def polyval5Tail61 : Box := ⟨20965033633512852562707131236531111534654896999212317760951,2105620243753313151733967474674762148991511040349140732462⟩
def polyval5Tail65 : Box := ⟨23051298256784717662628771363617782211124914845305181606424,1519405838811545192691298734789117892760676481705650795018⟩
def polyval5Tail69 : Box := ⟨25345170657502487808956004467863454459143591347407799156126,823116863128222323594055310781496946859382638123123660024⟩
def polyval5Tail73 : Box := ⟨27968750000000000000000000000000000000000000000000000000000,2⟩
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
def resval6 : Box := ⟨90778894636815230551929220995630281503841464959245652056,11911522872412373786307224661769991120095689757985702174⟩
def polyval6 : Box := ⟨15738870002026180755306150602942732292960687879861280694391,3920561195393870112496512858700094978828740052962505888453⟩
theorem cell6_lo : Holds Q cell6 (63/64:ℝ) := by norm_num [Holds,Q,cell6]
theorem cell6_hi : Holds Q cell6 (127/128:ℝ) := by norm_num [Holds,Q,cell6]
def resval6Tail4 : Box := ⟨-30193904000698327265202640827680104207285610844278914514,11668815079488358697361331999446582675213491014299541696⟩
def resval6Tail8 : Box := ⟨-31651764217148128167938206864214793397046641760800921416,11545182864886956905808272113505668360788821488474534225⟩
def resval6Tail12 : Box := ⟨-33179947807020720260744622177914119398315014120835922319,11393686864634244856597334662925451234200189506640695714⟩
def resval6Tail16 : Box := ⟨-34781913850605151371538023171574478602019721153596644661,11212283464667874847186801921850838205265048415872584064⟩
def resval6Tail20 : Box := ⟨-36461224657342337127352086612293693775849443977307051968,10998808661888318961425063386644165840882969629842739846⟩
def resval6Tail24 : Box := ⟨-38221614521365907221836284095038325526810050223502117135,10750971025083519062866616339770852712759409827844471915⟩
def resval6Tail28 : Box := ⟨-40066998032818510068469763526614445607311676455555000969,10466344811096390830284420519758233976814732728883445089⟩
def resval6Tail32 : Box := ⟨-42001478782757401738811035567669016065467958745288765553,10142362725438929886597991727478797132034963000349264485⟩
def resval6Tail36 : Box := ⟨-44029358488336017705852720922426684409214075906108855216,9776308309329862397427916920410744014585213539316271347⟩
def resval6Tail40 : Box := ⟨-46155146558559780613874480848919554923281404834683819681,9365307934352492220974304939154792601941686264952798827⟩
def resval6Tail44 : Box := ⟨-48383570121887600635892705505612071289973130190747118826,8906322384997270100717438279082724896615144186302765432⟩
def resval6Tail48 : Box := ⟨-50719584537977509961812362472857502747756471222746805930,8396138008375552956964227571690435815597937237103579475⟩
def resval6Tail52 : Box := ⟨-53168384416951466815249813658097725795123774880398965955,7831357409364938022320009059970806925812902353347353603⟩
def resval6Tail56 : Box := ⟨-55735415170682913655001876390299780735520398713840325252,7208389668370102222734392300877579716662311908606102087⟩
def resval6Tail60 : Box := ⟨-58426385121786116962432862747658309341159517476951403739,6523440057753424248973074265828100081465996780853804790⟩
def resval6Tail64 : Box := ⟨-61247278185240629667566069697390498013477275373543371879,5772499231379147355567790410136119143285992431052700823⟩
def resval6Tail68 : Box := ⟨-64204154081055058764029768363402216283278904589782816684,4951326607511479006675384842617466281946995303518361107⟩
def resval6Tail72 : Box := ⟨852893283946634972071747127700324893976659397194805444487,678037146589170610777175390258917654037470214243293270⟩
def resval6Tail76 : Box := ⟨-411818390671126644580613121705958869701897276396932676,161406927345978027815226635503512856977280682792145025⟩
def resval6Tail80 : Box := ⟨-431671077156974793962218585810889183416616176653930984,159792886148538081851792568398497084794005244688578355⟩
def resval6Tail84 : Box := ⟨-452512651627331279085106096451957416974821929165492004,157801278585271971896615266207497415116817057017112669⟩
def resval6Tail88 : Box := ⟨-474360482925366637425841926128805554681489697993808105,155404164655940735632582622379467598202633307234005656⟩
def resval6Tail92 : Box := ⟨-497263152648691173264973762650923271083415917372321868,152572107060413784762754236592513544033502862639460962⟩
def resval6Tail96 : Box := ⟨-521271589608827182120731493068133205261060199532593597,149273933044826137565331717794859770289476542242788448⟩
def resval6Tail100 : Box := ⟨-546439181519814855331620627772257376674117505883333334,145476640579675399959380076515131264196741779873572828⟩
def resval6Tail104 : Box := ⟨-572821893715937067609792978026002415042295585460041981,141145299707399852225686413755740936594540120742654223⟩
def resval6Tail108 : Box := ⟨-600478393602187016145416704083382653291300369480656374,136242948797611437191026428127597611233189064352177668⟩
def resval6Tail112 : Box := ⟨-629470181113350004647820808866674293879789069629621179,130730485453608152023727665198031568274168798115241412⟩
def resval6Tail116 : Box := ⟨-659861725471799771110100819104871108240179328812998115,124566551801093839339989500943454920588604407381944792⟩
def resval6Tail120 : Box := ⟨-691720608548118521188453471761508591161967239691045971,117707413876697190430594971944944440213448387061601800⟩
def resval6Tail124 : Box := ⟨-725117675143332592018992520781150012896700189994243006,110106834819890643991407211659841326046030677268082157⟩
def resval6Tail128 : Box := ⟨-760127190526947469416148000417154829673392628013587934,101715941557231863580211730296939267653682277099896457⟩
def resval6Tail132 : Box := ⟨-796827005581135721193461692688013304990517945420412704,92483084652450016704856022804656683684591140383242091⟩
def resval6Tail136 : Box := ⟨-835298729953464595882851123768385969124758739253950665,82353690978129903591138043278102414931571543326979397⟩
def resval6Tail140 : Box := ⟨-875628223596140905351256864273177003738494184161850804,71270097768840517079285983784525688322353999125262806⟩
def resval6Tail144 : Box := ⟨-1056386891251855944674485242816723773024677417658006136,56331610423599771080680806861458042284964531510944838⟩
def resval6Tail148 : Box := ⟨269383002725400322847227159197739497496196496299,86716339495941163174410231421988819695334250101⟩
def resval6Tail152 : Box := ⟨282314528755208093822848983905871123771566956256,85059764332858397361444198580513299458502449424⟩
def resval6Tail156 : Box := ⟨295944997593950703938204849795138131728192081621,83137520365803367129115341168223028746390541652⟩
def resval6Tail160 : Box := ⟨310233562472217329097843332494723980626562212067,80930323045012203778067369431880271986563910670⟩
def resval6Tail164 : Box := ⟨325211995697882742373661832770846065203261162503,78418290807035543817240614908495689195468832584⟩
def resval6Tail168 : Box := ⟨340913604907823057976694288985716231881049323361,75580387037828381038302816882623505477133045893⟩
def resval6Tail172 : Box := ⟨357373305870352711510712719523317217560161226444,72394358070075226126426266769402315853773978949⟩
def resval6Tail176 : Box := ⟨374627700127241069307767577855959959147470224552,68836668004422770245893173530360757914777518696⟩
def resval6Tail180 : Box := ⟨392715156384793086567061823645968547963432951890,64882430179271674656018471356303311475287247604⟩
def resval6Tail184 : Box := ⟨411675895834585667295417146413428808775711349920,60505335120789644058465469292954698829665545708⟩
def resval6Tail188 : Box := ⟨431552081593587315692592972234520254541357584212,55677574796480267342722090588293974802564160904⟩
def resval6Tail192 : Box := ⟨452387912462549638080635580520374523514100613988,50369762986898138640265584324827716304813083484⟩
def resval6Tail196 : Box := ⟨474229721211161827128602660595950331242001380889,44550851580927781584972152232469340406066380812⟩
def resval6Tail200 : Box := ⟨497126077608525452724185039414974727957194655416,38188042590420977055956243502185832474370213096⟩
def resval6Tail204 : Box := ⟨521127896428059196142884332357890818742655797229,31246695669892283670983719305740940297213577398⟩
def resval6Tail208 : Box := ⟨546288550667058200462796429877521560676069349873,23690230916379852878207477324620765621909344991⟩
def resval6Tail212 : Box := ⟨572663990382983489946147997824112752060434237712,15480026706799601369786488048539037025050109711⟩
def resval6Tail216 : Box := ⟨600320037251988273382633222324695305871282923606,6575064229018912169631687779146281086971859211⟩
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
def polyval6Tail5 : Box := ⟨12502340646969372138974120292147824412159893462559106208134,3847746349003352237351276075976757485917323908498174324695⟩
def polyval6Tail9 : Box := ⟨13105965830165856133283832173100627849286833285402940521043,3765196592253731820630255587846634869530969283055693623244⟩
def polyval6Tail13 : Box := ⟨13738736934666442842090143727883735392441893782410286925078,3670109777101712321059637868936249992892139017284898837665⟩
def polyval6Tail17 : Box := ⟨14402058956116882495098838706256345472109639154806736613259,3561608054450294909261501288286240061890388837532821214273⟩
def polyval6Tail21 : Box := ⟨15097406927713676704241538306492151317488164983967373152880,3438762515860434561102111076065105455191261047359877625971⟩
def polyval6Tail25 : Box := ⟨15826327099165855315200626714811944548844563874815287423873,3300590441599794458461626420830052920359122242400632063268⟩
def polyval6Tail29 : Box := ⟨16590440374897057051113652266899666024464379913656944481762,3146052416933414621255147251569450479207114970350879399416⟩
def polyval6Tail33 : Box := ⟨17391445918460852808433547954988847907545082490500123028549,2974049300084609129652150421462665176508489849494137195670⟩
def polyval6Tail37 : Box := ⟨18231124930981551589732648499080457477648525586471172552159,2783419034412187703478032932438356069502044003199826369554⟩
def polyval6Tail41 : Box := ⟨19111344612022475046915703918552570432880498471279923693129,2572933296983217777324088015261723489232450072343784074580⟩
def polyval6Tail45 : Box := ⟨20034062311689508101397754699743894916957871939848386036439,2341293975333408737670199225412226959074845870269543649229⟩
def polyval6Tail49 : Box := ⟨21001329883202984722725812734469083805064326659346468686099,2087129463801067396731774234987946389046723122574946609847⟩
def polyval6Tail53 : Box := ⟨22015298245616750666194613973691332855833703946442810889133,1808990770394518867968006823417199491186750591460899764490⟩
def polyval6Tail57 : Box := ⟨23078222166830550678845131212218434572210061369543297371046,1505347424705937914610543423050118912145749015810280098504⟩
def polyval6Tail61 : Box := ⟨24192465277531777038595786687141986871043575509989314780558,1174583176915672215456405752540726351343705143389855060715⟩
def polyval6Tail65 : Box := ⟨25360505327238165206950852864487750141169017410719675771005,814991477438321867335316067907690705771809785236467034001⟩
def polyval6Tail69 : Box := ⟨26584939880760942127811176247423400325340881005839506469520,424770720065682711487321319912189231232168133590009467936⟩
def polyval6Tail73 : Box := ⟨27968750000000000000000000000000000000000000000000000000000,2⟩
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
def resval7 : Box := ⟨74083171432429553136985599775391869036819530457176890326,19106050754217241957226797935329664058961533154644063254⟩
def polyval7 : Box := ⟨24837219188440572921758134413062747585599853764345141621570,6847996280868900973909699718342681175841787247790742818342⟩
theorem cell7_lo : Holds Q cell7 (127/128:ℝ) := by norm_num [Holds,Q,cell7]
theorem cell7_hi : Holds Q cell7 (1/1:ℝ) := by norm_num [Holds,Q,cell7]
def resval7Tail4 : Box := ⟨-46211949236119582468207670593217173834567542255196475263,18243162339742693875514694038526768766673851074846988608⟩
def resval7Tail8 : Box := ⟨-46941179582449569204095158031415066073196035361179337048,17513992326501930021976657953816887507330188164927895546⟩
def resval7Tail12 : Box := ⟨-47681854519658127051802784655366084676860991174509758166,16773317396545810051086185906040123339723268979815740362⟩
def resval7Tail16 : Box := ⟨-48434216402342542664479057584737808818516641630980425644,16020955513867919534956110991602938553693482958544324727⟩
def resval7Tail20 : Box := ⟨-49198449643804667284115533840746604859565686119313860074,15256722272405820434746649950082033507709677128820345099⟩
def resval7Tail24 : Box := ⟨-49974741559706834192327418855290636584455730288912433214,14480430356503653857244213151426591696289913537994337190⟩
def resval7Tail28 : Box := ⟨-50763282421318836619008757391076172654669194761434195284,13691889494891651442340328942559178691397693214449166458⟩
def resval7Tail32 : Box := ⟨-51564265502160505557104612372249535287770559377051422907,12890906414049982505185756860375441135800895042036297171⟩
def resval7Tail36 : Box := ⟨-52377887125373602637667003635269048473860749540002926174,12077284790836885424700764147913433237794815952265846495⟩
def resval7Tail40 : Box := ⟨-53204346711841158921358388617313922658474978278615485778,11250825204369329140812599474912521753949782061943788527⟩
def resval7Tail44 : Box := ⟨-54043846829066078245948621232000794674526550872701348830,10411325087144409815018627154133090126777500773266416943⟩
def resval7Tail48 : Box := ⟨-54896593240820985686021110280743306576685884366152496974,9558578675389502361809414745760202727628938187189838986⟩
def resval7Tail52 : Box := ⟨-55762794957581490180445387437184643546562459060380488339,8692376958628997512784305803502955256252377727029659044⟩
def resval7Tail56 : Box := ⟨-56642664287755198199129720766576633960169745549545276584,7812507628455261458673880788837518991452909692078530688⟩
def resval7Tail60 : Box := ⟨-57536416889711440236241226899070751845960911302501796412,6918755026490891286529363446855181578072566678187166491⟩
def resval7Tail64 : Box := ⟨-58444271812714151025841794309620296706899015215962024195,6010900091107006803961842309186619077768904001227884235⟩
def resval7Tail68 : Box := ⟨-59366240029110697548657177434415447689094866563164408247,5088715088712434184697528132584111140481240730166054207⟩
def resval7Tail72 : Box := ⟨852727951220362419618249506862124831763075991704026127619,775509757607767995353673594430575336974341122900308848⟩
def resval7Tail76 : Box := ⟨-632384720066416868250826987009367983079210126280515985,252022926755461917028168930199970936740996088491151799⟩
def resval7Tail80 : Box := ⟨-642333560793882306895439151340470896290404869275477879,242044970142623177292739898666637830427109743885384683⟩
def resval7Tail84 : Box := ⟨-652468804404058687341045024564082793155952014279592083,231909724950487580689705510791637176261395439820539660⟩
def resval7Tail88 : Box := ⟨-662763971464406726905265836305012016384772586875972282,221614557889240667083721361633388160565661148614558841⟩
def resval7Tail92 : Box := ⟨-673221583786011673996915514782279008371787033411650260,211156945567633236033817753252475301077791181779929844⟩
def resval7Tail96 : Box := ⟨-683844204557350216489679948610547608346202478274280585,200534324796294669126181315501594190816492465441542590⟩
def resval7Tail100 : Box := ⟨-694634437411796831080408687058035500272804626022079636,189744091941848053830214017915932986121697732746871880⟩
def resval7Tail104 : Box := ⟨-705594927064907907129356208202774934195991044028300509,178783602288736977729756355943440978636971623743701236⟩
def resval7Tail108 : Box := ⟨-716728359962646426699557335179099838584931922159256449,167650169390998458151885290974655682233627280051670843⟩
def resval7Tail112 : Box := ⟨-728037464939837189591985906045823349330284446506161430,156341064413807695259200673630656535104745477496188980⟩
def resval7Tail116 : Box := ⟨-739525013889011684807552038203555105857863205107945888,144853515464633200054174341476262244094814074186585088⟩
def resval7Tail120 : Box := ⟨-751193822439806524139382979350466400893671084180804895,133184706913838360836539840821957211028968091854513742⟩
def resval7Tail124 : Box := ⟨-763046750649081962095768799045172475965502166374199994,121331778704562925449947351318699774274041729089997316⟩
def resval7Tail128 : Box := ⟨-775086703701929810338622648991676887908977467889720399,109291825651715237006359291410070658704882031321387371⟩
def resval7Tail132 : Box := ⟨-787316632623777572350230120346649741384624369037441989,97061896729901323483435888258493509705182813673280296⟩
def resval7Tail136 : Box := ⟨-799739535038677887847897116582787468538527224445263124,84638994348514592167762270285042997886401265260637315⟩
def resval7Tail140 : Box := ⟨-812358763711808532970441524083657068903493101299196298,72020062634730111365463516766689976223367420141080891⟩
def resval7Tail144 : Box := ⟨-962596061558922947175182617845252058998814423472714857,56388940688449026852958050633224818472966338126722174⟩
def resval7Tail148 : Box := ⟨467475353385629028965051167107158536037399190706,149163913300272354567433610917564870247094343376⟩
def resval7Tail152 : Box := ⟨474779287500577177476665571823144636847786497898,141788341865853631715151459995381788086940941820⟩
def resval7Tail156 : Box := ⟨482270728027550322544062916293213910758303126760,134296900059249658065166955986328969777967245443⟩
def resval7Tail160 : Box := ⟨489880375691947801652087920024931440403056025206,126687252394442881215053499805683450901297036665⟩
def resval7Tail164 : Box := ⟨497610094375402870563487092978752396038590216499,118957533710987093691668570253213413317250744226⟩
def resval7Tail168 : Box := ⟨505461778652685436823539928477033303866816826927,111105849433704522664430954472660516768621403537⟩
def resval7Tail172 : Box := ⟨513437352993065517098983590428309626142210065043,103130275093324442292250127120879403899183666118⟩
def resval7Tail176 : Box := ⟨521538772231606803275805122885910584090260765285,95028855854783156110261147185764630104179567405⟩
def resval7Tail180 : Box := ⟨529768022048301395946332278672033141278623311812,86799606038088563439114410419422672734064419570⟩
def resval7Tail184 : Box := ⟨538127119454765391997178599340173419998472635148,78440508631624567388164357821532946871323920851⟩
def resval7Tail188 : Box := ⟨546618113288613943025555313696198679449971998501,69949514797776016359942763906186446773692063885⟩
def resval7Tail192 : Box := ⟨555243084715636953160126460673099738361858157448,61324543370753006226937049555856755547609233713⟩
def resval7Tail196 : Box := ⟨564004147739898500872318486444161366856229622587,52563480346491458539175520087261987583752394585⟩
def resval7Tail200 : Box := ⟨572903449721885012436168807754947384193232218583,43664178364504947915207517821741703364620650128⟩
def resval7Tail204 : Box := ⟨581943171904829300101135011119231228837539818928,34624456181560770937315159191457892452983504904⟩
def resval7Tail208 : Box := ⟨591125529949392593385452533277213206015786404910,25442098137048285445310670260459781785834497725⟩
def resval7Tail212 : Box := ⟨600452774626082122984802175271886188243676377463,16114853603297265684393244243841590498487443055⟩
def resval7Tail216 : Box := ⟨609934308778399888309488449264403288145387951700,6640190549631951916931944818917334747052751378⟩
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
def polyval7Tail5 : Box := ⟨21356995953775136272725759258479524957626457088986602648772,6514270108015351839672200917608746822925949573572409731147⟩
def polyval7Tail9 : Box := ⟨21693981335271737774063128084141241242437501662447835475719,6177282616274010113281719737894549688996120902936020611372⟩
def polyval7Tail13 : Box := ⟨22036286071417945665597666186244794623010347764091288481795,5834977879921955663234413959742815157619292572265478598198⟩
def polyval7Tail17 : Box := ⟨22383991961696856630746770584703854825490529043596887139975,5487271989642882036995789426380134036842389636034272739019⟩
def polyval7Tail21 : Box := ⟨22737184229568908657386451715473335211681065315784071678228,5134079721770829440939561169495141742434400323117659518040⟩
def polyval7Tail25 : Box := ⟨23095949443423879073904502731193557142662958577081598455192,4775314507915859017712835861021748411803802141567170839586⟩
def polyval7Tail29 : Box := ⟨23460375537595991696205387695123133684882243867804318265557,4410888413743746395188514641401825887492770563577083741881⟩
def polyval7Tail33 : Box := ⟨23830551833916704688199367778703075552441631065083129278992,4040712117423033403176335931948519311111013552530302058937⟩
def polyval7Tail37 : Box := ⟨24206569063607734989431159845512269190062843459074097622452,3664694887732003101941673959289829738285355128917623579068⟩
def polyval7Tail41 : Box := ⟨24588519389519528670854244715827332423873384910059108953862,3282744561820209420518717850598803683318369115554568347739⟩
def polyval7Tail45 : Box := ⟨24976496428720627409517319416714747020333124274860779699660,2894767522619110681861320647703152879944939769067288461973⟩
def polyval7Tail49 : Box := ⟨25370595275443467792258489182283550375162177209491386672989,2500668675896270299182908610535002530833051522667589413876⟩
def polyval7Tail53 : Box := ⟨25770912524392237527672811245036961346609726123762338589212,2100351426947500565242714305375344745257390571639993442371⟩
def polyval7Tail57 : Box := ⟨26177546294418501480386394754166359568765634407140216901661,1693717656921236708169140819286941955805157699703127537386⟩
def polyval7Tail61 : Box := ⟨26590596252570422132241134935921083730689587842148724407988,1280667698769337008216830835418636315534613110944774437686⟩
def polyval7Tail65 : Box := ⟨27010163638543370046871115118332089128401124583828364711336,861100312817449823579357348465699635075120401307656639943⟩
def polyval7Tail69 : Box := ⟨27436351474813701460439944290256913480785820299169413092740,434912655824826036747778790587501552269019940889061001136⟩
def polyval7Tail73 : Box := ⟨27968750000000000000000000000000000000000000000000000000000,2⟩
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
def pend : Box := ⟨1031681434145528796543091972753308670123774969842289020804784,3781323780677352575861378096758637666671169846863635199⟩
def zend : Box := ⟨1003808114423033732850957031250000000000000000000000000000000,2071370323400658417968750000000000000000000000000000002⟩
def betaquot : Box := ⟨428761840125089472572403828624619504127560977951182897185025,394794667521041789451247618379440793007517949699090841⟩
def crit : Box := ⟨170289679690895129276934058298298855193491849691490590025,9293427628588179345137874583655968938408943059431948673⟩
def subsonic : Box := ⟨397470283853314614542126609789661210616370635164555025460,4534603599887159603926561513850740465193894373501352096⟩
def pendTail4 : Box := ⟨27869608968432547751611743801654417116458878544458481366584,1618602670327078363867637053301292382066958116336842902⟩
def pendTail8 : Box := ⟨27869645467468964134540437941706073045512137004887349301866,1618482265952775415601801529410496864938958748324759140⟩
def pendTail12 : Box := ⟨27869645469088508318305702608537417326635457442949716692476,1618482250422343959985006456285037771540706091147497704⟩
def pendTail16 : Box := ⟨27869645469089326873116703095894126909572214644224580046769,1618482250409227451843028514147580694622259078230929284⟩
def pendTail20 : Box := ⟨27869645469089328895695579704610306335594669914274837788773,1618482250409178156397671185158728257863915337812964566⟩
def pendTail24 : Box := ⟨27869645469089328913408544324566366590405116420850448446175,1618482250409177504405310001874516117502990042099727324⟩
def pendTail28 : Box := ⟨27869645469089328913860665530297193217067183849508756867324,1618482250409177478330150606559076427860692225817719696⟩
def pendTail32 : Box := ⟨27869645469089328913889398975820582581629197448756986329939,1618482250409177475454885800123961246772882206462483187⟩
def pendTail36 : Box := ⟨27869645469089328913892967302343524641068470307485072241051,1618482250409177474625826924197544866129291705728547729⟩
def pendTail40 : Box := ⟨27869645469089328913892837549692305116661054082807040190776,1618482250409177474016003585535623437879154199528122071⟩
def pendTail44 : Box := ⟨27869645469089328913888425892788056092021575516741453497006,1618482250409177472873525514343275531659720863242753249⟩
def pendTail48 : Box := ⟨27869645469089328913850324200727942015391847084238550613181,1618482250409177467306438982490888950949755581659771562⟩
def pendTail52 : Box := ⟨27869645469089328913162291464926547328554089365626472274850,1618482250409177393323263904134844142537513498669324144⟩
def pendTail56 : Box := ⟨27869645469089328880157840465998244375769734640171532616877,1618482250409174704829764353880356429470923593217813866⟩
def pendTail60 : Box := ⟨27869645469089323785104515922322900253713073325150598913634,1618482250408872396550054383487408821641217512431905424⟩
def pendTail64 : Box := ⟨27869645469086015305972795936377266318479645127407140614517,1618482250263164913911974650940813465642013280191260454⟩
def pendTail68 : Box := ⟨27869645454205417417796072488940281777257239433992568416600,1618481770317089656684661340422872117609978511335629897⟩
def pendTail72 : Box := ⟨27867850972816212026428219649216374460490653011090579852449,1581228777913881245873240374276938571515765210949926976⟩
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
end SepticProfile.ExteriorCertificates.C31

end
end

end OAI
