import OAI.MathematicalPhysics.Transonic.Certificates.BarrierData10

namespace OAI

section
noncomputable section
namespace SepticProfile.ExteriorCertificates.C10
open SepticProfile.ExteriorJet SepticProfile.FixedInterval
def cell0 : Box := ⟨250000000000000000000000000000000000000000000000000000000000,250000000000000000000000000000000000000000000000000000000002⟩
def resval0 : Box := ⟨109474205405326573371796773703743228542590665570010879512,363098636350392360961200008173726941822182429404456707⟩
def polyval0 : Box := ⟨3764871751711487558194594655545284515371005354861191784553,15628856560182167485573530884851255849888339383857974831⟩
theorem cell0_lo : Holds Q cell0 (0/1:ℝ) := by norm_num [Holds,Q,cell0]
theorem cell0_hi : Holds Q cell0 (1/2:ℝ) := by norm_num [Holds,Q,cell0]
def resval0Tail4 : Box := ⟨53864113215121200397911732886173769245141261142203,1711547704707907946421059384155715122946068466499⟩
def resval0Tail8 : Box := ⟨6241440863720340603864293737286187058257361674,354032977372552134682231345121618770430324145⟩
def resval0Tail12 : Box := ⟨5439614170020486494870564431280644806551053,465978043713460632793995276709659388825887⟩
def resval0Tail16 : Box := ⟨20875304473409288013652790999697043874456,25495418107105937165221587016770744038791⟩
def resval0Tail20 : Box := ⟨272581072403869951872574285669657250407,367543565738475313511517311127385252586007⟩
def resval0Tail24 : Box := ⟨10393912592197310992899328616810435855,5879970976554423940650792609165490000955547⟩
def resval0Tail28 : Box := ⟨1053262733301635388517195372068796878,94079497864470771664043109137209936808371024⟩
def resval0Tail32 : Box := ⟨265987136660768861499717983280646135,1505271960586699751127281838350652305652237280⟩
def resval0Tail36 : Box := ⟨-370197165193144213982676973740345400,24084351367318955472863977959569086326370264091⟩
def resval0Tail40 : Box := ⟨-137145166130403645857377594150047189703,385349621747599503869250916722409523622378805464⟩
def resval0Tail44 : Box := ⟨-35172450195934042139892533095615354236306,6165593914985338271368090862025496502851782263989⟩
def resval0Tail48 : Box := ⟨-9004376846859767504507242854843973618887944,98649494198149069014483937676066072164469166672915⟩
def resval0Tail52 : Box := ⟨-2305122512276736033733856549387836673282632101,1578389746117781354012128384402621585325639149718158⟩
def resval0Tail56 : Box := ⟨-590111403848261724623857337500082278179363926409,25253682708427354516326772878795797278583435442565179⟩
def resval0Tail60 : Box := ⟨-151068518400955338545737208089380778876395116436378,403917296594715183044946645948798280038583927417437605⟩
def resval0Tail64 : Box := ⟨-38673532471774564963008184109592745014862234224650937,6426420302932432299820770885413287265018460846134703515⟩
def resval0Tail68 : Box := ⟨-9900231728560722263322666611377365426631248275272802297,93541154330071408039803686047994827744728801628546270187⟩
def resval0Tail72 : Box := ⟨752695102077800526300092142349910879331901984289897488094,2516815834570812436049349490916722504929952485432718082⟩
def resval0Tail76 : Box := ⟨-24646833236940227405712869515197935410080936139641,583628191348477097231128642814102517353156691427⟩
def resval0Tail80 : Box := ⟨-1275809964917397171384434083467586245179580682,62032630540359456824119956507188070894602732⟩
def resval0Tail84 : Box := ⟨-691305881849931191270304309378504051114669,52641330885957466268092709943629193145606⟩
def resval0Tail88 : Box := ⟨-1832850207234328034268925199313866298995,353870558779852988615881322385687340078⟩
def resval0Tail92 : Box := ⟨-17497156553984988727698295999965885472,2447561115972779204450525259571553698141⟩
def resval0Tail96 : Box := ⟨-504909878107211725518637102938452100,39118384590799019608120375467865652431097⟩
def resval0Tail100 : Box := ⟨-39564081050114297270770881696878190,625892472550973262051344172016352533444832⟩
def resval0Tail104 : Box := ⟨-7894898605978350280589938172079640,10014279380520551312379602345458099354068437⟩
def resval0Tail108 : Box := ⟨-5639525670106884899641460174423477,160228470037818337964692298378121346812123741⟩
def resval0Tail112 : Box := ⟨-459616771788213413190588581992415726,2563655520181233915868395092812179330756507003⟩
def resval0Tail116 : Box := ⟨-116500243775617307509848011341901889786,41018488213693481755789127331135281714241508513⟩
def resval0Tail120 : Box := ⟨-29820736491695895735438515145198073551788,656295783462223016104218703676504134984661007735⟩
def resval0Tail124 : Box := ⟨-7634085194410037903561237671143205305070853,10500725378441820516878208210260574290549706442980⟩
def resval0Tail128 : Box := ⟨-1954325422283084737410209029094173968460470077,168009773875046842975922470118296299150464122968129⟩
def resval0Tail132 : Box := ⟨-500307303074160389829750296287109249522592132634,2687687343916587074937862103945600552749857784133711⟩
def resval0Tail136 : Box := ⟨-128078689237566732507963079000842730077410792038101,42882923744102747940777380085600353312548093900643094⟩
def resval0Tail140 : Box := ⟨-32788386366546724325541666005467548524494018406840619,655387781818526827967822689506128945660912758728946920⟩
def resval0Tail144 : Box := ⟨-8564711929407883517748021002286777602797836128059000292,2530335307100132821026780603053062166140740428949756719⟩
def resval0Tail148 : Box := ⟨53019096359264666852148706508005754103400328,1049447639055922976768362116644057104761485⟩
def resval0Tail152 : Box := ⟨905071762124162608300632634840892262508,39260062369407017828887244445654718951⟩
def resval0Tail156 : Box := ⟨275419594122607619123578508490664229,19115068629414860348597336751149572⟩
def resval0Tail160 : Box := ⟨462159735658552666924717978299274,47977435299313902291087538776779⟩
def resval0Tail164 : Box := ⟨2956560689186308062603803465195,25692226908598922766907295180570⟩
def resval0Tail168 : Box := ⟨59011441014241257691930558383,404495195933841713434489572514673⟩
def resval0Tail172 : Box := ⟨3252155594570658508076686169,6471744426258937921773151867325231⟩
def resval0Tail176 : Box := ⟨458937568082218515200419334,103547897461170692525676573174070806⟩
def resval0Tail180 : Box := ⟨164658916303453915469651491,1656766356793305335678706655591145632⟩
def resval0Tail184 : Box := ⟨1652481097348630445859293155,26508261706457410601171580068586943599⟩
def resval0Tail188 : Box := ⟨389517608864082008956523914450,424132186938432705420837009360971077732⟩
def resval0Tail192 : Box := ⟨99650164294616115662363974004213,6786114897593863928777238323575011935041⟩
def resval0Tail196 : Box := ⟨25510124678398423838943118507898915,108577814445769779873033858192278309022843⟩
def resval0Tail200 : Box := ⟨6530588245932334508667787363820414095,1737238908706150241245630546935868250265799⟩
def resval0Tail204 : Box := ⟨1671830506802978741361829740887999826362,27794255198232549264124708503694590381833879⟩
def resval0Tail208 : Box := ⟨427988624510755821555941497333289098373242,444306843852002155783817426569546239973726419⟩
def resval0Tail212 : Box := ⟨109565174903235197157090634540625899581861360,7006192194804905528286198358635373756111710036⟩
def resval0Tail216 : Box := ⟨28053700262625174984259900987435360096435145261,85800949303965702847405353444341275653207919581⟩
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
def polyval0Tail5 : Box := ⟨1987065734222797484266670451020037890100012879323035,51631326731816869389414898894266475783923704659488⟩
def polyval0Tail9 : Box := ⟨184551482955914808696510653043619403355687366007,9452242671489701011145846940535196277173859589⟩
def polyval0Tail13 : Box := ⟨139168564416416366454576367175999382634505996,11045370087494274546235370082199456403019236⟩
def polyval0Tail17 : Box := ⟨468002433035053120744040328201468803446458,422141557413108511643852340166712981486439⟩
def polyval0Tail21 : Box := ⟨5369644900785748531226972567921654495209,5904787035603882930105036395504713650806765⟩
def polyval0Tail25 : Box := ⟨179712311864734464746553418124406496160,94463104294457251746419850151943972579606411⟩
def polyval0Tail29 : Box := ⟨15927218589514809740861583218755932711,1511409052393620533006273420947287359135102295⟩
def polyval0Tail33 : Box := ⟨3547223402980215725680627027111392851,24182544763580119550136868100788808104305382967⟩
def polyval0Tail37 : Box := ⟨7504699251414887350111294427285950240,386920716192545935817603056592441500453976186514⟩
def polyval0Tail41 : Box := ⟨1440052028558210322769196478062630045524,6190731457734333050608434590703470628046547389661⟩
def polyval0Tail45 : Box := ⟨368039041024730426092697567906113365921208,99051702978719876979322353897151323727400254361426⟩
def polyval0Tail49 : Box := ⟨94216111060892113678462874735257562691280238,1584827159331954763022166890886522201770167879536597⟩
def polyval0Tail53 : Box := ⟨24119310408203009672704654880964735800128405752,25357211937458485819372178457292330969138341699588178⟩
def polyval0Tail57 : Box := ⟨6174543221188928794895557567778939927298745511828,405709602365106951521784590305455002319179268700418412⟩
def polyval0Tail61 : Box := ⟨1580683061986235185478443323302682702703416488185029,6489871747479839934268689864118423800776606565123466289⟩
def polyval0Tail65 : Box := ⟨404654878180186102957061729156607347267326113372028790,103458584020493784736501352858198444742140373328385531642⟩
def polyval0Tail69 : Box := ⟨103591824345812350176123811976878419193845520259535498280,1558220092188705471459484573261541977485500284281835811405⟩
def polyval0Tail73 : Box := ⟨26656250000000000000000000000000000000000000000000000000000,2⟩
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
def resval1 : Box := ⟨109259051372692171429423502321815909540113662814270623165,290303251795050509453072111620823619448792226617857247⟩
def polyval1 : Box := ⟨3747078517316292673160257215009269065178747830486986420848,9575256773823998332129026538819105028622799313089176579⟩
theorem cell1_lo : Holds Q cell1 (1/2:ℝ) := by norm_num [Holds,Q,cell1]
theorem cell1_hi : Holds Q cell1 (3/4:ℝ) := by norm_num [Holds,Q,cell1]
def resval1Tail4 : Box := ⟨52317249047397484146886039723281741081015338373062,3066733894619107065184325766389848980123516750385⟩
def resval1Tail8 : Box := ⟨5881231037981766401827563283175516832685914609,6070241279937898072710934869422033514000180712805⟩
def resval1Tail12 : Box := ⟨-316141440732775651618171115968857667771301607,19184133691155764865748010236201811357961739791120⟩
def resval1Tail16 : Box := ⟨-2104940172441935471199135629097460145033328741,60630245481228236156907931096078126698854195895564⟩
def resval1Tail20 : Box := ⟨-13795059522056629848210808405055976738725244544,191614374229035363751973810955353883003461714106833⟩
def resval1Tail24 : Box := ⟨-90407303648514692788097732372746787756945724903,605549238843586817168673967222388430422752416313771⟩
def resval1Tail28 : Box := ⟨-592493305248291425294732773247016253168685121182,1913527869826778765917834976160884356228508447629529⟩
def resval1Tail32 : Box := ⟨-3882964125280705203881002378483976353211937678237,6045682627995695835208753108728260295268759640904933⟩
def resval1Tail36 : Box := ⟨-25447393691440906455334242980531925231283427760878,19094167317209423640149403722146490499077167423630327⟩
def resval1Tail40 : Box := ⟨-166772039296227779230753258432345208746900670602081,60260652232192924484068947638369926477862032126636391⟩
def resval1Tail44 : Box := ⟨-1092957236731758930972696269954129692757938123739365,189887544164517907206905814874706248772812040425020897⟩
def resval1Tail48 : Box := ⟨-7162804546645253695608774757062916621689092835735194,596429891240020352956230222307324735836922566677432647⟩
def resval1Tail52 : Box := ⟨-46942155876894226465242360606405137285718881021987651,1860708833276024094177101107812602057066703065567983913⟩
def resval1Tail56 : Box := ⟨-307640112754803745336729421500608436895678850210999123,5721479062839593763417343062187432698040404432833497716⟩
def resval1Tail60 : Box := ⟨-2016150242946753197564479734455162619862555474658060356,17038843694731219681512045596217965940270057111778359233⟩
def resval1Tail64 : Box := ⟨-13213042227317476835286705555452688304135747785992004068,47010148484754094698945634221661527311536610217075431284⟩
def resval1Tail68 : Box := ⟨-86592905319323763251767278633023400716937743194975652834,103742037795906806269992204049702829850068874724494638859⟩
def resval1Tail72 : Box := ⟨755386955769298664035611713163388583071952036551132288823,1620497880143839912002617750077552360366091386139340228⟩
def resval1Tail76 : Box := ⟨-24102758807392376640927154030305615909015346860573,406894102792143459623190962121276490652754417677⟩
def resval1Tail80 : Box := ⟨-1219989769348597378266370223323340990634065843,60542367258614455674670291056946923854413608337⟩
def resval1Tail84 : Box := ⟨-3309506272727783702108218852413611494072816,191215692471624596642514282933164255346802975122⟩
def resval1Tail88 : Box := ⟨-17457618230778591046828889035522260151196427,604326973991868957172859904033160973376915804790⟩
def resval1Tail92 : Box := ⟨-114399311951470353104650642642522369265033055,1909912440982255284389418646709423169467458717904⟩
def resval1Tail96 : Box := ⟨-749727229456373610970831313153177230330385720,6035878311182119727707327788496698480654643920097⟩
def resval1Tail100 : Box := ⟨-4913412368144936584058895402219752893501549322,19073812239894230899725714037198605923620740134917⟩
def resval1Tail104 : Box := ⟨-32200539295664353245908595613662720081761923310,60265994114768038434759969362376061521534683000174⟩
def resval1Tail108 : Box := ⟨-211029454328027165856130998337345578099791261196,190361042538762175283503078470454881886375236718453⟩
def resval1Tail112 : Box := ⟨-1383002631884142573989944648746867145416129955695,600918854531462662566864061575372619547380847421325⟩
def resval1Tail116 : Box := ⟨-9063646048315903861954703435976328766402405147326,1894507655603743129886408424459662751644120833281522⟩
def resval1Tail120 : Box := ⟨-59399510742243112075564758273511472336856890872724,5956825837688955825418451253147445361896328905551672⟩
def resval1Tail124 : Box := ⟨-389280633600365285167565001974998934641122937941322,18624962442922930823415200715312162586815207656759714⟩
def resval1Tail128 : Box := ⟨-2551189560363416732402395394124668052329048487721869,57543208311117666703217743566595502198838576222788999⟩
def resval1Tail132 : Box := ⟨-16719475902811326029502204772671633656541622069047422,173208497616941858389774361277275054794866098506694636⟩
def resval1Tail136 : Box := ⟨-109572757289967344110317367803172044192023252103836389,490693430634717848572182720096755116772965361848871446⟩
def resval1Tail140 : Box := ⟨-718096137591722674619751480934730326333990539207354801,1179041535159772122348096640997397206691575019503939506⟩
def resval1Tail144 : Box := ⟨-4777169302791392598593037769419026278629246938074642606,1275575641262121320532532529887461762901695604351742582⟩
def resval1Tail148 : Box := ⟨52241177506938974274159267982656057756691945,776976383675144150925742671146774845034758⟩
def resval1Tail152 : Box := ⟨870814139681952353873369286874171055990,2622176262709372167640116690023821907554⟩
def resval1Tail156 : Box := ⟨359772728200752083106705763478494428,8203833773222825551558997723336078687957⟩
def resval1Tail160 : Box := ⟨659475899072804424795116786389055815,25927821416842133488800169784629862872327⟩
def resval1Tail164 : Box := ⟨4319159922756092843054980507110319148,81942483300947233113616104841943225984257⟩
def resval1Tail168 : Box := ⟨28306029161215355577863083807294950433,258964057295547555969085878014268495840540⟩
def resval1Tail172 : Box := ⟨185506392376659878290860667639464221759,818358259176910283692215681375669194628841⟩
def resval1Tail176 : Box := ⟨1215734693062029492520479045181221938532,2585786783649367084856587492498389323639487⟩
def resval1Tail180 : Box := ⟨7967438884448980211993098561844011450199,8168238051185449301127935347807496290658740⟩
def resval1Tail184 : Box := ⟨52215407473124115425365603919639708358528,25788631573488529365734126599405385609176487⟩
def resval1Tail188 : Box := ⟨342198894415865738285132259826826002187900,81327638477512322838506279075370144904610774⟩
def resval1Tail192 : Box := ⟨2242634674443817347572122999315182340367537,255874382204736630484976030811950386969232710⟩
def resval1Tail196 : Box := ⟨14697330602435006406810319904723964072214235,801079907929295796478375622373583753604595139⟩
def resval1Tail200 : Box := ⟨96320425836118357606563272383637110362924840,2481938500881450834989480984101935926246868954⟩
def resval1Tail204 : Box := ⟨631245542759623021526404115861581589505945955,7517325879952723173149697460430020343982009439⟩
def resval1Tail208 : Box := ⟨4136930789046607164921148567698325447690933580,21616578892625392988775751190785597511548235004⟩
def resval1Tail212 : Box := ⟨27111789665525661108221673913374001929888035214,54282018747436668686108450998755328983413493955⟩
def resval1Tail216 : Box := ⟨177682038458981122345409351125281112533721650343,79564334741929135222326448695801843624596903269⟩
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
def polyval1Tail5 : Box := ⟨1934046440475577041789594067649353313288609137748194,117172492855876030790085486219110486051637042854841⟩
def polyval1Tail9 : Box := ⟨177966116806698143193758163389592123852290734691,268525025030509413601728204709046522452020971299728⟩
def polyval1Tail13 : Box := ⟨15184313857527375760468760899853083292334412594,848648162394281488603674564941942583590096551616521⟩
def polyval1Tail17 : Box := ⟨98663748870953558498020391504523499539296121734,2682096196242612267734624080537732059853502800028601⟩
def polyval1Tail21 : Box := ⟨646599965036489173700798637800670981031835113298,8476413696938824166435915427290196411412170486559445⟩
def polyval1Tail25 : Box := ⟨4237557499911063844623938451948052873046272378523,26787459183317080713363701181468257636038676975120046⟩
def polyval1Tail29 : Box := ⟨27771256830418927552976828418381473431540413951590,84647220911677120803408197999244610528755919584293742⟩
def polyval1Tail33 : Box := ⟨182001708763749441103644581946591355990889443756399,267432788354667446522489019228669191247630085999825597⟩
def polyval1Tail37 : Box := ⟨1192766398554091217022496461084659561180575593546853,844602125653771655717659426353409172377452421649707645⟩
def polyval1Tail41 : Box := ⟨7816913869564084413739707475447155407526380677486753,2665312621505687655430421186928809735241857836693165319⟩
def polyval1Tail45 : Box := ⟨51228926735575177168796067187531234882236675683781173,8397180469018306862621103258102936411489417475297304875⟩
def polyval1Tail49 : Box := ⟨335733894254265486077689112837564098529780511030749681,26365411850350596280348751701109719481593333011217671191⟩
def polyval1Tail53 : Box := ⟨2200265649384754829687683619154238735635275292460642870,82188540654551598864320980049383012146947833786789292729⟩
def polyval1Tail57 : Box := ⟨14419660959807971455780338359009221476630182339008960850,252290640445225475563812920870607010601770396852580611555⟩
def polyval1Tail61 : Box := ⟨94500690066207039635166580934808488410850450883871853131,748435571164523304543111646631809082030371814695377298194⟩
def polyval1Tail65 : Box := ⟨619319722427475704698507150646165805827823724424556669072,2044775127889506262857941173748538497080323655959322941976⟩
def polyval1Tail69 : Box := ⟨4058773816657076660952118449590329989510917271909372517786,4361081579127978002283621512310541671954520199922275821506⟩
def polyval1Tail73 : Box := ⟨26656250000000000000000000000000000000000000000000000000000,2⟩
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
def resval2 : Box := ⟨109153107018158050893485201060445433960460074661929486650,273953376740453969234295506423438237769289374936150014⟩
def polyval2 : Box := ⟨3738285754618658347390551443342077819309156475197326225388,8324810948504685875793916608988756547328813042981020530⟩
theorem cell2_lo : Holds Q cell2 (3/4:ℝ) := by norm_num [Holds,Q,cell2]
theorem cell2_hi : Holds Q cell2 (7/8:ℝ) := by norm_num [Holds,Q,cell2]
def resval2Tail4 : Box := ⟨-141639236444684328196259000243102221567774944106848,33851566017228883291849814262607661916475913523510742⟩
def resval2Tail8 : Box := ⟨-443359762036086318346516867829708473874998884516084,57634134339612168863202662610274447794187972207284085⟩
def resval2Tail12 : Box := ⟨-1017345488079634190583756626130084139935750257123129,98060305025734545180160816334512065303918612814524949⟩
def resval2Tail16 : Box := ⟨-2334398453340352596596727217996685255864738603231801,166687699224177003937316734936366279347884011323865462⟩
def resval2Tail20 : Box := ⟨-5356504920671186634761736716394126234509908705853461,282987731683735480367819233747194428949291842543154198⟩
def resval2Tail24 : Box := ⟨-12291022950216081693728177496286772496123381714481002,479611514797243538074651402714923976947341524571697974⟩
def resval2Tail28 : Box := ⟨-28202950879358623664410567848991140515873175072068629,810961061870993159394461672977861644072220071560521362⟩
def resval2Tail32 : Box := ⟨-64714421372838724399778643038680967485697483989276317,1366862336738548574959989789474588580189351456115210297⟩
def resval2Tail36 : Box := ⟨-148493551314392306003280891161514411774721123444907046,2293713196384167618418343939787433251201676027141123277⟩
def resval2Tail40 : Box := ⟨-340732935784461824484098833547030364953309792832133219,3825563956582594173168405645689566296799388966569844877⟩
def resval2Tail44 : Box := ⟨-781844952192517423192148018548960966045081827542052167,6325673611379103303735506066540367562050553958735921823⟩
def resval2Tail48 : Box := ⟨-1794019494656658441172330344246452463515242038989696876,10331093390136910274210340312962049666146569451621160053⟩
def resval2Tail52 : Box := ⟨-4116552697798353152425417089670104976981598124068110178,16568354580883220003549414917310618116668679055474762825⟩
def resval2Tail56 : Box := ⟨-9445831644652239560863465861876705943605485954864832115,25841706969874915799571025183817349757002866158580612261⟩
def resval2Tail60 : Box := ⟨-21674381942643994893520381667349791525256714865717410978,38524601049899405496220195095569922765937930537117573319⟩
def resval2Tail64 : Box := ⟨-49733983224734750430642365541475750976194954145834205403,52962824075533339355415552473574400860318783755272357915⟩
def resval2Tail68 : Box := ⟨-114119405653569052929291862047512920370123405743536433670,61076745019562773447641776893496889744045084402954627655⟩
def resval2Tail72 : Box := ⟨756731304667172299282109742598817320616798375949057061521,1172750711512832649498711705123100456774381802544809308⟩
def resval2Tail76 : Box := ⟨-25924410738005947872876331978536063131563986883953,393656481379969843330564112745611296397173210158137⟩
def resval2Tail80 : Box := ⟨-4779881845272951043733022641148903745541836716889,670151079619167888658270108926361962213658655271868⟩
def resval2Tail84 : Box := ⟨-10965167136187673060911301556304460641390868318604,1140435202522839314543304293186043567208096431659444⟩
def resval2Tail88 : Box := ⟨-25160643972044808920960480613599814628394848159499,1939077553249132679937302375482946512712070741369071⟩
def resval2Tail92 : Box := ⟨-57733551459943392347868687540625884392896891456425,3293170095275282236259906458078977559289618185857875⟩
def resval2Tail96 : Box := ⟨-132475264468257333335477245648682277438471387744272,5584018420257866297961249093538997377830279093340464⟩
def resval2Tail100 : Box := ⟨-303977414382958816578206904303578950031468100339310,9448108438444280128964125001083915223375067454084747⟩
def resval2Tail104 : Box := ⟨-697505823640684400612815882706503397745304568893107,15939122103548141338182618631474002825346867473696267⟩
def resval2Tail108 : Box := ⟨-1600495138759703531906413553567353122003158104021022,26780857626656968773519194334846082811565031138471884⟩
def resval2Tail112 : Box := ⟨-3672492189130490199103946893736142236147311318230327,44744842641001408908101872951407250972047279154461716⟩
def resval2Tail116 : Box := ⟨-8426891499137138255928189431462092919083325776724475,74170944179421903287033586261342675891469239575938964⟩
def resval2Tail120 : Box := ⟨-19336324403468068129411109950428754430304512210347892,121571936712474386777033296477350764153821911333577469⟩
def resval2Tail124 : Box := ⟨-44369082178694140254322926951862859770394231245631872,196014190428927807723646438908307902255071894180558846⟩
def resval2Tail128 : Box := ⟨-101809186291197815190846087900496911123231570812971796,308274064271409269466006394563137841936130544663837943⟩
def resval2Tail132 : Box := ⟨-233611107201437849343235027612901844511110760362853952,465972813791673975370081429752099737627890720278172813⟩
def resval2Tail136 : Box := ⟨-536043469131354919844080700480478443714789710189286632,657415814671183217572056724126380848553868724067205074⟩
def resval2Tail140 : Box := ⟨-1230004110374347409759194963899633848666829492046746407,805984818037502725910660283872710098518378769225092054⟩
def resval2Tail144 : Box := ⟨-2877363750210111299133728919037387858697052839491556990,644849823400348837675013379189109166268687100008346552⟩
def resval2Tail148 : Box := ⟨52086484652354494331752216776121223374475162,40322955896008689067550581724011221706741855⟩
def resval2Tail152 : Box := ⟨510608674567731964592839168519541276067178,67624951230009739360420341049321385181762146⟩
def resval2Tail156 : Box := ⟨1169680382007450539737358424645714099140836,115065104443964868811561128534579586635751405⟩
def resval2Tail160 : Box := ⟨2683945135726232402223548252980341292884448,195607465776751379234981986679240747790604137⟩
def resval2Tail164 : Box := ⟨6158573873052768361936590945933509854017419,332117818919868527749077045402917472387004442⟩
def resval2Tail168 : Box := ⟨14131448385708572178771606194406049830815409,562953143400961600683368307745419856128587784⟩
def resval2Tail172 : Box := ⟨32425986534287801231019786468677390366730961,952054849766503879818203727697577268292785793⟩
def resval2Tail176 : Box := ⟨74404588547707894817764192282733083433860635,1605076255054142465499073264675444510119822368⟩
def resval2Tail180 : Box := ⟨170728584960701116047616048848942378087597538,2694391588047703329824904228916749244728828489⟩
def resval2Tail184 : Box := ⟨391753389026452446917623830189994699734849317,4496015136022454096165968185310562871948200907⟩
def resval2Tail188 : Box := ⟨898916358084016230529782624696585687945077680,7439400959117283727973937643467512974764954872⟩
def resval2Tail192 : Box := ⟨2062651253226220639870165085974879758739219591,12162149967621977873539387778642282144443128099⟩
def resval2Tail196 : Box := ⟨4732954466980623790159971720236853299597196349,19533928415399310039476890403830949731012081656⟩
def resval2Tail200 : Box := ⟨10860225620532970449903725900953035932282572560,30538005235871948136113355798219873676846001918⟩
def resval2Tail204 : Box := ⟨24919846863458901293615442096346331686080354129,45703707317230232526131834563258404010994474648⟩
def resval2Tail208 : Box := ⟨57181019013481463019844680560210136590164271468,63299646510937985884911554237484453305524583919⟩
def resval2Tail212 : Box := ⟨131207424919503118673283724660952639135659936121,74327271483887175541956961278720226062268442226⟩
def resval2Tail216 : Box := ⟨301069962818605197577308019521778977818363040464,49564664490447601685613615611015476635644757430⟩
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
def polyval2Tail5 : Box := ⟨21545703144450971651069601565756142302845377414359236,3012239511990296409725357944485369604548089460236635242⟩
def polyval2Tail9 : Box := ⟨45058993221654478883118990075585999612198243292490144,5127180475614652418072988129935365588393744328696123639⟩
def polyval2Tail13 : Box := ⟨103391860905102870581955519342575776389804974035530329,8720220032823162058677241388094440572043346222753400502⟩
def polyval2Tail17 : Box := ⟨237242708171481966075741586351553886392316427971033113,14815449635099153125846108911334074941193279103735324551⟩
def polyval2Tail21 : Box := ⟨544376531728572010671070546062478879394206751962573237,25134852055541246318855213091356175997836043820856597336⟩
def polyval2Tail25 : Box := ⟨1249125044058800647069177700642890941465203963019609128,42558505232266545973293423700578111867211142229797144928⟩
def polyval2Tail29 : Box := ⟨2866239238382323801796347724717153826466935556139732773,71867643981871161897619062914816913472051227709124668384⟩
def polyval2Tail33 : Box := ⟨6576865471328874057150445063156521927675693921946817757,120915839930652915770640199771007368995983625759863647407⟩
def polyval2Tail37 : Box := ⟨15091259253142715243780461232581442769953291864070552397,202405667580059038661110062757026020678214123771705517041⟩
def polyval2Tail41 : Box := ⟨34628366178143656950942895612778058481884382528845089896,336411788885910647085487082594275009157876922977253632761⟩
def polyval2Tail45 : Box := ⟨79458163434432362381102748673062936229438077423822482995,553519960323321252502152544538345782288633839101520031146⟩
def polyval2Tail49 : Box := ⟨182324505403835975690315450101310482682996909371689399072,897508228836796596823622460466317590775502096020343337044⟩
def polyval2Tail53 : Box := ⟨418361359411287928295373890874512453772525924738138697554,1423785612454447606138196111731022271757461508218695592089⟩
def polyval2Tail57 : Box := ⟨959970941156758053108701160032971586083333794524884905113,2182650465241431377866392336186997970202824638737411163872⟩
def polyval2Tail61 : Box := ⟨2202746948623981066454716762519747478530858051648964906791,3158426429388097193297212791575054035642509862838321901825⟩
def polyval2Tail65 : Box := ⟨5054417703345204652991858358376179837928393281840286588163,4091507393011909750439970085158455511382731289140908135339⟩
def polyval2Tail69 : Box := ⟨11597854434221209056217586372622241127560391559972081147072,4004690061203892407440806179353495746145280768409042449322⟩
def polyval2Tail73 : Box := ⟨26656250000000000000000000000000000000000000000000000000000,2⟩
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
def resval3 : Box := ⟨108970262779697193010441812862657567852992248932117857069,1807042952266915771648071240110625007999326502776438581⟩
def polyval3 : Box := ⟨3756133661379832994272148685471547727340130800109549217549,236634840242706204954800169419433646013515774672974037818⟩
theorem cell3_lo : Holds Q cell3 (7/8:ℝ) := by norm_num [Holds,Q,cell3]
theorem cell3_hi : Holds Q cell3 (15/16:ℝ) := by norm_num [Holds,Q,cell3]
def resval3Tail4 : Box := ⟨-193295191444268995764075789412098118411998949947276819,2010483937065788585609460194184662768627538145725197847⟩
def resval3Tail8 : Box := ⟨-286644779925680500780610181251149263864965522779674523,2566297035864068634532247311690654604051494723645271471⟩
def resval3Tail12 : Box := ⟨-424963830143835311915809256230956063314590301694569198,3268278544279451431016755294619802522868745848529388416⟩
def resval3Tail16 : Box := ⟨-630028055556302333992314024589193008705653544234494449,4151015544453708633058252480110368880026602393388117446⟩
def resval3Tail20 : Box := ⟨-934045023665309307421995393542672429938385363489386472,5255198894759523622441787719214313662202079848630135449⟩
def resval3Tail24 : Box := ⟨-1384763898273636076713749126065532776964518662107717718,6627449226425422963917031794632732973693854673978479786⟩
def resval3Tail28 : Box := ⟨-2052974969490451787401346231194021128286481140274863306,8319141560687869866353847419522957986185936286328817131⟩
def resval3Tail32 : Box := ⟨-3043628036959030391181614799595134198475438042518803553,10383473768903023691473207371407176765790546533996706085⟩
def resval3Tail36 : Box := ⟨-4512315914724631725695932451148493963854058142308854761,12869581249699577190153217900053420391546919673511818775⟩
def resval3Tail40 : Box := ⟨-6689711971052941385967560890115113981944305518795837497,15811819141395551562296827723943307886113641150211503368⟩
def resval3Tail44 : Box := ⟨-9917799884004814305084653020403626770924863461498149231,19211293310769001671887537523892875162308684744099445810⟩
def resval3Tail48 : Box := ⟨-14703585889017564676510409820503200895914057763720790576,23005140068764100580198253980774532432567804005870442335⟩
def resval3Tail52 : Box := ⟨-21798729609819126799213058871351224249128425699577570199,27016659315991820519025086195165827007808025406055924411⟩
def resval3Tail56 : Box := ⟨-32317600358762210131461228194128510441396579380477024477,30875788848979928555934513605518203549836390167498912237⟩
def resval3Tail60 : Box := ⟨-47912300929599069108801119932069900492404569255753985876,33893959912247034957961080019361897150828240806321811853⟩
def resval3Tail64 : Box := ⟨-71032148265036180440358736616011285517047881157564720175,34869187247904363937831714291848951333582100494432521302⟩
def resval3Tail68 : Box := ⟨-105308302665075397217339813690922642807728837675004066298,31784964806860151903931853479902432252782586004416645351⟩
def resval3Tail72 : Box := ⟨757401527621900264417934961452718153362669579887888003077,968056718500906815155047139359993278330448187247846532⟩
def resval3Tail76 : Box := ⟨-2347637211986391898321725933143031860895424243658486,25105903786543904885952078305855512751808859617137464⟩
def resval3Tail80 : Box := ⟨-3445322236578914486811436431131947516156559011276401,32063443313937716932472496473160682191697167320186661⟩
def resval3Tail84 : Box := ⟨-5107843942832249873437522661848019279972755841701678,40859610492071071352167787132694173033680282935692517⟩
def resval3Tail88 : Box := ⟨-7572609146229814875698466853533830678378714145446225,51934019867196671277267094440884811969695178674485438⟩
def resval3Tail92 : Box := ⟨-11226734788740882931161545695511862254209015151427505,65806873883334435765388792148754022550103647955991213⟩
def resval3Tail96 : Box := ⟨-16644140953650310569082146460244954564601194263411687,83078813672189237548733284233671605835388618562313919⟩
def resval3Tail100 : Box := ⟨-24675690064648743090730570516858044187112789189433160,104419491256023268746208603490861838018177069435876005⟩
def resval3Tail104 : Box := ⟨-36582824061764871964824225553250185868210736034394615,130535828837623986620575325691203397044434385325209613⟩
def resval3Tail108 : Box := ⟨-54235687546235742768953000370949584173630542045684596,162105804531084716212835358334366638340113146258427077⟩
def resval3Tail112 : Box := ⟨-80406854283490847639103728849794677317471804158082845,199655486946717025936315824202564622140073965084533814⟩
def resval3Tail116 : Box := ⟨-119206789998834549573025878056540016616647634315416283,243344629158951192703335154017907018862271308114073737⟩
def resval3Tail120 : Box := ⟨-176729445623193520938768082993865782829853947641676039,292607241901243938961631303142265775782753852288142377⟩
def resval3Tail124 : Box := ⟨-262009378413651391824668977595583434717542647401914055,345564925855020873062510997307959598410148024027031624⟩
def resval3Tail128 : Box := ⟨-388440727206687242471729471825079343374653397621232602,398087462512852665154769991613393987835288490692114382⟩
def resval3Tail132 : Box := ⟨-575880907265269007535740842554895013831451249011609283,442309936022834247829269536811364747444287800646160005⟩
def resval3Tail136 : Box := ⟨-853769432832954120136672220220947247264449237893739827,464317581609905287254890514616127691479359707167521536⟩
def resval3Tail140 : Box := ⟨-1265751794745190621533054874238250214546897959230708454,440562365353160976659287936134610276112638702582586303⟩
def resval3Tail144 : Box := ⟨-1925951187195281530597760503645308832205423267567018810,328649559583207933474471244167342253034254290012553924⟩
def resval3Tail148 : Box := ⟨516003369269661632864284577619340779226692170,4537526895122417299320402501555636567417726198⟩
def resval3Tail152 : Box := ⟨688382977602110520157347985835176711678710469,5786131892536488836795123816614913578729473318⟩
def resval3Tail156 : Box := ⟨1020557573590723383623865007769954871904326724,7360948605198061539844800989954823016308218749⟩
def resval3Tail160 : Box := ⟨1513022657225835257394039761161666258372167164,9337157864581781046045832845870657138274210686⟩
def resval3Tail164 : Box := ⟨2243124367575007650645053390499367207717555326,11802849571726859238418888851933565529561328068⟩
def resval3Tail168 : Box := ⟨3325533100499417738226077845960565520282464682,14857517725892423892980858517869720732613203773⟩
def resval3Tail172 : Box := ⟨4930252892965140314529376965804050009349267561,18608402296336898796399164327624520863779422650⟩
def resval3Tail176 : Box := ⟨7309322401554424575373706019789333249228803581,23162367603109248215003968493044024135013290367⟩
def resval3Tail180 : Box := ⟨10836400308409715944973350023252797285114812026,28610368603109068449507702023073633936449726496⟩
def resval3Tail184 : Box := ⟨16065452471918553314259571723176317436039861495,34999899575198386025435596867493387849437035160⟩
def resval3Tail188 : Box := ⟨23817758275981496689543372870818505785327334253,42288294301990962304357396717711468703672354463⟩
def resval3Tail192 : Box := ⟨35310901469141082360600835796900641766676291004,50265913577772558580473903211931788574920547926⟩
def resval3Tail196 : Box := ⟨52350004904565624670756829910787918717098491244,58432457335721434549369234592839544588800368723⟩
def resval3Tail200 : Box := ⟨77611244671933509666298301467239126519837094850,65800892520747037979876525208761084951781481209⟩
def resval3Tail204 : Box := ⟨115062172592106069802746853165530395094417564621,70590327616476916088506912917372240271734281676⟩
def resval3Tail208 : Box := ⟨170584863283404080279125442318998909126493924439,69749403455761606337844123178908288599551470163⟩
def resval3Tail212 : Box := ⟨252899757841736947568499696983951950325810668759,58222148460246985503664399012717324635295616445⟩
def resval3Tail216 : Box := ⟨374936863173036560967345744923068926191399769184,27823765687053744819454475976013779622293409024⟩
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
def polyval3Tail5 : Box := ⟨32964555278082668278814886844797594884078438940074755033,297598376925244632324869604149027782331464235486988520381⟩
def polyval3Tail9 : Box := ⟨48868629391423686566126490119157461102454753519376892430,379055271045253750652325506763824605906058551909057961073⟩
def polyval3Tail13 : Box := ⟨72449948118204146214884519748693733075521348406920317072,481513918109597379727629146253367917936676882358883551926⟩
def polyval3Tail17 : Box := ⟨107410317536969345442523039410315096639296629986131038781,609717108380996065502256144195656286623585290707259524890⟩
def polyval3Tail21 : Box := ⟨159240642858559405023849860113272343114987543343246266719,769108255609781425921488074661886507833083921029952212359⟩
def polyval3Tail25 : Box := ⟨236081439097129404295211934413422056340803451432768192193,965701739372424855549021042939253367085906680506908453804⟩
def polyval3Tail29 : Box := ⟨350001387118714573274451357691000784955229223850189296790,1205752931581151263050621193234097414961375981392306624128⟩
def polyval3Tail33 : Box := ⟨518892850931091394191590009957600585413591861178206603975,1495090655840551222078390159296438753058797757566295819295⟩
def polyval3Tail37 : Box := ⟨769282067605265926490505962147425309220017937020319193127,1837896660291748799430309675370321472968006821692394955172⟩
def polyval3Tail41 : Box := ⟨1140495380649641831373198444550288319121674017644507606020,2234597263527321271400439725643992312744271855804893170635⟩
def polyval3Tail45 : Box := ⟨1690835868997016508255603401245281344212316714538488100596,2678350729102370235516061090992709186017583052568508029889⟩
def polyval3Tail49 : Box := ⟨2506740478210803884423526063885400272462212031249627103019,3149338788812236306012650623222594109641881775216270599987⟩
def polyval3Tail53 : Box := ⟨3716355880732512105270154320583436956533616648484730797065,3605655197660020476354402256423871291139813455028663864797⟩
def polyval3Tail57 : Box := ⟨5509665301337056471882571376043209814934340999437693493178,3968958264757422872170865890280208258320902028036197332578⟩
def polyval3Tail61 : Box := ⟨8168327444134382961043945046969939131845140850756231236161,4102113524311407058373281603322434904679676342055000061742⟩
def polyval3Tail65 : Box := ⟨12109914048398937781132381986900655804175265908129623618456,3774641394729582037400424430606292057629686315513149766169⟩
def polyval3Tail69 : Box := ⟨17953494121220985910929399487378417450039398852477011967627,2609670881657912056097854627654062815708827538183120780459⟩
def polyval3Tail73 : Box := ⟨26656250000000000000000000000000000000000000000000000000000,2⟩
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
def resval4 : Box := ⟨105573252657486391949680181864660865767507492113567705090,9200412178309804892796085318913073800352026023657470179⟩
def polyval4 : Box := ⟨4571134332697409908911802825254813439010206065994280820988,1870270831318661548299285564442899308272379128022374958266⟩
theorem cell4_lo : Holds Q cell4 (15/16:ℝ) := by norm_num [Holds,Q,cell4]
theorem cell4_hi : Holds Q cell4 (31/32:ℝ) := by norm_num [Holds,Q,cell4]
def resval4Tail4 : Box := ⟨-4242492748753838137165003124293355597847918990230374417,9921901580870434795113700971525169282220130120006146333⟩
def resval4Tail8 : Box := ⟨-5140754798934282392785023476617430490488975810236344023,10941713049619140913838561150239540533425790252673549688⟩
def resval4Tail12 : Box := ⟨-6229130737530582733655590555287202019291111422729084534,12031081875490019241864592278032484164789130814795145160⟩
def resval4Tail16 : Box := ⟨-7547932399040940762074138461855077260751859482196657058,13184915799230128717718774143808567994989055453529426971⟩
def resval4Tail20 : Box := ⟨-9145944418407545340743507016813976309680146932485244675,14394361684377667121551283760849744508265452407854409593⟩
def resval4Tail24 : Box := ⟨-11082279872462623812721686181530574658772813607329713453,15645645114661769837646802042479496335708114077300822834⟩
def resval4Tail28 : Box := ⟨-13428566974931886893311839876591787958610030468746927459,16918615895082924034751963223199372372264039506058635938⟩
def resval4Tail32 : Box := ⟨-16271598721153800026077961295113027767403588603471291992,18184929744477896907955747384186017213981148757026863357⟩
def resval4Tail36 : Box := ⟨-19716543502855555849579777141099667363607118031690345589,19405781590323941145453482948493801766560022464443403709⟩
def resval4Tail40 : Box := ⟨-23890835458879260370545044410432575008225747617169153278,20529086943432960186425448876363271713242178224730055738⟩
def resval4Tail44 : Box := ⟨-28948888472291171706520324366684627788583743430574473443,21485984749787090706910742627603269332545920132668231397⟩
def resval4Tail48 : Box := ⟨-35077808192332918062424601595582227726498530759088519680,22186506992393727118345396840510854759940965687673943032⟩
def resval4Tail52 : Box := ⟨-42504313378243972957636612910841162624080682153075252012,22514226058476931694213353369266176397214694229503573733⟩
def resval4Tail56 : Box := ⟨-51503122596777524913194576976817869775946491425569452951,22319649173868785151535117679527900839027318176312337362⟩
def resval4Tail60 : Box := ⟨-62407116511058141654892925123746479462509185624729388881,21412078431097935783411769887060777455163466058181223463⟩
def resval4Tail64 : Box := ⟨-75619651677072315509146570175654742136917986661578332575,19549593150414405809676886022302864063122456249625621699⟩
def resval4Tail68 : Box := ⟨-91629421655693674191799070835492830367091895308750141632,16426733471544289533135975609330875811593949628169977549⟩
def resval4Tail72 : Box := ⟨757694656511927805386099621183629735360791133769688249428,951151196332242567772158729862557332027860921265928905⟩
def resval4Tail76 : Box := ⟨-53627713032891351511569374679106367644139080813894705,128339657823488562885219271458205118740838714411426645⟩
def resval4Tail80 : Box := ⟨-64952858297795464547774034361768859526475198049371424,141627866407227757908942912550033470227113676687317589⟩
def resval4Tail84 : Box := ⟨-78704364276594940497847140495996494548206480046388499,155849683480769308351916221897830839315802732074266265⟩
def resval4Tail88 : Box := ⟨-95367274519538741774827096431270194632111932305045418,170947996254565522064458120514562300478996695465714987⟩
def resval4Tail92 : Box := ⟨-115557976142118911250609501952158498529892372278509177,186819339985208438392426135160051128864503081780129730⟩
def resval4Tail96 : Box := ⟨-140023356201994190145520113181217153541535894875293423,203299206723514149922843615568357085318893211224821948⟩
def resval4Tail100 : Box := ⟨-169668429100536121474387442956349768796276197947101724,220143821776463787333934476174176494404002944118583814⟩
def resval4Tail104 : Box := ⟨-205589814544337193050829424202810730346827445617526640,237007344346041105168306249756223444044191565923097925⟩
def resval4Tail108 : Box := ⟨-249116303300773616033201087972909180996125160732069448,253413426375798237155755738742984145500019037371712006⟩
def resval4Tail112 : Box := ⟨-301858011340632318635372339545683458247257624044012656,268719824816142684346196414036286901814909413413384657⟩
def resval4Tail116 : Box := ⟨-365765940659887542142446935931043569172278634231291126,282074471334995633799115765094436620807532233601786941⟩
def resval4Tail120 : Box := ⟨-443204150032787161923228598223077394677458090331089568,292361048644824523275917145489402901320579993646770260⟩
def resval4Tail124 : Box := ⟨-537037205410381161396056394089047948268153782324830107,298131690335980156979108525641949302271818184310369043⟩
def resval4Tail128 : Box := ⟨-650736144897686901193053757222073383978207074144017334,297523894696579614151282650177971494936184205024581488⟩
def resval4Tail132 : Box := ⟨-788506878127224720172196237340290037014277447210551336,288158102179239131688615017803806080965139415504941794⟩
def resval4Tail136 : Box := ⟨-955445769740979143515092598282922226791076996496019471,267011606320479001485778841593424643109304531675596273⟩
def resval4Tail140 : Box := ⟨-1157728240948731829529794332870251407487548070213955231,230263512812950110145608290748843724572298914000481775⟩
def resval4Tail144 : Box := ⟨-1449867293146357813146830870431878858197468783325844568,170340005647897677723753541763306561799339376562870223⟩
def resval4Tail148 : Box := ⟨15906010772394960408772938431848793874372057442,33810795741766776305170828865353058487405165103⟩
def resval4Tail152 : Box := ⟨19211047436920745356623308998223445355531794665,37178856132422803550347968975317253199579191173⟩
def resval4Tail156 : Box := ⟨23278317170747437234074143250819912164296423278,40747404635368916895574002066893282188921943105⟩
def resval4Tail160 : Box := ⟨28206690751829844002295094309236074344878296014,44488824854535348210070934512211653904749876494⟩
def resval4Tail164 : Box := ⟨34178475932855581793360671690895522052289698000,48360819841100353775654245458417773929893781285⟩
def resval4Tail168 : Box := ⟨41414578809356510191675356820735139582850856318,52301454291646733334107679572144161887425584733⟩
def resval4Tail172 : Box := ⟨50182674655414358127412353368906345141883153783,56223550135269965275620762592425509629127798781⟩
def resval4Tail176 : Box := ⟨60807109669366581327110972647582223391813355061,60007699702717654000658802505043233249976035969⟩
def resval4Tail180 : Box := ⟨73680899069883275281185910954308375620936094464,63493577257284812009466979899462192884931544068⟩
def resval4Tail184 : Box := ⟨89280265371358143154994049737862939405683854370,66469158506644202540250382540028678731173344157⟩
def resval4Tail188 : Box := ⟨108182254633185212878800046795483574228113474715,68657370986914587385352500256523623224205895989⟩
def resval4Tail192 : Box := ⟨131086082336778898766849693219991533901210271857,69699592568525656475671817619133836286755304497⟩
def resval4Tail196 : Box := ⟨158838998509221962678801539951915640763784842415,69135286698699274979654098665229428880476809055⟩
def resval4Tail200 : Box := ⟨192467628886746197903710891587537686867161453426,66376906414758824620751500994045428379230270106⟩
def resval4Tail204 : Box := ⟨233215951478915647082240706487226981492422430399,60679008623032173870361697076477304958331598731⟩
def resval4Tail208 : Box := ⟨282591313348713040658863127358611880770755877814,51100288340766836988335053994772847607588986008⟩
def resval4Tail212 : Box := ⟨342420189876551499933083108378336145423454510187,36456960681037533793910050229573240314633876901⟩
def resval4Tail216 : Box := ⟨414917235313814299154168881095867562868624204367,15265459999063884153579303145988383888997213940⟩
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
def polyval4Tail5 : Box := ⟨1017136746226048888684707838412069110337232658903396800935,2056274071979130370662468749262998111003125184874350680655⟩
def polyval4Tail9 : Box := ⟨1232477765740491444750966011199424119579837580740126241011,2257104851746774045202370597766056940950762712726782489826⟩
def polyval4Tail13 : Box := ⟨1493412042518627428352911262451716552118029031169660474032,2468698816395491543489058551096251018296932486886720913269⟩
def polyval4Tail17 : Box := ⟨1809590072162041513211683192257051075428261627113405612141,2689034600148171995198883961974593569545713921503065888073⟩
def polyval4Tail21 : Box := ⟨2192707796667472270376228057099157386452629407276677930691,2915080617881145484134051365521076241066420151098511512805⟩
def polyval4Tail25 : Box := ⟨2656937366937426363892412576510414747387899803390920137581,3142502325905217610556279263781791674359463867994654620792⟩
def polyval4Tail29 : Box := ⟨3219451393640910695780112060929809856071881769474762911917,3365296842037723843127810793316009378319236178984491977461⟩
def polyval4Tail33 : Box := ⟨3901058190153605344713449409920316523628581374249446860268,3575338086677089236415233153977775035899877914757383184321⟩
def polyval4Tail37 : Box := ⟨4726971506084470423066990163993335362708652040112566888259,3761811859290028263048080722681540234519479644570601983309⟩
def polyval4Tail41 : Box := ⟨5727743225090081168302177794740361236301837426001913508212,3910515684161500911901133992049037134002327756830378047273⟩
def polyval4Tail45 : Box := ⟨6940393528993501457814869898658353748314097476740268653633,4002992678821358119100800317451879010551752414262076475127⟩
def polyval4Tail49 : Box := ⟨8409780334825904512007500875571517131820279714408737156280,4015461902487241800575374821467947591947079133559093851814⟩
def polyval4Tail53 : Box := ⟨10190258662505695566002437178163389871356182644651339336228,3917499368153996751014626113786178139319507112370967081873⟩
def polyval4Tail57 : Box := ⟨12347691315878115039624612947924978873375201110820566762712,3670413832523510433228108933483585214811178481776864789503⟩
def polyval4Tail61 : Box := ⟨14961885255493795093748397331688313640875184872398052513992,3225249226657004465793895760953248964766449106276910817285⟩
def polyval4Tail65 : Box := ⟨18129543788544749665572427199852197081276986235579726509214,2520330688333851751090970961150659079281331863376963459723⟩
def polyval4Tail69 : Box := ⟨21967843839391681774154238989589551351546411979024637626387,1478253031340279325870503294924053418073780523560840995527⟩
def polyval4Tail73 : Box := ⟨26656250000000000000000000000000000000000000000000000000000,2⟩
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
def resval5 : Box := ⟨92701588538466408246591416445367881036909805628961121118,14996780588115600668762160351787468005032048249512676080⟩
def polyval5 : Box := ⟨8556829472528679171057994672785275550357531189710157297888,3743298317365569374008730525552752068006436397500906952835⟩
theorem cell5_lo : Holds Q cell5 (31/32:ℝ) := by norm_num [Holds,Q,cell5]
theorem cell5_hi : Holds Q cell5 (63/64:ℝ) := by norm_num [Holds,Q,cell5]
def resval5Tail4 : Box := ⟨-17987831818793803160087535702868899961062425189929471772,15170875397122682976473262876880527125917280383620883211⟩
def resval5Tail8 : Box := ⟨-19777886267177670848274129570951738621794309717561442812,15536848384945785874968816019490827541706041751400369626⟩
def resval5Tail12 : Box := ⟨-21746015929820179479754677375911712897328018850639114916,15864877116532055266209626775104634401991662685648464547⟩
def resval5Tail16 : Box := ⟨-23909997372644600294893250252706758341111267839848213535,16146349912899120505188856557743877048125578768136836259⟩
def resval5Tail20 : Box := ⟨-26289320131316366606459424347066238857329987829075571864,16371484436191986644627367870081042869137146342110379085⟩
def resval5Tail24 : Box := ⟨-28905413170708024550995173055728737568492416683127315437,16529190073905748539715224682706815270986412881370691609⟩
def resval5Tail28 : Box := ⟨-31781837886863009444354036653629837874608714832697416553,16606915980374147292376308354584921916411394711914692753⟩
def resval5Tail32 : Box := ⟨-34944500308697695641130223748829251330691346800775966682,16590482581279185645243800078092428261430533516291686181⟩
def resval5Tail36 : Box := ⟨-38421884416235137825172515625635580789072035067784363212,16463894803395150877282140586527781978554856039117408925⟩
def resval5Tail40 : Box := ⟨-42245308676716023911690391485358402776787767557080316820,16209135112997465108066799570407516209878689616732674577⟩
def resval5Tail44 : Box := ⟨-46449208109035612000894546841507289401965551249607357982,15805934249272885264520211090418174557955124585320113390⟩
def resval5Tail48 : Box := ⟨-51071444416871924640687533837530404363930820251388467902,15231517321946006361749381932524987119760599224465294834⟩
def resval5Tail52 : Box := ⟨-56153646983666356875369333103469184582794564071173734118,14460322703168011038662854617864489763065934326493789500⟩
def resval5Tail56 : Box := ⟨-61741587800569860531395397625159964853965490274789218978,13463690880274483922501729779495823007037030075211965124⟩
def resval5Tail60 : Box := ⟨-67885593704077148107191474222784930341620589499340684119,12209520145863944770660978500052625808713624634813014026⟩
def resval5Tail64 : Box := ⟨-74640999632782679355171688958723932914647750705738837962,10661885681849973603480497271448062807405259140785198208⟩
def resval5Tail68 : Box := ⟨-82068588632604012810120355428604426766280911787035631475,8780615158256982752582289782616698520684931390165290353⟩
def resval5Tail72 : Box := ⟨757695406959046545268325036267097748639241312719958545355,971094123934876678726130440566177001592848222687754027⟩
def resval5Tail76 : Box := ⟨-232420588606464272166751604621256904295920210132062432,199165767260263503241184281015287332247538837433575528⟩
def resval5Tail80 : Box := ⟨-255523171276436078020563905881833525516767745351129279,204099510270965076880631233615706918740991600224952324⟩
def resval5Tail84 : Box := ⟨-280950696697027529670111496223588922449229554550105031,208556576688848031394655084562163694695156403292999849⟩
def resval5Tail88 : Box := ⟨-308908557849482124523949768931794111738869009626583140,212426400013705692335999538895572068026304770757859823⟩
def resval5Tail92 : Box := ⟨-339648551275019068911989567799354209592970261775695256,215583522010858665747542366616132098685795340046343075⟩
def resval5Tail96 : Box := ⟨-373447531484156401627470529599534244597876117585703647,217885642237596623798820897403530428026253243682690412⟩
def resval5Tail100 : Box := ⟨-410609903231073813911801528163557344911633046469952553,219171658692133791291720898312387614503086419325383435⟩
def resval5Tail104 : Box := ⟨-451470363082543810972437464470942921765149446297861857,219259495082091358560796459331833229170366025039525429⟩
def resval5Tail108 : Box := ⟨-496396913805509482649687611445572469989002759454730598,217943692260705484833943729786535573455931331851166527⟩
def resval5Tail112 : Box := ⟨-545794178721278497945196370139732158884950526973471710,214992739086986171274350557414168351439900321483670252⟩
def resval5Tail116 : Box := ⟨-600107045876497983488034580604593372953786872759119537,210146115420829099382796400415505447351253596081127224⟩
def resval5Tail120 : Box := ⟨-659824674851515006530624404399397637416283080672338443,203111017160170713538354432980088905439447750272562984⟩
def resval5Tail124 : Box := ⟨-725484902292759196821650233847445201986210816726101353,193558730138599318025653107186556236897250985235924508⟩
def resval5Tail128 : Box := ⟨-797679085846824029783088894446538893595321511294943558,181120616299680850534378969692465717264730803979251607⟩
def resval5Tail132 : Box := ⟨-877057430122323067722422696018129334713700989145666323,165383671817033872994570953853333128618682150640597880⟩
def resval5Tail136 : Box := ⟨-964334842656031634032872734701396875503208245484393137,145885612701300502488390383199987142713141508613320901⟩
def resval5Tail140 : Box := ⟨-1060297449557124161083384924223115808992548218605327717,122109433260481394337481723114831450502457433648782382⟩
def resval5Tail144 : Box := ⟨-1211730867456848320963491559439958103270253843920086459,91132873113724666366150192230956836689898496377323368⟩
def resval5Tail148 : Box := ⟨86899330671880399797762082646885392062073303600,65392866348725016903216768223526472056666107113⟩
def resval5Tail152 : Box := ⟨95490155561145300055446975660571380905064535469,66648641834209058012495007423604948149631424248⟩
def resval5Tail156 : Box := ⟨104992535452939556622333376811082733223177848104,67688499658535393947939106890600041105612809830⟩
def resval5Tail160 : Box := ⟨115440513559921124729156218511438474702636486810,68468214784202903023841016014239066483413701596⟩
def resval5Tail164 : Box := ⟨126928186975565844319470779179952965953418334577,68938257416360493482380061486960922916552239716⟩
def resval5Tail168 : Box := ⟨139559017472160881216391447068389559381344578990,69042631748918050133485832892684175617389365890⟩
def resval5Tail172 : Box := ⟨153446762471634835222274401185827035632441394607,68718132555926839279072369600616423578773271145⟩
def resval5Tail176 : Box := ⟨168716499582144446700784884152302441095677907926,67893521320892650032386811656789418174827003286⟩
def resval5Tail180 : Box := ⟨185505753088232464416490309887678511984474043816,66488613460048105052361671882173885145631603167⟩
def resval5Tail184 : Box := ⟨203965732539855215901229856215389154586104190319,64413267342368674742627704150253817550577062196⟩
def resval5Tail188 : Box := ⟨224262694595420459230988447434797189068483784787,61566264854681954765511603633244052093705149315⟩
def resval5Tail192 : Box := ⟨246579440384042706884733025808088010443912307133,57834072208898354909728927482909804849299457484⟩
def resval5Tail196 : Box := ⟨271116961872753947229877006410264984518815545019,53089468530425002371444940620390624725431999021⟩
def resval5Tail200 : Box := ⟨298096252066395422167786191925232794095500147038,47190028491469243886856768178739035308096569248⟩
def resval5Tail204 : Box := ⟨327760295343447262811601726739456495376907728500,39976443848371747621266367635863258226039474563⟩
def resval5Tail208 : Box := ⟨360376255853428321771049689861170133550754207682,31270667195323163472641135209347304681618177928⟩
def resval5Tail212 : Box := ⟨396237883716707345250012388460025632155680340394,20873859540801393220895537305433214645933124254⟩
def resval5Tail216 : Box := ⟨435669612802582085501566789509229472899666322465,8564019287635763298899700697922996859831273427⟩
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
def polyval5Tail5 : Box := ⟨5306467760853268595046353607698719505578515533560946469097,3816830905848163298977578993185920291150295929511825152920⟩
def polyval5Tail9 : Box := ⟨5834520930514823215909777592805792884679937426859191182581,3881971130842719257811786204435378826408195899025751163786⟩
def polyval5Tail13 : Box := ⟨6415123605418732125411889203293016498599692551669734526835,3933133212637280222616054831672360992604446472463126099343⟩
def polyval5Tail17 : Box := ⟨7053502997778058755209166541207138295782549754029253754828,3967595820405794836645666279549462649952844286933560885992⟩
def polyval5Tail21 : Box := ⟨7755408562609848667111341123603507804172564794793629521327,3982280334735560407891776006370410993955192010778997813068⟩
def polyval5Tail25 : Box := ⟨8527161892743083114209928142723596763416931409600476817007,3973709655886139962394986394945047650108530255483685762338⟩
def polyval5Tail29 : Box := ⟨9375713652999424436531256884050475845577137545582707099832,3937962560609368187667396529490778216263313792485578794608⟩
def polyval5Tail33 : Box := ⟨10308706180171064386991381295420392302340338680962435598187,3870623127492228460315770671444594646321083517700499853176⟩
def polyval5Tail37 : Box := ⟨11334542312424398138273969254927827836677890099494996994038,3766724714758460968055161061056420593752708181061059642104⟩
def polyval5Tail41 : Box := ⟨12462461068029697145950843886973243659998591952877615678536,3620687921466607626494561146594334330295926813148139299034⟩
def polyval5Tail45 : Box := ⟨13702620855004359782055360718354074127534767407476905385543,3426251904660393807391995368502815002221121163109078380182⟩
def polyval5Tail49 : Box := ⟨15066190961083208499570756393330169094589661268576327877107,3176398360721857770653587318792302432699052771390352966744⟩
def polyval5Tail53 : Box := ⟨16565452148004656446111858633555393750871845330794335202443,2863267408351580753825555256028231109502237182071087162704⟩
def polyval5Tail57 : Box := ⟨18213907256098035513406683783711096369236331008746363121331,2478064532596976485432016784613022131197349554465713581290⟩
def polyval5Tail61 : Box := ⟨20026402815313455649762450501085446705161943376628020936085,2010957663446230926795542296449900591925491562907980554220⟩
def polyval5Tail65 : Box := ⟨22019262757969789605985865790388680071096442041427846842475,1450963367906463580108343416332118950575269786141628009972⟩
def polyval5Tail69 : Box := ⟨24210435493316040384431315447640628556354788655269336283136,785821026402081315110406183720217306085319163760872277336⟩
def polyval5Tail73 : Box := ⟨26656250000000000000000000000000000000000000000000000000000,2⟩
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
def resval6 : Box := ⟨74663979229571250273547064933112581615304847149822178283,13695723825700038131118462614770891882171828281665014478⟩
def polyval6 : Box := ⟨15122329837039679847800659104334996554085507299452257634474,3746284071160265579606479966212895742049690677990850510153⟩
theorem cell6_lo : Holds Q cell6 (63/64:ℝ) := by norm_num [Holds,Q,cell6]
theorem cell6_hi : Holds Q cell6 (127/128:ℝ) := by norm_num [Holds,Q,cell6]
def resval6Tail4 : Box := ⟨-36051358883708680356441675109517557478622588086077654923,13340659364843741909986496226668939631699515437820986671⟩
def resval6Tail8 : Box := ⟨-37792013324072357292612716309917234416515395330577852669,13174181457624950226719531896999709353912019476487376126⟩
def resval6Tail12 : Box := ⟨-39616655201521896842111009360904422725945991325877508421,12973833250231889208107916861498224440610128726702079217⟩
def resval6Tail16 : Box := ⟨-41529392881588048399877720748741391966114934648099888615,12737155506815946733966531270347596089357515614648556784⟩
def resval6Tail20 : Box := ⟨-43534479736866751161929341324465288993942177638979263478,12461544652454787579455573439820850530427260436964822365⟩
def resval6Tail24 : Box := ⟨-45636374491761850380740600831120013751439378976166492857,12144244333803919527509931941670508584195363026946055399⟩
def resval6Tail28 : Box := ⟨-47839751143014934825940902400220316258382094579852614388,11782337179776738230311927995926586506267026672275688694⟩
def resval6Tail32 : Box := ⟨-50149509353306273797423015393518899671425916409337622000,11372736137043296578629355164509509052356529692432974283⟩
def resval6Tail36 : Box := ⟨-52570785346665913871869283081931564052996457113154505375,10912175358820733163497241740631107054928286230632412227⟩
def resval6Tail40 : Box := ⟨-55108963329927738339541581160830498158801587902403428657,10397200624483261035332797498531119366125683708870855869⟩
def resval6Tail44 : Box := ⟨-57769687465624465358995108611998087907444528037332486995,9824159266405966236508871463865807376398825740457536874⟩
def resval6Tail48 : Box := ⟨-60558874422947787794877945258976606519961706536246092463,9189189579288178734135502203090883429262670923199086731⟩
def resval6Tail52 : Box := ⟨-63482726534683304588169489067503452819360379473582956444,8488209685976327080912905093163289180551697705621432128⟩
def resval6Tail56 : Box := ⟨-66547745589377396220135872744981987939962958805367337384,7716905832520172395708522804303020276864030520102794375⟩
def resval6Tail60 : Box := ⟨-69760747289403597922685515724810629334447022532200728042,6870720083846988316077952585843367235468167402902630987⟩
def resval6Tail64 : Box := ⟨-73128876403799421516320386914069825670149984436045988263,5944837389776651094130949165312177861280927185056586790⟩
def resval6Tail68 : Box := ⟨-76659564947568538219250015055429308187040032266750476008,4934168713673364851183907436694064356505953039772883847⟩
def resval6Tail72 : Box := ⟨757542524009467495787046392105256159034205572952413094842,926816098860166526768999455215988069410170985037287416⟩
def resval6Tail76 : Box := ⟨-469841100500604316938454224169095732520264979431663153,176028375439387763063893026007963277532151994173022856⟩
def resval6Tail80 : Box := ⟨-492500827295175304915848050966711069923233968754977977,173927971705297466797004656134474124683858250567765326⟩
def resval6Tail84 : Box := ⟨-516279332483644833446827817787651148929245934525673683,171388564669770413450431795658131230996700168480142828⟩
def resval6Tail88 : Box := ⟨-541205892477917360058878289769268300345152567292851399,168377994544268960672989029008903591474333710822976151⟩
def resval6Tail92 : Box := ⟨-567335935459785268676435438472419237666930893250759480,164862404474700029888634389020296138365647555918543709⟩
def resval6Tail96 : Box := ⟨-594727566971499097133085091083626918633775441010833935,160805948949578698086762515841554448673153345759688703⟩
def resval6Tail100 : Box := ⟨-623441697958352741152557076650636508320253092121871545,156170686482646671427442010094416897811814692437764261⟩
def resval6Tail104 : Box := ⟨-653542180216139990821481155089850945519850698491650701,150916466774274016609057640170310312626550684826312389⟩
def resval6Tail108 : Box := ⟨-685095948378797675370706631868919956683944619022553379,145000812053852604410790815925874997568274592236673157⟩
def resval6Tail112 : Box := ⟨-718173168761377065299779257823514944704620212780823149,138378792310391601814504653507812454575110747010168283⟩
def resval6Tail116 : Box := ⟨-752847395389325145093587821617305502249816171321186967,131002894104028173240086257325709961074632199663347033⟩
def resval6Tail120 : Box := ⟨-789195733561039050399134222297122264681178309567168545,122822882635941563108121722248827239897911680091709536⟩
def resval6Tail124 : Box := ⟨-827299011307408763203309417675555909219742626943561524,113785656738186214103062233172558721797479382677781149⟩
def resval6Tail128 : Box := ⟨-867241959129623786811225696019916906383452709286837436,103835096428203090936120868011382160966056546739559208⟩
def resval6Tail132 : Box := ⟨-909113398414937459855640689768288026685438045606124011,92911902655188609134021766318893973295414387331581233⟩
def resval6Tail136 : Box := ⟨-953006438958418987800432825592052603041993230962646629,80953428846264893655962972596039206191707924627881237⟩
def resval6Tail140 : Box := ⟨-999018762117951173381188471056619600652324711281110464,67893498543046409657613658887056217565066538540612396⟩
def resval6Tail144 : Box := ⟨-1092638968399520518217269561491385345981535306621279921,51516196356197545923533374164565886734556018337661203⟩
def resval6Tail148 : Box := ⟨200241067113867954369217803697395476046622110064,64588745563950268070588896124985635632523163357⟩
def resval6Tail152 : Box := ⟨209854931644336413004126109385070780060874768808,63361339062298968705716891990321954760518530168⟩
def resval6Tail156 : Box := ⟨219986968237908706678000819359577620267018620084,61936709692554028839181736476629098159595731899⟩
def resval6Tail160 : Box := ⟨230608192092383421138489455746297607483413763028,60300399187778575527163313286826100268770082377⟩
def resval6Tail164 : Box := ⟨241742220851301350842236542176279955064037345265,58437633150026319086476964352819614693345949753⟩
def resval6Tail168 : Box := ⟨253413813325019352814980531629884436995268809302,56332778728975013394404228370107486388355263572⟩
def resval6Tail172 : Box := ⟨265648923707991384838372290103175905972557133371,53969298534995178556650945224209404965953070983⟩
def resval6Tail176 : Box := ⟨278474759293032464742814279163606278145379932143,51329702193857979970136919941206835348584717702⟩
def resval6Tail180 : Box := ⟨291919840972348450332203756841500661750424752275,48395495410336728827375869194724817286872154696⟩
def resval6Tail184 : Box := ⟨306014066659625524037993608847477944997239602787,45147126415574078371376511869672266099320351811⟩
def resval6Tail188 : Box := ⟨320788777774211108018257338704899675490626920957,41563929666897577221906561175716885783994317710⟩
def resval6Tail192 : Box := ⟨336276828935227503736039136835768028629585513851,37624066662266672852072598375859512383469922108⟩
def resval6Tail196 : Box := ⟨352512661020597499977645767098331121417809606426,33304463724715788068726554280894703707367620779⟩
def resval6Tail200 : Box := ⟨369532377753443769680264069712183934581806914294,28580746605005176410305194531933070768400318560⟩
def resval6Tail204 : Box := ⟨387373825986167746091669446162174375922012719114,23427171743187580861089700714603399746521260330⟩
def resval6Tail208 : Box := ⟨406076679860748020149870000739958766557343967621,17816554021925950997056098631351865864571744474⟩
def resval6Tail212 : Box := ⟨425682529063484422441001794199079550051800408439,11720190833574075151825750378519078728722511424⟩
def resval6Tail216 : Box := ⟨446236407017496758380141737792516597847014029492,5107686490580910558181506055636937010136003334⟩
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
def polyval6Tail5 : Box := ⟨11942280323864878988489026330132035916783628966256941221685,3675244202210868989441145488921364481292424072980178949838⟩
def polyval6Tail9 : Box := ⟨12518865377178722004145015960957731111529407275954103038734,3596388014439943330035261844666370435045176878916069742133⟩
def polyval6Tail13 : Box := ⟨13123290596566125011226289200713800914122901301796112065389,3505556248251181712196890057653261863058398472035171311224⟩
def polyval6Tail17 : Box := ⟨13756898160928998010934960319556596999385813878744358986467,3401910371062486245599544562345873491604662808042288072696⟩
def polyval6Tail21 : Box := ⟨14421097027272537256856466489986403379810425543246210471016,3284563081642889361349999591317880983455665170509302248744⟩
def polyval6Tail25 : Box := ⟨15117364178842246783407443576198155110197026242617859421118,3152575677876624502193527301318330502893262212162009403585⟩
def polyval6Tail29 : Box := ⟨15847247909333669930071395137888873573425359621894719156822,3004955302228565854439813924153507331049158438088031807962⟩
def polyval6Tail33 : Box := ⟨16612371265842812999861399064193867120314031394718639692565,2840652045524855093643326947963245162712076550273161020776⟩
def polyval6Tail37 : Box := ⟨17414435658046300310384558206678009102520992204127420383962,2658555901928252339870227202680221871717795675494747159614⟩
def polyval6Tail41 : Box := ⟨18255224641636898780984521885723592701934639300895016212662,2457493567637765420409081568015096827281841676212524209065⟩
def polyval6Tail45 : Box := ⟨19136607884427661344407356214633467299513260045451485026088,2236225075472319505662985122146041408270261091167135261279⟩
def polyval6Tail49 : Box := ⟨20060545323944140200955568666794397399130749557179203257809,1993440257110289722455019433243937825937559942961748446452⟩
def polyval6Tail53 : Box := ⟨21029091525749934176352908783967250588463876834805115593841,1727755024349750012160876189786959653279645252661756917073⟩
def polyval6Tail57 : Box := ⟨22044400252197206467186573524656185584628266809238370934367,1437707460327363962805535442524206615976487722035251673810⟩
def polyval6Tail61 : Box := ⟨23108729251761739035687555339887462573080602112928303845611,1121753711185983421749510201723573040264535061415618824234⟩
def polyval6Tail65 : Box := ⟨24224445279619113164494467029935687733025447072772654475722,778263668210652230218822178404946635008527029596861360349⟩
def polyval6Tail69 : Box := ⟨25394029415847308545963666292005443012146193614496544039011,405516426284709976427319675117379436790012426662243325796⟩
def polyval6Tail73 : Box := ⟨26656250000000000000000000000000000000000000000000000000000,2⟩
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
def resval7 : Box := ⟨53198423671258937285267285514354328471373947748792917848,22346143434633446402992401426745748669759354670348188662⟩
def polyval7 : Box := ⟨23812758518545569095006694717232589496964398942892656224109,6542371117983513947884271088835080714823915891858911983186⟩
theorem cell7_lo : Holds Q cell7 (127/128:ℝ) := by norm_num [Holds,Q,cell7]
theorem cell7_hi : Holds Q cell7 (1/1:ℝ) := by norm_num [Holds,Q,cell7]
def resval7Tail4 : Box := ⟨-56733414595288383138821780521604504279582597078561402608,21244676593908346609324838534200542903318654665278600035⟩
def resval7Tail8 : Box := ⟨-57628650809945167263329332088908406150348756010735742687,20349490653164436919906800334396331137795796179933126048⟩
def resval7Tail12 : Box := ⟨-58537961090133336380199413807228204176557270379504136211,19440180378507694797204777813061082754460289967356901986⟩
def resval7Tail16 : Box := ⟨-59461619178892306246944364919439695347772430824558564582,18516522289753278536934122152917054220166573757810166613⟩
def resval7Tail20 : Box := ⟨-60399851472983322079859372295020029245284110946199645831,17578289995662278994048410877444867529432301281652605961⟩
def resval7Tail24 : Box := ⟨-61352887935710006967023321327685755476127124106970123387,16625253532935594299858492723618727210622699735115786012⟩
def resval7Tail28 : Box := ⟨-62320962158913517689973375114503704925096204594558390547,15657179309732083583180289392801639212256931418537551674⟩
def resval7Tail32 : Box := ⟨-63304311420231177373314356455873879931031504475322323539,14673830048414423900293995004003904450284412006595366221⟩
def resval7Tail36 : Box := ⟨-64303176741253889030830111694225015654327964327179068929,13674964727391712242809461267452711410173642463819270922⟩
def resval7Tail40 : Box := ⟨-65317802946601186257745777203739737577772192318984025251,12660338522044415015807921513723372563549753587303606429⟩
def resval7Tail44 : Box := ⟨-66348438723928416454808909140172049607005030311909778356,11629702744717184818272136076641589120710682121846967025⟩
def resval7Tail48 : Box := ⟨-67395336684880764678354936809296412266648659332759907807,10582804783764836589984191542414532498307811821771073799⟩
def resval7Tail52 : Box := ⟨-68458753427009058034746233937253216101691382467649943272,9519388041636543114793199458083904764907664428676404400⟩
def resval7Tail56 : Box := ⟨-69538949596662519028666911861825677764461248695143183137,8439191871983073252318302122126029862902927765915100552⟩
def resval7Tail60 : Box := ⟨-70636189952871721563343053569663135129498935214895054814,7341951515771444362706597824379796204859693241058413199⟩
def resval7Tail64 : Box := ⟨-71750743428980588171932219945160752582331213544190391756,6227398036147006505907432349027537398632417219818659117⟩
def resval7Tail68 : Box := ⟨-72882825915925887040276073867205196116167223971643134864,5095255001987935877836614360695495649760073032761776762⟩
def resval7Tail72 : Box := ⟨757316223037119578338600843287446604305246806700537101223,1038507048914478356775638466079577281182926832555633157⟩
def resval7Tail76 : Box := ⟨-741981386699951164488633404941195631519387599799219444,279963984617501239905642978400266324805377132340784284⟩
def resval7Tail80 : Box := ⟨-753664989678326339341251493636034084229843310009701207,268256599976834994602359145598067900636139767732566218⟩
def resval7Tail84 : Box := ⟨-765556908725097569151245990397113573585526148074059297,256364679742613202963541107675693536588414777514631435⟩
def resval7Tail88 : Box := ⟨-777636469029919662124264867420154222422431988680097048,244285119437170122689730642974869840124235319342413656⟩
def resval7Tail92 : Box := ⟨-789906630158758682575938360788420429693695190926578045,232014958308329519507507105617023485179277688975328505⟩
def resval7Tail96 : Box := ⟨-802370399561032589252411853732881967574956830414134588,219551188906055598431656443481414450896544351735769994⟩
def resval7Tail100 : Box := ⟨-815030832140677026518962872410985741982512279188686313,206890756326411160777442727260074282736101734002892367⟩
def resval7Tail104 : Box := ⟨-827891031004311268823574702959016034990467449150902914,194030557462776918446003766111748476434769758055129817⟩
def resval7Tail108 : Box := ⟨-840954148221816660782479357032795859951665923407898690,180967440245271526483086675102110777339883360847170856⟩
def resval7Tail112 : Box := ⟨-854223385598917545662204174364064560790253482165854048,167698202868170641602763547509491399751053487729478142⟩
def resval7Tail116 : Box := ⟨-867701995461952596918128469712039686230718027260198980,154219593005135590349768511241533307673440801578305937⟩
def resval7Tail120 : Box := ⟨-881393281455028890641756412477805979661871256820506550,140528307012059296660093455406322906855350880908805545⟩
def resval7Tail124 : Box := ⟨-895300599349754103986445289770274273705279142892020585,126620989117334084055117920482022067759645602134359603⟩
def resval7Tail128 : Box := ⟨-909427357867745352524489482685418378347195035540313481,112494230599342878868501004934625394840374491462698881⟩
def resval7Tail132 : Box := ⟨-923777019516125759613614510908256417196001048412232565,98144568950971147270043959921472893394490994743998176⟩
def resval7Tail136 : Box := ⟨-938353101445200606345329307700306448743393102121082927,83568487030146654704525015608107972882984189642696396⟩
def resval7Tail140 : Box := ⟨-953159251863430377460424357131067695335593208685539404,68762406944367649906714018282921183537101527652874000⟩
def resval7Tail144 : Box := ⟨-1013235548767877625190117939592734266437472139939024427,51595095331442812908782132576689456759493292771774837⟩
def resval7Tail148 : Box := ⟨347466338775591059925324596209686671233941681312,111095556102394736101536324322649220980001819738⟩
def resval7Tail152 : Box := ⟨352896621966412505854542200221174366276707093591,105613272245068292630009012351298804246768125680⟩
def resval7Tail156 : Box := ⟨358464902162568313440026313009523387664300344584,100044991195938952667726705871791739896677398793⟩
def resval7Tail160 : Box := ⟨364121043924878429200818302299401054398021501998,94388849433377929426302360672380442025946087898⟩
def resval7Tail164 : Box := ⟨369866432750241869537814496523981201583479004214,88643460608014083249899656990003732219028917618⟩
def resval7Tail168 : Box := ⟨375702476848914828842146721633200857145102383084,82807416509341121458164860077729984190516344220⟩
def resval7Tail172 : Box := ⟨381630606651252212084847058244438127619073715759,76879286707003738168586851064187588539456136883⟩
def resval7Tail176 : Box := ⟨387652275158066896364063452038864475787392102803,70857618200189053887018540574333584739759309526⟩
def resval7Tail180 : Box := ⟨393768958296763818361155842646404406807722344035,64740935061492131889652597981263117711629225266⟩
def resval7Tail184 : Box := ⟨399982155283093811993972123821769908171643280530,58527738075162138256782162576703026758886938857⟩
def resval7Tail188 : Box := ⟨406293388988615485444261187715915219314744264269,52216504369640464806520975889153492129476778390⟩
def resval7Tail192 : Box := ⟨412704206313955201343949518997929119773202370390,45805687044300748907225656322075004056510547983⟩
def resval7Tail196 : Box := ⟨419216178567956647133014533873221335006305424635,39293714790299303124231660807186785365507220387⟩
def resval7Tail200 : Box := ⟨425830901852812926407359404090523668184619542693,32678991505443024071973875155175377044626535707⟩
def resval7Tail204 : Box := ⟨432549997455275594856344372128718229643663489029,25959895902980380079914090857361668791884915002⟩
def resval7Tail208 : Box := ⟨439375112244048273905913294886671665699094507310,19134781114218377453830830844401937137910474336⟩
def resval7Tail212 : Box := ⟨446307919104321456667945852897834755960835334822,12201974282324271321754060124928818652862372747⟩
def resval7Tail216 : Box := ⟨453351542290516468484510387169245056994703867842,5159681184958557217786684886382965534760104012⟩
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
def polyval7Tail5 : Box := ⟨20399927182075750091993482970137449881601372871870330193366,6222117208992442604817545366880100605036095577489374434661⟩
def polyval7Tail9 : Box := ⟨20721811397672632322726844047700001929362062924602843725862,5900231096129643684365050915839931007475619283755816307555⟩
def polyval7Tail13 : Box := ⟨21048776470331395624242634653856372731793706497430833653978,5573266023300710656456575496574825390157786414859104626105⟩
def polyval7Tail17 : Box := ⟨21380900655785308256972500267822652313693115722717732368304,5241141837846674212516365781706700724309496251153718340522⟩
def polyval7Tail21 : Box := ⟨21718265358412345887248525885700140915030448169387959906150,4903777135219636182280614344634634100766011022628171642868⟩
def polyval7Tail25 : Box := ⟨22060953267222834987611797045361729946983190907893604476185,4561089226409147077552261271586826703469007965504595344116⟩
def polyval7Tail29 : Box := ⟨22409048375959602682176166253299517854081323758763593438486,4212994117672379382852207740985085371307248649318133588885⟩
def polyval7Tail33 : Box := ⟨22762636003684953310226655530116742969974472497827626465123,3859406489947028754791215309521439645864628704324744547097⟩
def polyval7Tail37 : Box := ⟨23121802815692603357613239403452592154186246076878410869575,3500239677939378707402945545730904984205215781830797492407⟩
def polyval7Tail41 : Box := ⟨23486636844749581751684743166447332931024293196654644762524,3135405648882400313331251696470638289625545324379915134573⟩
def polyval7Tail45 : Box := ⟨23857227512673301605241513020603661063169402274129442451407,2764814980958680459776283446832421120831223270317978412140⟩
def polyval7Tail49 : Box := ⟨24233665652249092005270604427025448893102404009081956545573,2388376841382890059768049781950292456808018954504464976965⟩
def polyval7Tail53 : Box := ⟨24616043529493561893746937039977173168965826746689731174011,2005998964138420171765575749698421489868160598378544058134⟩
def polyval7Tail57 : Box := ⟨25004454866269252882253816464957191484473455623237513156205,1617587627362729212304000646137101885081856408473415279360⟩
def polyval7Tail61 : Box := ⟨25398994863256130533941316293732345691182272266662649537178,1223047630375857621977465907750872127300757566369903239063⟩
def polyval7Tail65 : Box := ⟨25799760223292014718450638491382013265778209449634328868530,822282270345927351042975129401793042098891717660207887627⟩
def polyval7Tail69 : Box := ⟨26206849229907309305637596028463631331831469567291499714968,415193314942841189054738806432142713130702690518370757407⟩
def polyval7Tail73 : Box := ⟨26656250000000000000000000000000000000000000000000000000000,2⟩
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
def pend : Box := ⟨1030350037279067114154763372090335748914369554862219076593150,5092357461968888127593715731921297418759972532491614214⟩
def zend : Box := ⟨1003724895910728141144960937500000000000000000000000000000000,3405117040933954140625000000000000000000000000000000002⟩
def betaquot : Box := ⟨428745259451727429107640686532731269546256820826393536631198,394761207583293054307402326721983953761136968126875887⟩
def crit : Box := ⟨106933283595904187464645143088450444882498222710350260744,13127819136982251172502239750491463433827166202811218660⟩
def subsonic : Box := ⟨580386446567631667800804201128378043227867028015900874255,7190144706403394251796908793965799634630323899119991876⟩
def pendTail4 : Box := ⟨26620466022210149838326204999044386825244234870252677782805,1543178179241237463030613805984492324307202212559069178⟩
def pendTail8 : Box := ⟨26620499480705932429226008152325082795550027910796737900927,1543011581808613818631202743515822396447038446467986641⟩
def pendTail12 : Box := ⟨26620499482067852517798279889931745646741369807477518351590,1543011563510683062055543745122952472254667037655709153⟩
def pendTail16 : Box := ⟨26620499482068484317036293751834925988131914936537422613285,1543011563496352462438064374616732150797413507576028423⟩
def pendTail20 : Box := ⟨26620499482068485751389295976563665722083064847831761159551,1543011563496302410846797257989842492041080379865296650⟩
def pendTail24 : Box := ⟨26620499482068485762950633545092296029612308188043966459794,1543011563496301798113942920752799340215984510374420938⟩
def pendTail28 : Box := ⟨26620499482068485763223146629413117539565620208481990728713,1543011563496301775496824867512657622282894398607054046⟩
def pendTail32 : Box := ⟨26620499482068485763239269983235959788373240412901643290601,1543011563496301773198828939642247470218771043910959149⟩
def pendTail36 : Box := ⟨26620499482068485763241193409784352561219549753722684836954,1543011563496301772588686478540186084646181048956889031⟩
def pendTail40 : Box := ⟨26620499482068485763241235384633610320207415465775277607849,1543011563496301772175302162306402819473149792564067021⟩
def pendTail44 : Box := ⟨26620499482068485763239552085642306327932659356753257790148,1543011563496301771461025313727314217138299684104479012⟩
def pendTail48 : Box := ⟨26620499482068485763225501293228265286845566909957328932552,1543011563496301768243278752427556157698961860582671817⟩
def pendTail52 : Box := ⟨26620499482068485762986346205854885313177456917129237854379,1543011563496301728566242909172984186137051991878771597⟩
def pendTail56 : Box := ⟨26620499482068485752180158100392091966833411383188717674992,1543011563496300269919090163351656549536071657100988295⟩
def pendTail60 : Box := ⟨26620499482068484173107724211321283402001435696681964188525,1543011563496119159950151617777478507514540600929818860⟩
def pendTail64 : Box := ⟨26620499482067499898111373738243776275288624003648090301872,1543011563409519877267306499627682948341061870940507335⟩
def pendTail68 : Box := ⟨26620499477692945430932123779104856080847368399947952840312,1543011267823629285302611277727482434373700470733035392⟩
def pendTail72 : Box := ⟨26619919810929468864358071434855088603715973107813365584739,1514364680129697534098699507294699844926579208317018841⟩
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
end SepticProfile.ExteriorCertificates.C10

end
end

end OAI
