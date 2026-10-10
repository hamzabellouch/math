import OAI.MathematicalPhysics.Transonic.Certificates.BarrierData34

namespace OAI

section
noncomputable section
namespace SepticProfile.ExteriorCertificates.C34
open SepticProfile.ExteriorJet SepticProfile.FixedInterval
def cell0 : Box := ⟨250000000000000000000000000000000000000000000000000000000000,250000000000000000000000000000000000000000000000000000000002⟩
def resval0 : Box := ⟨121427163362180812555846834793356935422513864634506913538,305783601366777779889189645574451665936524015266732640⟩
def polyval0 : Box := ⟨3857743947997213320311455805042455816302017200337359288406,14800784606825636040069028837527994381511854323263475305⟩
theorem cell0_lo : Holds Q cell0 (0/1:ℝ) := by norm_num [Holds,Q,cell0]
theorem cell0_hi : Holds Q cell0 (1/2:ℝ) := by norm_num [Holds,Q,cell0]
def resval0Tail4 : Box := ⟨65821047971990138424433070609246604477203485058603,1891173935805261672308540835525632006870480812589⟩
def resval0Tail8 : Box := ⟨8398103160852691678127266803324544439447120206,441233195798138860261455028789044898573654377⟩
def resval0Tail12 : Box := ⟨8053543398749052194995085903996652429983413,643931481402599484065576046571958333246490⟩
def resval0Tail16 : Box := ⟨33978915264102678754446523244354030462063,29296507861282212559446857808241717180415⟩
def resval0Tail20 : Box := ⟨487316794516878888059717682839516698501,406946083040480134102374572264606849167938⟩
def resval0Tail24 : Box := ⟨20386832015704084563634583491681135160,6509909163085034945659122201487611228525958⟩
def resval0Tail28 : Box := ⟨2263589698625489462806982722319811034,104158476079910356241843309689423260900131524⟩
def resval0Tail32 : Box := ⟨628027966135393684958332640616629348,1666535606470967932547935995311229871011601732⟩
def resval0Tail36 : Box := ⟨-153842460428949890735530385533499644,26664569699326771613666592569171027971136199761⟩
def resval0Tail40 : Box := ⟨-148116358133815867367428675569314364221,426633115048182076944783806375583680711094962391⟩
def resval0Tail44 : Box := ⟨-38094580591411940811156607614329937928541,6826129805051840063419977728917686030907216757175⟩
def resval0Tail48 : Box := ⟨-9752908051338348346004576938375191077546336,109218067737440616502345419914543321658961245044378⟩
def resval0Tail52 : Box := ⟨-2496751109769725061638767187491221038902205248,1747486743094095594849486718689851671873773554548203⟩
def resval0Tail56 : Box := ⟨-639168423516927018528856825553753095838642970893,27959188669053643887796915260740813521513732549790168⟩
def resval0Tail60 : Box := ⟨-163627111371171183949943721593029247085123654694524,447193618272749549101448176144184813974842425711369616⟩
def resval0Tail64 : Box := ⟨-41888505777492353091160890063064101285011374200071980,7115827394948707118911100204145074445923223043384693953⟩
def resval0Tail68 : Box := ⟨-10722647648009157395756508266639476498400820808551532867,103800339104406156577687650879737380921870475914676918688⟩
def resval0Tail72 : Box := ⟨860618805169688644449721208085252592381429203044077929352,2580287283054446217948166326726308731208054758937481961⟩
def resval0Tail76 : Box := ⟨-31059515747704648047141472889115601236590609383630,660911931093968398167424028281370572203908471446⟩
def resval0Tail80 : Box := ⟨-1770864977613033758872520576167146200896195596,79934397839952992255891339564291824535321232⟩
def resval0Tail84 : Box := ⟨-1056223386676589288495430329131409269577958,75210102020663673364392768525090317395998⟩
def resval0Tail88 : Box := ⟨-3080067034916039930544495478623456325631,496077884987086867427770380531445445599⟩
def resval0Tail92 : Box := ⟨-32311654110042924796739863930373414209,2856472623771911482611764894825882288929⟩
def resval0Tail96 : Box := ⟨-1023568009266242162502664872163607739,45629149670445161759464336900708614433748⟩
def resval0Tail100 : Box := ⟨-87941730638358431112841668031360009,730063151564299700698280740598990771881654⟩
def resval0Tail104 : Box := ⟨-19205084053627538413096958217734873,11681010041153288680028323346062176983838290⟩
def resval0Tail108 : Box := ⟨-12288171797738052752544654703245089,186896160540549073081939203246782088897713149⟩
def resval0Tail112 : Box := ⟨-528912174144843986873128093543600059,2990338568162219138495926760838381313671948911⟩
def resval0Tail116 : Box := ⟨-132033870751110637794894650880867176328,47845416966863834251341697616507475062956595764⟩
def resval0Tail120 : Box := ⟨-33790195135046031668566838682918308373503,765526639791795331616845023745509644760462173187⟩
def resval0Tail124 : Box := ⟨-8650210527475898675787961935044105349379966,12248418127101199410699968663118958620914813738408⟩
def resval0Tail128 : Box := ⟨-2214452494380700764093710039133461764596396469,195972613984683583741333302960773962486727778232381⟩
def resval0Tail132 : Box := ⟨-566899825316861990656155772037718823500011968210,3135030355227893314337448561016968604939551027686303⟩
def resval0Tail136 : Box := ⟨-145126445160490132139039193558177230140785354112567,50024429702169745287705342101501623907386241977734763⟩
def resval0Tail140 : Box := ⟨-37153513189173033076566911939013510908281388763215880,765560022696996154441082242747261402319856505533234165⟩
def resval0Tail144 : Box := ⟨-10082218454115936282503206324154289398280923465330468887,3053643089394003137790396638399595429330705952701963370⟩
def resval0Tail148 : Box := ⟨76409323695678477647193055435054587156201051,1327434292802261206073152194115829185039509⟩
def resval0Tail152 : Box := ⟨1437402220413793503129129795327074079514,57753336245415846417399667729060160804⟩
def resval0Tail156 : Box := ⟨481735683795871362040993384201116520,31211028018954586875768667692131807⟩
def resval0Tail160 : Box := ⟨889653725707352150291031790856775,86030520200070288934464051865053⟩
def resval0Tail164 : Box := ⟨6258661538543666836737180957527,35868952134921938292830541813365⟩
def resval0Tail168 : Box := ⟨137245380597915187909439699983,560756394816308319293047216397840⟩
def resval0Tail172 : Box := ⟨8301190398178849053446057178,8971707814584431088074947968046721⟩
def resval0Tail176 : Box := ⟨1284058305602827755272912556,143547292469873915991001005130693764⟩
def resval0Tail180 : Box := ⟨494176305098567280672835798,2296756672566240101222209063942803706⟩
def resval0Tail184 : Box := ⟨2511501804735436447683988149,36748106756490559850772961126071863088⟩
def resval0Tail188 : Box := ⟨530859729160519605394981259098,587969707607502090355055504312651260559⟩
def resval0Tail192 : Box := ⟨135658419040721487691449729534888,9407515194545070117400778512394384621321⟩
def resval0Tail196 : Box := ⟨34727301228600410772859087190134128,150520210555927027174104742384961695455117⟩
def resval0Tail200 : Box := ⟨8890173520402254622477450509155160354,2408315034358847124908365172421652784390423⟩
def resval0Tail204 : Box := ⟨2275884054515222365523043610522451460270,38530906908635811888118685562294310176456001⟩
def resval0Tail208 : Box := ⟨582626403169731273852800807259954273483040,615948298377536022797390232233700504010724577⟩
def resval0Tail212 : Box := ⟨149152863618436801995095372324440294987057394,9715342237230444017580981982810971256975525295⟩
def resval0Tail216 : Box := ⟨38212716085159058094509967098031849639602788689,119634762067746401425364811728445847349264020672⟩
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
def polyval0Tail5 : Box := ⟨2243419712496735026362118882406785261783025759426728,54774343581192422029425513109213981163325638857001⟩
def polyval0Tail9 : Box := ⟨229424854581095943683705154859960375233142909699,11079889544214847175300908858198478474483625043⟩
def polyval0Tail13 : Box := ⟨190365708669401878368934753739073376695302228,14266602715497973229077138864224634738237960⟩
def polyval0Tail17 : Box := ⟨703811582041479718728469149685552609468741,463571109350442747625955582646087292751833⟩
def polyval0Tail21 : Box := ⟨8869425528984250973402124998404867538817,6206676519607209491224885327194829299774487⟩
def polyval0Tail25 : Box := ⟨325675114303216066032086887878562274307,99285628779462118599758679173739675407308049⟩
def polyval0Tail29 : Box := ⟨31625296196336056178787361278133876777,1588568992841365454845420855181061211912221821⟩
def polyval0Tail33 : Box := ⟨7680767270910858584377318344035411420,25417103742871042929288095166469753667032544558⟩
def polyval0Tail37 : Box := ⟨10355582261629956016869734922017474048,406673659835820782086829458382434371252745424613⟩
def polyval0Tail41 : Box := ⟨1510261459269518538511738776444751162972,6506778555968923488376437993640578656759429492386⟩
def polyval0Tail45 : Box := ⟨385041256146795151178332442382649490944687,104108456534551361843805745843590444660354186480203⟩
def polyval0Tail49 : Box := ⟨98565288383637493551026803587080838342571434,1665735212148013434306648048709090325875172143394065⟩
def polyval0Tail53 : Box := ⟨25232671517374640467767025578499445637629704817,26651739738741390197483178286860341125465658158332547⟩
def polyval0Tail57 : Box := ⟨6459563130877650537095017673893718560412080598012,426421779979590929878503979082187678421876426439521228⟩
def polyval0Tail61 : Box := ⟨1653648155814339000287160768961356802138352515138835,6821198184563465025168380343681799123109526840279543601⟩
def polyval0Tail65 : Box := ⟨423333983348328412652800090656321734942915220790019740,108742295381173509562960921159190872527601452431854081287⟩
def polyval0Tail69 : Box := ⟨108374167306799279704711156563409387626139885436371502831,1638276277198750714316248778969966713763921899732701651722⟩
def polyval0Tail73 : Box := ⟨28156250000000000000000000000000000000000000000000000000000,2⟩
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
def resval1 : Box := ⟨121182768999191061170985140868755603809676479400125103973,222270889986323114740344650219878543396263467740576867⟩
def polyval1 : Box := ⟨3839067236827689012727521259880597338663239800297228082147,8432601963253330466301906741065184084589296344115106841⟩
theorem cell1_lo : Holds Q cell1 (1/2:ℝ) := by norm_num [Holds,Q,cell1]
theorem cell1_hi : Holds Q cell1 (3/4:ℝ) := by norm_num [Holds,Q,cell1]
def resval1Tail4 : Box := ⟨63887278373438877207766665480018369583061951258247,3256728232645723995661970012560246275934666215910⟩
def resval1Tail8 : Box := ⟨7918008737381305676707816009863943999322928658,6574603913426752111162185995615447036524447540904⟩
def resval1Tail12 : Box := ⟨-334289154433840768992577531385089956318769002,20778040508091023977575197478727487977487023030007⟩
def resval1Tail16 : Box := ⟨-2239685165620712836124395114248882663121969374,65667708176026827034736293709952739492120860319954⟩
def resval1Tail20 : Box := ⟨-14678201444116812993626371756867818680657618825,207534786735000136258523320467780785060733784270112⟩
def resval1Tail24 : Box := ⟨-96195063773059257876029294996515826815826744779,655862607699561209434388494587536053406400428215672⟩
def resval1Tail28 : Box := ⟨-630423970055185087041236101872635345775570749280,2072523323035098721187275390980351834150677328762568⟩
def resval1Tail32 : Box := ⟨-4131546530165404162584947553267439835657615500680,6548058073634276357404855855558179090188531864476553⟩
def resval1Tail36 : Box := ⟨-27076503340094956166934566431514220268328958104384,20681078345574684974508077758667488458165274406208962⟩
def resval1Tail40 : Box := ⟨-177448572289647936643412021630336090595796999400966,65270546999589163041196418091981232321117135912375523⟩
def resval1Tail44 : Box := ⟨-1162926963357438111535492635860168268489875559258274,205685059041592877352401571261808522846699396889900530⟩
def resval1Tail48 : Box := ⟨-7621358147059299983889698223203668484328925032693121,646120424782166373764060329688827403922913985775619876⟩
def resval1Tail52 : Box := ⟨-49947332752567437249910938144878404632513431851393570,2016199536752145340322573777423775205497672341348218392⟩
def resval1Tail56 : Box := ⟨-327334839927187011396643638918026801338036685932773282,6202709587149397152618713046517178242571103816692430934⟩
def resval1Tail60 : Box := ⟨-2145221606934277440338587268017924011930075437916894198,18492943495913385135403693335342918827281457271743654908⟩
def resval1Tail64 : Box := ⟨-14058924302899806305564583971631715877724523458248370917,51167869090402180249662878656153437901301790380773164377⟩
def resval1Tail68 : Box := ⟨-92136195034603062382708711581819411015214638040602138948,114012359848224435203319577702896439239438383132895893664⟩
def resval1Tail72 : Box := ⟨863772573342925226308295455059333024646506548449961179095,1528405140720293435702469568136856322969303099787398349⟩
def resval1Tail76 : Box := ⟨-30357873236767137375102008049677451471766597773453,427970248440579614868863367049782689976771928834⟩
def resval1Tail80 : Box := ⟨-1691533030128839509747943538192321518346849419,69137714465699149423501875726345663525368587634⟩
def resval1Tail84 : Box := ⟨-3966905349361245360022168861895608899902515,218354574534115344366556423367409694352047404362⟩
def resval1Tail88 : Box := ⟨-19542159274653711772654560230641923320482404,690098186591821396840517879774229635405619272833⟩
def resval1Tail92 : Box := ⟨-128053157636646293915478710448122045025267061,2180984759805396403332943481737055796665668914255⟩
def resval1Tail96 : Box := ⟨-839208987256641491463949310853081533472860605,6892554372634037805994215187545709036836666708256⟩
def resval1Tail100 : Box := ⟨-5499840013190252623525923407469480959707635803,21781028022885972971171214681737823129431330988541⟩
def resval1Tail104 : Box := ⟨-36043751509979033011261505464406675901735709768,68820143074442713362545800554977145467905800173791⟩
def resval1Tail108 : Box := ⟨-236216329895705324245452079442475757134619777449,217383337095337452694226612502623999064087286250382⟩
def resval1Tail112 : Box := ⟨-1548067339604452148511869054147517897313926636924,686237187930268227205710001011231326558815840698310⟩
def resval1Tail116 : Box := ⟨-10145414116831702714233214696537654809477758448437,2163595639575605399148973973446977221051376286726929⟩
def resval1Tail120 : Box := ⟨-66488985956068278987277342127500338249180099158150,6803606196084226842601439533797615774612633329203331⟩
def resval1Tail124 : Box := ⟨-435742218361692235752591154402717171278079465641678,21277151196481712587095480530573033880433766098649535⟩
def resval1Tail128 : Box := ⟨-2855680202255437115480626818920728277619955408189442,65767785405151091448553489479397406394571320825961708⟩
def resval1Tail132 : Box := ⟨-18714985773559020398931817290777469860041228366236647,198169053677057629918345371399855830657153507334463176⟩
def resval1Tail136 : Box := ⟨-122650530825227334318326953201031435449775940005697422,562810137117232683832094970561147540138345644318543831⟩
def resval1Tail140 : Box := ⟨-803803062900372971952991404774896245894965425537766898,1362591594014343823322014395146606618017014061424513942⟩
def resval1Tail144 : Box := ⟨-5507643775178589128133660888856468192241668490790825331,1537084643493974537398996946964984468050649336439115649⟩
def resval1Tail148 : Box := ⟨75261583599108029543053266637668376065706577,922331661752536604665280738232334319610821⟩
def resval1Tail152 : Box := ⟨1381756615954585186876170287080675195124,3658362225171202843409785654570733003924⟩
def resval1Tail156 : Box := ⟨592788130789417325878102554067437960,11446408879542831138790229467716952813224⟩
def resval1Tail160 : Box := ⟨918453301357416264988253285222004430,36175833670116709810496439703802761432358⟩
def resval1Tail164 : Box := ⟨6013831728997283117943852516403751766,114330385376890529752739274800231443450267⟩
def resval1Tail168 : Box := ⟨39412211072716753106408240774129490276,361320071690021211708241909604994790201697⟩
def resval1Tail172 : Box := ⟨258291865711422447442065799978079225553,1141816126389227596155324307852436956828877⟩
def resval1Tail176 : Box := ⟨1692741571081561292975162214574762301377,3607826407481543924165182017061332629200507⟩
def resval1Tail180 : Box := ⟨11093551160233639061725750455232355173338,11396769438438184620768390994295487507153584⟩
def resval1Tail184 : Box := ⟨72702696883705004655810275274009850675223,35981777862834751742128556633637185685575495⟩
def resval1Tail188 : Box := ⟨476464394297047628033271017663383758544300,113473498856171160815890237890029318801882665⟩
def resval1Tail192 : Box := ⟨3122557054465130333530713952552660115049434,357015598403804763542076009040858049352761655⟩
def resval1Tail196 : Box := ⟨20463989912142701710112653407042823229745259,1117750427338685630067689440870950207038769065⟩
def resval1Tail200 : Box := ⟨134112804288219820329629795327165937293592312,3463206835418103032798321769201966947999836520⟩
def resval1Tail204 : Box := ⟨878921674183466003684722398683348479614799596,10490384841431735224758243663996071463393067146⟩
def resval1Tail208 : Box := ⟨5760101084020193575201099033382533128710442435,30172521977752341369701089251310766716632099991⟩
def resval1Tail212 : Box := ⟨37749398730741668184737709188529051326362815390,75815434868006157255563109950035807677969867207⟩
def resval1Tail216 : Box := ⟨247407543030024085319254158679709005384339232201,111524109065286502150404873335430728944450317275⟩
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
def polyval1Tail5 : Box := ⟨2182178061965076986751839683488216587790844775015533,121608275855752513856429856358534909048191302746631⟩
def polyval1Tail9 : Box := ⟨220555488865857802513046705736219916230985966346,282690405601269747193264406692608486407410015085369⟩
def polyval1Tail13 : Box := ⟨16015517738593234711247442578677626799616789946,893415615445652891109573982130700854444154158818920⟩
def polyval1Tail17 : Box := ⟨103800984092338424139751042116951581468301581750,2823580799766087974626673605391048156418273499037485⟩
def polyval1Tail21 : Box := ⟨680265958411410888042851651732336764256383224324,8923557482570611447138273657025891023754434001936685⟩
def polyval1Tail25 : Box := ⟨4458190934069603741967900869327446062271650800749,28200540125380313250729233523175460654096608099762228⟩
def polyval1Tail29 : Box := ⟨29217200103717064611063133405968944593333999248602,89112505873679158272330138165082471565396205986746633⟩
def polyval1Tail33 : Box := ⟨191477842599554348652850034240178235111965757437265,281540387674541307368680969757522670880756263354998331⟩
def polyval1Tail37 : Box := ⟨1254869189260402614558353887443528464632066567455523,889156952692073662201631380056072107590520664205852774⟩
def polyval1Tail41 : Box := ⟨8223910718736956558962919538842053371348891706611580,2805917155967948475527679588594001750388956929625414082⟩
def polyval1Tail45 : Box := ⟨53896221286314503114506571150196454510063082650841698,8840179248735802415061052244344089200942733156409131226⟩
def polyval1Tail49 : Box := ⟨353214275821990750816431603943162626410590266095529611,27756456345482477581850013086319189337979356516771352740⟩
def polyval1Tail53 : Box := ⟨2314825078027000405074586584954618477511041136489714233,86525615404120456756404554566724849266039513776880381579⟩
def polyval1Tail57 : Box := ⟨15170437631357898038075929461977289882692412354185624308,265609226114688511737600149418155661381908457319181291744⟩
def polyval1Tail61 : Box := ⟨99420980060902273611417275415278134466437258017402902928,787981414000705674098900319781180269104626908103776465720⟩
def polyval1Tail65 : Box := ⟨651565334963817075342618986546256181159455083013612064335,2153064453705643435955639056496202620802846007549528128829⟩
def polyval1Tail69 : Box := ⟨4270098898195911181318241599737555371917413529650051312462,4593916499319370697280222458808863023109719071456645587821⟩
def polyval1Tail73 : Box := ⟨28156250000000000000000000000000000000000000000000000000000,2⟩
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
def resval2 : Box := ⟨121062481839897521584352171737586413745812612893494471784,201429874508666916211697440014342869802307527075563534⟩
def polyval2 : Box := ⟨3829840284556984820178363202924017128116523160088244600899,7119602666500162488608512235012673824821111141814367672⟩
theorem cell2_lo : Holds Q cell2 (3/4:ℝ) := by norm_num [Holds,Q,cell2]
theorem cell2_hi : Holds Q cell2 (7/8:ℝ) := by norm_num [Holds,Q,cell2]
def resval2Tail4 : Box := ⟨-133839003777907627697263137460419480825020225230165,35285620728761806348605444682371406360847721715018864⟩
def resval2Tail8 : Box := ⟨-451588542240700579633040146391273976907052189311682,60078551764025382324288904172455240913424165232755459⟩
def resval2Tail12 : Box := ⟨-1036231782804700367570629791363831023154132596447144,102225528247324420234174957566148830018049316294934169⟩
def resval2Tail16 : Box := ⟨-2377734903858533275266414651416546526549582653724054,173782268891196979363374526180369499368877277738425032⟩
def resval2Tail20 : Box := ⟨-5455944632932355775851663875206142490447270239489318,295065244681795392482994771477692478971320590752587307⟩
def resval2Tail24 : Box := ⟨-12519197068165711132433353625523485421235933024876911,500156684411687008020151470304143650186433820278745492⟩
def resval2Tail28 : Box := ⟨-28726518646381746347894972388314983715695764903587884,845875901404212503900661347064038028430872231358538880⟩
def resval2Tail32 : Box := ⟨-65915798676841645191857692130139215341834179543009220,1426117317744330389060956849961961854213537058953917766⟩
def resval2Tail36 : Box := ⟨-151250228706470154434509907169078546408312106862349769,2394092397224858730694750178111803293721647252820827135⟩
def resval2Tail40 : Box := ⟨-347058400914086623271453451443672741898577925537343890,3995183746447314090327232030654633229516237381330466106⟩
def resval2Tail44 : Box := ⟨-796359348843023035720873690206942877939419929836540552,6611314052070053732308402179990969905214576782258017754⟩
def resval2Tail48 : Box := ⟨-1827324193332738955443039027754802171345014256868397173,10809839592648086702800177246869060294141589918795013415⟩
def resval2Tail52 : Box := ⟨-4192973577054527809885161678489756436924860603706651323,17365469932890270548795244723981867307661519710025181074⟩
def resval2Tail56 : Box := ⟨-9621186805288489877493505464079209538097484416248473252,27156566054658952853197183283458481014127702797688800718⟩
def resval2Tail60 : Box := ⟨-22076751460771341292038759384677635613082082240970426078,40664471244068292301562869653157908272126781711183840202⟩
def resval2Tail64 : Box := ⟨-50657259314010174918845547802631304897222025195138545599,56376496688021248724377209250604676146525351378100011803⟩
def resval2Tail68 : Box := ⟨-116237730247481308481270552272521882821132360360977728205,66356852377655880278510798206261941311567436194083489325⟩
def resval2Tail72 : Box := ⟨865347565680026721403756893118906073794772622877325914869,1002930521169973368795406338467241779894437470430570006⟩
def resval2Tail76 : Box := ⟨-32255229364040813633916416093867813428234159685903,432617424816202240575919390582441665342367866533167⟩
def resval2Tail80 : Box := ⟨-5126709773246464004939886144099111502338023764264,736636991797320700848024958292399262511013493263352⟩
def resval2Tail84 : Box := ⟨-11759941038446493257574395555832288024218367586038,1253653354616631536746258564623261180277004553110461⟩
def resval2Tail88 : Box := ⟨-26984329451665737235364257087119191092653996594516,2131754885491357679914330323411273517887597049050549⟩
def resval2Tail92 : Box := ⟨-61918175651039526336557618582711058300781307768960,3620795620432087342238215455656668472204137178473112⟩
def resval2Tail96 : Box := ⟨-142077292793136639511157390289975584067380884911864,6140469857875908266267943895713483628888271247625449⟩
def resval2Tail100 : Box := ⟨-326010204841950590165832926133704472016036333903323,10391737870601783115195270546704036837791539577640548⟩
def resval2Tail104 : Box := ⟨-748062210164982663283481850699650349647045856129259,17535942836489550031302432535231091876468117381097083⟩
def resval2Tail108 : Box := ⟨-1716501698307912996834855966129051936731226542359795,29475203704064834138203547676709295452033343723370016⟩
def resval2Tail112 : Box := ⟨-3938680553912936729881773521016520344793834153868498,49272991802654648547837462769310344571685373051759375⟩
def resval2Tail116 : Box := ⟨-9037686662975323752771786889419916724666719646143397,81739077173967962091514825048723071837136326137550611⟩
def resval2Tail120 : Box := ⟨-20737853476585232357629393070430310340884773523613606,134123297992019390342854283559207638140696275453707015⟩
def resval2Tail124 : Box := ⟨-47585027325425926533361455281019757566859057277755770,216601260227845436164934336931009283650361938949703791⟩
def resval2Tail128 : Box := ⟨-109188486075386714861050108253522915910891355063768722,341501657122530809813908368705240821704272670942798783⟩
def resval2Tail132 : Box := ⟨-250543630245366892691631394875476933805565318371618272,518313856859495036679311719534366185776624166692519213⟩
def resval2Tail136 : Box := ⟨-574896794689833209275905546820078161029421862830478588,736740134625266999688477797830563318908546483660202936⟩
def resval2Tail140 : Box := ⟨-1319157193600151099500392821943169701435770156368476612,918437890214071761485170391834603428599549281117931766⟩
def resval2Tail144 : Box := ⟨-3212888257971270847570936952659264366526935773869788786,774661773496235426307874009229651706040611401534938445⟩
def resval2Tail148 : Box := ⟨75016436949867505432685369035050888379290156,56190304684287581099258965676128569944915012⟩
def resval2Tail152 : Box := ⟨713696227288036232688471554739057199791945,94530853120251540590369608129016614820680570⟩
def resval2Tail156 : Box := ⟨1634535294910425719952783938031820622929731,160846136285951558385434060267374837649160857⟩
def resval2Tail160 : Box := ⟨3750599639257190778004122866371286822610840,273434252081596700754919176473532992837594840⟩
def resval2Tail164 : Box := ⟨8606116659329868767720917633144099316246006,464259003142994411198906881012908937466096678⟩
def resval2Tail168 : Box := ⟨19747574013007147917087047263345586309385841,786939444192031734926397430398529347133330674⟩
def resval2Tail172 : Box := ⟨45312734516173428471143746122698058870879532,1330859704704084300718433814720592303014972939⟩
def resval2Tail176 : Box := ⟨103974488612161388262763857711781289935698842,2243714937063047122030523285373011956837146351⟩
def resval2Tail180 : Box := ⟨238579604554693767311439357340267731454496008,3766474909216923914797593944796289494131839207⟩
def resval2Tail184 : Box := ⟨547444170865740370448062219681346163173973450,6285002013394378757003953568602632461807314662⟩
def resval2Tail188 : Box := ⟨1256164041240053251486307572043600041252417022,10399687508418192456952932009797151375172922295⟩
def resval2Tail192 : Box := ⟨2882390903914713418215400217707299111892500525,17001977254102851940086490471962547586710952085⟩
def resval2Tail196 : Box := ⟨6613927043134157050471607848683620055207200798,27307927173958699165834446734359750717112999687⟩
def resval2Tail200 : Box := ⟨15176300644194536432696976007031168883057170831,42692885058934302328387782409603189014045862271⟩
def resval2Tail204 : Box := ⟨34823501943837322211145200492072651287757087549,63898774041175616342784869548391629714383874660⟩
def resval2Tail208 : Box := ⟨79905921480111389199448631093967304425247909123,88509922932538880008259656197872607414083504379⟩
def resval2Tail212 : Box := ⟨183351930121195342595088858327151970186711224582,103958065369419360245222514554421847967632750479⟩
def resval2Tail216 : Box := ⟨420729113215513897763169465378375677210380013467,69418306004809064018415985900381940681994469342⟩
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
def polyval2Tail5 : Box := ⟨22831021655650309936021227392079025576154158074049831,3172623863794932035257407739767896272324839739165835509⟩
def polyval2Tail9 : Box := ⟨47447876267428138781233941893133295451588935851102972,5400183803925408048883944024333585382758039038036261715⟩
def polyval2Tail13 : Box := ⟨108873291155285244037554869913247450441963550512726652,9184545487710555379753901346113989338382430251004820670⟩
def polyval2Tail17 : Box := ⟨249820384369429818195135620228902629654329719564947157,15604341763707502035109502653514772556960884093726568046⟩
def polyval2Tail21 : Box := ⟨573237236441134364042183638280904282011718282806338395,26473263454321303107230528685316975225280987963540216626⟩
def polyval2Tail25 : Box := ⟨1315348745751398934510134588944900329697144256164721320,44824787376432238613919670089323843673483958635013404733⟩
def polyval2Tail29 : Box := ⟨3018195980587642736649439648668070392617812551613127526,75694839236598603976928312751209352519036837443114391223⟩
def polyval2Tail33 : Box := ⟨6925545036370986763880427421830555353448011879841997452,127355417999695180019975563666140585752238704406299299752⟩
def polyval2Tail37 : Box := ⟨15891338521186547679710898324389890280498133551344328727,213186056145921748500672413484226581158679227146103594766⟩
def polyval2Tail41 : Box := ⟨36464226088879296546044203541232049211950569877352890763,354331695842180920509246604860334533125639860990072444766⟩
def polyval2Tail45 : Box := ⟨83670723047540127395668436219995452246436176413675930902,583009866802365182503213072309961051164629743733969923433⟩
def polyval2Tail49 : Box := ⟨191990634279037491374171323868486573720111067963119671268,945337019209180813291619897441744455135089327576815494260⟩
def polyval2Tail53 : Box := ⟨440541234834599667070515385961997097549685323667649147015,1499689530966209237563539726986213657954383596090210090939⟩
def polyval2Tail57 : Box := ⟨1010864828476605425951945788683531625167782751852587069340,2299083200144849615142660049384395474048186698669452448256⟩
def polyval2Tail61 : Box := ⟨2319527936663409960006236607231358205810859468110230543142,3327097271680422926109964484102126810848916936091238204350⟩
def polyval2Tail65 : Box := ⟨5322383069851187894441989257834822016469605027180747910069,4310510246867044451298805631634593023794477805533231663316⟩
def polyval2Tail69 : Box := ⟨12212727287653939113398660507895434511374330395422084323037,4220563663842667326456668112123495513413092274073342554546⟩
def polyval2Tail73 : Box := ⟨28156250000000000000000000000000000000000000000000000000000,2⟩
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
def resval3 : Box := ⟨120877814526287936657728572218701573072782944311254894260,1712451780645252773680487165391096348027846499987299965⟩
def polyval3 : Box := ⟨3848658232081926193098645612988441760274250092316740314210,247635929662370735880124412573820234274537576843047811080⟩
theorem cell3_lo : Holds Q cell3 (7/8:ℝ) := by norm_num [Holds,Q,cell3]
theorem cell3_hi : Holds Q cell3 (15/16:ℝ) := by norm_num [Holds,Q,cell3]
def resval3Tail4 : Box := ⟨-185458144376601285888668563911639345286590648813496273,1987648830208453725147534294894806867976491478040396814⟩
def resval3Tail8 : Box := ⟨-275042752324454670517290476678423764402701988519484362,2538207522298362083325080133185024376969310206398966373⟩
def resval3Tail12 : Box := ⟨-407763303564789665674695671816767098426737185177860467,3234096854295002340520479103722715846971117431053214298⟩
def resval3Tail16 : Box := ⟨-604527498697343624723453858964780657859689543899804272,4109999855494257980019810739812528399672256548289564706⟩
def resval3Tail20 : Box := ⟨-896239297357196845139902971508320286283056871971858909,5206896795172237071752472669608207024240043247891342049⟩
def resval3Tail24 : Box := ⟨-1328715202961228196263328750026106563134104183439109368,6572028045631542269670449153119901717509745526275065367⟩
def resval3Tail28 : Box := ⟨-1969880249377931589264092395546218048440690166528057633,8257934260049738655212726718309652560513711400771239433⟩
def resval3Tail32 : Box := ⟨-2920436364573223366059476990427465159259764054677681522,10319860952757182504901913575390080713166877890288515324⟩
def resval3Tail36 : Box := ⟨-4329678701136793247025129606325867579789411545332998934,12810392903575611279779442527326695652962443819035900317⟩
def resval3Tail40 : Box := ⟨-6418944060031605706615760492181044408271535611483490197,15769534610317671193351374656337612922556985886211920712⟩
def resval3Tail44 : Box := ⟨-9516374236960558794487293108191980039818571968122848641,19207460590496433024792823188499609341943613205422286309⟩
def resval3Tail48 : Box := ⟨-14108454252122077207204477824826831841425798797375082223,23075649239279827288791005659909522911133506755432966010⟩
def resval3Tail52 : Box := ⟨-20916420101590681721683868767944649479372647157981024086,27219824963347889972876053478293263404074787983581142581⟩
def resval3Tail56 : Box := ⟨-31009536696794524648625557430795063523524618891222954367,31304674791122760280927861834699846792444650718948867957⟩
def resval3Tail60 : Box := ⟨-45973037521679898870944433699619300151525074176112692671,34695094114303385378137118377786055723373106072567783387⟩
def resval3Tail64 : Box := ⟨-68157102738288457211599871833445629265884168136527011868,36270880948407906317031477460870056510678702624803819004⟩
def resval3Tail68 : Box := ⟨-101045717003868779161477622501936979594273332272469677873,34140042294002950621487843436708685994553603524251568597⟩
def resval3Tail72 : Box := ⟨866133017397729786817794369661325271623180181621219373837,760164636534531164449038240913369454933546038842187098⟩
def resval3Tail76 : Box := ⟨-2378464052613485927678568636837012761858071712362145,26173141883873086010359064319764820863587166155444135⟩
def resval3Tail80 : Box := ⟨-3481917483706596207221024136850204627597909519373928,33440450037650930835335295480653361001417867180454539⟩
def resval3Tail84 : Box := ⟨-5162097373330972879505780111481210274399104593235165,42635318327752044487684777901494610536488661202022824⟩
def resval3Tail88 : Box := ⟨-7653042304763577920038897704144879372955514222642115,54222541602871689071305342716342376584739640345368162⟩
def resval3Tail92 : Box := ⟨-11345980575976221737459390064898717127233985595416422,68754330870356832329761199615051632270536753172446441⟩
def resval3Tail96 : Box := ⟨-16820928214436434174590433890376743889642519434834024,86871990520316776586148653547012373652274068909367393⟩
def resval3Tail100 : Box := ⟨-24937785156650465106909126293455714540116760864748381,109296666639908277987971848027952644664031556584206269⟩
def resval3Tail104 : Box := ⟨-36971391863233874571995569501003347211337946932744375,136800243355319681646823135991247174427825174418282506⟩
def resval3Tail108 : Box := ⟨-54811756846829369449885796084111684760807670418634870,170142275462960770988898354983052021672352892270309114⟩
def resval3Tail112 : Box := ⟨-81260903017924916545211653846521466070725578226503666,209950701158952251724946713922258758797643866618434529⟩
def resval3Tail116 : Box := ⟨-120472955788326898785695461434380079364196353811717579,256511610954109093317833805394134272613561763878604449⟩
def resval3Tail120 : Box := ⟨-178606593544433777134490603479714419177115612397765523,309414355908055806764270051822430947376746394390691950⟩
def resval3Tail124 : Box := ⟨-264792334917024767661175745010092991446408920706372036,366969461494202047577646629635935342740930224244950045⟩
def resval3Tail128 : Box := ⟨-392566585809535831076799378664297673342794662095598317,425273238182684814903888318677215913974896563864452039⟩
def resval3Tail132 : Box := ⟨-581997678831824004498585577534505606949458724311068439,476727273368793138962147754979185948814472735910568014⟩
def resval3Tail136 : Box := ⟨-862837822746301375411101878766003594785390332748978500,507722147021405467080041463964527080222987831851072432⟩
def resval3Tail140 : Box := ⟨-1279196398229301535058558055186382810784210826444572880,495046301292240036967127180656227558539271676537793735⟩
def resval3Tail144 : Box := ⟨-2063641898918682794572840412641231270970477340789397728,392413337707145520956437639061651637105382784002649614⟩
def resval3Tail148 : Box := ⟨724109311328269825633271910761247299232749114,6347319066300298399469552041937378150077123948⟩
def resval3Tail152 : Box := ⟨963176447930732144389762768606608371752463630,8094149581886857351342870467557539609218530656⟩
def resval3Tail156 : Box := ⟨1427950558643268553579556665537502041628246518,10297102871973798796156034858048859113116717019⟩
def resval3Tail160 : Box := ⟨2117001141732952675281483286324131098717818559,13061529260245827395867773260305564070624726847⟩
def resval3Tail164 : Box := ⟨3138549726619221787300476275478337201676809131,16510638785460387414429086038225241717696673632⟩
def resval3Tail168 : Box := ⟨4653041603181015387066472434634554179470910233,20783584931686123866367758646169708589997990983⟩
def resval3Tail172 : Box := ⟨6898344154723704271643796889632904476444565293,26030342395183512143286875003057108243193493284⟩
def resval3Tail176 : Box := ⟨10227106511250214447189917681625490154518064481,32400338461287451421018890703078413999398568366⟩
def resval3Tail180 : Box := ⟨15162146922002294510165387595059306582969150044,40020712015681230828875678746927161667805187549⟩
def resval3Tail184 : Box := ⟨22478567034722377623808685998328128863163863561,48957755796685573321538970455295891197210320950⟩
def resval3Tail188 : Box := ⟨33325490020233898322415234588131622162235557326,59151563867749340653567638747256195392578328793⟩
def resval3Tail192 : Box := ⟨49406542835813177745156840414482218094252958897,70308542667453381259586617719969039045981138330⟩
def resval3Tail196 : Box := ⟨73247429325269077906366332935899315090701914195,81728330547167015177623775111231977102939174111⟩
def resval3Tail200 : Box := ⟨108592619414593845361154551073023214203330861999,92029432911331524589918660631384397984682786066⟩
def resval3Tail204 : Box := ⟨160993458745925964377257822489929217946370136776,98719466117913086114916295259605422328837650849⟩
def resval3Tail208 : Box := ⟨238680067749616564734061742423253854069120462922,97528253117144048525419344607735383498027129204⟩
def resval3Tail212 : Box := ⟨353853971557441211508343616442751857648864942849,81380567216434158759276750304479127737396255045⟩
def resval3Tail216 : Box := ⟨524613702548224790066944131941081210926261096730,38822730694741368851563379554319934742733099058⟩
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
def polyval3Tail5 : Box := ⟨34723236682115295200852134886921630150616408184937385018,313505881769641890824686246870432362372548944074866942179⟩
def polyval3Tail9 : Box := ⟨51475594673950132946659172167912287503456458847661092845,399317551177835302964869689906053532679287483049439744294⟩
def polyval3Tail13 : Box := ⟨76314891733677280621788491649762773685154887237181130300,507254087874548147821528739068413736805714420279808933708⟩
def polyval3Tail17 : Box := ⟨113140270860318148051005211373259128642675232987864296169,642312107363752156492582185025742442861391078816244342552⟩
def polyval3Tail21 : Box := ⟨167735557236272913562108981546840331052706028760693127298,810226458749754387017806898579493013282163399338353622257⟩
def polyval3Tail25 : Box := ⟨248675533012454878967883404191594839582157294892589409800,1017333724857377905217438818403323372389439786250808851619⟩
def polyval3Tail29 : Box := ⟨368672699682400470139694772781503937826718528568437488115,1270224736836263457333131317958368673823467649047886086264⟩
def polyval3Tail33 : Box := ⟨546573914387878022110822674424277186156265143704608796615,1575041540420757220348343972918308857400817546224983602844⟩
def polyval3Tail37 : Box := ⟨810320493344489085539355861285674555801037009095709779241,1936191910533806603340862045196322903572390518597585754649⟩
def polyval3Tail41 : Box := ⟨1201336698750837343797121144054043862506294252097365686273,2354128721507295718255540583049001210367532155477007927875⟩
def polyval3Tail45 : Box := ⟨1781035868670808375474645884996913162854730634608379010241,2821650191221280678450304443530800912241752402450660897783⟩
def polyval3Tail49 : Box := ⟨2640466048186451443171983625824371964634888459980346403446,3317887208526396917153870554176917772576943142164500531879⟩
def polyval3Tail53 : Box := ⟨3914610072860937180315657124627462051836531118132635774094,3798706253695768601961878296664358654552622802691220672888⟩
def polyval3Tail57 : Box := ⟨5803586087792871790106306705215385178441814322034634638314,4181597097929997855907426669815086772317079302191395528306⟩
def polyval3Tail61 : Box := ⟨8604078273831076262072990451987208467186958893489644448403,4322123509073323653090869690843785292051744543174269485620⟩
def polyval3Tail65 : Box := ⟨12755934317590616513296171037887917052546288588058896331180,3977528596892327945055227609702142968718297257754607982913⟩
def polyval3Tail69 : Box := ⟨18911248491454164217228202510520459086103351470291105788296,2750859882622055204974063657989721793383157565066755550546⟩
def polyval3Tail73 : Box := ⟨28156250000000000000000000000000000000000000000000000000000,2⟩
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
def resval4 : Box := ⟨117823340142438253318324126000739212229901600919994287983,8526616596537746877061860967532744591826738809059052584⟩
def polyval4 : Box := ⟨4707263881689720810566103686536229044520899323452050170303,1968786335160611295124079995649300606899435084041738662269⟩
theorem cell4_lo : Holds Q cell4 (15/16:ℝ) := by norm_num [Holds,Q,cell4]
theorem cell4_hi : Holds Q cell4 (31/32:ℝ) := by norm_num [Holds,Q,cell4]
def resval4Tail4 : Box := ⟨-3816746116998218427184172722505897095223318739601932984,9271596065912304625877416321082911943362724557026233490⟩
def resval4Tail8 : Box := ⟨-4624884769058201316675772933026795674668111220783168478,10235834413147096986510021714455794204807667595917448829⟩
def resval4Tail12 : Box := ⟨-5604043183332980183173698051999836015725449077489940231,11268982427422026017365896738236226342276611382391260636⟩
def resval4Tail16 : Box := ⟨-6790504308132845095588907095216757246637064154246263866,12367316361705960181129849765604391033280398985770381867⟩
def resval4Tail20 : Box := ⟨-8228157287554852659959481714454679539300921760903185780,13523845067233964745553382198171732571795467479969793362⟩
def resval4Tail24 : Box := ⟨-9970183255410912288504192799027974805332276838367301236,14727281795383860513364248458714036591218377426522007022⟩
def resval4Tail28 : Box := ⟨-12081022599899279823990264006969016240160000512977529443,15960753508172090181742204092103845303077442991762110721⟩
def resval4Tail32 : Box := ⟨-14638758718910017518823473609389136961165830784852799286,17200185305424074371092533280496723985808619068137370418⟩
def resval4Tail36 : Box := ⟨-17738006452553994263004738353560336883354489940459708803,18412284195152061947613756403121783920184034779083855872⟩
def resval4Tail40 : Box := ⟨-21493412040763151433846555453704291983492580696070322338,19552029444821936070314940097123239644911607662054621948⟩
def resval4Tail44 : Box := ⟨-26043894075114989145951498198652653182097603515416193079,20559556037214745330631119169460714817023884969939477752⟩
def resval4Tail48 : Box := ⟨-31557782324621841140401534526254541279319978443254009284,21356292509611775252522713127433809266371546479337718220⟩
def resval4Tail52 : Box := ⟨-38239044529051196092568094665115289738030819776742334354,21840183700064707246058048870891348341944546842220202396⟩
def resval4Tail56 : Box := ⟨-46334831499040742037103173220741477298283186997913928625,21879791470630123564162437456457497569356924287338030072⟩
def resval4Tail60 : Box := ⟨-56144619628586208124557268094770810230170367822799834687,21307020880981888343528965959458766712438518175146319776⟩
def resval4Tail64 : Box := ⟨-68031289002239815958877170397741799066799757790790102962,19908163793691307588178636943399362199472934731349716547⟩
def resval4Tail68 : Box := ⟨-82434295599432125031846508084005262299639691239938735644,17412881519946147537608560623484323158555975764313506874⟩
def resval4Tail72 : Box := ⟨866486082247933311407137621177386156475699529597419599095,721270328329099567996261985687102389283183996314839098⟩
def resval4Tail76 : Box := ⟨-50828119878096107512581594922473045654070012224021954,126461066124161569669780964533320301243775899705282819⟩
def resval4Tail80 : Box := ⟨-61553127555382909181003308322883918710349386032979313,139709032105193914702594981226575974326915690900158889⟩
def resval4Tail84 : Box := ⟨-74584858310880689410273271364414196750631033841367987,153930431115275841936448917729999568356467398435865416⟩
def resval4Tail88 : Box := ⟨-90375606522958864850227634051491434033717444528618575,169083190975238217804709512862865450604492996928280693⟩
def resval4Tail92 : Box := ⟨-109509496156040401234434178079050626967248946007641521,185082904066008410658093078144255988146699397951634248⟩
def resval4Tail96 : Box := ⟨-132694321064430762306720205695464340813553820081283088,201789161883152484301509199774114003022323786165937111⟩
def resval4Tail100 : Box := ⟨-160787725821154872714694805298001663005459307233487211,218988535482318518350159729570898485359091458305411940⟩
def resval4Tail104 : Box := ⟨-194828931391765416640008195677480895520724447635852651,236373253477393935934511223138528243881208667289812717⟩
def resval4Tail108 : Box := ⟨-236077177616645245035675774780929056934375775207691638,253514572003952052996174902027073566522828192972265297⟩
def resval4Tail112 : Box := ⟨-286058304551151675895805061122422352826283740303545965,269829605361202707361278595897813838423016232072059844⟩
def resval4Tail116 : Box := ⟨-346621195783517571483154612982819320016097814036450248,284540110807514911577070906748131256309386963479133004⟩
def resval4Tail120 : Box := ⟨-420006171661104842864764880759403551482532476383978782,296621385503267680419049802382052417380649252492880854⟩
def resval4Tail124 : Box := ⟨-508927862402250234817403140818944957234178798075455538,304739024849029471551073935819270478699698591053237413⟩
def resval4Tail128 : Box := ⟨-616675626705581402008498710775849159631099989971021579,307170793642627292567338796437481145632318613571119221⟩
def resval4Tail132 : Box := ⟨-747235230505355359436934573384706259624490587475345488,301710255372150549396620614796542159229690051369851240⟩
def resval4Tail136 : Box := ⟨-905436287010705681968282716672082979354175945866319010,285548067255444843268753297039369018667157265491745273⟩
def resval4Tail140 : Box := ⟨-1097131282856876755072124270612374158036788826402296315,255125934313092801356703631898853081783255745107362723⟩
def resval4Tail144 : Box := ⟨-1488551357282527160888824555948897531488129356142416745,201029767104774983745206209612677084785477569231909011⟩
def resval4Tail148 : Box := ⟨22269590916202551419540057861464627845153374463,47305870042797912723134621319526272802725121714⟩
def resval4Tail152 : Box := ⟨26894376465254946887260619086989786733960244196,52017479887212548449853929569805999906439441974⟩
def resval4Tail156 : Box := ⟨32588323144848552698117823384547248449200851022,57009073417540911248736362246179507253432650390⟩
def resval4Tail160 : Box := ⟨39487766504881444785797888170983836460867874793,62242112617895759577213135532353460480727007759⟩
def resval4Tail164 : Box := ⟨47847926898044571216582157421491822666903193091,67657307667324724525631740161621230612217269716⟩
def resval4Tail168 : Box := ⟨57978060323002673831848963823712655364920327017,73167865800622743673705843222874203533976306587⟩
def resval4Tail172 : Box := ⟨70252896974625494091865977108415909443731376381,78651644049354085878901107184064010026228851480⟩
def resval4Tail176 : Box := ⟨85126503126031740029017261290587628819093523834,83941366482521191676190151368742799161207916100⟩
def resval4Tail180 : Box := ⟨103149077782282038722818517818448355780148770348,88812459034593808079756179925716877258929230513⟩
def resval4Tail184 : Box := ⟨124987305440972977847390635022736597199757733904,92967955380700170826767513144555385512064508581⟩
def resval4Tail188 : Box := ⟨151449017841616041922774084193946008102828973536,96019805900720887658995984675796802835885852851⟩
def resval4Tail192 : Box := ⟨183513076982224924035527814404244941639425204194,97465773877089253200024584381104904953417943432⟩
def resval4Tail196 : Box := ⟨222365584824743813798007178697751675951048670174,96660922984668449415531001583590489085358435470⟩
def resval4Tail200 : Box := ⟨269443759145511574630445725791472451712673062202,92782480921322070021472441452207465841368893624⟩
def resval4Tail204 : Box := ⟨326489098570193397318192391691449802610828718327,84786597276809842012525100615898412086238741897⟩
def resval4Tail208 : Box := ⟨395611803454794578817721311305377287318748436944,71355189227043870037738919816915504283668299885⟩
def resval4Tail212 : Box := ⟨479368835830562783050233463713588334179453178695,50830673958245034308069121426554877755150666285⟩
def resval4Tail216 : Box := ⟨580867293907284440411027119836578924024222130613,21135517764748139245768669090541740753216402678⟩
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
def polyval4Tail5 : Box := ⟨1071541120976285713591082381113795662699590190480019465061,2166395436310158705650683470416717953084140757633934722285⟩
def polyval4Tail9 : Box := ⟨1298400081089522674026801017894021025581236884921983650261,2377986617647891713578719565438462020591686126186446526099⟩
def polyval4Tail13 : Box := ⟨1573291114013853439114274673916421612906909775651785657790,2600919173347364250847500229755149830714121399457172286411⟩
def polyval4Tail17 : Box := ⟨1906380757274928948550486320349807704785187351853377011813,2833063961664759003396674986287668060650373270558199440282⟩
def polyval4Tail21 : Box := ⟨2309990541061755985882231396233814858857181445964768471272,3071227628971087456411850543596599680897350351216839342907⟩
def polyval4Tail25 : Box := ⟨2799050651047484179462829756732676535216113418785466045544,3310844222875641377931534985854728010782168872875382263001⟩
def polyval4Tail29 : Box := ⟨3391652220155082550174183109839839583848148579580262444467,3545590276029427931144760088244360392484357269369047878274⟩
def polyval4Tail33 : Box := ⟨4109716549137128863591028917874252403283741194781978397674,3766905625863947736116425426473707556963727155166940728519⟩
def polyval4Tail37 : Box := ⟨4979806011324860986360694957244027779868158348242280281038,3963398283730615712719554926826163461304331000567891001209⟩
def polyval4Tail41 : Box := ⟨6034106638238561235691681198721388367010669190904583807539,4120106841359727850549510160841397988994452298825453885165⟩
def polyval4Tail45 : Box := ⟨7311618733507209954276457787131849381211614642119052150139,4217588023657224397405702466299571047540164674292388496657⟩
def polyval4Tail49 : Box := ⟨8859599557852563738191155910632791035859350595462924956674,4230789837299743480392536690938275815030457955540223012651⟩
def polyval4Tail53 : Box := ⟨10735311452413541222622385937922713703692180112607052191169,4127662048363621067761098353966190535496287177401307818224⟩
def polyval4Tail57 : Box := ⟨13008140066350299998334293879757436897044578376358747639047,3867445114225901113950120738110032769835438960239226133794⟩
def polyval4Tail61 : Box := ⟨15762161045429719624265953636770489433500120320800503537740,3398565788402854937273053797085003731002968453631672084488⟩
def polyval4Tail65 : Box := ⟨19099250127624502516294876340170834178000418881737776823797,2656051918063111859372551177923592540117868738805754102628⟩
def polyval4Tail69 : Box := ⟨23142851910780907656054933258582415558239595497104706096359,1558359854138299183739675143957576685936629887421776084577⟩
def polyval4Tail73 : Box := ⟨28156250000000000000000000000000000000000000000000000000000,2⟩
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
def resval5 : Box := ⟨107029676831305620125812080595393257213271606130957138718,13289989688545693351327538336104637969297767521090226721⟩
def polyval5 : Box := ⟨8906465839662140063330555287733488441791710978994940621981,3942304095284906847124974588145789690401305471348117834523⟩
theorem cell5_lo : Holds Q cell5 (31/32:ℝ) := by norm_num [Holds,Q,cell5]
theorem cell5_hi : Holds Q cell5 (63/64:ℝ) := by norm_num [Holds,Q,cell5]
def resval5Tail4 : Box := ⟨-15314782918423974274606580212278753805795291726226290340,13520095066394052524963321273911073732511156703957414652⟩
def resval5Tail8 : Box := ⟨-16838850268149295675243353986663415488690216045851832374,13870932546122566290175859829958686544746988378196919228⟩
def resval5Tail12 : Box := ⟨-18514511676569531340667108762636570493285964002254605635,14192016303394306857839029560661127819571884410742170616⟩
def resval5Tail16 : Box := ⟨-20356920870990381241804874271194645401056984935819016518,14476180317415481520365041246767361507966551547790543316⟩
def resval5Tail20 : Box := ⟨-22382671203369892364650960883224893555082866387434404516,14715272642726235644047185538693199414803265142432124330⟩
def resval5Tail24 : Box := ⟨-24610007248792231498360467397235196542895803745702736749,14900038961683722976952687602324544340039408674281356282⟩
def resval5Tail28 : Box := ⟨-27058989129698705879993863972680947216868453549189416822,15019993954379046312285608576474496497413680493108370490⟩
def resval5Tail32 : Box := ⟨-29751673183968113687898224102757740417569032624959675560,15063278637592201819893969627493260601351142992053472726⟩
def resval5Tail36 : Box := ⟨-32712310611564349388056430628468870473460505190684817653,15016502196384002055465288832244632244987775173307262372⟩
def resval5Tail40 : Box := ⟨-35967565888835235845314872877019720011890084655417898718,14864566679925393283943013261698638742067161505217723411⟩
def resval5Tail44 : Box := ⟨-39546756917573762427849030974150582044221500586792715298,14590472765577990895005559436990395851968950917680518766⟩
def resval5Tail48 : Box := ⟨-43482119071703315774482196644234288332197747936095774525,14175104610615743229326280920441501785833361792216983361⟩
def resval5Tail52 : Box := ⟨-47809095519678366419300493023254026668697347727842376800,13596991607597720119666020831242735083713949331181303557⟩
def resval5Tail56 : Box := ⟨-52566656437339799120784580349096761327912079714396332908,12832044635374714053446416796535483602702178461322309688⟩
def resval5Tail60 : Box := ⟨-57797649986152263578050797089711865672927921807048455578,11853264150956033582744281727798541064479946431549469655⟩
def resval5Tail64 : Box := ⟨-63549188204004405767516406999084772350677041805501401250,10630417195273649169836869055990328526741419955101354721⟩
def resval5Tail68 : Box := ⟨-69872825655631033797945657421363161490183455596976709136,9129675369036550160301114211074727182042431914280589501⟩
def resval5Tail72 : Box := ⟨866535129933323594092777556798052325735671349865124210363,721628363600871189315026977434889294732964745357248854⟩
def resval5Tail76 : Box := ⟨-208440301762000023363828644861956951980901551379298821,187186598844235944656943193979948115869844251874624176⟩
def resval5Tail80 : Box := ⟨-229149843071702271608245375481495285372574778329775407,192168837567120939334887141288330456753249501053782224⟩
def resval5Tail84 : Box := ⟨-251952915176612995894147227630981459974398205493963603,196759836820115091460520744669005912729812249431245253⟩
def resval5Tail88 : Box := ⟨-277025159887728768060524260172764561309977331982285650,200862823342075156577066883906037202034448434654098075⟩
def resval5Tail92 : Box := ⟨-304592384483060501672035923404841084404805524024449333,204367798840617759985898854128356208497255923552321301⟩
def resval5Tail96 : Box := ⟨-334902868471143068833904007913557271153215434815367924,207149824417574656863697496564693913982330363343741524⟩
def resval5Tail100 : Box := ⟨-368229598059558143304011944211253769261831710245536203,209067274063446619691158134948237924529436627105905348⟩
def resval5Tail104 : Box := ⟨-404872724757766985082857889395342780495690994852306171,209959897485887999960973234833583293478025544790652695⟩
def resval5Tail108 : Box := ⟨-445162268640516793059572559305931847086993099877181213,209646672181986627942457238069032654865512145326072799⟩
def resval5Tail112 : Box := ⟨-489461090617391617723549829012716440896706575945710668,207923422612239151684161974626767556664181835630459578⟩
def resval5Tail116 : Box := ⟨-538168160477744498433316786189259297538419906852282863,204560182054708480964009644785711118977406905172788236⟩
def resval5Tail120 : Box := ⟨-591722150144100443443053802679851953962011166238400486,199298270206648260068684691588835503721619577630349526⟩
def resval5Tail124 : Box := ⟨-650605384496054554826868145577301506929067914299814073,191847056834518586747284613988838307750495077711099683⟩
def resval5Tail128 : Box := ⟨-715348185347087498046880820227025017253159908039223333,181880378726063950285621477243199649857906424101697970⟩
def resval5Tail132 : Box := ⟨-786533647697625899467526459417517270827566090974476823,169032573841659490114481757570995373798050361742217673⟩
def resval5Tail136 : Box := ⟨-864802891321807075011096524003411015402387640296583494,152894092863365544143578105890526359858791224747815985⟩
def resval5Tail140 : Box := ⟨-950861197523862099740704322702537329086359480017112120,133006630615777675022837104946729363497448225624100975⟩
def resval5Tail144 : Box := ⟨-1200889142696898833180726023485871603507792420760624035,105273145274299784338970611408811852711910075785172263⟩
def resval5Tail148 : Box := ⟨121686764570498258609215404394179392184122282074,91467030370866593361276294841652292338798594636⟩
def resval5Tail152 : Box := ⟨133714397902487314721075822762486348832400314440,93219038649871694418854338672262506421687137085⟩
def resval5Tail156 : Box := ⟨147020533828783576869504513044033193942863228203,94668076968906639877649238810091182162571345892⟩
def resval5Tail160 : Box := ⟨161650786466111567960802798816072339052776007826,95752379077526471226905241080210168524386290481⟩
def resval5Tail164 : Box := ⟨177736919358624092216766794268301683160452164661,96402558762940472856923421113055973030408152333⟩
def resval5Tail168 : Box := ⟨195423809519892416043342033966576194775386164658,96540173541626169533293489360626234353345347070⟩
def resval5Tail172 : Box := ⟨214870750911403875305376971004813720850288960795,96076683545104878601439353777332310057064845377⟩
def resval5Tail176 : Box := ⟨236252889096049110492547639192126500738751552110,94912297723285360664278530417898733552780050794⟩
def resval5Tail180 : Box := ⟨259762798656779758687433958772024680099989072303,92934695544362959740678532850942314931555718630⟩
def resval5Tail184 : Box := ⟨285612217586765258812670350181116577398441008382,90017611171861061273660116388791827389516967310⟩
def resval5Tail188 : Box := ⟨314033954271537364231781542220067009028934143103,86019265762873032351824172841704932359592262280⟩
def resval5Tail192 : Box := ⟨345283984238031995654655431932580746128420642083,80780632059363183331499988068711370869435310755⟩
def resval5Tail196 : Box := ⟨379643755554541286621527225014505135318846740130,74123513822848726319978894768513393307164014069⟩
def resval5Tail200 : Box := ⟨417422723644767532829496650609829179876594917413,65848420876866068676335477808716149706078047829⟩
def resval5Tail204 : Box := ⟨458961138345349895504005252733784445313012382771,55732218554769750381152746642812060374654918396⟩
def resval5Tail208 : Box := ⟨504633108308086052120536027691032623102771024865,43525528184402889927384073036259205237251151375⟩
def resval5Tail212 : Box := ⟨554849970526003610175429768388756006819502067549,28949852847700435054516064102512138647151753564⟩
def resval5Tail216 : Box := ⟨610072581964079405090085202601714254231870935505,11694085377261411687634978706764247495001845473⟩
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
def polyval5Tail5 : Box := ⟨5590646512805900796461022199482203470615614433860202210637,4021429688778494614754699921954091124790730607629950016512⟩
def polyval5Tail9 : Box := ⟨6146978507755143434940793147084806717710353746026450598063,4090071072443350068639615727631490085195690539947967363635⟩
def polyval5Tail13 : Box := ⟨6758674344736743382596246897481837424929155516181188611174,4143986558579632126251544763514617302063689555270096715878⟩
def polyval5Tail17 : Box := ⟨7431241030389205074320051570333869878176944343539925732711,4180309137842096323160706620313902361663141784146363381042⟩
def polyval5Tail21 : Box := ⟨8170735921719033716347573059108034460828528564114820250321,4195795377841275710089443958694066425347997889536642604804⟩
def polyval5Tail25 : Box := ⟨8983819153417130466080685487807304644679827457731663159594,4186782029654675282410683631809189745258491609738321275795⟩
def polyval5Tail29 : Box := ⟨9877813621018875391235431103741657678538251381141350243780,4149137940547945509831020671755394336799101399132257775912⟩
def polyval5Tail33 : Box := ⟨10860770933314408449018452764262288140821172187532699492492,4078210771137462706517051121722492338846555190500100698602⟩
def polyval5Tail37 : Box := ⟨11941543927790791980571962225686622120127200922563609800115,3968767973294801006075735658482510025829148040422430292253⟩
def polyval5Tail41 : Box := ⟨13129866402203862294143493847030178416687295306136573801399,3814931429256751873889631040307339874739853716603580041423⟩
def polyval5Tail45 : Box := ⟨14436440780368581344835600434720216893220982682602845013323,3610105090896276061327489426491652322722100924264852014423⟩
def polyval5Tail49 : Box := ⟨15873034501714886579788587208381555698929442549574195800644,3346894890360590907491250166747295625095590223015347009203⟩
def polyval5Tail53 : Box := ⟨17452586002725144008649340338460660131651940359412593068694,3017020118663652302940251796836306320879506802218612430195⟩
def polyval5Tail57 : Box := ⟨19189321244756956378975462389478983321048042445183887198323,2611215386639646292467178283141907618969828877631491904567⟩
def polyval5Tail61 : Box := ⟨21098881837739325110600880540900575616867662802610402077940,2119122192160422798419973967833648915199283163548527594119⟩
def polyval5Tail65 : Box := ⟨23198465913691592633760101545604461887395063401050272059062,1529169017854266447106449808311440625440798774897070737140⟩
def polyval5Tail69 : Box := ⟨25506983231525499841857852002924245207190849986466695936179,828438766356017828781125993182378850838456593368495849085⟩
def polyval5Tail73 : Box := ⟨28156250000000000000000000000000000000000000000000000000000,2⟩
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
def resval6 : Box := ⟨92780682117577488855121833419577816615699359387701441340,11732215131671660582437164397261376575972042269844219026⟩
def polyval6 : Box := ⟨15823933242528270994061002727369024139799228916495142005366,3945544041288146243082668540584814514783646836032805686761⟩
theorem cell6_lo : Holds Q cell6 (63/64:ℝ) := by norm_num [Holds,Q,cell6]
theorem cell6_hi : Holds Q cell6 (127/128:ℝ) := by norm_num [Holds,Q,cell6]
def resval6Tail4 : Box := ⟨-29530400634561611397409635887184501704618928775154756900,11497526251873318175388443779914340928760427386334948171⟩
def resval6Tail8 : Box := ⟨-30956227471983795688157222308689611821724694959332109181,11379323879421222634955489834358249252807147671772342708⟩
def resval6Tail12 : Box := ⟨-32450829748029219261426592111819741929085745382711347488,11233956493768180791450113484939177667747536344592641038⟩
def resval6Tail16 : Box := ⟨-34017593133096896389902364126740346649513474641832486874,11059428134780138086368725244991295250060197683406142204⟩
def resval6Tail20 : Box := ⟨-35660001656473894575247299056274007962758633122247585801,10853625196074942319241407704203296859984398094221573900⟩
def resval6Tail24 : Box := ⟨-37381707552451774724221404398911759625824311490612921752,10614309533972818924913836172516940343489122925073085689⟩
def resval6Tail28 : Box := ⟨-39186539389387283307084839405741472554809191607028375411,10339111737818436103534727721694587836315380705118614335⟩
def resval6Tail32 : Box := ⟨-41078510583321007870434622956792175942116664683310598360,10025524052658217610034091261871467893159860994948013803⟩
def resval6Tail36 : Box := ⟨-43061828322636191613211315426653244156739450719926456972,9670892936645399347570157967384308314471162161511188639⟩
def resval6Tail40 : Box := ⟨-45140902923610313376648767452301417627597194613541832992,9272411234785700254506711065066824863946871555915435760⟩
def resval6Tail44 : Box := ⟨-47320357637663458310974622948075941201814767841326021549,8827109949724936698534984507197364045558762224028618745⟩
def resval6Tail48 : Box := ⟨-49605038932111920120418865225740767624470130600361454627,8331849589323444214671435800007900271241868318718415861⟩
def resval6Tail52 : Box := ⟨-52000027267288411798536190656562037431895054929078111234,7783311069758737658614086288038182757594839443407461944⟩
def resval6Tail56 : Box := ⟨-54510648393994007729458483512338805826575791014570944567,7177986151845147047852162524250654029508623917780770374⟩
def resval6Tail60 : Box := ⟨-57142485196395324428316846379426978454762812965974067585,6512167387154408154719490681819664028922479753776046781⟩
def resval6Tail64 : Box := ⟨-59901390093002277036197360229266260417352588445821561541,5781937548903424238546070597547497992937819784252432042⟩
def resval6Tail68 : Box := ⟨-62793255133388898728725182463385067810624757934822231272,4983152926225666751828255496800253620499264621562622014⟩
def resval6Tail72 : Box := ⟨866436381129543769820354690862568230088854605781546546646,668158041304016213828202197031671175062432089657890735⟩
def resval6Tail76 : Box := ⟨-405323193915380455937017017919297261024218157894273743,160087554889705231021257805585703050170169975767849541⟩
def resval6Tail80 : Box := ⟨-424861516035738575588074421808996984623423345130149532,158538071374689045830842433470531822225549129134905754⟩
def resval6Tail84 : Box := ⟨-445374317005753343418159554208277237910593911785141174,156618225431550404903287872276259780183951370135817175⟩
def resval6Tail88 : Box := ⟨-466877501297731562499982644728596912768955229722711623,154300555710580148936057356572021073129256981045543345⟩
def resval6Tail92 : Box := ⟨-489418884061175674733887318996806203499492404738116757,151556130258721257462481213883538409166122724878959613⟩
def resval6Tail96 : Box := ⟨-513048590711457429725861999527573665858901022491216925,148354310352216820199139070240073676661186677215299924⟩
def resval6Tail100 : Box := ⟨-537819166777616871697247445246831183491511957054749212,144662658195861179347860234743290970390760851752010981⟩
def resval6Tail104 : Box := ⟨-563785694747276374908778972808214101116979669114008062,140446839869755265282699665852976195203050186739067344⟩
def resval6Tail108 : Box := ⟨-591005916553916421555841445790531834436896561058784268,135670523265417291718505199434918928717359373173061120⟩
def resval6Tail112 : Box := ⟨-619540361977980492568423264073794637670603031751741090,130295270758960657562225447652323246452211815703256701⟩
def resval6Tail116 : Box := ⟨-649452483247333011988666496788069906230267909595597297,124280426356556639859018440317535643854630100955085508⟩
def resval6Tail120 : Box := ⟨-680808796136382218496817157481547223375083877395052834,117582997034275093259968655594965048776756538176988714⟩
def resval6Tail124 : Box := ⟨-713679027877630983553874653632387583994314696749975836,110157527980627430710955080662576996096812667347455772⟩
def resval6Tail128 : Box := ⟨-748136272214567614741412164508854354040284108345200023,101955971435691229776064935094905721013143224738018192⟩
def resval6Tail132 : Box := ⟨-784257151940729181388004330192924502615141091202210977,92927548805539630174284878255590686078268383116317713⟩
def resval6Tail136 : Box := ⟨-822121989326904660638030239085407777116862117417218641,83018605713024151635436555335787983757814393276458769⟩
def resval6Tail140 : Box := ⟨-861815343368803763946765541056137789422410808544468494,72172447428714943337885640921006547431239914264660160⟩
def resval6Tail144 : Box := ⟨-1057028706565708061842393011791313011458826524415549343,57378595165446190175618239119089836495859583402910219⟩
def resval6Tail148 : Box := ⟨280432644936255213272605048893780868202610895122,90260999352527707809468251274193917951430032327⟩
def resval6Tail152 : Box := ⟨293894479044535130940157500531682653075714202382,88536095402042545353212095079559650362038336086⟩
def resval6Tail156 : Box := ⟨308084041133028704918121120734947139338795866979,86534602109540971129126786443339108450121734494⟩
def resval6Tail160 : Box := ⟨322958692995619272072763244450031897492433478371,84236454433167200042182686158986597706645818178⟩
def resval6Tail164 : Box := ⟨338551510159353007659770638169364718310154157921,81620954900318612498738532937348762826440007148⟩
def resval6Tail168 : Box := ⟨354897166470553792226250432047234076252806758574,78666203596858117987238919661975312499005664195⟩
def resval6Tail172 : Box := ⟨372032009869173387950270753032949675765805216327,75349033620945890845854306326224526067148450160⟩
def resval6Tail176 : Box := ⟨389994143215512468007275522133580429677022482028,71644943230346703454560329309864430675822475085⟩
def resval6Tail180 : Box := ⟨408823509019792797378705199112205130853802697486,67528024500813633268290039111158683699078324019⟩
def resval6Tail184 : Box := ⟨428561978262571376939239090901797695246832109864,62970888320305003002126946576147878846245347902⟩
def resval6Tail188 : Box := ⟨449253443503506348077104754466619705889156195663,57944585535122138762394390268332873220760530705⟩
def resval6Tail192 : Box := ⟨470943916485521208634987794775911601915728559504,52418524054952886619654276219888647234626721045⟩
def resval6Tail196 : Box := ⟨493681630451410341176045383260890724221177575331,46360381714256566501105357266312844300681172605⟩
def resval6Tail200 : Box := ⟨517517147400407941415460951809130355257445628951,39736014677408392280997508161990501057356330931⟩
def resval6Tail204 : Box := ⟨542503470523227595477792704926791785112396837632,32509361164512491551278781393819971301466184901⟩
def resval6Tail208 : Box := ⟨568696162065658019103688558236480247781437408526,24642340263765206788845976886700888483547171078⟩
def resval6Tail212 : Box := ⟨596153467061024835309338556874871526451935259370,16094745577122841633190162795892255933605984798⟩
def resval6Tail216 : Box := ⟨624944932612304308363739350584109817387695305548,6823854002426736313553520560753201986469926340⟩
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
def polyval6Tail5 : Box := ⟨12582206574491829943306915309115319222796385372211357952408,3872347030267460992661863762162994780958558518157408497441⟩
def polyval6Tail9 : Box := ⟨13189687750914694471987707929438059288660646092978609955399,3789270608149060040771161638247928102124096536371680590769⟩
def polyval6Tail13 : Box := ⟨13826501046041208657265846040650420192849409884667555295073,3693577061060124938148258825003628116307407366075384489004⟩
def polyval6Tail17 : Box := ⟨14494060419734776445403559436431639197908186409122127963974,3584382932997284222292355499562414123379870383325490656120⟩
def polyval6Tail21 : Box := ⟨15193850327814789100006529069376041881235371031576201619182,3460753382283545741513637757441854180698519293476134906700⟩
def polyval6Tail25 : Box := ⟨15927426897552695042491140717155436056829680599984044992261,3321699412220252831272621310415114500505394116880947921724⟩
def polyval6Tail29 : Box := ⟨16696421387834631282558051734425404418515906668247717579480,3166174968957121805657093127353791575728106157482488255622⟩
def polyval6Tail33 : Box := ⟨17502543816602026107394971369579828248320951157497729022406,2993073890084973980641435130022075354609925726157655388623⟩
def polyval6Tail37 : Box := ⟨18347586763429376342593485260911097517396075705001839408262,2801226696449657328921782163239846558840761849982893433980⟩
def polyval6Tail41 : Box := ⟨19233429355694853982921552264090130755821599968690694871502,2589397219316414876745548162774311912777937859827346213382⟩
def polyval6Tail45 : Box := ⟨20162041447207814596173800041252130651697580803828483759470,2356279054624349463223285913429268512220141921961953779075⟩
def polyval6Tail49 : Box := ⟨21135487998585248075034233896414019527170496058145030725881,2100491835661907509344138006828252264624246787908159735632⟩
def polyval6Tail53 : Box := ⟨22155933669117842725710162147941184247683529553666217660245,1820577315065527887819784493563473972327197571468821977225⟩
def polyval6Tail57 : Box := ⟨23225647630336624586946952508792799041809628098301213581530,1514995246593797771669657684285241656405766585929747984260⟩
def polyval6Tail61 : Box := ⟨24347008611984155330886095945019672256266810599791029041255,1182119056657598513123871293865414937700338105752251805525⟩
def polyval6Tail65 : Box := ⟨25522510191635983250359830589895328624137329814586526419666,820231295090689964173810690721259842625318769213699408702⟩
def polyval6Tail69 : Box := ⟨26754766550107403221430237966089676368223535238087790439028,427518847511603692952773473560780085506015160728486979272⟩
def polyval6Tail73 : Box := ⟨28156250000000000000000000000000000000000000000000000000000,2⟩
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
def resval7 : Box := ⟨76640825297596881164020429230403864642582905639818842422,18770175468398431064383325720665482436688067908597155734⟩
def polyval7 : Box := ⟨24980455227620645278420336049668126193180980137637434236436,6891711338809056742860857165489399523713380733643758480838⟩
theorem cell7_lo : Holds Q cell7 (127/128:ℝ) := by norm_num [Holds,Q,cell7]
theorem cell7_hi : Holds Q cell7 (1/1:ℝ) := by norm_num [Holds,Q,cell7]
def resval7Tail4 : Box := ⟨-45004313021368587759988616069231948738113727961245708695,17929289554465089364002633993717078770300793882286921883⟩
def resval7Tail8 : Box := ⟨-45714489616341968212012378725546286418665842332107499632,17219174558696633044274364017420030956815590608813228675⟩
def resval7Tail12 : Box := ⟨-46435808872633795707108005807013159915283183933366631084,16497855309878373633052057397534024672069742638139068026⟩
def resval7Tail16 : Box := ⟨-47168509664986705538427828182886639538334674941088355578,15765154517532250115330904582554897695176729037183841991⟩
def resval7Tail20 : Box := ⟨-47912771587937253692080469988888134836802447436973642363,15020892594581728746171374324130949588266216671953815597⟩
def resval7Tail24 : Box := ⟨-48668777062123296981028066858357774887830058187636040368,14264887120395685807462969257007379942400504737042796230⟩
def resval7Tail28 : Box := ⟨-49436711386552333546150147857985286290549494050172976632,13496952795966649254923129192983902833928968469619682790⟩
def resval7Tail32 : Box := ⟨-50216762784025624492938167119046385703097061546890664011,12716901398493358309148752802866040128754635366459026831⟩
def resval7Tail36 : Box := ⟨-51009122447272143056519320467724812968798372679776060697,11924541735246839745650962877551618145989990839295442919⟩
def resval7Tail40 : Box := ⟨-51813984585810435217283197494390205304788132212744231223,11119679596708547584670020539192738728534091338847181456⟩
def resval7Tail44 : Box := ⟨-52631546473549903373816191055989587344241993851607305188,10302117708969079426801528555898786936319971351956048903⟩
def resval7Tail48 : Box := ⟨-53462008497143180569919238512321922333636578946066806987,9471655685375802216020406404731821931507617551476600358⟩
def resval7Tail52 : Box := ⟨-54305574205101446283002263135320767665403730442077365272,8628089977417536104372583905452106184064178970183480994⟩
def resval7Tail56 : Box := ⟨-55162450357684694325683813971325909892301409686728148789,7771213824834256367838302989539468676676361445659124569⟩
def resval7Tail60 : Box := ⟨-56032846977570529187677583099882501960531700785229431697,6900817204939184715236336451464634204988749643505561470⟩
def resval7Tail64 : Box := ⟨-56916977387709144194282709408717742461294826751870805933,6016686780685202554491983010590098773665063934968562595⟩
def resval7Tail68 : Box := ⟨-57814817138449179610854997450147287764587150224980494963,5118600293285440223644740374537823612394999818652696365⟩
def resval7Tail72 : Box := ⟨866278466911775237402183776619593562568995291673736500705,764161220507709396855159205925271449221302080430037907⟩
def resval7Tail76 : Box := ⟨-619747562554970535026518356647171289517860449729067091,249325248857158418947962101698635645044466924918844031⟩
def resval7Tail80 : Box := ⟨-629496259659775403835594239716858585794831485314825472,239546703380768139748267934284039618221393152497155642⟩
def resval7Tail84 : Box := ⟨-639428946159251279920804296990511571599734225425303588,229614015244718203448238772056211533542189498103412760⟩
def resval7Tail88 : Box := ⟨-649518360058367715636767581391879069899053637512021172,219524601344663486832138155277010745382278646116538334⟩
def resval7Tail92 : Box := ⟨-659766972683231386956478854916250418484346125124182764,209275988719797199795008982135981993665205574406070038⟩
def resval7Tail96 : Box := ⟨-670177295995883419838162989121418973099089620268360000,198865665407145140984618552747518599846660279314081079⟩
def resval7Tail100 : Box := ⟨-680751881595010947530047325260133784836545923144385306,188291079808017612537831506073107713648653134285456876⟩
def resval7Tail104 : Box := ⟨-691493321340438833657827301708814667181346599813621266,177549640062589726354553048805608413646484808873961032⟩
def resval7Tail108 : Box := ⟨-702404247988399143870673961049607801990572876609859084,166638713414629416133430868738536344921610303761901291⟩
def resval7Tail112 : Box := ⟨-713487335836826869817912397642207562190215263862326864,155555625566201690186007648023696441748672346683164557⟩
def resval7Tail116 : Box := ⟨-724745301380837659864771114553612150232726805433440792,144297660022190900151093070914462848304575619933921714⟩
def resval7Tail120 : Box := ⟨-736180903978548194700986148675472721923078160033157206,132862057424480365444233173052687293221188576483891416⟩
def resval7Tail124 : Box := ⟨-747796946527402404296974673249418996835845361589704537,121246014875626158772969617429209563828154066407032254⟩
def resval7Tail128 : Box := ⟨-759596276151169476339384412636447146809660634129337555,109446685251859269825453273496915936669328946225280282⟩
def resval7Tail132 : Box := ⟨-771581784897822220035614262140637269373884882228205087,97461176505245480320289877962378994395099961870266938⟩
def resval7Tail136 : Box := ⟨-783756410488718243532210987880144265693351686798673859,85286550953069766371945117424259633803697036037588194⟩
def resval7Tail140 : Box := ⟨-796123493064185720066917872774358511328456757588919549,72919812464080409453002290984285041293569382401746531⟩
def resval7Tail144 : Box := ⟨-961110820004390951481613948145135160296158367830986400,57435385187427065803424981871993913858549191037114689⟩
def resval7Tail148 : Box := ⟨486655069720996329741725740425285919646020158561,155262505274029977849475646535114623414217481933⟩
def resval7Tail152 : Box := ⟨494258554782661682656629689797947894253502184362,147584339467755658553353467180325007923216631533⟩
def resval7Tail156 : Box := ⟨502057354474827967523794814493218221642749061673,139785538429302028064220703281739278321171059877⟩
def resval7Tail160 : Box := ⟨509979211126784180727014661735005573430905795596,131863681776911282439589810035930175314520320025⟩
def resval7Tail164 : Box := ⟨518026065077307034920098239608125389057425401999,123816827826387658515965682409816262233022187240⟩
def resval7Tail168 : Box := ⟨526199888631862120380508558830983799827152104820,115643004271832567904924533724282638380210069720⟩
def resval7Tail172 : Box := ⟨534502685216936493727132699285196849979713612949,107340207686758194452921209071124645252405074348⟩
def resval7Tail176 : Box := ⟨542936489870660139935447461234505468000015790626,98906403033034548238936330094780081732130587837⟩
def resval7Tail180 : Box := ⟨551503369741598647774351860569427426413786614631,90339523162096040399349011867144833660026461017⟩
def resval7Tail184 : Box := ⟨560205424595416967022489525451954126520519687822,81637468308277721151098764011523331408836970500⟩
def resval7Tail188 : Box := ⟨569044787329537710373133164188049727408948144214,72798105574156977800636646590406751748497240630⟩
def resval7Tail192 : Box := ⟨578023624495920139752964555725656396943660827780,63819268407774548422615655156178709791795096382⟩
def resval7Tail196 : Box := ⟨587144136832087971559942735301697379116094277040,54698756071606716643994608634808996261300594590⟩
def resval7Tail200 : Box := ⟨596408559800536158230157106075806261253771084169,45434333103158531072417279262204188054236374698⟩
def resval7Tail204 : Box := ⟨605819164136648989203317454848494020882220342432,36023728767045830155516577320556005259245860699⟩
def resval7Tail208 : Box := ⟨615378256405326390463387246827365118417933964343,26464636498428430565860901708086478075797318632⟩
def resval7Tail212 : Box := ⟨625088179743411430692969795935951698039005485537,16754713330162106619031743299647586051645929848⟩
def resval7Tail216 : Box := ⟨634959740589374849457069766557323789563935558793,6891302381729487498694382656044082076866554370⟩
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
def polyval7Tail5 : Box := ⟨21493478085662281697156318319010380307009772787663000525598,6555934840609365243439815808755857821853183071868273981301⟩
def polyval7Tail9 : Box := ⟨21832616965003250918716545193745732623939482879200666023207,6216793826725197187954361782844105631733044421333655147131⟩
def polyval7Tail13 : Box := ⟨22177109203381393839096990137393017017273337172079647511443,5872301588136946210408829128137698085006510131321637348065⟩
def polyval7Tail17 : Box := ⟨22527037112030933957827809429622730130323380820381302703674,5522373679487238576505374852166482790056173617005884387720⟩
def polyval7Tail21 : Box := ⟨22882486459030830749606959993464368518384643054203451756897,5166924332487341193185766860367144544058073528033913997542⟩
def polyval7Tail25 : Box := ⟨23243544365987118347840092486570688613909615851949516829358,4805866425531053587924641575789103938025779153809594497967⟩
def polyval7Tail29 : Box := ⟨23610299329179364352438258131412263478235763292809332388954,4439111462338807583090583312057448188468582940044180686110⟩
def polyval7Tail33 : Box := ⟨23982841241251187283089610533857120658325382158981008420397,4066569550266984652419897696360820164291819363298002985290⟩
def polyval7Tail37 : Box := ⟨24361261413243188606406427006848955395712581219582664897517,3688149378274983329100031899470363544982421638853030925726⟩
def polyval7Tail41 : Box := ⟨24745652596973538284353461934948229989329818084519211109314,3303758194544633651153180727368348657367577185740180406378⟩
def polyval7Tail45 : Box := ⟨25136109007771698847377500506238204044790840215626946524800,2913301783746473088135474586618057035792851397288370521629⟩
def polyval7Tail49 : Box := ⟨25532726347570860084526683621616628848323524208478850553348,2516684443947311851056320902976941726549464650796393710964⟩
def polyval7Tail53 : Box := ⟨25935601828364744370705358536109210406239264919794378927923,2113808963153427566530054590724813037633673813424507445110⟩
def polyval7Tail57 : Box := ⟨26344834196034532064705721649023889168809405345664580558260,1704576595483639980397206368967983965783162159265936449676⟩
def polyval7Tail61 : Box := ⟨26760523754551771450423640247176341523207158549084260284359,1288887036966424304693935940794634953220022213583411707735⟩
def polyval7Tail65 : Box := ⟨27182772390587971402435855391333895528792752724338914414400,866638400954091437916534275819835877571099186472941720957⟩
def polyval7Tail69 : Box := ⟨27611683807381293192416614144048383977728521912240943652887,437727186593926031174060567747233942653892535448766060954⟩
def polyval7Tail73 : Box := ⟨28156250000000000000000000000000000000000000000000000000000,2⟩
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
def pend : Box := ⟨1031868442077320513669627970960184615071760204022428449891729,3724489109188351653222254972910645134156848852742825618⟩
def zend : Box := ⟨1003817095097508290489687500000000000000000000000000000000000,2005079289788125234375000000000000000000000000000000002⟩
def betaquot : Box := ⟨428764208907435595132200787179752780390504584072923943253110,394799447866260886612920741092342995768344415717952674⟩
def crit : Box := ⟨181824267631981640803943720615898575610474861636651900695,9119132221848594918216088696714437187787434204683043570⟩
def subsonic : Box := ⟨377128764643902224768963244456256316145214105616076582060,4402634996047529221433795237650856949554179755227514102⟩
def pendTail4 : Box := ⟨28047743435854542107533642339820541122967289046617662306146,1630633752061700205786163230392992287109029264696648967⟩
def pendTail8 : Box := ⟨28047780274557835917796769837517749934842163293632822214394,1630515325343967313088665115847604881180852331582046729⟩
def pendTail12 : Box := ⟨28047780276207502587492984977624256057830143917246582940430,1630515309839097917442328710129941290465767871870431905⟩
def pendTail16 : Box := ⟨28047780276208343977809504702355942835423252905907017361820,1630515309825891691749748076677832267048336335555494653⟩
def pendTail20 : Box := ⟨28047780276208346075508327555450703797026047180086023467424,1630515309825841647383785714390220366281544318059008654⟩
def pendTail24 : Box := ⟨28047780276208346094040405583707746474824035212480953065434,1630515309825840979826470856455478840898546183781826255⟩
def pendTail28 : Box := ⟨28047780276208346094517398339176573749319799112176243698136,1630515309825840952896155976799665421896286186440408498⟩
def pendTail32 : Box := ⟨28047780276208346094547938230936192905761278052563346605214,1630515309825840949900531316348910048265793549510329178⟩
def pendTail36 : Box := ⟨28047780276208346094551745496885416473226610879488585417772,1630515309825840949029217864757136897244284935974522048⟩
def pendTail40 : Box := ⟨28047780276208346094551579639971620477558116830858458100592,1630515309825840948382802149380397103706688000975222370⟩
def pendTail44 : Box := ⟨28047780276208346094546702698388198393300793381462756248777,1630515309825840947161668613030842843110241301093211153⟩
def pendTail48 : Box := ⟨28047780276208346094504430156449407828199078316237865967747,1630515309825840941164024218780864569768072440588418660⟩
def pendTail52 : Box := ⟨28047780276208346093736667122566188993480891510587733848629,1630515309825840860870342011179664978088499917779426241⟩
def pendTail56 : Box := ⟨28047780276208346056698503451775113738789302567454804229227,1630515309825837980540262084521395219196637180306465680⟩
def pendTail60 : Box := ⟨28047780276208340312247376878641738717515380097928743713266,1630515309825513271885084186718874651262542106698760353⟩
def pendTail64 : Box := ⟨28047780276204599823614335198096598286334778925921389761611,1630515309669009903449111280711960301195971167408393763⟩
def pendTail68 : Box := ⟨28047780259403375218756186216625797922483845889185342874346,1630514797481203169507528721917102243644093470631484661⟩
def pendTail72 : Box := ⟨28045786094293799104915481393950739832600406586937997541319,1591947203746057734536546967613908638970662700879642622⟩
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
end SepticProfile.ExteriorCertificates.C34

end
end

end OAI
