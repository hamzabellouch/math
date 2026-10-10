import OAI.MathematicalPhysics.Transonic.Certificates.BarrierData45

namespace OAI

section
noncomputable section
namespace SepticProfile.ExteriorCertificates.C45
open SepticProfile.ExteriorJet SepticProfile.FixedInterval
def cell0 : Box := ⟨250000000000000000000000000000000000000000000000000000000000,250000000000000000000000000000000000000000000000000000000002⟩
def resval0 : Box := ⟨126363507204633039916648738948031126360479106157103601582,306320180705849918338712269606332493728391651714738120⟩
def polyval0 : Box := ⟨3888098208089495119899257073891870403150540376726023652757,14825258304698176267232856241559119336784670475533235017⟩
theorem cell0_lo : Holds Q cell0 (0/1:ℝ) := by norm_num [Holds,Q,cell0]
theorem cell0_hi : Holds Q cell0 (1/2:ℝ) := by norm_num [Holds,Q,cell0]
def resval0Tail4 : Box := ⟨70659354677926231692490394423297328628457412373552,2011012148954404300173868424535188651944541934456⟩
def resval0Tail8 : Box := ⟨9297694587552371045368315320709150351808186010,485630439078868205351557492333470341144686892⟩
def resval0Tail12 : Box := ⟨9192438374999458802062133399277267194431771,731566175948485943130757057065996882934854⟩
def resval0Tail16 : Box := ⟨39970401437694908366775661739150408191362,31130827444059408335726510711623244542047⟩
def resval0Tail20 : Box := ⟨590523156947395174954295551527749735379,425638120252924572772536722693621992750010⟩
def resval0Tail24 : Box := ⟨25436292294388753651036416702363655201,6808724826807145194094851431995066227575508⟩
def resval0Tail28 : Box := ⟨2906200511935372022584488174939185298,108939509311119476658280520206000014495358029⟩
def resval0Tail32 : Box := ⟨829783936165726849033049644309674811,1743032135096426734912018361263489355700568488⟩
def resval0Tail36 : Box := ⟨-22672161731953305767834018064152514,27888514156104976183563912587546279869552664900⟩
def resval0Tail40 : Box := ⟨-153270106710340020612986983654814245847,446216226351039595479589160171843038200249408027⟩
def resval0Tail44 : Box := ⟨-39483188127665692671256056526525655949828,7139459584593641863485691818415868129943715218982⟩
def resval0Tail48 : Box := ⟨-10108687651388444003625027528532458471566241,114231343876549982025668928887882260741270033508953⟩
def resval0Tail52 : Box := ⟨-2587833724709176460391988429993673767090037664,1827699075929530526209062899073274597018950162059440⟩
def resval0Tail56 : Box := ⟨-662485639516738541615211538115216895185244615905,29242564134503613086592967920619739545485878599914646⟩
def resval0Tail60 : Box := ⟨-169596315572140734642164636439694820270312739532084,467722029583090462288993421525019532707155262682453592⟩
def resval0Tail64 : Box := ⟨-43416602933713216994920658890144915614026576194985961,7442849372343053566557970877193005036735485313307292991⟩
def resval0Tail68 : Box := ⟨-11113411468686276078284836941259308313283920837932308941,108666131501908350969698874330103625277812044807165368978⟩
def resval0Tail72 : Box := ⟨910304629844516179608048798872398890884134888983007214794,2700296590526082791430685223562303954352549563732077175⟩
def resval0Tail76 : Box := ⟨-33896201343246270418122844714707299647869020163927,713837020122718506060426309195337837848527215258⟩
def resval0Tail80 : Box := ⟨-1993394888632748746601078987370016243446359340,89478399738219728673647951479137042333083734⟩
def resval0Tail84 : Box := ⟨-1225992028161327733490489623368702578029560,86920373679698581657395732089130774488172⟩
def resval0Tail88 : Box := ⟨-3685220821977216789933228648095262045361,569812747471055017353113498804037708454⟩
def resval0Tail92 : Box := ⟨-39834442253162560999214471283365713830,3057892517779473598884146570949246874338⟩
def resval0Tail96 : Box := ⟨-1299603857631376275206061581528203525,48834744931789393601711750843423235906546⟩
def resval0Tail100 : Box := ⟨-114934396801978420065881886920928156,781351805446728252107166291533625529441447⟩
def resval0Tail104 : Box := ⟨-25817784397320716385808262076574353,12501628385340533638137437745923597331226461⟩
def resval0Tail108 : Box := ⟨-16327858883531107769481381843799992,200026054006861541290686811654880069402426710⟩
def resval0Tail112 : Box := ⟨-564005131197019356582363521396175179,3200416863573652354562809680991892251321982149⟩
def resval0Tail116 : Box := ⟨-139607315293292411669368853473828333466,51206669686370704605491719355734730801148204562⟩
def resval0Tail120 : Box := ⟨-35724233003656670267317814201844143515884,819306681490890409882104561762279277652697053446⟩
def resval0Tail124 : Box := ⟨-9145285443695852066305106718833388541217712,13108898330156664421332584940574250992971518493730⟩
def resval0Tail128 : Box := ⟨-2341190952349932674877387515962051610861754382,209740178416429737173219994594192765475084487286646⟩
def resval0Tail132 : Box := ⟨-599344866013897908337782324512260232635236062427,3355280968945827816178685073172853375998943545774650⟩
def resval0Tail136 : Box := ⟨-153432430400773585813454814287830830509892386277087,53540652698049192528775766777985116070293027096278497⟩
def resval0Tail140 : Box := ⟨-39280549472739458373399711838289691124755956679573516,819825848332482864482456492985729897280921970397083713⟩
def resval0Tail144 : Box := ⟨-10843789305137717036639467479655281317993560334609691912,3308525162531777680562901440144477831165303885017546268⟩
def resval0Tail148 : Box := ⟨88589448913257675841827281484028423711122826,1508756001606679575354987321229468758870913⟩
def resval0Tail152 : Box := ⟨1719353002324320862506643293363786266815,68537329209209800414774425011360683048⟩
def resval0Tail156 : Box := ⟨594326615026888707707191448035583833,38279745923061204560650598818027410⟩
def resval0Tail160 : Box := ⟨1131696576576607100541119306235760,108688603826355376267908082175710⟩
def resval0Tail164 : Box := ⟨8205894350985399729655224295762,41367532377287050470519906982670⟩
def resval0Tail168 : Box := ⟨185395028930837754767728034674,644699957269863471070598884730487⟩
def resval0Tail172 : Box := ⟨11547553670200159231315454695,10314667502762848159378775511290606⟩
def resval0Tail176 : Box := ⟨1838405432707567269047553386,165034634779834951993194004473042291⟩
def resval0Tail180 : Box := ⟨725038259083152469635279007,2640554146518446979945662259461139104⟩
def resval0Tail184 : Box := ⟨3028603445262466224641188937,42248866338065673742484484734959560327⟩
def resval0Tail188 : Box := ⟨605723657566067516680383660935,675981860843295793357757655632749009339⟩
def resval0Tail192 : Box := ⟨154689895322026913547528539047716,10815709628478759214866808255871128637720⟩
def resval0Tail196 : Box := ⟨39598617186677848532383595361776678,173051316932040926460631236066328775740723⟩
def resval0Tail200 : Box := ⟨10137220658743565087055361146258228174,2768811567271173658162909790007027841559531⟩
def resval0Tail204 : Box := ⟨2595127888329517917369655785765356494094,44298552144281558911399948900426830566033332⟩
def resval0Tail208 : Box := ⟨664352890025155471327898586522374512219612,708154003635944022765939927201750229562752265⟩
def resval0Tail212 : Box := ⟨170075234642335003720644148004591207964847877,11171019012179935468079994618381353929068155509⟩
def resval0Tail216 : Box := ⟨43590805550639993424207554686214717108924841722,137893988329276919796454846104985657915402050950⟩
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
def polyval0Tail5 : Box := ⟨2332563350107456049409126675202368572022075066093275,56729003422024612783557148085276935319440800967781⟩
def polyval0Tail9 : Box := ⟨246008345785956391642632755417921106557952033857,11841212502838549895199035217795211600526187781⟩
def polyval0Tail13 : Box := ⟨210449658122161170804066839613261477473596504,15724453652378024403347742551487721032412302⟩
def polyval0Tail17 : Box := ⟨801866157692116025192140311805965501122788,482523583443450090979469019997109958619548⟩
def polyval0Tail21 : Box := ⟨10409693549986973021480851551215295971731,6344351871196735794771138845464859136971402⟩
def polyval0Tail25 : Box := ⟨393555005830410997884290103091143963606,101484788779735348465458571045062647606116568⟩
def polyval0Tail29 : Box := ⟨39325821287841891245277275279703659942,1623755330908624613182986959208041183629346962⟩
def polyval0Tail33 : Box := ⟨9815317772868072464706539476020811956,25980085117113277534488652034476002380611690064⟩
def polyval0Tail37 : Box := ⟨11879085980465873688363812110142876660,415681361810087127335772484657099671664341916435⟩
def polyval0Tail41 : Box := ⟨1542572007847702467154423370311869518681,6650901787531169506816744166991643362786392653950⟩
def polyval0Tail45 : Box := ⟨392761030685877922546405899801160834338750,106414428232320022790625927555370169896267633828832⟩
def polyval0Tail49 : Box := ⟨100539541375149279362214450010400977256018564,1702630757461515272022477125234200779744435439801974⟩
def polyval0Tail53 : Box := ⟨25738062882377875836963262374970431973826815582,27242067989954298932350423803963601506829561301905443⟩
def polyval0Tail57 : Box := ⟨6588942982089399730393634367068811923211578331133,435866910705468649049554061806802003805653589386714074⟩
def polyval0Tail61 : Box := ⟨1686769396261146486648432750876145936111344678611996,6972289225032896261906795934298219775014270336337755589⟩
def polyval0Tail65 : Box := ⟨431813048387200261023874334097267347216591175639101048,111151802924254993546605402549223962572676789453142174891⟩
def polyval0Tail69 : Box := ⟨110545121940038682768202235675473461745518805640326504963,1674793288112160828518775711631958010047596243514968125254⟩
def polyval0Tail73 : Box := ⟨28843750000000000000000000000000000000000000000000000000000,2⟩
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
def resval1 : Box := ⟨126107225548879387777843881063896951197019385044429825167,218620727795586369180080818736073878085006201359107145⟩
def polyval1 : Box := ⟨3869128201684804416803180573197825554699467351203837282652,8354506683644940343057411220818089065237158182885437078⟩
theorem cell1_lo : Holds Q cell1 (1/2:ℝ) := by norm_num [Holds,Q,cell1]
theorem cell1_hi : Holds Q cell1 (3/4:ℝ) := by norm_num [Holds,Q,cell1]
def resval1Tail4 : Box := ⟨68568254324418999181663710861366147095815066939367,3396472197700609828537492862487866065997337510217⟩
def resval1Tail8 : Box := ⟨8766834474896750836223350003144405947189027851,6825970762318708434446241888512789166497931676838⟩
def resval1Tail12 : Box := ⟨-343871413688756514080544043765291008749887955,21572404111184802972748338255913687391500710296662⟩
def resval1Tail16 : Box := ⟨-2309366782407219223536630755496038091345543289,68178253245214701248024659453413492914771272925644⟩
def resval1Tail20 : Box := ⟨-15134902112543876743249936869298736922968983805,215469112472767553006275098353454367804329993517826⟩
def resval1Tail24 : Box := ⟨-99188097860973299798443642646667579708468230890,680937445582274794094798429320640427989159795495047⟩
def resval1Tail28 : Box := ⟨-650039118281297181962088040952141414709386290019,2151762037698010294274531467779218950412912645888364⟩
def resval1Tail32 : Box := ⟨-4260096365583352183869577254953477718339900376308,6798424985918010957500748672935804968368398701965255⟩
def resval1Tail36 : Box := ⟨-27918967541490952986774135109993662679848259603408,21471925243132586248506109570961601755017979396845454⟩
def resval1Tail40 : Box := ⟨-182969745679917302008312682384620535139331916394115,67767155167067783928659273660041382926140142594306388⟩
def resval1Tail44 : Box := ⟨-1199110525287907899570326926299392904614028818414293,213556839816235690029085932514543927746348317176899495⟩
def resval1Tail48 : Box := ⟨-7858490738526823406031852385062111094511168904526563,670876364661844032786095752731185850122321716039429892⟩
def resval1Tail52 : Box := ⟨-51501404904008803243924667590396919833696661291744919,2093635915867532973793573999937416317981998431570854403⟩
def resval1Tail56 : Box := ⟨-337519607178852927217421386049291744192210902346964857,6442173653531146553613672641783406222668347493087711567⟩
def resval1Tail60 : Box := ⟨-2211968497588049131926687249576164206250221309799901861,19215210202909698604461897519944876157749285068813973318⟩
def resval1Tail64 : Box := ⟨-14496356714349943322692785486428260796616733607297844251,53224109274061892515696401679652729968127271733910547252⟩
def resval1Tail68 : Box := ⟨-95002754825804232497364750672993023693278269652053254620,119026867386158915110319365223680954584569640504306864732⟩
def resval1Tail72 : Box := ⟨913666744704759350762049025377882499033468450450097599306,1578672520567075574195627115728025776998564002078103006⟩
def resval1Tail76 : Box := ⟨-33124789714489858375069867342367495192566755424239,456499933235381257474766559200380075292458850509⟩
def resval1Tail80 : Box := ⟨-1903425447232079877430951125271646611423896100,73478489910950770770128055753873071574302867013⟩
def resval1Tail84 : Box := ⟨-4286894859097064993979500409211269601647516,232056784180337042680554728215757539080558169486⟩
def resval1Tail88 : Box := ⟨-20605381803287640991396991220983803676429407,733403392066732435822009952570660107774780110397⟩
def resval1Tail92 : Box := ⟨-135017504809495504233729909394416289886694739,2317846988654164276291170806072281678055327306074⟩
def resval1Tail96 : Box := ⟨-884850489646669579636773777017760534198972778,7325082971335466386986515184939802906683129469998⟩
def resval1Tail100 : Box := ⟨-5798956161726989103203219965564845009485647244,23147877122689531300603860350695205316869756238985⟩
def resval1Tail104 : Box := ⟨-38004039100887982017884366269895661608591273970,73139046284181817531712135614851544733749377495982⟩
def resval1Tail108 : Box := ⟨-249063270651454527107400355499720362094675986472,231026552565896298851115709997145300191735950339752⟩
def resval1Tail112 : Box := ⟨-1632261050541314419420363218027551332151135871852,729312895173609586160193744583954197911518599364228⟩
def resval1Tail116 : Box := ⟨-10697186020827509826565263819095354838779632590819,2299450468218464215258060526735188637995488040042014⟩
def resval1Tail120 : Box := ⟨-70105078306095223154736517475880068995878802749785,7231102322746481224887402988970925854533126581181818⟩
def resval1Tail124 : Box := ⟨-459440641186830520747982133311995703729650889195052,22615980280658353966212630739447375566637632800202478⟩
def resval1Tail128 : Box := ⟨-3010990186082403320009116061263227440935771748161842,69918735196539748799733083371977896092096195080862697⟩
def resval1Tail132 : Box := ⟨-19732825283601027771236290566318425770239243819224645,210761121604762628933043136935179501011087883958863127⟩
def resval1Tail136 : Box := ⟨-129321043874175225329462973319070777564584819150372315,599153652543634545081815512866664032960254558106949608⟩
def resval1Tail140 : Box := ⟨-847519272169463736026912868935857443077735947086321127,1454821235059120698966758703058502890776669521472578176⟩
def resval1Tail144 : Box := ⟨-5886871728247922364187657078913867033750794843543542899,1665101570002990013704226106801301500872080863624663935⟩
def resval1Tail148 : Box := ⟨87248671775029246815008117994738369158588216,1034816558188993033624792826051822133020722⟩
def resval1Tail152 : Box := ⟨1652310753955885386999385929343451867409,4218878599398344858354117596444728712065⟩
def resval1Tail156 : Box := ⟨719615007441625149844253387286286019,13197692844780053897758691704354526707711⟩
def resval1Tail160 : Box := ⟨1057951451066135974272691459627632683,41710686505538180181482978094792747497944⟩
def resval1Tail164 : Box := ⟨6926597136345373042029201368564108999,131822781024321470518602171916743228549608⟩
def resval1Tail168 : Box := ⟨45394099115329008782711408306889106366,416601583051988301609528901140303370560942⟩
def resval1Tail172 : Box := ⟨297494766916870416987036463122825381607,1316512704623727428009689060473163065073341⟩
def resval1Tail176 : Box := ⟨1949661704404162531772921060299414976673,4159820845011676774436512473648046345480508⟩
def resval1Tail180 : Box := ⟨12777302945973866334025476145926752446258,13140472693588796160462039185610439173179917⟩
def resval1Tail184 : Box := ⟨83737332586731148907658888629258588858192,41487028088560194951119489162429984503617122⟩
def resval1Tail188 : Box := ⟨548780982840399032781914190574136430830159,130835366521031366642667494666631077091457222⟩
def resval1Tail192 : Box := ⟨3596491049142837688993518697876296511303025,411642296123587681985633142749557758391286972⟩
def resval1Tail196 : Box := ⟨23569963739662540383863736284551696100654891,1288789659917362354218751352462413324347892495⟩
def resval1Tail200 : Box := ⟨154468114364254787134405793016938745927455691,3993236375218443236000117259390871127768098317⟩
def resval1Tail204 : Box := ⟨1012322234297901345797022960073090398777383986,12096472201914351275130633578122768164220822896⟩
def resval1Tail208 : Box := ⟨6634354994853208316258019095262147849442469240,34795908902442620716257805374415557757781756291⟩
def resval1Tail212 : Box := ⟨43478909365812352003412831055475637483572205402,87461184327726800382815939213626744799454559804⟩
def resval1Tail216 : Box := ⟨284966219025477998987387103719519814895754471027,128887904479208496360840782952504234594067879465⟩
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
def polyval1Tail5 : Box := ⟨2268421182950658937655436110757129942561122531330090,124503605893651463204592114027673576443132780181482⟩
def polyval1Tail9 : Box := ⟨236293148880059809140077074877666680099614171711,289160683300652500105593348857876422317449322693717⟩
def polyval1Tail13 : Box := ⟨16391865073442662023369146090869962460993809052,913863568170934239338054511096515075798862137032439⟩
def polyval1Tail17 : Box := ⟨106145880788614160779633381879679874187536499108,2888205215188750697057881789687108411146917498054506⟩
def polyval1Tail21 : Box := ⟨695632895660373189671161829153619824081862726761,9127794592419827029330570939380144708122473874670757⟩
def polyval1Tail25 : Box := ⟨4558899685228628613139984983236380131558921759169,28845978108690893691704596449758687519962988066255055⟩
def polyval1Tail29 : Box := ⟨29877204974940271224376823781429334326061503930042,91152066920262148375325632624358826392946800789996953⟩
def polyval1Tail33 : Box := ⟨195803250523562809806718780696132089278331533562083,287984168305781214115073393209865051169411456823279833⟩
def polyval1Tail37 : Box := ⟨1283216182631174393690850829796076461588141288918825,909507805032356741517095274475226392325209272836064618⟩
def polyval1Tail41 : Box := ⟨8409685574491641027107044142593909544169350268054111,2870139714808680034464996185031436484534913532002433153⟩
def polyval1Tail45 : Box := ⟨55113715380988398417002799787733459431876376870265985,9042523895706566523279341759713521499114776063889329482⟩
def polyval1Tail49 : Box := ⟨361193245120845603831403584598579523672925010477224118,28391834266464513232334523000328984232859804687776121615⟩
def polyval1Tail53 : Box := ⟨2367116051223976399300253147412527581568685393543359825,88506649911317407104309215803476790107605558679317811847⟩
def polyval1Tail57 : Box := ⟨15513131753301669755925768755686250976540425607696860326,271692844622137951291226785117693819631237674503707802503⟩
def polyval1Tail61 : Box := ⟨101666860258490129693360135167279898179072206575123205870,806045855199733192001488836712179884549767670506500293770⟩
def polyval1Tail65 : Box := ⟨666283935444852390294632195132226731123867623612905717421,2202536498641515525502123557833516860893732171400831978699⟩
def polyval1Tail69 : Box := ⟨4366558868953046948798732566850701439579638143795265073570,4700330793255413047268425044489419324519911007426783999017⟩
def polyval1Tail73 : Box := ⟨28843750000000000000000000000000000000000000000000000000000,2⟩
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
def resval2 : Box := ⟨125981106125814242767179283681015901305945000280017636871,196197915479624680149964173543583846993908428607794528⟩
def polyval2 : Box := ⟨3859757199528558509298081173405491746512650886440408557815,7033441274442591461909739410456816624883900040300352215⟩
theorem cell2_lo : Holds Q cell2 (3/4:ℝ) := by norm_num [Holds,Q,cell2]
theorem cell2_hi : Holds Q cell2 (7/8:ℝ) := by norm_num [Holds,Q,cell2]
def resval2Tail4 : Box := ⟨-132139032636919226375985209799787565206390710631639,36138233365066676472100437890670447711257694100108245⟩
def resval2Tail8 : Box := ⟨-458257439050432602934108444418092544082972675322536,61531316352479567094858647508866032643751934000664107⟩
def resval2Tail12 : Box := ⟨-1051536115864169901536612421391306340522143332276249,104699954399873739247604462625571062323497692681798504⟩
def resval2Tail16 : Box := ⟨-2412852190983960937293949600322827093390918493296642,177994521896905661878432681951018157948305115451499579⟩
def resval2Tail20 : Box := ⟨-5536524673175553166388902713315622667493327228923609,302230490847078500443958140220100311330323043438747021⟩
def resval2Tail24 : Box := ⟨-12704095829321960564179014643451362800567513357498615,512332845266455818946920223250278474561147103157911795⟩
def resval2Tail28 : Box := ⟨-29150786886679222282623387669518234645940093268335837,866539055149266573745842635377020419714077905441279429⟩
def resval2Tail32 : Box := ⟨-66889323532278619054748327852222125297363265594737397,1461118003822670979959012103228482117384714540041523945⟩
def resval2Tail36 : Box := ⟨-153484076433297559834178500695325274225099220283949024,2453228965151822622895576101147777821418810533740221849⟩
def resval2Tail40 : Box := ⟨-352184182386211578350668617079701953273048394561267699,4094753184682781452992100928992954237558583064077335803⟩
def resval2Tail44 : Box := ⟨-808120954338530232483936624654326737098872978155181635,6778157869282709022957695485166448156127583470749356974⟩
def resval2Tail48 : Box := ⟨-1854312344229190742044922236074974764052434255376279669,11087544407771057461840188748834543181817703997228018232⟩
def resval2Tail52 : Box := ⟨-4254900521389455111855420675510689107472956321026401973,17823335736916673631924629035575273973784992636267737804⟩
def resval2Tail56 : Box := ⟨-9763284218682043716927555283008050932562047058793777379,27901212122018404816575249716373317558473299827322998573⟩
def resval2Tail60 : Box := ⟨-22402807834287698915969053369891162664367340395522548717,41851160100519138047918824520987729348348008124430571492⟩
def resval2Tail64 : Box := ⟨-51405427453758558466208170043201425736618529191887253595,58209005116925152892643409930357765740090534971824090541⟩
def resval2Tail68 : Box := ⟨-117954319936755036854195497796418525549974340783194879687,69042636086134448708760173858047933287784840685237684751⟩
def resval2Tail72 : Box := ⟨915345770431645065944441867319273885633036177029576085648,1018354372073829416499326064107219234507340457589194504⟩
def resval2Tail76 : Box := ⟨-35073895641451795503309107155124002723454396674585,453560998372236572425740858080991741666974614411460⟩
def resval2Tail80 : Box := ⟨-5322101478297896193766245619033732125785892724058,772331303434984184764236283220769722781482592419651⟩
def resval2Tail84 : Box := ⟨-12207811651702004181658861721917819972616483525567,1314431381299603811585487707795511592536044115532974⟩
def resval2Tail88 : Box := ⟨-28012011904299711093491784492502373913431012790404,2235175880549143978558643076648596245827088733929114⟩
def resval2Tail92 : Box := ⟨-64276293265326428416979182940846177332909533750815,3796622335421110229569437183627572024456426564601706⟩
def resval2Tail96 : Box := ⟨-147488223641828982014866111553255363415688614210642,6439034384896075399206719429226756856134254884849423⟩
def resval2Tail100 : Box := ⟨-338426113392067444946345440995212883585236692804132,10897890673184880564194157525168369197588616071186270⟩
def resval2Tail104 : Box := ⟨-776551723233168545432080264662424673136974972664174,18392108650702349452157294933690087843584302966395429⟩
def resval2Tail108 : Box := ⟨-1781873664570881020860248353554417015369281716469318,30919014670139606966547718769028889428059671774925717⟩
def resval2Tail112 : Box := ⟨-4088682906106833034244707636726951547612146946996049,51697588905211017352766641231525637356556202824311825⟩
def resval2Tail116 : Box := ⟨-9381881689528287175004961318257833355394614387943326,85787035153103081091943518707625365045200958871864786⟩
def resval2Tail120 : Box := ⟨-21527642533697203675498110225620454532438875062810101,140826328056647687976933946879939595308030261153110924⟩
def resval2Tail124 : Box := ⟨-49397275343593714948077317116216479254752467621981295,227571430836353260238842743782385282903646378209338187⟩
def resval2Tail128 : Box := ⟨-113346865898174703934057839160359805880353315398183195,359149519155162887664551566746612391442860375084262191⟩
def resval2Tail132 : Box := ⟨-260085438307655851824849015856201681463273537917915934,545972534694691246095678153842983157943005363269841568⟩
def resval2Tail136 : Box := ⟨-596791403912164725808844485247865877488703056884730649,778307912033413883247219776480810646530525514135370020⟩
def resval2Tail140 : Box := ⟨-1369396774266656637630493760808940664221929377727452505,976462581815108685809990230529536560263031172684593682⟩
def resval2Tail144 : Box := ⟨-3400256770869269648136197923107855915204293271099547775,838864059963502925055293447683733244987393830505746710⟩
def resval2Tail148 : Box := ⟨86957934747212818635255641188895320600182830,64808869405845638306664357122067489703119544⟩
def resval2Tail152 : Box := ⟨823407812479299085034405523629896070726414,109085299167169794442542785300133224579093812⟩
def resval2Tail156 : Box := ⟨1885670732791002565063990166975508111378027,185610953407192897975032557402689708648971518⟩
def resval2Tail160 : Box := ⟨4326854159461806341988643875288865061565612,315534108041216064250204364906497470249827151⟩
def resval2Tail164 : Box := ⟨9928388856460573475289355956336202615313749,535740291347566409648966837467312694223247916⟩
def resval2Tail168 : Box := ⟨22781656528011912407591416206439410658813262,908105021570974308259355409756424756773890198⟩
def resval2Tail172 : Box := ⟨52274732755147895558042639561657437577726708,1535776843043872073830896859720547111052233359⟩
def resval2Tail176 : Box := ⟨119949472561933123187427771570747844309508148,2589196406018985560430157493678691060084529765⟩
def resval2Tail180 : Box := ⟨275235763237241311082839054490602748146319508,4346447501513880272955917027257858086638420842⟩
def resval2Tail184 : Box := ⟨631555301968273048655852804130603205966326886,7252832308369333784720443193380892418793655377⟩
def resval2Tail188 : Box := ⟨1449165234753430990316239382567838927573527068,12001251946397271879100803584136438473971380007⟩
def resval2Tail192 : Box := ⟨3325250965470426576791017874914394365012990132,19620566932902450957138640315388240791697143480⟩
def resval2Tail196 : Box := ⟨7630112645673116406293643752024730878637449368,31514439670751417742507065302733736014641432384⟩
def resval2Tail200 : Box := ⟨17508037615868961913658856656870415916640006787,49270840471625788863308808320706011373194659867⟩
def resval2Tail204 : Box := ⟨40173899835215718914615280262667037034246591215,73747918010006724421868798072971174462175594171⟩
def resval2Tail208 : Box := ⟨92182931256062568816296072862659745385114540425,102162660536653326009141421720032096980360804740⟩
def resval2Tail212 : Box := ⟨211522726568980976122029585844718333741565594858,120022273347291752154237496143088280323088520591⟩
def resval2Tail216 : Box := ⟨485377383994855213392725423922477139289062673517,80239979790571122727931069718317592428472498060⟩
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
def polyval2Tail5 : Box := ⟨23391531179076707178239681946637296507291283577343959,3245917184544861568134010053547154698732974939646014487⟩
def polyval2Tail9 : Box := ⟨48539284449912560710491161569530365455458418872546190,5524940157597116950777712021517983706235883019757091413⟩
def polyval2Tail13 : Box := ⟨111377598648836094840040345703993874538465167450472632,9396731880114674715085867043866192408621254175625158310⟩
def polyval2Tail17 : Box := ⟨255566762112776629382836022631371549070676359167864975,15964848241735995119336499717473707148216975364810139027⟩
def polyval2Tail21 : Box := ⟨586422860606341912910525095389518003585734643389747013,27084889032672178513846499068838943039707825275543587745⟩
def polyval2Tail25 : Box := ⟨1345604446367307341543357301414695588211346976021483714,45860432002974127244554812877817594476483314429562115868⟩
def polyval2Tail29 : Box := ⟨3087620636431771793772663778213056836672451217647608828,77443793481228584231388260620447843585878333545625538415⟩
def polyval2Tail33 : Box := ⟨7084846680059962694293727052475521663390673007318714508,130298190481929549245450540003742121511020814300876867111⟩
def polyval2Tail37 : Box := ⟨16256871679017181288544250965157652361611864971051328205,218112524495705451315869229535036565354037820890481477394⟩
def polyval2Tail41 : Box := ⟨37302977569275235209458488797531856514013921657458347049,362520865301055419993162132475318374057799016693966199976⟩
def polyval2Tail45 : Box := ⟨85595320121144981437716634581390663013428754472915692568,596486504284050505327431295759617889532206127719871178884⟩
def polyval2Tail49 : Box := ⟨196406809966715363836884379872492618121539081312264828580,967194669734942576194979833391284455092546977019144161237⟩
def polyval2Tail53 : Box := ⟨450674580651190720426219151720171780270101128091779110094,1534378172725731782028851672968534702407849535645407868091⟩
def polyval2Tail57 : Box := ⟨1034116778738715052715982495544777897572563454884463469787,2352295581874310764149447607526124557350535939181852332135⟩
def polyval2Tail61 : Box := ⟨2372881804258312984503278867811028050354219043401590117333,3404188178695059800739826724378780494020595589652284903028⟩
def polyval2Tail65 : Box := ⟨5444808722563548660688008963068124778679986413242817179906,4410617620740660265119794190400884364632527471201932293999⟩
def polyval2Tail69 : Box := ⟨12493645006811909685394462191258885071863158309299041441401,4319277573267543025154456351109465724610358908277140447542⟩
def polyval2Tail73 : Box := ⟨28843750000000000000000000000000000000000000000000000000000,2⟩
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
def resval3 : Box := ⟨125794676557141190950149676185969518476074701641965731607,1711338360919500770144683287183147836024308370836237259⟩
def polyval3 : Box := ⟨3879045456974639926824463046394419237778337600636969345851,253139166129065016393767088826268736477979288644199005136⟩
theorem cell3_lo : Holds Q cell3 (7/8:ℝ) := by norm_num [Holds,Q,cell3]
theorem cell3_hi : Holds Q cell3 (15/16:ℝ) := by norm_num [Holds,Q,cell3]
def resval3Tail4 : Box := ⟨-183786069655808189374072052677011408865284516006986494,1995267193154107812797064544027272982672192359440101181⟩
def resval3Tail8 : Box := ⟨-272570601314919196735396028175626609338270072693020715,2548383269385369689250238042532334214660870721384388998⟩
def resval3Tail12 : Box := ⟨-404098229342915947726076605893412838054135480865330453,3247734529514387700049798996402966238717324974352176554⟩
def resval3Tail16 : Box := ⟨-599093860770923259997038606242597034864524650143294049,4128343407080663052875895119458809732046857972077316162⟩
def resval3Tail20 : Box := ⟨-888183683927274421731508080566525400758257590574544047,5231664785918131326381666283142543044853513275557606869⟩
def resval3Tail24 : Box := ⟨-1316772392525355818546922093041919841985707569821555006,6605605668112442498263004707640428065047590465485577825⟩
def resval3Tail28 : Box := ⟨-1952174493963032404037407450216847461223302924291343164,8303647107655905898723908921255327675839535650244308027⟩
def resval3Tail32 : Box := ⟨-2894186783162251874307809923805232502726135682309919057,10382366786886118312483900580754244773358032319917232737⟩
def resval3Tail36 : Box := ⟨-4290762512129042660116314125518088439606662580286639398,12896244199311747237656890282716855622865275655682138402⟩
def resval3Tail40 : Box := ⟨-6361249053655086219405566587700811661922394401946203727,15887988908635947987595542518650814289515285435927736392⟩
def resval3Tail44 : Box := ⟨-9430838786402343179855495328914152673670411082403837403,19371651269828870996886226270888823698396918877374921671⟩
def resval3Tail48 : Box := ⟨-13981644086707579291037806729727340369672004270282551338,23304281608604398016371165949249544461159049945117529687⟩
def resval3Tail52 : Box := ⟨-20728418308795918819913720665983140741638713407701589207,27539639496003403922185519981279340252325165129149341272⟩
def resval3Tail56 : Box := ⟨-30730815555011311288021405594539407368285917697998674599,31754032569340804883028639649226214149574900017950977221⟩
def resval3Tail60 : Box := ⟨-45559820851120255657009994148653127923781318368277782204,35329206441260713981069954177020620772803318277254004678⟩
def resval3Tail64 : Box := ⟨-67544490368799959742893507431958978213175085534737775182,37169451191054624762913843798707713123427177342052457551⟩
def resval3Tail68 : Box := ⟨-100137351425386720229150765625968554114058565754565492422,35418453573287491416593662818029548596616240475329796248⟩
def resval3Tail72 : Box := ⟨916183182770132661175661752006849848220798561523116247204,758709440373211557911798459721932939138909502184012015⟩
def resval3Tail76 : Box := ⟨-2413870900254698211535507936813154681009728706802126,26896786743319709221643370286021714809375065666296289⟩
def resval3Tail80 : Box := ⟨-3530381394146468333675342928550610054979746326673409,34371094800119437983781672480313083148567960280145438⟩
def resval3Tail84 : Box := ⟨-5233947004440001009969397807663481668926355211819484,43830962080602114446586828029801614173895161337445121⟩
def resval3Tail88 : Box := ⟨-7759562625022221647990834513039660538170233197022342,55756839976959520389578870333320388710306711667674295⟩
def resval3Tail92 : Box := ⟨-11503901757705964509955052862678666815382192191819092,70720512285222782860437331042175086262781307997704841⟩
def resval3Tail96 : Box := ⟨-17055053492866705188917914873723498726201328744196842,89387597345995048006101977060294644080630642621921070⟩
def resval3Tail100 : Box := ⟨-25284886447304815569121734589462894126231431428573951,112509198794683209966785162498069372734638425175490664⟩
def resval3Tail104 : Box := ⟨-37485985190283768705583887655078605747819845678584607,140893731756262942138826931829676031951999234052920178⟩
def resval3Tail108 : Box := ⟨-55574664676255961975364186746619638981939979606024760,175344705789104734144287299807212678972034591380262873⟩
def resval3Tail112 : Box := ⟨-82391948302824155579955509040400258426016123791009789,216542014419504310212739802782202266536732600222638518⟩
def resval3Tail116 : Box := ⟨-122149781463919067208673898755832494250485678556074766,264831673962659072740789684834835662674021506423272549⟩
def resval3Tail120 : Box := ⟨-181092563278683295569470581059975127542243211259682213,319869741172402630147246346092175283419654648855377353⟩
def resval3Tail124 : Box := ⟨-268477897232512422926643069209350348483867036546099217,380036978510823230619867060085758768170003624935123743⟩
def resval3Tail128 : Box := ⟨-398030598260774965727442190806579295782681822579115921,441496728094094378115038139362653420763413583137308622⟩
def resval3Tail132 : Box := ⟨-590098323865535913230220020038974419279559985925383183,496701930159076730156950190014565145152052838551116930⟩
def resval3Tail136 : Box := ⟨-874847394593390964034046109496173108250847660484924649,532057127897358084946838271811322901408919496017110602⟩
def resval3Tail140 : Box := ⟨-1297001369732746402635217413001414981915254075863154622,524290971824178114469564924271174169738998346163147052⟩
def resval3Tail144 : Box := ⟨-2154908537170752436718218243808151856796282821526262382,424612677961755696076515634566719911497969277429744721⟩
def resval3Tail148 : Box := ⟨836198365190619691007686495296448721679896152,7327032468035828372894603419550563627108054327⟩
def resval3Tail152 : Box := ⟨1111788707838976697982479516439318462687016246,9343542686742466420159575324594518805862833037⟩
def resval3Tail156 : Box := ⟨1648274551089460599297993654626902898860886501,11886549986593197752177629696658122393449342422⟩
def resval3Tail160 : Box := ⟨2443641402955300893921080393183089962973303049,15077706959833253287675457393082818231788466950⟩
def resval3Tail164 : Box := ⟨3622808654190113299679587039141252649573552847,19059247371560915457115234372837228125428542441⟩
def resval3Tail168 : Box := ⟨5370977316478238812907992541943769969304858004,23991812287543864324275630789296511115603613718⟩
def resval3Tail172 : Box := ⟨7962716248002541555438159016949015685188310588,30048538655487681489534242609491930945462939888⟩
def resval3Tail176 : Box := ⟨11805086171501161498525562748004944017303969892,37401938052797806539731375052596981100900597004⟩
def resval3Tail180 : Box := ⟨17501572977880081492986109878060663836259835784,46198803112266232962025940548695261964715102349⟩
def resval3Tail184 : Box := ⟨25946871733941084705205862757118844188344602485,56515703030381460758658533734822323272350451351⟩
def resval3Tail188 : Box := ⟨38467408251160439536808924300954558388180149907,68283550756338668404499364628818902504434381267⟩
def resval3Tail192 : Box := ⟨57029668652726157001355568495939914849670863997,81163533313011354863949594138030178144038380960⟩
def resval3Tail196 : Box := ⟨84549057357968025214984252063264457758434068919,94347331462309971426755044100170875014945600974⟩
def resval3Tail200 : Box := ⟨125347792982122637988483688491131725061507399388,106240428997645043688543134556909606518337825895⟩
def resval3Tail204 : Box := ⟨185833759671223187917436114999659669770215645174,113966056934526275913862871355608816461787167430⟩
def resval3Tail208 : Box := ⟨275506934840744393905576570260010022906457891704,112595401575650262153665767570600648750737159679⟩
def resval3Tail212 : Box := ⟨408451464056031393161322333013445000934628539956,93961864054097051543551189143249477333753638129⟩
def resval3Tail216 : Box := ⟨605563830733981485848037462970220306574363564869,44844654954617315558721638922223514438585599623⟩
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
def polyval3Tail5 : Box := ⟨35526958347293464160938343248818540999986588248404106235,320776713248218723830407668666281104664909231035797296691⟩
def polyval3Tail9 : Box := ⟨52667023485595417262890019542391145204798332054862667103,408578832033109578312045645566857482845301091480602990606⟩
def polyval3Tail13 : Box := ⟨78081238690269547668258816714275504073543691431892637695,519019173604302362510047144423088186208387137979668694682⟩
def polyval3Tail17 : Box := ⟨115758959933455037537154005543619513450656701853843266408,657210375772714125742159475497670359156703770425836739545⟩
def polyval3Tail21 : Box := ⟨171617881960892267953787971949106124561398903713726208842,829020505887788374716008827163926692909335813772105974500⟩
def polyval3Tail25 : Box := ⟨254431254614537308567244351564900230768964879824476045281,1040933434492645586188909893317597364919124624804105908517⟩
def polyval3Tail29 : Box := ⟨377205816696183090694953563282084140727694627691935252802,1299693349038697663309312081767217299207233022307855564299⟩
def polyval3Tail33 : Box := ⟨559224645435147954607948213308190251101465977684669527198,1611585502231047504014245175898424767605045583156976073991⟩
def polyval3Tail37 : Box := ⟨829075773012148921922924101530305282332982072939041363471,1981121043530108570935591593835578234404007978750223335993⟩
def polyval3Tail41 : Box := ⟨1229142247228452436802199087459928834717620400517479475553,2408765082527861381507639455221128724919297400816580068575⟩
def polyval3Tail45 : Box := ⟨1822258849071050604185447647989346991665609866354971640223,2887151417850624109832156616175887456071289973628218277057⟩
def polyval3Tail49 : Box := ⟨2701580976901013823946131715765798666829147482868438097825,3394930850318321960011343550289190026694841465440640926235⟩
def polyval3Tail53 : Box := ⟨4005215712616283306656359469910726268792908553672741642311,3886952171011299706920842961951821701882883161963129855196⟩
def polyval3Tail57 : Box := ⟨5937913037494760941527668028968734762189695856557234810999,4278800333792494146043503834850495194913578610647533612823⟩
def polyval3Tail61 : Box := ⟨8803224038542156349547783471286806483728475896072036673866,4422702430607146138427715981336598208733904099234925245663⟩
def polyval3Tail65 : Box := ⟨13051176900647601537884744355664346678326590514881379377235,4070291091136824429012098816518923759293477527662271265246⟩
def polyval3Tail69 : Box := ⟨19348959052030963118180903192860017646178690540921663741884,2815436847160180812083887184036153397126010327731206887846⟩
def polyval3Tail73 : Box := ⟨28843750000000000000000000000000000000000000000000000000000,2⟩
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
def resval4 : Box := ⟨122852031991062987048856869611111346993668803717956271116,8357913544855043422631644669118778871648030455218561224⟩
def polyval4 : Box := ⟨4757595602282676241928371492641954090311845299614166534877,2014308527902557112346271281268812841118655232454039046318⟩
theorem cell4_lo : Holds Q cell4 (15/16:ℝ) := by norm_num [Holds,Q,cell4]
theorem cell4_hi : Holds Q cell4 (31/32:ℝ) := by norm_num [Holds,Q,cell4]
def resval4Tail4 : Box := ⟨-3678131011171934191961046400126491411406052028185639163,9097090436647163357397268968848465544706420487055445540⟩
def resval4Tail8 : Box := ⟨-4456928254131765097194426003111214777329438455443305520,10048275327732741324113888955003506027305301771344805642⟩
def resval4Tail12 : Box := ⟨-5400527722197853562459944004178144056394558636235069052,11068841528496808611024731590008793344607556389057565989⟩
def resval4Tail16 : Box := ⟨-6543901530389899603754443004437012890720874219620183642,12155603225240543065822883987799506238535084410098400410⟩
def resval4Tail20 : Box := ⟨-7929344953338873510304186749349520051627533936743874394,13302280422413253857016867896846191105365081322394200347⟩
def resval4Tail24 : Box := ⟨-9608107808018032973218622054557118369466914455933031175,14498515441485403503422113658952708883058511783435445334⟩
def resval4Tail28 : Box := ⟨-11642290276654561566916514119470279766830618316075620411,15728637488357079125451851576464817006937571348371177914⟩
def resval4Tail32 : Box := ⟨-14107140093991642459318027920497587071260868697780368614,16970115271208332584124256096328365139012458479099575211⟩
def resval4Tail36 : Box := ⟨-17093836084002270988023158284257201309158944601561886581,18191624800828641391137340022053733071115970941234230248⟩
def resval4Tail40 : Box := ⟨-20712861013635809110817159485490759799924622272528053630,19350643154404179994623664629560855778826466183555181705⟩
def resval4Tail44 : Box := ⟨-25098088530970918614885455200098417435036596975600357062,20390459045648020872687628110204448662279699560942071070⟩
def resval4Tail48 : Box := ⟨-30411735370297968253000517464535225646517462564902645122,21236466742811296259940133066250998088005382136360244571⟩
def resval4Tail52 : Box := ⟨-36850362014292161092370413306029593442381211134667967681,21791580268509918764678675999059193065210044816934256917⟩
def resval4Tail56 : Box := ⟨-44652143787580258139040573299016705319019900642389852640,21930568756185859342703329129527171881395385977723817803⟩
def resval4Tail60 : Box := ⟨-54105681351324012534524630778322525199305437346794808876,21493069936712446979574326077499009792868550769831377054⟩
def resval4Tail64 : Box := ⟨-65560676491515003786092189446724533632432041950801655179,20274985296300898460233960752284274067729604567489216447⟩
def resval4Tail68 : Box := ⟨-79440483225080715544699328118432725299243352425028997967,18017892683840904760449953199257158363930967909838031315⟩
def resval4Tail72 : Box := ⟨916562839266580575150404216306506781160598760002799821207,711022826685816226025737679087396994019110901361487101⟩
def resval4Tail76 : Box := ⟨-50119926601779562409973971499294870768020534397653540,127027014951929453695597170619529643553456446962341847⟩
def resval4Tail80 : Box := ⟨-60691716347629175488377886282776426171150402661278136,140405862460396190377745411819705644875481124018187911⟩
def resval4Tail84 : Box := ⟨-73541073010437941365171193989560083747033293445048016,154787349256199386902466271940036309704828033324686905⟩
def resval4Tail88 : Box := ⟨-89110836008430934779836914731029905298635633939631517,170135790441336529372535551273637402748548487892428931⟩
def resval4Tail92 : Box := ⟨-107976954498753231094990105861176575807855218543221332,186374544358541916081900342297904786566874299000313763⟩
def resval4Tail96 : Box := ⟨-130837317043273439648045772623917430056161419728892218,203372643819324251690964881025595285439108233032404814⟩
def resval4Tail100 : Box := ⟨-158537565821785749850852291998121959412972584975739385,220928135468665940773818696904379785286321789107666849⟩
def resval4Tail104 : Box := ⟨-192102378317526326484210599782876757535858374495745455,238747193263776829449136019584457449360122921655747696⟩
def resval4Tail108 : Box := ⟨-232773371812290475164484411502624775804189574695478228,256418016765160972093968881692886595034131036325583311⟩
def resval4Tail112 : Box := ⟨-282055032839327618783278831366564189319115168519806883,273378302698239722684194640603889428091589537089464610⟩
def resval4Tail116 : Box := ⟨-341770370599553523356397882245095579778481526182029698,288874807197854670568743350387329899222581560553325468⟩
def resval4Tail120 : Box := ⟨-414128353051920715253259223806052752338225116989494079,301913185748057947421820904256041383645695707549430098⟩
def resval4Tail124 : Box := ⟨-501805620249166022125468963460305175871321305166500761,311195895242876314108575999979490513367925327221091208⟩
def resval4Tail128 : Box := ⟨-608045497628799620748150937688770334277392555856140769,315045452234369766316153993968860588723646686810840685⟩
def resval4Tail132 : Box := ⟨-736777971922889710707070167062914477338271103740865307,311309744375690817226739275298138607497606956421881177⟩
def resval4Tail136 : Box := ⟨-892765067858680641568452530540578262607756951236966828,297245365325521900852949474691695981389020613455921350⟩
def resval4Tail140 : Box := ⟨-1081777602413697561344898355267984258121245178032603471,269374034747111301519416127987509181547196423174854755⟩
def resval4Tail144 : Box := ⟨-1531723997271778046160117915343154962314015714997809489,217203719212016898004414064130402433329222308221724006⟩
def resval4Tail148 : Box := ⟨25712194929614888117797770824733480092469728652,54614830698592541106094402659577807374609103503⟩
def resval4Tail152 : Box := ⟨31051503594255772695525186388814137271852329472,60054331000742960916963058810786898786936855951⟩
def resval4Tail156 : Box := ⟨37625576959816057960486869547799671661222953587,65816997626550615356324516238837695758796034416⟩
def resval4Tail160 : Box := ⟨45591483519893840678619870732112558933931124129,71858364495376286132131350311915309108299118744⟩
def resval4Tail164 : Box := ⟨55243893583183796052202718650283634461148436639,78109968248283877873108243630266652586685982893⟩
def resval4Tail168 : Box := ⟨66939865575958037038205305621100184686825761661,84471590171981685537744364148356900187023235052⟩
def resval4Tail172 : Box := ⟨81112052621347622872457766473006218768807082209,90802195806518816969453311984741241255299899454⟩
def resval4Tail176 : Box := ⟨98284707085088964974543189992988067092484957231,96908639855043939437234904966789198230272234300⟩
def resval4Tail180 : Box := ⟨119093073527513998216450896467039242664463667065,102531620400503665026096782671023671881155914034⟩
def resval4Tail184 : Box := ⟨144306887438255595387728263169071166467970815085,107328251405652717744310545157605824089444238710⟩
def resval4Tail188 : Box := ⟨174858849010276861263511156248465989422283855634,110850482286347691238238523876801540798226225576⟩
def resval4Tail192 : Box := ⟨211879125244671025852987861885641105975640200373,112518422589855083208657523794200425326201063284⟩
def resval4Tail196 : Box := ⟨256737156675488231478128561807159352025054750951,111587421886489297326104531661267859234036547117⟩
def resval4Tail200 : Box := ⟨311092315213680988660311515401318410300568859792,107107501888695839786584111042780000587835527179⟩
def resval4Tail204 : Box := ⟨376955287026625215762734118123996255894778511124,97873429827612095595036565560115229638509971499⟩
def resval4Tail208 : Box := ⟨456762451106383978234484381266613680425537421739,82363347445298030269690665557202994476340984642⟩
def resval4Tail212 : Box := ⟨553466005237211719729289432398310016334985633697,58663414265987250810903411853695554816933717852⟩
def resval4Tail216 : Box := ⟨670658520129210052432192420046244055390884888466,24374759188639840651680917008862001931762706745⟩
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
def polyval4Tail5 : Box := ⟨1096408258620030353008298699557771931968511527839868457239,2216733599014603073401906716405567572892447604397120852924⟩
def polyval4Tail9 : Box := ⟨1328531868136573842315465708081906268012063269337706885018,2433243669015409278465885632905722511280050319571159875556⟩
def polyval4Tail13 : Box := ⟨1609802258371450314041406999301600860278058227708006393418,2661359464434878200799571937610660065255437540363127307401⟩
def polyval4Tail17 : Box := ⟨1950621865871676017203734579455758386719929067681428827969,2898902589612469797393863984875095105494663772960302843544⟩
def polyval4Tail21 : Box := ⟨2363598164824522084351778752128235614889820674387697597142,3142605760623565150700764619678941275188451267435209948697⟩
def polyval4Tail25 : Box := ⟨2864007823610325221168235488878485269536368439519578966859,3387797265099789125846575167757727194187549705687909138222⟩
def polyval4Tail29 : Box := ⟨3470361813514998912753629698104070681944574993730647812641,3628007116589781445497930475186264308660884090870220109824⟩
def polyval4Tail33 : Box := ⟨4205090159817150579632484251166247417678703541766402224489,3854476757722948853848889056516844089170685659602746550674⟩
def polyval4Tail37 : Box := ⟨5095371665088950232705956612842558591708147297527711712904,4055550122424844584691564669243873531872272676500166244234⟩
def polyval4Tail41 : Box := ⟨6174139297531798701672603526674947621945196678001835714797,4215918929908687128587134562400033902160867961241892510397⟩
def polyval4Tail45 : Box := ⟨7481298435304814903379641591466074147733033083094289261444,4315689067845232437133693220511005527801021578026259529096⟩
def polyval4Tail49 : Box := ⟨9065203031695287088418744560328281287253818292132840553914,4329227596415025552244733649434889714767943327965553092998⟩
def polyval4Tail53 : Box := ⟨10984444306893794151031034584652146229898074447013160551486,4223740986457845053437778733346245828391041744328175298421⟩
def polyval4Tail57 : Box := ⟨13310018133006689588040981488591407552381302466328775896127,3957524350771685328367030583227959886565218752703023521567⟩
def polyval4Tail61 : Box := ⟨16127951287420568808249008269480815006584968400595514037749,3477808221535293450603636265477948670644477161401729631794⟩
def polyval4Tail65 : Box := ⟨19542483723962187035435638042467207646855365717656448701790,2718113363593947450085615927090000705158303394664308335362⟩
def polyval4Tail69 : Box := ⟨23679924899615052425161563531596331416296419322046178089479,1595004567552093709769232304099767793596049759628621673024⟩
def polyval4Tail73 : Box := ⟨28843750000000000000000000000000000000000000000000000000000,2⟩
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
def resval5 : Box := ⟨112795059000391727050398133167373591708114108178938407875,12768252872424799313032124042876484761245287282608213739⟩
def polyval5 : Box := ⟨9054401554632399309125548175745507444393467578487736073119,4033764879086799782706129489172499783512228109782899660599⟩
theorem cell5_lo : Holds Q cell5 (31/32:ℝ) := by norm_num [Holds,Q,cell5]
theorem cell5_hi : Holds Q cell5 (63/64:ℝ) := by norm_num [Holds,Q,cell5]
def resval5Tail4 : Box := ⟨-14378215021052635020135831938265719100160882263316051461,13001870955910260397232543350537952044312871722388288050⟩
def resval5Tail8 : Box := ⟨-15809087970014393589982930632751034851604856359601442665,13351317326733564779376198285554904000567774358539119329⟩
def resval5Tail12 : Box := ⟨-17382276056813827313317823324053856728022370638505634430,13674134128560534853674787230356672037993138567377152840⟩
def resval5Tail16 : Box := ⟨-19112014641687892564996388104634691025133268220965420229,13963678357536577568945438165445235866522900647489234300⟩
def resval5Tail20 : Box := ⟨-21013882328761036068364958002967920696210025988032278951,14212386929296372897721716515941983755515985233887471714⟩
def resval5Tail24 : Box := ⟨-23105007965189368841875661617980291277025151739127002932,14411667675446629546069548660579337041904074813452465762⟩
def resval5Tail28 : Box := ⟨-25404224917582808498307928052074253051189237912531303800,14551778961617331881475108746357502036216060893199357754⟩
def resval5Tail32 : Box := ⟨-27932240691519093216957461551209049845327791605004030947,14621696157444010443646549242997297680312454113707432709⟩
def resval5Tail36 : Box := ⟨-30711823430163182061407935418365252547297088447127742384,14608963573969778475124235707569296720406320274978331639⟩
def resval5Tail40 : Box := ⟨-33768006971667816165468726639500795261660893043803610382,14499530341370130899618672272691159842352066430216776866⟩
def resval5Tail44 : Box := ⟨-37128316312169796864065801484934978514108256876963894704,14277568542677317534167080116569472234566821797080358584⟩
def resval5Tail48 : Box := ⟨-40823015504976026689341328605422083039329467602283631545,13925271745966744317253276462377184429271375519660096410⟩
def resval5Tail52 : Box := ⟨-44885380228601077183334814428761102719497161685933664344,13422631886652243348387464832578570233445721369863252039⟩
def resval5Tail56 : Box := ⟨-49351997478493811590558609066518246313773701760314720379,12747192241344959873302873356957418830975272559683967377⟩
def resval5Tail60 : Box := ⟨-54263095081561990518022159632884216952743044055530646875,11873774003208124708064686599377757222362358644190839487⟩
def resval5Tail64 : Box := ⟨-59662903979772592821112580601259809659674607699039194082,10774173713208545495504769493453532840690394286491325572⟩
def resval5Tail68 : Box := ⟨-65599680330084159787679233283306526832207191720959741460,9416822895178902715841316484112933627825591980916767069⟩
def resval5Tail72 : Box := ⟨916631763599583556246696666027606703963993131209622830963,703716128161719626575484825819503916138523673674407719⟩
def resval5Tail76 : Box := ⟨-200225284229053844268240491455991010881213354563889102,184301091859724031699146753114325040324836444071980034⟩
def resval5Tail80 : Box := ⟨-220114361513671915416594339586501136151485884135932637,189379158834362491456666896381648868627504064992272335⟩
def resval5Tail84 : Box := ⟨-242018297918120942168414744584210946247050353450223223,194100423543624138915248978224971625422119721808876936⟩
def resval5Tail88 : Box := ⟨-266101932694350216076859783450457133616635525248903117,198373158152967231063699059086128585037996095798808253⟩
def resval5Tail92 : Box := ⟨-292582169171101233177149350061126153722061982438683878,202093017656633265762195391843088591857107159570732862⟩
def resval5Tail96 : Box := ⟨-321697497083550487526105120604364572492213821158209689,205141391126053785756977191909257783266179538145071712⟩
def resval5Tail100 : Box := ⟨-353710138669799608210426554202107966417835329402469217,207383729631682516406184598047170893637068565219424317⟩
def resval5Tail104 : Box := ⟨-388908410329706050521745244860786625201712840935380905,208667691380284771115520162044327283101746527467397815⟩
def resval5Tail108 : Box := ⟨-427609319297391632446548838934308520248381284190303352,208821084791495870825797854412645754850967056256894923⟩
def resval5Tail112 : Box := ⟨-470161418712862402423606316286505892714078428553997757,207649588269669252551812496520340220528680732975374036⟩
def resval5Tail116 : Box := ⟨-516947946806452846858972037164592855239944820568559619,204934223239130443967023795486867098005973991448300619⟩
def resval5Tail120 : Box := ⟨-568390278468624030694125734938448302470222288623097192,200428554600503780848653686855094838191940994182102714⟩
def resval5Tail124 : Box := ⟨-624951720291090737550513792856290206547179484527403581,193855590110344287727601168553821653108992482780467406⟩
def resval5Tail128 : Box := ⟨-687141683258668937769112973076208424303170269710656325,184904347261175979101992239797069234269010182545864035⟩
def resval5Tail132 : Box := ⟨-755520270672546021357453723533623684776465350815913374,173226053017014265795364022570285934097030467019456296⟩
def resval5Tail136 : Box := ⟨-830703322690939996391055309132467665864972015147779536,158429938207879495326637562062125047156560636726427672⟩
def resval5Tail140 : Box := ⟨-913368548646342547306513064927459344263214859515521783,140078565064419510157374606098478111724479215324786547⟩
def resval5Tail144 : Box := ⟨-1220004003656173625892307871010752729443042580184255797,113428425718671967540730510853081786983512768103213474⟩
def resval5Tail148 : Box := ⟨140512261034696635585754320296939929226481707310,105597625506078463655581939251080265827068499305⟩
def resval5Tail152 : Box := ⟨154400260963391439414098026065084058912954576578,107619442249676388488925921873700249481251483996⟩
def resval5Tail156 : Box := ⟨169764880508217632058142754143243746752994807127,109291300106675766308344485823547709972938075495⟩
def resval5Tail160 : Box := ⟨186658460106208239940793045117251471374724041989,110541908656342543906845311060186613650516173889⟩
def resval5Tail164 : Box := ⟨205233147309537527092318273475672078717808991533,111291141807216508787183705386980169622359001555⟩
def resval5Tail168 : Box := ⟨225656231871901194153583581416178112395942419068,111448415804064712537373725652871969990391830772⟩
def resval5Tail172 : Box := ⟨248111650823272573350390780351303198277697825536,110911487027673545464915999530055279633410849455⟩
def resval5Tail176 : Box := ⟨272801645066886957619775371612766908270353245129,109565119678045683271889410990168840809223633690⟩
def resval5Tail180 : Box := ⟨299948580827463479168567611488445946960667169376,107279609691570994520116720393280299985060427693⟩
def resval5Tail184 : Box := ⟨329796952354705474985719542478244965210648111411,103909149858522468416062653697102508262186045151⟩
def resval5Tail188 : Box := ⟨362615583919086132935017562302166426149867700706,99290019563929108687927714937190417479863736271⟩
def resval5Tail192 : Box := ⟨398700050931819123501198025606570511801354745283,93238580874918609173069128733550648740382669360⟩
def resval5Tail196 : Box := ⟨438375341994418550126689849631175684220498843492,85549060825223369710798797275967992687159374436⟩
def resval5Tail200 : Box := ⟨481998785853143832402671196863147930536463973353,75991097685331350847883059769701497436892967819⟩
def resval5Tail204 : Box := ⟨529963269619446057370618901843213827054926162589,64307026735623063577980093130573810416228219135⟩
def resval5Tail208 : Box := ⟨582700777240879970704255422080117622334048573821,50208878558729841686319681358146202663549849111⟩
def resval5Tail212 : Box := ⟨640686280409759764878509847770506835091994772372,33375060100134992530885791241510026070646132876⟩
def resval5Tail216 : Box := ⟨704457012578497695068811910199242225955326917294,13446203878014486463270634052032091764743006674⟩
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
def polyval5Tail5 : Box := ⟨5720547263353080853850467358426226653244594193684394367152,4114960184569873860951262917049814757369718949713034343024⟩
def polyval5Tail9 : Box := ⟨6289805801406774384184888500703057847008335297255291976404,4185202400131911817285479437207595571264167169805606174334⟩
def polyval5Tail13 : Box := ⟨6915714614854090366216560181041737350488609228026125043114,4240376941216146346582229765768000236003040509729477609442⟩
def polyval5Tail17 : Box := ⟨7603908633412293007924973579427317302696870329722169916476,4277550208005733921814740584645551873273915617276657453203⟩
def polyval5Tail21 : Box := ⟨8360585958983129220960610608679627601002069664871535145567,4293403432444931368737865442192133536093800595553918409006⟩
def polyval5Tail25 : Box := ⟨9192561476922710370675686366517163140238610402527871369125,4284188277088432095548855093614008746272585890598656711953⟩
def polyval5Tail29 : Box := ⟨10107328232922239938705097982216603574165730819624734430886,4245677630609816260623288854863931731382617516555913395143⟩
def polyval5Tail33 : Box := ⟨11113124917846653708213376091209657985223700767528683279118,4173111087038004470008863622893671410817047929293436171030⟩
def polyval5Tail37 : Box := ⟨12219010068099600491468745038172451991684190301153026604449,4061134552389650090827146621661133183754440926106281326667⟩
def polyval5Tail41 : Box := ⟨13434943649787524347271016991891130532278181719708677194703,3903733365231187544246166867730054387198069726647651044597⟩
def polyval5Tail45 : Box := ⟨14771876761456715371616001179623669736962160992048756628660,3694158254766848785363132279099242659321010846942114313930⟩
def polyval5Tail49 : Box := ⟨16241850263295740375325944094301538087795899053757659242304,3424843390725636313988098518962335388215078102302763774029⟩
def polyval5Tail53 : Box := ⟨17858103221090353689238588146208033518445853403758992520222,3087315702967536466917169865485220259930588250068293883333⟩
def polyval5Tail57 : Box := ⟨19635192141612883771832100767802477923620971966463434096822,2672094564639154952759823047540293388315399941782920383278⟩
def polyval5Tail61 : Box := ⟨21589122073319343260909884100429217811531361528375602536174,2168580840102429984468822329274644056836409559626584120929⟩
def polyval5Tail65 : Box := ⟨23737490753127987818339541462622903851489225030246375695509,1564934196878486443540578382305882763854871140752664712858⟩
def polyval5Tail69 : Box := ⟨26099647410755817705779797714349861083772339332448676021140,847937458940295319686734229790530687145948762984069395748⟩
def polyval5Tail73 : Box := ⟨28843750000000000000000000000000000000000000000000000000000,2⟩
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
def resval6 : Box := ⟨99931085627316135410741834852639961570474665934268976629,11115662666898762204154238915011342854377651826747074231⟩
def polyval6 : Box := ⟨16132768344488517588876841197265868622008939170850322460553,4037123563145905794451052355641859573725221190222541343755⟩
theorem cell6_lo : Holds Q cell6 (63/64:ℝ) := by norm_num [Holds,Q,cell6]
theorem cell6_hi : Holds Q cell6 (127/128:ℝ) := by norm_num [Holds,Q,cell6]
def resval6Tail4 : Box := ⟨-27185203658595807480461129224628101530524013061095243281,10905968813577357013277549971169331797614865585934823838⟩
def resval6Tail8 : Box := ⟨-28497806446400750847394371100629984215675723050440204901,10807400747882908210246308844071022647316359328747562987⟩
def resval6Tail12 : Box := ⟨-29873713328510300029271676232163031743332637382071893240,10684151627068652157370772564057566576481552684492041918⟩
def resval6Tail16 : Box := ⟨-31316050568654756405022272043524642781906544010976459960,10534394368011606427784889053160256148265000979075630318⟩
def resval6Tail20 : Box := ⟨-32828025509716128435460507183992941066953430036121892800,10356193958317943835893931140158722336622697266936708679⟩
def resval6Tail24 : Box := ⟨-34413000339999950270299035514475214679015134642505007322,10147501080845400636174618867696870452007510881451912530⟩
def resval6Tail28 : Box := ⟨-36074499578122120267387101079588320408402387381718436239,9906145929364115746604906335578792003194157488382934872⟩
def resval6Tail32 : Box := ⟨-37816217910511167976619657721729404282034482370560014796,9629831704542863363174850118397810640622050119811036716⟩
def resval6Tail36 : Box := ⟨-39642028407306006736252652740866397538034657887937021199,9316127774030257528240390828854852594217246153834001236⟩
def resval6Tail40 : Box := ⟨-41555991134926647697405447082742776562402596614389825552,8962462479715442074104233335242609536327375734753590372⟩
def resval6Tail44 : Box := ⟨-43562362184469733676143141463146570753998647338609326874,8566115574414016091806451631379500791116438463453848240⟩
def resval6Tail48 : Box := ⟨-45665603136005393782325659631079792508405453604938511183,8124210269344814505836328749897082828293885756456713179⟩
def resval6Tail52 : Box := ⟨-47870390979821235524476772348386881928786142202444587081,7633704872839807175008016492127225649904768489053099809⟩
def resval6Tail56 : Box := ⟨-50181628516675365401630607964939381557126303255100103466,7091383999760686544963402848117366786232941643204845637⟩
def resval6Tail60 : Box := ⟨-52604455260172154433341587836784723428822355749760471205,6493849330078943568732173854260055861641208290926970751⟩
def resval6Tail64 : Box := ⟨-55144258844290351159288881817519523867211225123951342207,5837509893409884560126955768102195107421422973466554907⟩
def resval6Tail68 : Box := ⟨-57806314938428013370371145940163945379307085002178525441,5118564872484130356191054804224939279192658809648089569⟩
def resval6Tail72 : Box := ⟨916554528840021303848396304906846973029772467557594171765,646291062261549762595075122107433012465262150212099170⟩
def resval6Tail76 : Box := ⟨-381746009268454630768628999053053394642330222354486094,155517021722921747772657081290150126648112423386662151⟩
def resval6Tail80 : Box := ⟨-400143164222315109258937833494516369919917034310858660,154208846650641689358800025310237592113656146201058746⟩
def resval6Tail84 : Box := ⟨-419462534523629625680027702730956345262777863549669427,152556684311153975900774649903941549189478248444321058⟩
def resval6Tail88 : Box := ⟨-439714668153579081633290749400541293437434164503053411,150534814819190534612122950735756911566777540311460760⟩
def resval6Tail92 : Box := ⟨-460944598090231776983963736620236419950324093485169226,148116147910524042132563633879654584307336881714740925⟩
def resval6Tail96 : Box := ⟨-483199533462816902186165166553089818195639758087432404,145271990901250455568517356010139243731714914947976650⟩
def resval6Tail100 : Box := ⟨-506528962712735637659289679107486476624384576529459697,141971961915896366092079037874678725885921428461521815⟩
def resval6Tail104 : Box := ⟨-530984763640264542613177917860255254990449559589237420,138183898646760860934601602255030193966947125527430780⟩
def resval6Tail108 : Box := ⟨-556621318765547214080583045218585206399408509018739201,133873762399425417748409396467013600584171025094324570⟩
def resval6Tail112 : Box := ⟨-583495636259350358253722983643993748955819544243937307,129005537186988056430340519591077365806363544586285641⟩
def resval6Tail116 : Box := ⟨-611667476712495887212583903774398290859506875057349091,123541123623818339920158115154118377523104950094200653⟩
def resval6Tail120 : Box := ⟨-641199486025867007846813719087059428445170616926661380,117440227357274576724475640711409511761691805602969314⟩
def resval6Tail124 : Box := ⟨-672157334716496658448974497121429863263055993569450586,110660241762862434488548268560250875943883280813893861⟩
def resval6Tail128 : Box := ⟨-704609863949514411293171235833075610357440720572423692,103156124614715546587393701109831896655622661575648040⟩
def resval6Tail132 : Box := ⟨-738629238620747941383107348032310075707014292542682262,94880268429009371377168060324055301649869465389233485⟩
def resval6Tail136 : Box := ⟨-774291107895330330718277786359009259180125879373186207,85782364160464919817882059971916849410669522185991628⟩
def resval6Tail140 : Box := ⟨-811675352847319272242890211439207083720430811066749316,75809240826208116919712811953705700360131398452637700⟩
def resval6Tail144 : Box := ⟨-1064111968813411342845815682182279080587905576310637860,61523040835785821589944597430680086436323898449897862⟩
def resval6Tail148 : Box := ⟨323833942278764808705595373056534854156993000271,104188266413780775546083528301134686941532169954⟩
def resval6Tail152 : Box := ⟨339378862897090077321134546579550503145457336269,102195110565657575772458187191181624095849814271⟩
def resval6Tail156 : Box := ⟨355764463081031288071805370439937307404428124083,99882480236608550403410256098209480649099358164⟩
def resval6Tail160 : Box := ⟨372941180557013916630169658817675589575111217769,97227240111444114258293905091002761343596055292⟩
def resval6Tail164 : Box := ⟨390947209709885732317711714035302965769499944202,94205488088479038815439007397513562518885296015⟩
def resval6Tail168 : Box := ⟨409822590660727987809479950136259973332424841050,90791933484454159469820577034290570228512983913⟩
def resval6Tail172 : Box := ⟨429609296714270963039282848933362765082648301860,86959822497894471765361917367410085608599980345⟩
def resval6Tail176 : Box := ⟨450351327694675838103231763399227599250421487213,82680859853773369570874355915855058943068168198⟩
def resval6Tail180 : Box := ⟨472094807788222737922629913044648352542848609719,77925126419245657148314802939098262928046323658⟩
def resval6Tail184 : Box := ⟨494888088109957262126083507240949734612950408796,72660992588083245409929863484807344090052402249⟩
def resval6Tail188 : Box := ⟨518781854222372687364001335830135279870947823260,66855027221436497031139879215156897350306696854⟩
def resval6Tail192 : Box := ⟨543829238845217814058071391050100750494910680387,60471901922032727885091300740507203896210684290⟩
def resval6Tail196 : Box := ⟨570085940007063974443830239920505077944046609979,53474290407896174994509452037047289465227846869⟩
def resval6Tail200 : Box := ⟨597610344901365595059244116103531788614205723981,45822762740105664079775700655038643317280205556⟩
def resval6Tail204 : Box := ⟨626463659722434051486895387478151473128852867968,37475674146970855182136477236691831042875932415⟩
def resval6Tail208 : Box := ⟨656710045770151064826550264809557108446567858761,28389048174272527544247394736632948655555220774⟩
def resval6Tail212 : Box := ⟨688416762441318677625182126580803904816425616331,18516453866101150264788469394193127415020827625⟩
def resval6Tail216 : Box := ⟨721669143396716981442684317832856417134432479409,7808455729463095947307897027164781260876294142⟩
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
def polyval6Tail5 : Box := ⟨12874731857676355263186480037072653386814508018768908656049,3962454391234969240723320860070722768614707162125581688913⟩
def polyval6Tail9 : Box := ⟨13496336403575059512799837454620317075239467284062978987402,3877449023780842142480438944942489923607081125068338154474⟩
def polyval6Tail13 : Box := ⟨14147955048342564710675604014677962154247210965265221660698,3779533273732760788561532164202711350036773412950020181268⟩
def polyval6Tail17 : Box := ⟨14831034591002440216228904588861840439102449107258378866979,3667803148541520576349739563478649857291950875921870812654⟩
def polyval6Tail21 : Box := ⟨15547093999657713403779882526811840341230989803504669470846,3541302074911019175511467141188203509118952095904464707097⟩
def polyval6Tail25 : Box := ⟨16297725580171773523490112685029614326406836099905425728818,3399018065550560349432182805293028595955890464502890280130⟩
def polyval6Tail29 : Box := ⟨17084598516766747605762900137612958255228411838726482289426,3239880749575614382335212822006986911276035843890203983396⟩
def polyval6Tail33 : Box := ⟨17909462583798897219149793079570749650623942424389369263189,3062758250160766752501123594109181631385420954030734773094⟩
def polyval6Tail37 : Box := ⟨18774152036742988305271230867860441514344952028487797262642,2866453901768974675491652826137250058076036637651103280005⟩
def polyval6Tail41 : Box := ⟨19680589691037862435757347959020740520253929326502280204228,2649702798903403524037224912908467317447498826092497443385⟩
def polyval6Tail45 : Box := ⟨20630791197863363729838989693416915409665060336283263738527,2411168167929449742482541394879321499066139362350885042081⟩
def polyval6Tail49 : Box := ⟨21626869526356693786753857940812579046704480097922023962289,2149437553096327449965161195226397790809624204475932551214⟩
def polyval6Tail53 : Box := ⟨22671039662235327665323550535781897214565646435393266909172,1863018807448850787099677517547535764197608927181469549814⟩
def polyval6Tail57 : Box := ⟨23765623533274848745616121564001937172075289104357762704345,1550335878859782390899226618642898565338312841554947213802⟩
def polyval6Tail61 : Box := ⟨24913055172594555451503068803404174146859620199747517979616,1209724380930288978051239714949483970396987690713316803184⟩
def polyval6Tail65 : Box := ⟨26115886131269725925881309770754643662139174651913557548567,839426937998187670467669560334394622490530543637617802968⟩
def polyval6Tail69 : Box := ⟨27376791462113534896879326445815531414574196361798977671254,437588284584538423005974570343754252157346318621496457003⟩
def polyval6Tail73 : Box := ⟨28843750000000000000000000000000000000000000000000000000000,2⟩
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
def resval7 : Box := ⟨85768840615466831105224582742118514680307865685623882733,17606173550472253222618881906756096954805209368272308983⟩
def polyval7 : Box := ⟨25502364665435546433105676863661576520948996356888201993787,7051904420015257632135063249013783596714407705511521150501⟩
theorem cell7_lo : Holds Q cell7 (127/128:ℝ) := by norm_num [Holds,Q,cell7]
theorem cell7_hi : Holds Q cell7 (1/1:ℝ) := by norm_num [Holds,Q,cell7]
def resval7Tail4 : Box := ⟨-40722771161760469472886475948783140139215117809789491911,16839482260359786576638334838553778844374876987025202000⟩
def resval7Tail8 : Box := ⟨-41365394821926534452410448815540845140224219329080236333,16196924731943497734519233446501793944292168902912104186⟩
def resval7Tail12 : Box := ⟨-42018090633484903634244067031927818600516790835380695136,15544228928659672956441763264327505477059991316320351439⟩
def resval7Tail16 : Box := ⟨-42681085185487451303029096968697482182566500774524215216,14881234376664872227191577864121624895739890146329695580⟩
def resval7Tail20 : Box := ⟨-43354540988085075187370818060862382876985979082652484103,14207778574067279856240981476890435439353782208142922612⟩
def resval7Tail24 : Box := ⟨-44038623107143022181788108209933692637310814195694236580,13523696455009333286274338751544593268360730187180022929⟩
def resval7Tail28 : Box := ⟨-44733499213057926134172885099363078555433318328492302589,12828820349094429349576904556541114091510916244909022109⟩
def resval7Tail32 : Box := ⟨-45439339621862062376282661769208780502363468621438176349,12122979940290293108762834248463662011254090301833271333⟩
def resval7Tail36 : Box := ⟨-46156317336968303417465918965693533655266010085738178635,11406002225184052067684842314651668295839448774391640214⟩
def resval7Tail40 : Box := ⟨-46884608091573728547788827627744648693218998889057932736,10677711470578626937059023214246614897380427488989281332⟩
def resval7Tail44 : Box := ⟨-47624390391732310635852135158494435720247617349208607031,9937929170420044847102452783127497035629821848313254760⟩
def resval7Tail48 : Box := ⟨-48375845560107237703472155348848491695053660716291515168,9186474002045117758208820859355673286956980084347815910⟩
def resval7Tail52 : Box := ⟨-49139157780413592652218178746218064923438173947169237572,8423161781738762221286557766838857939241541548467654117⟩
def resval7Tail56 : Box := ⟨-49914514142562242034767543203442318131165318711801051198,7647805419590065161739661527855339379878914680079699950⟩
def resval7Tail60 : Box := ⟨-50702104688502693452616601859633610571119747746964990402,6860214873635502363511641888567076696969296181761805924⟩
def resval7Tail64 : Box := ⟨-51502122437709235332931627723301327781608476764078269761,6060197102682447875842381586464497494190243200611587727⟩
def resval7Tail68 : Box := ⟨-52314394112848050885742727096906273166654689250980627207,5247549084690656265860948351295768377123822068356992409⟩
def resval7Tail72 : Box := ⟨916423812766142311540270463709578923290364990255457943820,737060564594089409741273987371622439919817260030029539⟩
def resval7Tail76 : Box := ⟨-573671740911456179925008106650546477334035554493880608,239844655628531830934707629145207479487073704772573319⟩
def resval7Tail80 : Box := ⟨-582690673025285211998428384945129041270870281458563060,230793172273029069147889749636828134175940259612388980⟩
def resval7Tail84 : Box := ⟨-591884823882022174403717264853385878417364380466147724,221599019576422170033921513211855137090130628861685524⟩
def resval7Tail88 : Box := ⟨-601224049146190845458913820094345962937314520180740093,212259794311166561058350868893440765827467989817091964⟩
def resval7Tail92 : Box := ⟨-610710636068686992893364622994785132791762237354076641,202773207388667293183521295727335336451256205353428946⟩
def resval7Tail96 : Box := ⟨-620346909836823712940087048480294148810751994801081100,193136933620530541314675526375997859473458429967198906⟩
def resval7Tail100 : Box := ⟨-630135232327629240219999770187314909285681129043119140,183348611129725013083373286438384628946037127512658032⟩
def resval7Tail104 : Box := ⟨-640078002685692157540697757569386760150472514449049917,173405840771662095691163749485007577110360309009870601⟩
def resval7Tail108 : Box := ⟨-650177657911195361964685895132168364316877356977008274,163306185546158891256450810161453979530191292287458957⟩
def resval7Tail112 : Box := ⟨-660436673457231441174079221022510574062245967911261409,153047170000122812047213313858897371762488025063596950⟩
def resval7Tail116 : Box := ⟨-670857563836542989842513361836277069893895239740355964,142626279620811263396809727928637226662387935658949195⟩
def resval7Tail120 : Box := ⟨-681442883237836553744262409259298725531882802435689115,132040960219517699690693648943057648843212799424352640⟩
def resval7Tail124 : Box := ⟨-692195226151821265122854695151334923347114182420217696,121288617305532992816864425981237499923955922589477890⟩
def resval7Tail128 : Box := ⟨-703117228007125894413461605613255275328470159711066845,110366615450228650905339861763828092523846168038532382⟩
def resval7Tail132 : Box := ⟨-714211565816313705193628087862763102901873824304818567,99272277641102857980188289996492275577861574442138251⟩
def resval7Tail136 : Box := ⟨-725480958896650347872214085390486105819004627073446034,88002884623163689731324743408347118781464487154490555⟩
def resval7Tail140 : Box := ⟨-736928744739549088228154309040858759153589455875097486,76555657293635059362115248421660056853276255582643015⟩
def resval7Tail144 : Box := ⟨-960172002749796400727524910788970743237187870737749968,61579332040428510656385923455640090866752229062862572⟩
def resval7Tail148 : Box := ⟨561992129909860953998324470162859903299469585801,179225034514870002049353671357815344093205814672⟩
def resval7Tail152 : Box := ⟨570772352058670938255831429264225687507030137890,170358285139405535729122800599086819345011117292⟩
def resval7Tail156 : Box := ⟨579778446486946425923817357170099543415116870484,161352189102693079213369764013649559091519678800⟩
def resval7Tail160 : Box := ⟨588926647787076552158824588098262754814863197200,152203987802027854296642967462818876946864392283⟩
def resval7Tail164 : Box := ⟨598219196618317881616457279882989117052499725729,142911438970785548344499217207112060104240885792⟩
def resval7Tail168 : Box := ⟨607658370609256178653233085401381943051835752074,133472264979847244581651082810394111850480195897⟩
def resval7Tail172 : Box := ⟨617246483327227766122476761241876996714372046532,123884152261875656970954631640476117614509863850⟩
def resval7Tail176 : Box := ⟨626985884844858864488042551694876356947331940896,114144750744244558597588715580129370612250845050⟩
def resval7Tail180 : Box := ⟨636878962316073886161457094147836303095883210260,104251673273029536923219845827812960380347010250⟩
def resval7Tail184 : Box := ⟨646928140561193379160869903374345173723505993458,94202495027910043923657670295898005567175253305⟩
def resval7Tail188 : Box := ⟨657135882661264113271317664256377940360761190441,83994752927839309813513946722164676049030898718⟩
def resval7Tail192 : Box := ⟨667504690561766974854649069545697561981807663292,73625945027336448233128789001330321255911001841⟩
def resval7Tail196 : Box := ⟨678037105685850640700028977991269224394935689522,63093529903252782434518459896003481950117065590⟩
def resval7Tail200 : Box := ⟨688735709557241337910196760571564817677436702895,52394926031862087077905477482418271173858764419⟩
def resval7Tail204 : Box := ⟨699603124432981593090348896038168999878497138706,41527511156122055024061494033920037905208532942⟩
def resval7Tail208 : Box := ⟨710642013946261501619343575411819136828429276390,30488621642946795408405605560951500018218143721⟩
def resval7Tail212 : Box := ⟨721855084072511481315301819296200118738896103973,19275551818680989615873178559169745096027599774⟩
def resval7Tail216 : Box := ⟨733259799403877513515222089939330623498471227469,7885136180510224052889666720147275857717483649⟩
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
def polyval7Tail5 : Box := ⟨21993375913671102123215467865014547570474869765473747892401,6708545630673412826177341010423209398159017379560863070954⟩
def polyval7Tail9 : Box := ⟨22340402490069215036048756626975949127153963378370493160328,6361516836431479687463004744796408161239612113980492643106⟩
def polyval7Tail13 : Box := ⟨22692906968675077822882445581860409525821877520093382606321,6009012357600610060136334028765647170106987038522856712779⟩
def polyval7Tail17 : Box := ⟨23050973541008859717473033693999369253212238379831687103466,5650945785266643346184475372372308792020610558079709788597⟩
def polyval7Tail21 : Box := ⟨23414689969943388706762738869609092251053032483006651822919,5287229356332113684956945624150540516161754957512869720251⟩
def polyval7Tail25 : Box := ⟨23784145403369053468283323880487654643225478611773691365262,4917773922906448915226034179421324888139235785120523673376⟩
def polyval7Tail29 : Box := ⟨24159430395822105002019216293154354158806923462393199186112,4542488930453397381207296156085472397795620122634866075515⟩
def polyval7Tail33 : Box := ⟨24540636930679641540278471107022249065326804885604750576016,4161282395595860842924363565656047421933616809613433102137⟩
def polyval7Tail37 : Box := ⟨24927858442704984988558147473455195297181219335470717083742,3774060883570517394640946535890183746479509546980427271731⟩
def polyval7Tail41 : Box := ⟨25321189840948796714724863652171641704742442921131154974686,3380729485326705668474648780254094968573433871942196057434⟩
def polyval7Tail45 : Box := ⟨25720727532011545200290121872643659271343233746148341067264,2981191794263957182918426796368548456872705050972818229716⟩
def polyval7Tail49 : Box := ⟨26126569443673027241651225469070420432063225403582501351007,2575349882602475141657668006901373349284410890195134240322⟩
def polyval7Tail53 : Box := ⟨26538815048894734363438154288765584118245628352288954311032,2163104277380768022281953170567968926974128892386253651027⟩
def polyval7Tail57 : Box := ⟨26957565390200947646241462664947726734984141950941855744698,1744353936074554899405755586452605622991756874160367728316⟩
def polyval7Tail61 : Box := ⟨27382923104444573182455496114496550804668341825175178983066,1318996221830964882221795787731150765960984956168248557580⟩
def polyval7Tail65 : Box := ⟨27814992448000788999811931137603133965267633591689915480665,886926878310608838399900440516295981864822937341018394923⟩
def polyval7Tail69 : Box := ⟨28253879629952365163359616161741819722708376212374822930286,448039995830824130919449283981111772271836381790459303426⟩
def polyval7Tail73 : Box := ⟨28843750000000000000000000000000000000000000000000000000000,2⟩
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
def pend : Box := ⟨1032550679256382891817701018066987489644952953001374219091828,3589829067912247539722045687870472710451061025504052529⟩
def zend : Box := ⟨1003847234432268542552226562500000000000000000000000000000000,1831739794225888085937500000000000000000000000000000002⟩
def betaquot : Box := ⟨428772894688102078038901186720210500326495293357339467933631,394816976556210441085418022876346165138997463295634519⟩
def crit : Box := ⟨226303614907534545807998534338767657787818811570755295791,8690645171901163084913719296439222793496092538015208560⟩
def subsonic : Box := ⟨308097314610085551698060554724060423012136892546502480614,4057590705677992039761834935822506545358310056119591111⟩
def pendTail4 : Box := ⟨28700205468250483026718044217633873091360714716398862883245,1675974626682758125547831465646392855142778695051931649⟩
def pendTail8 : Box := ⟨28700243463657143159776879744187555097768839678432144272786,1675860878795773011313403985577948722065442426534325748⟩
def pendTail12 : Box := ⟨28700243465411409712753925159863607390082536332320891851960,1675860863181778630900292408347407323746709655862894696⟩
def pendTail16 : Box := ⟨28700243465412331953690925802891271332060597933233329681945,1675860863168092648059034590878173362332690296508456100⟩
def pendTail20 : Box := ⟨28700243465412334322491310228240746010540798221728200497079,1675860863168039311511710518491084431937615344693313497⟩
def pendTail24 : Box := ⟨28700243465412334344035056761333217681276441311655564345497,1675860863168038579335654493226444873373635341252155293⟩
def pendTail28 : Box := ⟨28700243465412334344605125548888255163962310968583474113353,1675860863168038548927263052619422510705155217910439151⟩
def pendTail32 : Box := ⟨28700243465412334344642530285367704244834422857208680501455,1675860863168038545444733188662047298456467047984137129⟩
def pendTail36 : Box := ⟨28700243465412334344647250630577729460070398930138739101282,1675860863168038544402104973649589370437229288164127025⟩
def pendTail40 : Box := ⟨28700243465412334344646924185765426767465369168561923759247,1675860863168038543606396052672113774656201113748994539⟩
def pendTail44 : Box := ⟨28700243465412334344640128959292690361511554055995463259093,1675860863168038542061649988741451636883818347787620107⟩
def pendTail48 : Box := ⟨28700243465412334344580519342145220794747768762249492694822,1675860863168038534276185997746047374696545230316256665⟩
def pendTail52 : Box := ⟨28700243465412334343478342529064789358264303965778259044468,1675860863168038428283765899896199685418547267808462439⟩
def pendTail56 : Box := ⟨28700243465412334289313606837011010618144751352767375473559,1675860863168034747817682847232983530840305043169513100⟩
def pendTail60 : Box := ⟨28700243465412325768802381632322941102594938915955515314784,1675860863167616130897703622390036459456656672514497194⟩
def pendTail64 : Box := ⟨28700243465406737587619831248351499541885992354727054391729,1675860862966169783586445404396754125501737470406311753⟩
def pendTail68 : Box := ⟨28700243440498381524810972677490426889687537264470401872213,1675860219442089549512035570617237892830273601701652001⟩
def pendTail72 : Box := ⟨28697458653520836205697530383605158810194217614588902827918,1632327945972616954538287440840676881620253430113596367⟩
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
end SepticProfile.ExteriorCertificates.C45

end
end

end OAI
