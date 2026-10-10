import OAI.MathematicalPhysics.Transonic.Certificates.BarrierData41

namespace OAI

section
noncomputable section
namespace SepticProfile.ExteriorCertificates.C41
open SepticProfile.ExteriorJet SepticProfile.FixedInterval
def cell0 : Box := ⟨250000000000000000000000000000000000000000000000000000000000,250000000000000000000000000000000000000000000000000000000002⟩
def resval0 : Box := ⟨124583845566452682552225151536523604504281675695736157128,305571993701976081668197274046833506374065337149032002⟩
def polyval0 : Box := ⟨3877495464125219664263723431637496957800802094461413342655,14809040902099401971310246100750158751358768451228303921⟩
theorem cell0_lo : Holds Q cell0 (0/1:ℝ) := by norm_num [Holds,Q,cell0]
theorem cell0_hi : Holds Q cell0 (1/2:ℝ) := by norm_num [Holds,Q,cell0]
def resval0Tail4 : Box := ⟨68914085681937083353705067238626212658649697259800,1966602308234765465284765263370556576829165095993⟩
def resval0Tail8 : Box := ⟨8971229771972800416895902122225769833926717658,469302928735922269055644270862331689944095140⟩
def resval0Tail12 : Box := ⟨8775997215374922555036220998951254082620089,699233087991861850858654007575056110586527⟩
def resval0Tail16 : Box := ⟨37761824820780724431818124895395151957209,30456037091296880694681301907129961636712⟩
def resval0Tail20 : Box := ⟨552164665858088463996464809948115680455,418796415533245609817982179371953400509334⟩
def resval0Tail24 : Box := ⟨23544086425868753773179379248175087221,6699353561712859553610955904933574345408203⟩
def resval0Tail28 : Box := ⟨2663436950177896137088137712762642363,107189575615555612647698173601883489086698528⟩
def resval0Tail32 : Box := ⟨752961372122469577728450840088262508,1715033197133408760507894906323110965448593526⟩
def resval0Tail36 : Box := ⟨-73385494256680755221817268523639821,27440531149166023131430685399022047527282429183⟩
def resval0Tail40 : Box := ⟨-151392951854651304912331308171738260570,439048498242069643909270430113736389831670279527⟩
def resval0Tail44 : Box := ⟨-38975879508165630888449199933362020220487,7024775935326538638899647826077950685224897133935⟩
def resval0Tail48 : Box := ⟨-9978701490104282528911471653372127419264440,112396405610144640292671598190864242194672943182901⟩
def resval0Tail52 : Box := ⟨-2554556078339431326483567354794196275766325216,1798340094864980950335481261340939322981114999310453⟩
def resval0Tail56 : Box := ⟨-653966535908391849889922861590265118380379365007,28772828424141105110636760405747355829321266626566364⟩
def resval0Tail60 : Box := ⟨-167415426283827594383105847459351007961182896004104,460208302804133225489150949537845717960607997983118522⟩
def resval0Tail64 : Box := ⟨-42858302848799503603120216109356487753901554033029598,7323153155153281588910663188453209403656341385922971959⟩
def resval0Tail68 : Box := ⟨-10970655142953495197595453824949348624818140808286980985,106884911770106439053934336117846245310669926749209066272⟩
def resval0Tail72 : Box := ⟨892140479906939325113180606675900214796985702340311472739,2654481005505556208772593523120696733146220770882031291⟩
def resval0Tail76 : Box := ⟨-32859901199097285795383020944144329632173012465226,694057397783594928990385888548382917394066771431⟩
def resval0Tail80 : Box := ⟨-1911719833915527852918028214649892275463971505,85936682928024409798374579671825083578331049⟩
def resval0Tail84 : Box := ⟨-1163270179496100744484527974549417162673034,82560230673646768819129038318062393710823⟩
def resval0Tail88 : Box := ⟨-3459982193324233458203251818998576441767,542275515665034163171107122657363935502⟩
def resval0Tail92 : Box := ⟨-37012643789695196520219707488481483616,2983618413215396398346569451363426431847⟩
def resval0Tail96 : Box := ⟨-1195243798019424794502498914123305839,47652813560795696510239517501970881887726⟩
def resval0Tail100 : Box := ⟨-104648882153345511793452674952453458,762441233926985567945540513448307074251345⟩
def resval0Tail104 : Box := ⟨-23278477390871954700282172746657351,12199059286132829466318787465003307764412142⟩
def resval0Tail108 : Box := ⟨-14767126217173443756347039380248790,195184948435216169825328922658368554357448730⟩
def resval0Tail112 : Box := ⟨-550986111337684878637673440602963829,3122959174446064701404364443937334033820697445⟩
def resval0Tail116 : Box := ⟨-136824028214276088106967069322548394670,49967346662929228766714332259763763080992941366⟩
def resval0Tail120 : Box := ⟨-35013580428248365911274330106071101712619,799477513782006150432839704316505749247165913935⟩
def resval0Tail124 : Box := ⟨-8963373683022755286899054851295046165122225,12791631817355724256782732306077542873659100974117⟩
def resval0Tail128 : Box := ⟨-2294621827402744570324355867928275036943464451,204663957870104209410637271042832177298415351392852⟩
def resval0Tail132 : Box := ⟨-587423171746616664374627442425342827605308877959,3274072616778704375190428671327390865941024821051723⟩
def resval0Tail136 : Box := ⟨-150380454631426157071003995778652681671427201040527,52244180275565880225355629371936247925939104225050831⟩
def resval0Tail140 : Box := ⟨-38498961033134060485581488675105188674041797446161452,799814886436128518178472582745065952119661324818435274⟩
def resval0Tail144 : Box := ⟨-10562185719241980522900830017140416696175622772326922459,3214484407301729236458643071461131904583616339974660578⟩
def resval0Tail148 : Box := ⟨84026381686144115479247184188878990779280777,1440108998423911674025555182615003702790377⟩
def resval0Tail152 : Box := ⟨1613162677744220021433527890383626905500,64452761674473433295222370240309489134⟩
def resval0Tail156 : Box := ⟨551647883289801033941252198480138399,35588242522931226910311778645281405⟩
def resval0Tail160 : Box := ⟨1039298189964743797919449244114640,100008993306959729827173606631660⟩
def resval0Tail164 : Box := ⟨7457041039068287685140304179093,39300064210940814237538687854536⟩
def resval0Tail168 : Box := ⟨166737893406856088893415087785,613176800977560071124107936674024⟩
def resval0Tail172 : Box := ⟨10280087590487360311780203565,9810350365554240479042105627403887⟩
def resval0Tail176 : Box := ⟨1620341537220888739984939501,156965565557175947754684129645583441⟩
def resval0Tail180 : Box := ⟨633575875246003622343997469,2511449040142096418355714827933848504⟩
def resval0Tail184 : Box := ⟨2829391679626879683120791111,40183184636741956682763120239284920730⟩
def resval0Tail188 : Box := ⟨577680204362170077343041179717,642930953648095553890904698183179914047⟩
def resval0Tail192 : Box := ⟨147564493890357002151917330758901,10286895120034407054005655020571198955501⟩
def resval0Tail196 : Box := ⟨37774814471690061172067634162152498,164590286506732664930702462129600521325718⟩
def resval0Tail200 : Box := ⟨9670331117336686288466049657632540450,2633435518174695423171228505462488521994535⟩
def resval0Tail204 : Box := ⟨2475604260851798848694768920882155376438,42132647412079903213837295156154007789289288⟩
def resval0Tail208 : Box := ⟨633754814263532130413185471282047803718320,673528213588009598593177825182318815145954213⟩
def resval0Tail212 : Box := ⟨162241965109131327681465071183927594614503888,10624349972847126604723473828078628006730523544⟩
def resval0Tail216 : Box := ⟨41576477830792371577556676031811742078508231411,131031460296236088045804863527089480529147198752⟩
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
def polyval0Tail5 : Box := ⟨2301116838976205506136494741082973169752875650937820,56016154892398081723126462925234605052783894003941⟩
def polyval0Tail9 : Box := ⟨240101251309608996938239242440343345596986893784,11565510493553301437610789872227393659277349635⟩
def polyval0Tail13 : Box := ⟨203227136124394020027735946481042972176344726,15194431834603995707057251475461863325292701⟩
def polyval0Tail17 : Box := ⟨766273561439638711028784146788448263709971,475611423658330701738618819820385595918407⟩
def polyval0Tail21 : Box := ⟨9845482199488472228958393671800172596208,6294339102913236453334034637384881525481993⟩
def polyval0Tail25 : Box := ⟨368468963563832532303499791313883120387,100685928374516978313574371651647602836536475⟩
def polyval0Tail29 : Box := ⟨36455464372024182294614516834183974194,1610973646878423854873377763017791484943615662⟩
def polyval0Tail33 : Box := ⟨9013074892195770524994080352217065019,25775578185674287190668983235254942930387180552⟩
def polyval0Tail37 : Box := ⟨11303827158669981589127585048025186099,412409250912199272771455652700834068619492264965⟩
def polyval0Tail41 : Box := ⟨1530805090861286860458550679127094203513,6598548013174373325062005069350167150602681539368⟩
def polyval0Tail45 : Box := ⟨389959246218499374972172215503047982376521,105576767845234123536801620506824173986251034057558⟩
def polyval0Tail49 : Box := ⟨99823056550271183110483864789862888617210433,1689228191939820149552938913169881394456855116106468⟩
def polyval0Tail53 : Box := ⟨25554649486667366646115862017192928312633856342,27027627113556733277395858996238574594468669808856798⟩
def polyval0Tail57 : Box := ⟨6541989284081333415760828865479516966479182669063,432435900702167582732948762994481856325649494799099442⟩
def polyval0Tail61 : Box := ⟨1674749250116016800652908324267620387652785903369414,6917404333859924907425758972886284763408993697465586641⟩
def polyval0Tail65 : Box := ⟨428735880241072943197350759091028981390173363136205079,110276529503179714643981685917905390041715840346891554504⟩
def polyval0Tail69 : Box := ⟨109757245425638620702663820509236856962775552989878038226,1661527485568716551182978212026185963755093806344122579980⟩
def polyval0Tail73 : Box := ⟨28593750000000000000000000000000000000000000000000000000000,2⟩
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
def resval1 : Box := ⟨124331845353620984971125308306056854723526071574790593833,219376519650684646254799556815248644787270959527856676⟩
def polyval1 : Box := ⟨3858628160023065030942419669927450774299432805902635246124,8374159369933601239077439600230059138927408542082886352⟩
theorem cell1_lo : Holds Q cell1 (1/2:ℝ) := by norm_num [Holds,Q,cell1]
theorem cell1_hi : Holds Q cell1 (3/4:ℝ) := by norm_num [Holds,Q,cell1]
def resval1Tail4 : Box := ⟨66879803675274683666144067354760733233950770938402,3344377488545739127148688046122724977290445999934⟩
def resval1Tail8 : Box := ⟨8458829072799208591831315530008139194132746075,6733696694591558689647216595328253234841194931311⟩
def resval1Tail12 : Box := ⟨-340347694655926328806668489658629929062225641,21280802114679662336168034965242363829160087848094⟩
def resval1Tail16 : Box := ⟨-2283757201478944447784410286135120199744960970,67256660238318719003176366068726802086110381679635⟩
def resval1Tail20 : Box := ⟨-14967054181221008467066658305572516317958295568,212556510366383669915775936558806819152486378057453⟩
def resval1Tail24 : Box := ⟨-98088089440034911045431114051321110467897041094,671732754130046135926848479037770085928960810347235⟩
def resval1Tail28 : Box := ⟨-642830103083512571856994005880763557487996251292,2122674399627693767047889153544170850333884644459179⟩
def resval1Tail32 : Box := ⟨-4212851363581905227946448797106348391269123645171,6706518146304065430164515344481576328826241901260150⟩
def resval1Tail36 : Box := ⟨-27609342696373915542936321771850896793930572398667,21181614551166809020356930774820195009452059574503442⟩
def resval1Tail40 : Box := ⟨-180940588294958070964905917249195014312283601065083,66850680607124484697362006708258486870863173201985432⟩
def resval1Tail44 : Box := ⟨-1185812239449838901646174788787140268908254286004437,210667212773233831169122104024861877288320764936650021⟩
def resval1Tail48 : Box := ⟨-7771339092458455757420333666558705519340860673083472,661788838725405964352078513423493267570612392596815878⟩
def resval1Tail52 : Box := ⟨-50930247876335226012645054449748568649647869888697391,2065210561029507283541471457685178741624951974204204924⟩
def resval1Tail56 : Box := ⟨-333776472482299362958676605867318042563159761961631027,6354273491466979287813138895791297679513859178383449928⟩
def resval1Tail60 : Box := ⟨-2187437490043388007582211686591069783429337704238018985,18950103136743895715017494688796643158662124106803019201⟩
def resval1Tail64 : Box := ⟨-14335590307717428141714896512604812196511464694719873130,52469476340505931752548430462361491800404024315529875521⟩
def resval1Tail68 : Box := ⟨-93949233615329232511696831242951390194413618631659640319,117187341224421445067304198158673526920481237077182593347⟩
def resval1Tail72 : Box := ⟨895426513179296673888103642300106706803802201160317716506,1558315180692993402072065458618794494975119240625620151⟩
def resval1Tail76 : Box := ⟨-32113998533596052839440770792054449027468055069195,445628342303580042493397592136187496303121641482⟩
def resval1Tail80 : Box := ⟨-1825660050729511870745948459754986778705990531,71876301478144896984825747282061406149789158531⟩
def resval1Tail84 : Box := ⟨-4168793946127670472090449483882889697213100,226999356487450196451212285050043718010943122022⟩
def resval1Tail88 : Box := ⟨-20213313712458786693412617518119697862762096,717419623567183783203054719512701266628350130647⟩
def resval1Tail92 : Box := ⟨-132449382581872289600533845231701711095729307,2267331716602806649037566319951588605009181398718⟩
def resval1Tail96 : Box := ⟨-868020060031688757312193836975600268938180571,7165438479742633966665776567141989240637482666034⟩
def resval1Tail100 : Box := ⟨-5688656258779179481455598659676811069239810664,22643378799904520362597820650379438633649999261191⟩
def resval1Tail104 : Box := ⟨-37281177656983068969310219085853360690241013193,71544956708488494909505420729543828938438560142645⟩
def resval1Tail108 : Box := ⟨-244325925892691443747596519864384994053569452626,225990895047604076575825032997469977711375724654847⟩
def resval1Tail112 : Box := ⟨-1601214387930290739032122106457338052683009241637,713413804985096510311091293890767912179823746200841⟩
def resval1Tail116 : Box := ⟨-10493718612739910244482730222579398252363876031588,2249306836442752192340746812802126874894440891764652⟩
def resval1Tail120 : Box := ⟨-68771634300452321358134965688883515971567265944639,7073314070566288263618747925037330159778633580214849⟩
def resval1Tail124 : Box := ⟨-450701782551448520359265289697546929943249363533489,22121816000731093569821085756310800222394224737369798⟩
def resval1Tail128 : Box := ⟨-2953719202129507977849960951325328566069581032428088,68386583915405725460755856165957029347360988653369443⟩
def resval1Tail132 : Box := ⟨-19357494163153872690105892975434410696954179773459836,206113093467639708107467146617024999315736984159316697⟩
def resval1Tail136 : Box := ⟨-126861273828779493848633242840988679068299723244146913,585737126651765967513148649587210164139720242984763451⟩
def resval1Tail140 : Box := ⟨-831398788711266691962987725003170663746916082886789427,1420764671201902845215406453804560922191162961284040389⟩
def resval1Tail144 : Box := ⟨-5746315755756899792395401540102143518793307589687256862,1617855080049362484936519782866591874060444836401481871⟩
def resval1Tail148 : Box := ⟨82758004351075050515481178109790852511330618,991982111648325971137506785909543593581262⟩
def resval1Tail152 : Box := ⟨1550418772883164511567814195071113434443,4008147229365167830055161402296758060850⟩
def resval1Tail156 : Box := ⟨671614439704413503863503268882679188,12539360781963964391374521133715087591100⟩
def resval1Tail160 : Box := ⟨1005533975934588397199178655898445594,39630058147226449862662245024184897175424⟩
def resval1Tail164 : Box := ⟨6583627288214606483527859910678002126,125247145509714573319904128711772033549676⟩
def resval1Tail168 : Box := ⟨43146416275281563613727445300847390582,395820491329237038950353645259210501734729⟩
def resval1Tail172 : Box := ⟨282764352761162704335343238299213979901,1250841819138779882782608830825827911663414⟩
def resval1Tail176 : Box := ⟨1853124462200115605570535781356468676167,3952318398671532979628130407574470422879581⟩
def resval1Tail180 : Box := ⟨12144636475466514062106049615635901062148,12484990053922500954395402870763593484923307⟩
def resval1Tail184 : Box := ⟨79591089605614564376017069441615333420878,39417525956590429545387049400006061163880278⟩
def resval1Tail188 : Box := ⟨521608164839353676290003289593856349430496,124308786450298760367862262040270615662477763⟩
def resval1Tail192 : Box := ⟨3418411269091187000106950359513175724383933,391107280354061371767378823428863710115699725⟩
def resval1Tail196 : Box := ⟨22402900093116035987441049039953272771172449,1224493112938082209756889585395328622795854741⟩
def resval1Tail200 : Box := ⟨146819646050247225616052100408564057383135969,3793987506245887213662623589652813871237659891⟩
def resval1Tail204 : Box := ⟨962197232355166862475189752522773647087271442,11492699446506912535221477558235818464221719572⟩
def resval1Tail208 : Box := ⟨6305855782093610955512105931989615147821386155,33057768289479731678342807034772845925277147861⟩
def resval1Tail212 : Box := ⟨41326056839965694637266733938122528215294738154,83082434370736672012546927728137907439773799830⟩
def resval1Tail216 : Box := ⟨270853278892222581006748880402547273999479630613,122354439503108274109752575522484561107713187649⟩
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
def polyval1Tail5 : Box := ⟨2238000204283305082874421116997225540958467033410489,123437669767373781323780207831938774957814109301831⟩
def polyval1Tail9 : Box := ⟨230687648881440921781454556760075184319279583651,286809519916982694655987429255186718886675425025849⟩
def polyval1Tail13 : Box := ⟨16255197189311450103544353569348657932186414668,906433215458891008659400724663363178715687891926741⟩
def polyval1Tail17 : Box := ⟨105293911876183544571787521344657243727216436019,2864722072024401033931200692249015340777054668184516⟩
def polyval1Tail21 : Box := ⟨690049641859972841980769153751454442902248972361,9053579154116750926683371275168270742415104361281632⟩
def polyval1Tail25 : Box := ⟨4522309276343296316079764193564391161261597275073,28611439618625235952273096058815855524229401087218462⟩
def polyval1Tail29 : Box := ⟨29637406071406990614117854916183872074769665920876,90410933625320276194382958243830021961566100177389783⟩
def polyval1Tail33 : Box := ⟨194231704429381981799441834324326077011934273336503,285642634765154120272583200123340841518849642571292802⟩
def polyval1Tail37 : Box := ⟨1272916898148354700198050800324292997920820407588872,902112735153868620684967474441848601292400183332561526⟩
def polyval1Tail41 : Box := ⟨8342188183705035948240788462006873957739827150366921,2846802588672052309759269623553277220078232529354469988⟩
def polyval1Tail45 : Box := ⟨54671364480729305198860685402895179388153924228295491,8968996078421417364452588091823036343477529288635727211⟩
def polyval1Tail49 : Box := ⟨358294254260907605492989479938472480327833343245750588,28160950997380444894196704441133994466804432257471461965⟩
def polyval1Tail53 : Box := ⟨2348117224724286409015840209138493394496051720565128869,87786781348364434779539302395929025007140625721335090815⟩
def polyval1Tail57 : Box := ⟨15388621043953274163148917695033425137211081966666970680,269482169508030995112169646554972015369869006537296052207⟩
def polyval1Tail61 : Box := ⟨100850866873697773504887375173175808058637767234770439247,799481508204216497431326699099688113119844597454711776414⟩
def polyval1Tail65 : Box := ⟨660936241191195819959935612081148114702958981976778426995,2184558672674897765370325880730778181434610145455668619436⟩
def polyval1Tail69 : Box := ⟨4331512161569294491108694256138218382784408511559928799898,4661657289134371850502188914300042378189109671730449226863⟩
def polyval1Tail73 : Box := ⟨28593750000000000000000000000000000000000000000000000000000,2⟩
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
def resval2 : Box := ⟨124207826556141529154530047189083507389099058123002531737,197516340569701764041014435634351137882823297777739020⟩
def polyval2 : Box := ⟨3849307594668002563724022884306702408367687578852459447630,7055325674876404131461759169892672525051802326387026984⟩
theorem cell2_lo : Holds Q cell2 (3/4:ℝ) := by norm_num [Holds,Q,cell2]
theorem cell2_hi : Holds Q cell2 (7/8:ℝ) := by norm_num [Holds,Q,cell2]
def resval2Tail4 : Box := ⟨-132712382697151943774008174737702444912517043867478,35822480026867034520910706454608513876573664488158620⟩
def resval2Tail8 : Box := ⟨-455760595342125889234528588364149415832630107848569,60993313545375580682395386959229449207601505730131333⟩
def resval2Tail12 : Box := ⟨-1045806175433146718515911678832138479239282595788039,103783615293687682726247857323067313244084111715088824⟩
def resval2Tail16 : Box := ⟨-2399704282987397977160454061259454049474446514918158,176434660718513300174482888261035823431618234890117513⟩
def resval2Tail20 : Box := ⟨-5506355515982674628532404745676696895511159370635708,299577175948521086332257754045463643706763315402863666⟩
def resval2Tail24 : Box := ⟨-12634869755802317883313495163691795491792007552549001,507824166012048215209487650357871915425586637193884119⟩
def resval2Tail28 : Box := ⟨-28991940909501133442222440284790531253126369119569778,858888196743608341621611962567239142624644304947223117⟩
def resval2Tail32 : Box := ⟨-66524835945697503524147416068782609012738711313477648,1448159480517083177860701957500954100314228518294515623⟩
def resval2Tail36 : Box := ⟨-152647724118106215347131683492387956680064220129586515,2431336849072876571833736194353010690408242609485639386⟩
def resval2Tail40 : Box := ⟨-350265090431154684230780522309103445731479060163244469,4057898512980034610277005560211537445233137525075198077⟩
def resval2Tail44 : Box := ⟨-803717410682264394124440825538571648860047442614249137,6716415083933408803171959220076567324979938330055027061⟩
def resval2Tail48 : Box := ⟨-1844207983840652598558240946288586829008059681844179310,10984806051122195118963363809143281440692630567159948695⟩
def resval2Tail52 : Box := ⟨-4231715081018906687012207599718379833176180374082545687,17654016483832331511687745264112893468704121404682253565⟩
def resval2Tail56 : Box := ⟨-9710082964519932367338489054651557347266415166219069736,27626008867895961831260097901436817843077708749800942036⟩
def resval2Tail60 : Box := ⟨-22280732367997826452357000997142199010268826855505099012,41412991974169125067163265492952737506368347809321543695⟩
def resval2Tail64 : Box := ⟨-51125313394110908635308933258475525097476606577095750818,57533368344714784628062272111521876508799965830121800846⟩
def resval2Tail68 : Box := ⟨-117311631848417876329384307160882676303723719038351982455,68054913159273338270472293563466839548218436579845706265⟩
def resval2Tail72 : Box := ⟨897067549200899935846872086327693018104445240341888808620,1010716059751145168923762067861508030228142544685645333⟩
def resval2Tail76 : Box := ⟨-34043828113611252622918179349058356830692055490081,445815841034768353564020235292173066581879914726272⟩
def resval2Tail80 : Box := ⟨-5249847475661485472670641852001356289759845964951,759131978973773408978666974473818286972361319726202⟩
def resval2Tail84 : Box := ⟨-12042192010447751062063003693613974353480979301651,1291956403290013648792311470131732624182016273442018⟩
def resval2Tail88 : Box := ⟨-27631981613955658451441926489051242606701724048442,2196932050886268436891437447087217567102717043242083⟩
def resval2Tail92 : Box := ⟨-63404276700945890355509019265763980117792867880356,3731603752082286784911919761259438352234246440655868⟩
def resval2Tail96 : Box := ⟨-145487296588746411111176819079860313226843551259507,6328628857470393278981741064555559946041543655835863⟩
def resval2Tail100 : Box := ⟨-333834791122160434445151503666805203443676025134544,10710721546664691845106662627392883734974110270692036⟩
def resval2Tail104 : Box := ⟨-766016486501939758699259034454965827908597507462976,18075509027690041346117511558416196604393747069968325⟩
def resval2Tail108 : Box := ⟨-1757699536409478770376145488448629755812390265220104,30385111170017157860422341160620103081309783451872386⟩
def resval2Tail112 : Box := ⟨-4033213011383761087900086249804784624085607809045564,50801003004244520304864743304794497938580209402108290⟩
def resval2Tail116 : Box := ⟨-9254600606212883543641313056120317608272131974276926,84290151080589882222655244146717063684517415359329277⟩
def resval2Tail120 : Box := ⟨-21235583674548073982396167315578037531769211191114809,138347632864037569064375644468449989259679989308592266⟩
def resval2Tail124 : Box := ⟨-48727117807331070625648026378993248787621199156321383,223514804284316910864206019886400930544623934712251527⟩
def resval2Tail128 : Box := ⟨-111809124072030308267467140664962504957584560401238258,352623576006016659941233580590601780327077126797008282⟩
def resval2Tail132 : Box := ⟨-256556939714521155325156934292559217921523106370847886,535744742717723919684437680168195319196657350613133628⟩
def resval2Tail136 : Box := ⟨-588694919750806465997970576001851515762491828914273995,762936771787973267102732393297778818366931872851741182⟩
def resval2Tail140 : Box := ⟨-1350818495533166105379503990082841100440616939377793603,955006031981985760919054251191367583057868808669812145⟩
def resval2Tail144 : Box := ⟨-3330478339692001799322675419608647244770493938368837408,815155597029915788653639174869848693879983865410043371⟩
def resval2Tail148 : Box := ⟨82484321462628555052366513384192022208021601,61567483957251314926837936035481854144940893⟩
def resval2Tail152 : Box := ⟨782159797181544891463912118555174163755214,103612434503257983504342047543569977675005617⟩
def resval2Tail156 : Box := ⟨1791252294173790562334885762215303028970816,176298709667336518349863108044903963499190332⟩
def resval2Tail160 : Box := ⟨4110201932583703743962941359393744998157801,299703409945822457634104824368709578620994853⟩
def resval2Tail164 : Box := ⟨9431259192394676191752064507885026064727030,508861349824754966600644841835334871056148345⟩
def resval2Tail168 : Box := ⟨21640944029703674190398083789359568355066897,862543365230695705855683186535926362043536234⟩
def resval2Tail172 : Box := ⟨49657256676259630615330118920022515084735088,1458722139712992892555958726386850914138911384⟩
def resval2Tail176 : Box := ⟨113943418421461106406329914626385685877662654,2459285239475406158668255263553488132587437624⟩
def resval2Tail180 : Box := ⟨261454286252892931019669928801298346404194857,4128360200521604492335458325092367102224605010⟩
def resval2Tail184 : Box := ⟨599932358946451143493819079347602190682826942,6888897352768809766512798830114387147724631923⟩
def resval2Tail188 : Box := ⟨1376603307864382274353757402558752806685389472,11399009561434121968598879186952019851343711159⟩
def resval2Tail192 : Box := ⟨3158750547396805321878535727538366661798098563,18635880986400226491542873898532755776841154389⟩
def resval2Tail196 : Box := ⟨7248061197934142182462730497901566658111480672,29932618003412231162771851729397102635676591662⟩
def resval2Tail200 : Box := ⟨16631383308280942400918345290005481655204584884,46797213946494046840803704514836378988129148619⟩
def resval2Tail204 : Box := ⟨38162331028027953116333856305465142468554079920,70044055625682518449561158319953175923971444695⟩
def resval2Tail208 : Box := ⟨87567190443468312295907157103445162554560258982,97028128062915890083565957620071780404664776424⟩
def resval2Tail212 : Box := ⟨200931459042218602646619318795661944577418356646,113980005043490872714669166142033208336179374120⟩
def resval2Tail216 : Box := ⟨461071553739709616570397660866389422452368688565,76166863881096872706037164235756221998505193193⟩
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
def polyval2Tail5 : Box := ⟨23188749434665371274323540636289776362422321400213103,3219281297377995681446054836822465063994495221077610253⟩
def polyval2Tail9 : Box := ⟨48142669514152912353614386983622071897537662496921676,5479601880542882114532076092993484553717014332942676945⟩
def polyval2Tail13 : Box := ⟨110467539471024098435681701044784248362249873366867267,9319620241892077365294011868680853115053039235395319396⟩
def polyval2Tail17 : Box := ⟨253478542587669606299466023596389457678208827537145203,15833834890029977259016408920522804168640001261226302496⟩
def polyval2Tail21 : Box := ⟨581631237245975538478721868886728442978361978713715159,26862615251716608328011473639877042737372642581058263036⟩
def polyval2Tail25 : Box := ⟨1334609599249036247176582654927994164176475567073339312,45484063294874541494752176326366784975458844482596613647⟩
def polyval2Tail29 : Box := ⟨3062391887412374251716971869684059762511162445035173053,76808197106477743724124906129947102282080658851077950748⟩
def polyval2Tail33 : Box := ⟨7026956854923054421125571583176277189710443144010629649,129228741820201445006246846404525204951904834867660912738⟩
def polyval2Tail37 : Box := ⟨16124037829356020245067046558843379469633476822515392757,216322168656820551864128678108491647921453946884892863470⟩
def polyval2Tail41 : Box := ⟨36998177346195026178373020285500407563512303255880632745,359544788820976668679388416643428506313076528305391698901⟩
def polyval2Tail45 : Box := ⟨84895926282701489295268916116466042056314615734342372654,591588867311940435797965441031743573807871133960641114340⟩
def polyval2Tail49 : Box := ⟨194801982593856125665980302028938717010368765993693226163,959251209644233555875605614303342761845157657823164167258⟩
def polyval2Tail53 : Box := ⟨446992147728404296891214731557305433027829639582562903648,1521771648776058568944838470510186736707385014777085071078⟩
def polyval2Tail57 : Box := ⟨1025667077256703507372437786593131927368974709151500261137,2332957042061197476224342102567137969656124029668962639949⟩
def polyval2Tail61 : Box := ⟨2353493140124519750746113724162954233677514512792255126969,3376171329982187642978789090815082257945933882561907298407⟩
def polyval2Tail65 : Box := ⟨5400319541763308103754689748161572566542221535366702435180,4374235089490693100923991091057672487567851695676112889157⟩
def polyval2Tail69 : Box := ⟨12391560196418217932111200348376520156889582497831612158161,4283398770772450806488068057496302484602084880125803234597⟩
def polyval2Tail73 : Box := ⟨28593750000000000000000000000000000000000000000000000000000,2⟩
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
def resval3 : Box := ⟨124022053416132146565805036927725827051243961937289958457,1710840082989494939965854557639045845255053845567340123⟩
def polyval3 : Box := ⟨3868423981582101870667525730431576027859108443571863079010,251129347401922618992194084684755365367684344758077645670⟩
theorem cell3_lo : Holds Q cell3 (7/8:ℝ) := by norm_num [Holds,Q,cell3]
theorem cell3_hi : Holds Q cell3 (15/16:ℝ) := by norm_num [Holds,Q,cell3]
def resval3Tail4 : Box := ⟨-184356081725971553076369576006645600706585563472533847,1992090586884553397954131354511648961040413869836316727⟩
def resval3Tail8 : Box := ⟨-273413226145090637607857913526551344226178799858419302,2544164182608954919515260245450202755528165069822983325⟩
def resval3Tail12 : Box := ⟨-405347458239542448338324102771460586785663284745154328,3242114341026374939436839761613550914236119808000647085⟩
def resval3Tail16 : Box := ⟨-600945898983641033317559886707076833657672519174888203,4120832994392796706141017603978714022048636551148978941⟩
def resval3Tail20 : Box := ⟨-890929414154633613140488903277230989576524632348835401,5221594073377617501927034298476264898541668871378202379⟩
def resval3Tail24 : Box := ⟨-1320843061494101423675573207591792703692583894560473642,6592052529200488914979924298698299497229212177138314409⟩
def resval3Tail28 : Box := ⟨-1958209444406450777010359779869187313845019679165435895,8285336736961661290947076228525588039939949469114685090⟩
def resval3Tail32 : Box := ⟨-2903133869534086921073196917361228731875715018718624168,10357528699199554413726976490729790207841256449790818065⟩
def resval3Tail36 : Box := ⟨-4304026971430838277372418961011177126299148699854729394,12862408230633910730618016855756746396711446151503043563⟩
def resval3Tail40 : Box := ⟨-6380914213155821628904796069338998395286958793771199632,15841693142943247822510186984282567123054889614061385614⟩
def resval3Tail44 : Box := ⟨-9459993272792679033459149007752607123068114621214352164,19308022444526997321821703978636061161527604953608287854⟩
def resval3Tail48 : Box := ⟨-14024866928437009050523490835459879350967069624459889042,23216430415765703219179836084096326404995631424868677689⟩
def resval3Tail52 : Box := ⟨-20792498122178829702302052041195451385582328796801046478,27417786574110926825726372139205576891314631708906432189⟩
def resval3Tail56 : Box := ⟨-30825816770083968059601847834327138781327363863769394763,31584241854232936336474991948139347878737617861560160553⟩
def resval3Tail60 : Box := ⟨-45700664439591401000408379557700043712554678870789377845,35091544982681823777633041376433230599836379017998726838⟩
def resval3Tail64 : Box := ⟨-67753297347786553364153190453367318681782395352708188878,36835309777037827358529404758904474343462181521264059178⟩
def resval3Tail68 : Box := ⟨-100446972250127826217259631579556449808991528887484611463,34946636627184371727866137617201952353753330693824158435⟩
def resval3Tail72 : Box := ⟨897885987370344544787042346167707978384567386756420072184,757228695624236898356513926951331824806314318526047578⟩
def resval3Tail76 : Box := ⟨-2400626999341618372008997397208907426580465924535995,26627580333671401771383069690928559632944988668520559⟩
def resval3Tail80 : Box := ⟨-3512218297454921030239657829341538387569283704787850,34024898987373700206207145673802727340908298834600356⟩
def resval3Tail84 : Box := ⟨-5207019505199970796422297941442773894290662102516013,43386213124339190968428723700736465491205754632629871⟩
def resval3Tail88 : Box := ⟨-7719641392322419154338285055085462514761753134161601,55186157986267714460743012133465649524085478933678312⟩
def resval3Tail92 : Box := ⟨-11444716728701608913483154435405549664777373502800664,69989248072781608871386079896622595551290804276150153⟩
def resval3Tail96 : Box := ⟨-16967309016522410866037143104315494994235425344047964,88452075027527014851940240602148179452117863855683885⟩
def resval3Tail100 : Box := ⟨-25154801301475654762253793362273462776581771521223375,111314625912565295445805820021415970269717385260953169⟩
def resval3Tail104 : Box := ⟨-37293128091234086732589865972974399781916928052155988,139371768341346411208038097843826678115606668794261912⟩
def resval3Tail108 : Box := ⟨-55288745323844234071794477988214664731440097673804414,173410724357253948886647265787786874518180813654369427⟩
def resval3Tail112 : Box := ⟨-81968059960178898605544300048122049668426857230334047,214092156237755926445924281246869795177412612350981716⟩
def resval3Tail116 : Box := ⟨-121521347867120067972320326381640572078649006480303252,261739932700738829711049030568138007716724018597177871⟩
def resval3Tail120 : Box := ⟨-180160882112078922705247219389400921040195613623374048,315985513607332449678988561761362860124997606531541833⟩
def resval3Tail124 : Box := ⟨-267096637859005503637392253057379634962847062289302914,375183859718621042554055341264304189024052246063750999⟩
def resval3Tail128 : Box := ⟨-395982818907399964231100088550890106761905420477827138,435473866312300702945323739702266769470791352179283357⟩
def resval3Tail132 : Box := ⟨-587062398563920485436379886795810016061368701361399105,489290101634817468934950591154400024063390033964805692⟩
def resval3Tail136 : Box := ⟨-870346498320789757161578849146027183145746262475380318,523033006980004753391196128860248811360796903541415438⟩
def resval3Tail140 : Box := ⟨-1290328491816532126317916837940338208540374665163909046,513455105949192481476966132270576064529446685847123688⟩
def resval3Tail144 : Box := ⟨-2120582368128140121509490997526273151287148156220810337,412708492520254091829202869239399985921238024963069715⟩
def resval3Tail148 : Box := ⟨794064999319187418512635381417985879241941071,6958586248117999503949594379448056050777872969⟩
def resval3Tail152 : Box := ⟨1055904233363827124584746193026361786755631455,8873676709021443488415687961954682751348408709⟩
def resval3Tail156 : Box := ⟨1565423442384858502631227883700192624949425118,11288797142256452030936683503245876856805636194⟩
def resval3Tail160 : Box := ⟨2320810895531809335595120130309046153858233252,14319469602288947546488093034022652614166573048⟩
def resval3Tail164 : Box := ⟨3440706883957331478347674293939220919616995098,18100773070711735432863303755211614789530942275⟩
def resval3Tail168 : Box := ⟨5101003224393750760413229439178773455813086264,22785267003935959072942480630388908541247690019⟩
def resval3Tail172 : Box := ⟨7562467473354863858176286226672390159013016755,28537376589535325870947614362213484161001646357⟩
def resval3Tail176 : Box := ⟨11211699301042371727279701237163105004418648974,35520930437339287010634813525436386945094419556⟩
def resval3Tail180 : Box := ⟨16621850164630190794587124437831085674397769494,43875327564447940306364652315866506220461537400⟩
def resval3Tail184 : Box := ⟨24642642964009024620259817782006705191336069904,53673268930368543771209815417762583791580559222⟩
def resval3Tail188 : Box := ⟨36533830243748562453071749913048121942216377525,64849114979163601934298037237886282154888200150⟩
def resval3Tail192 : Box := ⟨54163052000080438502889937011874727976556958363,77081050679006408023689676477071890691765588941⟩
def resval3Tail196 : Box := ⟨80299168808488204710420755602280095087818779912,89601345032037930123471137296274320808514155179⟩
def resval3Tail200 : Box := ⟨119047141422616087532452090338670951855397067849,100895576109289509568696230872879370621252642816⟩
def resval3Tail204 : Box := ⟨176492759404481721369439178676857175021527588884,108231506001364698411434620959006239817534329809⟩
def resval3Tail208 : Box := ⟨261658480413560051755482956582390075069379195519,106927978009000916144006529345011891871216528899⟩
def resval3Tail212 : Box := ⟨387920505366347368077873878684421465493888508419,89228771718654368096799038928037373689641853599⟩
def resval3Tail216 : Box := ⟨575122931543556604221472200972449587243758447254,42577586101506992707227439697618029771181925732⟩
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
def polyval3Tail5 : Box := ⟨35234869521930237040231852249738695130803960817110961415,318134277966875982514412454112524404147826977742705757363⟩
def polyval3Tail9 : Box := ⟨52234032649195790968965608710452792943467831599641427985,405213007368754285371976110786946736465432477954179981023⟩
def polyval3Tail13 : Box := ⟨77439310243663700120806725304965699007475691024552959530,514743390005348915786940704665001672244178207020620785914⟩
def polyval3Tail17 : Box := ⟨114807272043038679101509104307375646237910788769392215498,651795897211429530847332954235396250443375036908115518546⟩
def polyval3Tail21 : Box := ⟨170206961716489841670494559017996503333131452775966882460,822190180017056544602603778578136705878062598397708355031⟩
def polyval3Tail25 : Box := ⟨252339501681552373186870463827359202578244202782339454538,1032356578923873709755625655569691582995343741597982070391⟩
def polyval3Tail29 : Box := ⟨374104698578408667823819329055334890249974767656948416788,1288983545146178072988711225287203335218429785421960469413⟩
def polyval3Tail33 : Box := ⟨554627097881257162638818376900355914744358571307391154664,1598304282676461684656605971818737430731065866274590429396⟩
def polyval3Tail37 : Box := ⟨822259701289780314425357545209960650954712894543457015447,1964792366981442646089669029785887622681152186653928592748⟩
def polyval3Tail41 : Box := ⟨1219037113310880234275386490945193629152215370999929638590,2388908454021917157137420131178625439741114097440318725871⟩
def polyval3Tail45 : Box := ⟨1807277532023438424814740364638524675625371915882263172076,2863346086756259547411845541018025324059535029237672862346⟩
def polyval3Tail49 : Box := ⟨2679370498315392283702611486452987204207775067455294587275,3366930528456880038514537683633906653852978517803069463616⟩
def polyval3Tail53 : Box := ⟨3972287675819880331860129292651355812224604549419962370012,3854880404981060685785920040138044091479640066101002572499⟩
def polyval3Tail57 : Box := ⟨5889095736999165751278039500609818743204800443314807676520,4243472901882226404570168330058844560566084780413180284289⟩
def polyval3Tail61 : Box := ⟨8730850187577019626336587741630140008370865460751680453560,4386147705118932164913579560134292783248436615719718785484⟩
def polyval3Tail65 : Box := ⟨12943879400568695696708311124456365874892049569446743655705,4036576380120469806071252659743920109805420331487627923985⟩
def polyval3Tail69 : Box := ⟨19189885624415998399572233040568996278077029426698027826933,2791964530867260361053262816807708681721454361808053185472⟩
def polyval3Tail73 : Box := ⟨28593750000000000000000000000000000000000000000000000000000,2⟩
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
def resval4 : Box := ⟨121039517183547791764531486520462825459360534281933967255,8416517495865613591012479885867586495211895441451920933⟩
def polyval4 : Box := ⟨4739725184820511641037424130425053848941582693153147241539,1997753805651229353615132223953756958114302116035948355307⟩
theorem cell4_lo : Holds Q cell4 (15/16:ℝ) := by norm_num [Holds,Q,cell4]
theorem cell4_hi : Holds Q cell4 (31/32:ℝ) := by norm_num [Holds,Q,cell4]
def resval4Tail4 : Box := ⟨-3727561864292264884502250724741146942561419540583117649,9158161774444554288591280728340998946203218930799069363⟩
def resval4Tail8 : Box := ⟨-4516822380711820742482543618642748236523841288004918383,10113844756191320908390513524007098590877108092614100844⟩
def resval4Tail12 : Box := ⟨-5473102345424199498668449127929688159708555547410052443,11138719618725050102390948123271617143531256849165866455⟩
def resval4Tail16 : Box := ⟨-6631841304505535111042291653106960998577359409612209055,12229405844056943810391744550175704290652390513683800544⟩
def resval4Tail20 : Box := ⟨-8035902914341689854895661747616330653627811347657893322,13379366570652242518397451288209635328356955301805428744⟩
def resval4Tail24 : Box := ⟨-9737225709073218131971852112525406651828876059957946366,14577909101610023564691001903305352346095781386642589244⟩
def resval4Tail28 : Box := ⟨-11798744399988021001195508474923290455029161087736419232,15808929707311099279764776720177565857384481539406073576⟩
def resval4Tail32 : Box := ⟨-14296717933377208778760458440549432234591732736198898058,17049341858154637653603046277564703384749179642702050761⟩
def resval4Tail36 : Box := ⟨-17323550433617072531913213188485816864325957918968299791,18267113982205954128889001279432083363183320877743077841⟩
def resval4Tail40 : Box := ⟨-20991209382780525007759028008744659794225470183837329714,19418826263930319687337112464946371604695222202632698645⟩
def resval4Tail44 : Box := ⟨-25435367480829481476048600452799692706489158276837356946,20446635785241859279039151714963281001174951038900383542⟩
def resval4Tail48 : Box := ⟨-30820421400567294515254797432676778316960824731231041824,21274514672054792244170941656287649151645425310676523378⟩
def resval4Tail52 : Box := ⟨-37345573089300968854553947004963231912171805949500845468,21803595892547604985968071597054720337165372127699883986⟩
def resval4Tail56 : Box := ⟨-45252198574502558960029262336865736227979478465593635753,21906424796607368186094659023573568773568582774831114672⟩
def resval4Tail60 : Box := ⟨-54832776857624884785110037528190134058060194174523158570,21419869979830258780562961237786615038739142488550739811⟩
def resval4Tail64 : Box := ⟨-66441709171620612899070676013390075080975039347422428173,20136392888260262578325780832770821352535414421677526039⟩
def resval4Tail68 : Box := ⟨-80508096435290636037910162699967889704796146892069837368,17793306865900311310415591579178980919120967481527266470⟩
def resval4Tail72 : Box := ⟨898255936634979628197626018580822349128049850928286202486,712737868343686863738611994836998902130513831106893929⟩
def resval4Tail76 : Box := ⟨-50374401629309959768255736031747179844694218499338680,126800546864669571109943202210499252227407257815902596⟩
def resval4Tail80 : Box := ⟨-61001266781782868537302450660503925350465585524859843,140129235210836363289341626022589520777189050136386052⟩
def resval4Tail84 : Box := ⟨-73916160067149070087140762579433050659519661557149965,154449643633991604582859057351216077226706316333338313⟩
def resval4Tail88 : Box := ⟨-89565334696532743132259593651064176314623626080263275,169723735049189782932234471622501847932017533261774827⟩
def resval4Tail92 : Box := ⟨-108527677467621919143125828445316739045398933720329220,185872011979274951898811464803510290252978838637712937⟩
def resval4Tail96 : Box := ⟨-131504636435780640314350915780660621653865207753841316,202760040557454274812561501294667456062660543213710421⟩
def resval4Tail100 : Box := ⟨-159346166873110988120135185396100794635854678324708561,220181659719742118011146834234011880027120929936735132⟩
def resval4Tail104 : Box := ⟨-193082172502358479965954728357878734657812253492978033,237837936837253221926730524754345844661030343696160133⟩
def resval4Tail108 : Box := ⟨-233960603319172069624794773093361262515350263768160169,255310874612453394130263945545162772042256568647474928⟩
def resval4Tail112 : Box := ⟨-283493619302436504453945698519761915243051307759165552,272030650577330281879365697402671422717687723063373852⟩
def resval4Tail116 : Box := ⟨-343513527683782195806063926233810483413475282377004635,287234897975673666875464447863819230207576678310099203⟩
def resval4Tail120 : Box := ⟨-416240562987311034315605319638965361389345710070071053,299918204581904598920872429990337476945047566705646197⟩
def resval4Tail124 : Box := ⟨-504365017134005983642692960188053852443242415891239384,308769601204567644304981403000309211187749105412311222⟩
def resval4Tail128 : Box := ⟨-611146757737642885262271342111125566786783125795939352,312095318575714809908117604052062073755225765312998439⟩
def resval4Tail132 : Box := ⟨-740535815936706514843083702835984235058082503022554182,307723491011814737343526438219240693590915100880051371⟩
def resval4Tail136 : Box := ⟨-897318504560231037747306863405944868542076307851327962,292886754543819838809400910675481921218662052194500715⟩
def resval4Tail140 : Box := ⟨-1087294979164539143023024372774887434447933031758228688,264077776813127927627759616115333353610636952613620959⟩
def resval4Tail144 : Box := ⟨-1515139840411190891153105927114452435088309098712151826,211210491606281116293269176800765463891765422027212884⟩
def resval4Tail148 : Box := ⟨24417536059876951329928916199419967954078030617,51865925167747266826382833995003152271123447530⟩
def resval4Tail152 : Box := ⟨29488113494443579780304772934180320420794603364,57031659191338796725279398663913151862588604395⟩
def resval4Tail156 : Box := ⟨35731193531185910038450717812198216275946095637,62504315543241287778223338243324021170295172310⟩
def resval4Tail160 : Box := ⟨43296030324359327651434826611849613178847860759,68241657679165232938392387935845227214555175183⟩
def resval4Tail164 : Box := ⟨52462458054683111390067730363829358386961596634,74178671639154735489194538993515174704175645884⟩
def resval4Tail168 : Box := ⟨63569557867547249084139687430777242242054043362,80220187259900537863934794154316993239050459463⟩
def resval4Tail172 : Box := ⟨77028199541533055739582526609263504513254429190,86232274001308623562991045999438052052472734453⟩
def resval4Tail176 : Box := ⟨93336240232673554980944700771012729985919043018,92031514594405370900405178922315361237673201456⟩
def resval4Tail180 : Box := ⟨113096941024489194220114694635123065887867407261,97371666495598721251236854091008856410088237219⟩
def resval4Tail184 : Box := ⟨137041282541603395640239794773938073309154657908,101927111895538484244576225205481961840888489894⟩
def resval4Tail188 : Box := ⟨166055005117963520958682854482914799179379776969,105272363902687318429148589182883593488774982465⟩
def resval4Tail192 : Box := ⟨201211373779691639625539684574133632827079258351,106856734360998149306346238556507828396075595662⟩
def resval4Tail196 : Box := ⟨243810880072840866222225471153463309098312186348,105973071306426022300571333613607738746932918806⟩
def resval4Tail200 : Box := ⟨295429349371565582059969856693885233861417797337,101719233715842455602009636845479924933904536233⟩
def resval4Tail204 : Box := ⟨357976233234674791820787499837352170119804126851,92950678724514165518267459738333008590533919194⟩
def resval4Tail208 : Box := ⟨433765243140219498066018666396342667366820618235,78222180680787506072298243373482044465928426464⟩
def resval4Tail212 : Box := ⟨525599938722336756152344545918067320275244754640,55716268657111349876347189136051759643128198258⟩
def resval4Tail216 : Box := ⟨636890089515619776408945381032079504148420182792,23154921761788219672580859945646983886453409068⟩
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
def polyval4Tail5 : Box := ⟨1087370752105058141782213077918679849450434534782319459269,2198438847042870836706042419231710671800533612052634139804⟩
def polyval4Tail9 : Box := ⟨1317581019963599819405430973889577470989705477549369347041,2413161200823836347207749675863722465874350926378196609608⟩
def polyval4Tail13 : Box := ⟨1596532949191040999086402644543561133210131487454707187735,2639393201565838643945105384919112598801453995630742397306⟩
def polyval4Tail17 : Box := ⟨1934543242240911700471537644585283415354194769173586514770,2874974353412958104153742574723855234520462232722861501589⟩
def polyval4Tail21 : Box := ⟨2344115452171961889732462714812983231180910847434129301780,3116664240309694190481858871866879076112468818848947816548⟩
def polyval4Tail25 : Box := ⟨2840400324547037167312029830793886405931275900815768049951,3359829585572651499988606672981197326581533574335126292249⟩
def polyval4Tail29 : Box := ⟨3441756248060030785539391385456568433687428146228701769934,3598053651480599761810887361432859001680220633100383845234⟩
def polyval4Tail33 : Box := ⟨4170428361343505060854550431086220929534662238250684303631,3822649982539001364872970403392896589682717670708761218455⟩
def polyval4Tail37 : Box := ⟨5053371437010293170562527243997747972050009418541215923902,4022058485552315647060012011770496364603023763170729684492⟩
def polyval4Tail41 : Box := ⟨6123246982754755218253506013548167197606391024835162201389,4181096942809482198705297300235225704268178898659814691753⟩
def polyval4Tail45 : Box := ⟨7419631443913360215814581636455343219893929189609252338217,4280035088945606514483769065630470695052296334304296874298⟩
def polyval4Tail49 : Box := ⟨8990480200872329071807720540961576054957913767080258403451,4293451116725347535730807191661297918314416122153957089732⟩
def polyval4Tail53 : Box := ⟨10893901516979608049363251201756846054065186582221519000293,4188821632013540290959077347179230282909211682690218068396⟩
def polyval4Tail57 : Box := ⟨13200306058194265987641987631946258087886722369411948056552,3924785313500194285209533334431565237820235217092998328759⟩
def polyval4Tail61 : Box := ⟨15995011498718946507793454139848601234148550909582194742169,3449007435518520332076842489071524800939891415315864743183⟩
def polyval4Tail65 : Box := ⟨19381398561268881121941214599273721091143456593228055255651,2695556481460590284249887854710406699229793134506146935092⟩
def polyval4Tail69 : Box := ⟨23484735519604703428673327195366987207371501694936867845640,1581684691643691295356177804604036212398595829340199557154⟩
def polyval4Tail73 : Box := ⟨28593750000000000000000000000000000000000000000000000000000,2⟩
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
def resval5 : Box := ⟨110718029941957942867006039536098918413334623609685499804,12953234592649333469127524483895205778581610771998127503⟩
def polyval5 : Box := ⟨9001057946459613125755829394517079255765176277363803251556,4000514095900317089014563256358898292167343275576369551330⟩
theorem cell5_lo : Holds Q cell5 (31/32:ℝ) := by norm_num [Holds,Q,cell5]
theorem cell5_hi : Holds Q cell5 (63/64:ℝ) := by norm_num [Holds,Q,cell5]
def resval5Tail4 : Box := ⟨-14714189237857960799309200777330159632291161416794065671,13186038413107834742423837981835501455768558901534090301⟩
def resval5Tail8 : Box := ⟨-16178493726284427665646263416821761167802535291964264622,13535871030588081567237992866798762148603900223306758533⟩
def resval5Tail12 : Box := ⟨-17788441980877569105179123057864289614478780527986976268,13857946019643393507221971788574726870555932699392172555⟩
def resval5Tail16 : Box := ⟨-19558598798001968045559801559657932849459731652965199273,14145432279372805422665136465289691547392164339244389725⟩
def resval5Tail20 : Box := ⟨-21504906801408894861569193854003715391075344939147688990,14390554975956629585120282618996723533105636558163012527⟩
def resval5Tail24 : Box := ⟨-23644895082388268020809084076008951726901116805777666608,14584483867931314520317851663112445060516591846030360040⟩
def resval5Tail28 : Box := ⟨-25997837080629462218715660459173730513052340143530288954,14717209963247870148804742635258932695244423027288023898⟩
def resval5Tail32 : Box := ⟨-28584924167178151764375837413799651839787744876634515893,14777408711402039137788299255220848681417652551371609764⟩
def resval5Tail36 : Box := ⟨-31429456500907570799259961131063889776956594051484885095,14752288313152569138168549736381804031763619477931448260⟩
def resval5Tail40 : Box := ⟨-34557052877427868390664570231549771586359824800832323202,14627421584380727765732482863754434305184443419737932938⟩
def resval5Tail44 : Box := ⟨-37995881460402020180853488322830627592140649064137450534,14386559649700808636307256796667697216013545466604925520⟩
def resval5Tail48 : Box := ⟨-41776913473310565279610901696845604220593463339686885706,14011425564123409258914426547096099163218315143372818783⟩
def resval5Tail52 : Box := ⟨-45934202136496805083610348006014962438203580700084344195,13481485765749754683609720921861540181068716825736728722⟩
def resval5Tail56 : Box := ⟨-50505189361691379481756208974599324330433718664464940116,12773697047319393729040223596362687131119100460066617946⟩
def resval5Tail60 : Box := ⟨-55531042966196528420864858018052797327211875239822975334,11862226497445491499858500725416453568546193465088858771⟩
def resval5Tail64 : Box := ⟨-61057027425361597192569819167014007903186137356223299202,10718141600867273261879446895337764805520289724051489466⟩
def resval5Tail68 : Box := ⟨-67132586606652768493037685967306779716895151032464186662,9309062114675530337324203798776163537301130022861470654⟩
def resval5Tail72 : Box := ⟨898317605450922562082508229498464918491245011978430664968,708221737300074961284698643419184732536480940582123832⟩
def resval5Tail76 : Box := ⟨-203218309271795340251824374708218233242828428847866552,185327927570155141536983023748114617422979060842396151⟩
def resval5Tail80 : Box := ⟨-223406313866577163689889734053600785628048549048857851,190369491020007343937145644277977948398213334284730671⟩
def resval5Tail84 : Box := ⟨-245637837890018304279524248564126467369928504702458766,195041601644435495472769298682182884677208572778688917⟩
def resval5Tail88 : Box := ⟨-270081658980711371481032387844228642999116462197387883,199250687097661507158376571547588907867469101528618983⟩
def resval5Tail92 : Box := ⟨-296957924498321326877875612777439814936461528175149551,202890335517276079068323390755798275134118167316099246⟩
def resval5Tail96 : Box := ⟨-326508690946131758658104487081077208588097781660557729,205839622841088342313333174137412904197748642280070673⟩
def resval5Tail100 : Box := ⟨-359000102265192242569145170662371642056811765215381961,207961413582143992103661855452788782704996470590617318⟩
def resval5Tail104 : Box := ⟨-394724786813351987385716788011287091480576803946754571,209100475945705375392920812864882254676136115175661196⟩
def resval5Tail108 : Box := ⟨-434004492872683223532023914800127268264723151311804317,209081391715329235303810754802790977956167710456599015⟩
def resval5Tail112 : Box := ⟨-477192986420541321431606959368630439294951323639621526,207706239336708762065146893651480177580231723618143068⟩
def resval5Tail116 : Box := ⟨-524679237262540052029446473148323952068004335920591115,204752026406693193522290505921655028184955263092866058⟩
def resval5Tail120 : Box := ⟨-576890922222805527069675564177978118535873814400244224,199967845327731715907117373485962751168995214937349170⟩
def resval5Tail124 : Box := ⟨-634298276942394721551237343068605959523512702247472317,193071723192129467448307837996826000668599687781839938⟩
def resval5Tail128 : Box := ⟨-697418330976444736421262645485345512454963212704934275,183747133990868093586851287026573744623961819146535371⟩
def resval5Tail132 : Box := ⟨-766819564332788449977174865167258799264760150977995237,171639137970726537604228804232704974724157696021906343⟩
def resval5Tail136 : Box := ⟨-843127027446068478010951728164682901685498719639525153,156350109358252149760658565521408345164186161840828059⟩
def resval5Tail140 : Box := ⟨-927028466808379430804312019793723184993215495079304500,137434992565009419228526533606929655652239136573192106⟩
def resval5Tail144 : Box := ⟨-1212294828662497155269941830618104617774235307669758168,110392881350082086763776195057334747662680611137225499⟩
def resval5Tail148 : Box := ⟨133432202297227146218562558221409517609588575030,100282845103627460539016398740376681133299639599⟩
def resval5Tail152 : Box := ⟨146620520061305801087088485968076682221065836104,102203163738460980756605330242175939376016594911⟩
def resval5Tail156 : Box := ⟨161210965033223718561271666046770285710620117235,103791193205944696475470534776472064719665007723⟩
def resval5Tail160 : Box := ⟨177253330578480874835579692402109406835714636717,104979225525501779965623513415006818786263224399⟩
def resval5Tail164 : Box := ⟨194892098033061975287806923849380334704441925654,105691173644473463979173133702329861775367105824⟩
def resval5Tail168 : Box := ⟨214286127949011733776594886244470317594918110932,105841019888191336113673872450520349775643929253⟩
def resval5Tail172 : Box := ⟨235610089351034099600847569764463682581416397780,105331674342070246766624114410634595900030165343⟩
def resval5Tail176 : Box := ⟨259056032862804306313829336256951855329249489452,104053709673863519463646062126565067932759024761⟩
def resval5Tail180 : Box := ⟨284835120378174912118431567458755329745412620811,101883959434316468600685243099013601939798477658⟩
def resval5Tail184 : Box := ⟨313179526854780006327287788994775444862173656769,98683965560100433766498831430081276737395291596⟩
def resval5Tail188 : Box := ⟨344344531358216670323643559105122250077254137330,94298259337374511399725796815348423552087928150⟩
def resval5Tail192 : Box := ⟨378610816189436687342988063486379675355194020217,88552458470020890410607182491407145323952401345⟩
def resval5Tail196 : Box := ⟨416286994802047465721689620511969236335251355232,81251161118547159341430918863597485481214657886⟩
def resval5Tail200 : Box := ⟨457712391276778461644331830585048947732812073095,72175615817347836113453437424767804371692296216⟩
def resval5Tail204 : Box := ⟨503260096385976309754492493010979044932152194560,61081144021315511329653090207174422696842263054⟩
def resval5Tail208 : Box := ⟨553340327772143639247514936563746850013536997438,47694289657712137902929105316458740712766647554⟩
def resval5Tail212 : Box := ⟨608404124764553400933682541960295923699923344128,31709667432708182376384820157401908693876187053⟩
def resval5Tail216 : Box := ⟨668959774391075508454993870130802553961459083204,12786064109725651370071676604034917988461546829⟩
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
def polyval5Tail5 : Box := ⟨5673336587050260299497866475022033519697671491767266424798,4080967371534200469041622583372645757953238034372653138206⟩
def polyval5Tail9 : Box := ⟨6237897146317305321694380090310855847314874716943087288718,4150627759374193881984960371087605092796960824045872737024⟩
def polyval5Tail13 : Box := ⟨6858640445006845104894725532609746506270171568217431638283,4205344685183782052270658773453582129497229513970591097867⟩
def polyval5Tail17 : Box := ⟨7541154920019591296177094181459924050706299574614200341616,4242208750467072651623913422056382152976724456319487005049⟩
def polyval5Tail21 : Box := ⟨8291587521421731222203751377330526399586174295266101717983,4257928566779564733823112727156795954718391834443020813810⟩
def polyval5Tail25 : Box := ⟨9116696892525576957589731819662386439281979699065991930788,4248786720823570139449740238010433245266073442818228618130⟩
def polyval5Tail29 : Box := ⟨10023914240241198048073327745420586717470462990436820841076,4210590975992062750217549306394061825503979176337377989873⟩
def polyval5Tail33 : Box := ⟨11021410262974625988670895623281987017489406650630387816805,4138620201512153531501905406798879437334343717453100068130⟩
def polyval5Tail37 : Box := ⟨12118168738630343244585054316420906034032706368986808266401,4027564477447258239621855628950130081143989809621383208190⟩
def polyval5Tail41 : Box := ⟨13324067435475685393600121514633275629557139064580651456176,3871458767154321299266146849234297627912484703510122559644⟩
def polyval5Tail45 : Box := ⟨14649967074577064695996165117951312823627587893587746708911,3663609486374453584775611341716860889733946258671795784407⟩
def polyval5Tail49 : Box := ⟨16107809145033033190751926427845246491476397791300104196451,3396513229384118462568903555778525957324168930081085459666⟩
def polyval5Tail53 : Box := ⟨17710723452960409191210927161273201855123666827582313688134,3061766836911407759649273468747729199965282610505296719988⟩
def polyval5Tail57 : Box := ⟨19473146372855079027731387985654259290700917354418825326300,2649967907125813930638239636766609254594405633971787257851⟩
def polyval5Tail61 : Box := ⟨21410950866338231221887979438302120366680327986523262202335,2150604759167628260782473258602231471483844771815537346975⟩
def polyval5Tail65 : Box := ⟨23541589439312478628954086370760119498573326735982716877614,1551934757543249980849164728756865760415519462857282815514⟩
def polyval5Tail69 : Box := ⟨25884251599361639311883903745292473584214804257491819486937,840849785554241817849147549985769260283935276944012861993⟩
def polyval5Tail73 : Box := ⟨28593750000000000000000000000000000000000000000000000000000,2⟩
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
def resval6 : Box := ⟨97355576787549855223782778531234662287137570174372059036,11334809069559612714904836669735043369896777355655717051⟩
def polyval6 : Box := ⟨16020947261692153130733314161243127981829813799056979973729,4003829445686868724906429419913420158079687415354670222634⟩
theorem cell6_lo : Holds Q cell6 (63/64:ℝ) := by norm_num [Holds,Q,cell6]
theorem cell6_hi : Holds Q cell6 (127/128:ℝ) := by norm_num [Holds,Q,cell6]
def resval6Tail4 : Box := ⟨-28028205788637937508761433643581240906034935773356292030,11116626595200777497537614911364282809163973344603700054⟩
def resval6Tail8 : Box := ⟨-29381507972791823038770386374651084726547951183115389857,11010937609131947184961771099990932342389751106778581863⟩
def resval6Tail12 : Box := ⟨-30800080980718782957839848653946783461389848054378827576,10879672671728738772385893538353336871139157407053067920⟩
def resval6Tail16 : Box := ⟨-32287144316616172880320552850137821684043583839835756582,10720943932506762478319603618028037569292610777014786498⟩
def resval6Tail20 : Box := ⟨-33846004780777593038220175139736870227153219792175717370,10532752115627452508968283121929932901706872607385196254⟩
def resval6Tail24 : Box := ⟨-35480128821144292139769352031115164135360238937025089350,10312979960211051132992761692683905335597774783848886464⟩
def resval6Tail28 : Box := ⟨-37193150249743382202060918783924108290376604304511920352,10059385839903476498320650554696069380358685144579928760⟩
def resval6Tail32 : Box := ⟨-38988878323226210493283056123821709813358910721652282244,9769597052712098359020149293969377695202998073806658269⟩
def resval6Tail36 : Box := ⟨-40871306213536643986607960969617655841135413754929844608,9441102764377959161669133041080977430368780696118260787⟩
def resval6Tail40 : Box := ⟨-42844619887552931286806979868948449478879201891955634820,9071246587839888452649907661754593102306859590311650456⟩
def resval6Tail44 : Box := ⟨-44913207415448886614078198547793276673057147304191716541,8657218780481032024730965477044853731778983982015340684⟩
def resval6Tail48 : Box := ⟨-47081668728473458170954143268422118089035850413857698129,8196048039940745099044534560943712586448124943643636227⟩
def resval6Tail52 : Box := ⟨-49354825847847117027805559255195092512454575216547790682,7684592878322656030680885155007478427343855884961615591⟩
def resval6Tail56 : Box := ⟨-51737733607521091848908928017254871947189103032729155553,7119532553630816480236661658686796008401974782432377151⟩
def resval6Tail60 : Box := ⟨-54235690894632180396217208484478699948498235772899846826,6497357536217457082387718300493532418872711940470523522⟩
def resval6Tail64 : Box := ⟨-56854252414411165279586035390005836283033571175325537726,5814359486381103084922507229321639823675840816312613345⟩
def resval6Tail68 : Box := ⟨-59598919731167390868234497020048584695075859802038358791,5066614264655204083289685763805786494060948495866256966⟩
def resval6Tail72 : Box := ⟨898232506975403223118406224250902711840225145097024197635,652239742414709804694466771161030076288154496190932808⟩
def resval6Tail76 : Box := ⟨-390356957306044239843899426523816444777890269559841545,157159088117583497793789715173381032200648646034713213⟩
def resval6Tail80 : Box := ⟨-409170893857926844955282206684070331594378577309580474,155761915028254942323741446648466418361869447766276074⟩
def resval6Tail84 : Box := ⟨-428926133407579955296117047558742577910570564901857655,154011093765416851444108947559958515064488070893747587⟩
def resval6Tail88 : Box := ⟨-449635180476700383787515956930404524930483946089259319,151880267982149847990952362916283463076567140428818056⟩
def resval6Tail92 : Box := ⟨-471344084158850515320180619601929409576130014837116498,149341673877176721222732051381525672775126456797005527⟩
def resval6Tail96 : Box := ⟨-494101118680279349200031824544877087274469815537973954,146365907089075736991283930463316433170864981313648806⟩
def resval6Tail100 : Box := ⟨-517956889003460567754897736281712239050196923546927158,142921833904233629763235959492547062986645353417238051⟩
def resval6Tail104 : Box := ⟨-542964443356664643436527061860627889043069686547978175,138976497892340512128494887310023314271094508490069241⟩
def resval6Tail108 : Box := ⟨-569179391197638852587371061853425605915840096754717623,134495021719619390982415477820636647861165634997936351⟩
def resval6Tail112 : Box := ⟨-596660026872712305425376758122617522971956951451368753,129440503896924063452757785899048178387415501906755124⟩
def resval6Tail116 : Box := ⟨-625467459246304825339132111989732446436798953577365216,123773910207811162535389151521043626980955452823276053⟩
def resval6Tail120 : Box := ⟨-655665747589097617017421103194677862110672964825471726,117453959549055947045361764190415899838475152828126140⟩
def resval6Tail124 : Box := ⟨-687322044027041116049513273754176019387317499097414153,110437003902824592690232402179033260866160716075289594⟩
def resval6Tail128 : Box := ⟨-720506742867965027821474227295343090516900141769604847,102676902145807990059059114643171529265877099875700469⟩
def resval6Tail132 : Box := ⟨-755293637137903608854623535314810126478815094702926282,94124887386028823875271487453004442421825892811910454⟩
def resval6Tail136 : Box := ⟨-791760082730363088050963630992982180007732317360792604,84729427500520498486758588456492550353607991148643225⟩
def resval6Tail140 : Box := ⟨-829987661189040664968039435973866549359289717105386353,74436063368926966128684054096434828869831658104102463⟩
def resval6Tail144 : Box := ⟨-1060841284043945886280817556932795046412360877856564239,59966890873423761326964836636211083263556558141833073⟩
def resval6Tail148 : Box := ⟨307510860755658291454119641535964007276919842170,98949696312220590558138508138405451148589967228⟩
def resval6Tail152 : Box := ⟨322272321275693467524529082571268252810690363783,97057411783302496197620989871010100074508901715⟩
def resval6Tail156 : Box := ⟨337831998057051567578643866947391973131433634292,94861780564690271785010570164286598475668142667⟩
def resval6Tail160 : Box := ⟨354142915495860351910457667039844218214642165710,92340822651014484337772606659884493768691617144⟩
def resval6Tail164 : Box := ⟨371241342789884119779414185609192130551743684153,89471841173189331739837268357262864321006039558⟩
def resval6Tail168 : Box := ⟨389165301820212728550941100920039290233650315465,86230820686648781132055039524320541821160026425⟩
def resval6Tail172 : Box := ⟨407954650208597648676737221043488849924890367200,82592356392092743581828569122374598405837823414⟩
def resval6Tail176 : Box := ⟨427651169948613503532128864585100652007390733231,78529579730144381620167133659371910956577417034⟩
def resval6Tail180 : Box := ⟨448298660316542201161052397735757121256609120535,74014080150170801065355089586098549063485561563⟩
def resval6Tail184 : Box := ⟨469943035268102307425739956146431786106365699258,69015822861101890071973390732644775898794585039⟩
def resval6Tail188 : Box := ⟨492632425537604544286180133548750781904190052145,63503062362575708408227240993205357852742698646⟩
def resval6Tail192 : Box := ⟨516417285666571949712851251988947648115583647192,57442251544757222410517408797193192398731691687⟩
def resval6Tail196 : Box := ⟨541350506199824922884068618389444482997338588917,50797946134705830318214706714749233878185597432⟩
def resval6Tail200 : Box := ⟨567487531298522304393912713271102707082253871093,43532704256182155903946274105893693533893312130⟩
def resval6Tail204 : Box := ⟨594886482031695548485450529368856514194362139379,35606980858260939595371104445125045184282931402⟩
def resval6Tail208 : Box := ⟨623608285620530258278320372046173534252572789698,26979016756023852475967981370154714367793205760⟩
def resval6Tail212 : Box := ⟨653716811181164517375723106009632988855896026168,17604722003877262672268650301980543569601323837⟩
def resval6Tail216 : Box := ⟨685291235628895564261324579643298368299838831397,7437189023178293831723678554959617361451104337⟩
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
def polyval6Tail5 : Box := ⟨12768416812864797600964419031630465383255160983044484021344,3929705469054332780872372192130653455773127205009263223737⟩
def polyval6Tail9 : Box := ⟨13384888377034647344440293096581826480243486600842920602645,3845401142232776995838030735053961884827239195020591524103⟩
def polyval6Tail13 : Box := ⟨14031126182899227984740828994614813306321498564637522349905,3748293013583625356048920986657521316963118174033744094217⟩
def polyval6Tail17 : Box := ⟨14708565093559372471027649150606516714997008353307403294093,3637484554347771324146178007312787076478042506740539768089⟩
def polyval6Tail21 : Box := ⟨15418711534014126896260694220079643355795249683108795956566,3512027089329620620844813220058801218087010689365416332010⟩
def polyval6Tail25 : Box := ⟨16163144661421872806754190865529660583369877207185744713823,3370916986898190443786253968147833411570623711263494473445⟩
def polyval6Tail29 : Box := ⟨16943519876465121764904654299038183193765491484474017336500,3213092713908814911869085395014077185460803597839196967648⟩
def polyval6Tail33 : Box := ⟨17761572504475373430698028647022226949097635575872694453569,3037431739138351067816246271596637709112939979751062842525⟩
def polyval6Tail37 : Box := ⟨18619121654287097116477103669934163371996046746804394617548,2842747277621383841299336111785212000385867404353599458909⟩
def polyval6Tail41 : Box := ⟨19518074263401622633116272027480991668355584839895691839264,2627784867900205860702633972663491880237989409780076287094⟩
def polyval6Tail45 : Box := ⟨20460429338456196525697846103463751595730327787929495928516,2391218773805974599995716630327778274380170829030057766370⟩
def polyval6Tail49 : Box := ⟨21448282400427761716476834016258543801455918181838426574039,2131648201973673482407798494253087006383157749542873795239⟩
def polyval6Tail53 : Box := ⟨22483830144456288488049365054222077604056975619171692299996,1847593325858381392922428569429114216644570375460195104193⟩
def polyval6Tail57 : Box := ⟨23569375324649735737904325391644508950631856555981626530404,1537491106563894026959230171787042282203812274080861423353⟩
def polyval6Tail61 : Box := ⟨24707331874733046264843591262349617735224777216283602515929,1199690900315898241348544767379968532412999427221951489273⟩
def polyval6Tail65 : Box := ⟨25900230275960437337377290864057874747725687649320084466367,832449841908347206552913389613784356516100021734118089710⟩
def polyval6Tail69 : Box := ⟨27150723455532445493833782260193416400063082049313693663805,433927985220193036276300599419009439177972745725977640403⟩
def polyval6Tail73 : Box := ⟨28593750000000000000000000000000000000000000000000000000000,2⟩
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
def resval7 : Box := ⟨82480699562089573540859574537236204424901771044925292294,18021240262474477514008610356195389414189934847379052899⟩
def polyval7 : Box := ⟨25313103276117843824824578697117824168192772889139675313610,6993672936132482502253254081472755435374411743531300751222⟩
theorem cell7_lo : Holds Q cell7 (127/128:ℝ) := by norm_num [Holds,Q,cell7]
theorem cell7_hi : Holds Q cell7 (1/1:ℝ) := by norm_num [Holds,Q,cell7]
def resval7Tail4 : Box := ⟨-42263599711469334004656632461884304655269842652303300795,17228408677825967258784195433486480837964378921370127231⟩
def resval7Tail8 : Box := ⟨-42930534117135333352606229779923035539254731609414429159,16561538770238890828541636057570257578652430664489380927⟩
def resval7Tail12 : Box := ⟨-43607925929813820486953465705685797692882676378640721029,15884146965544530007218487606223058799865114750674242938⟩
def resval7Tail16 : Box := ⟨-44296006156203949428626360091401677567481303361151937003,15196066739161797115970225385867884588251572343641276299⟩
def resval7Tail20 : Box := ⟨-44994943454732123929955654942767821953358026876294624890,14497129440633652387106372986305326362522996428347717831⟩
def resval7Tail24 : Box := ⟨-45704909136847518471419520457799696576764357655856128583,13787163758518258242558930013396522344009248727997014500⟩
def resval7Tail28 : Box := ⟨-46426077217078796137079359900983638982250766150681183282,13065995678286980591426066849122564796741253539760813111⟩
def resval7Tail32 : Box := ⟨-47158624455692978717348916536468278325004128774101153899,12333448439672798012346296239738272741722539979176749488⟩
def resval7Tail36 : Box := ⟨-47902730402019900276989119550483788499432626562329788864,11589342493345876452803364165031370986022039640999863130⟩
def resval7Tail40 : Box := ⟨-48658577438460238867723624354453911627821457701517795330,10833495456905537861799369977504340614654115060833063996⟩
def resval7Tail44 : Box := ⟨-49426350825187941295988939036467610215829554599381161699,10065722070177835431858057990799292353818358963261787763⟩
def resval7Tail48 : Box := ⟨-50206238745557997960223160013710415697686432531205312764,9285834149807778748931708845231623291002046255565279631⟩
def resval7Tail52 : Box := ⟨-50998432352230696946658876647069267811032011409356183041,8493640543135079248819983427270776815573624342845361067⟩
def resval7Tail56 : Box := ⟨-51803125814023626118840456360147089737986543101650715188,7688947081342108711490436119571345360240083168146646412⟩
def resval7Tail60 : Box := ⟨-52620516363491444738045048836651407947591010806707881677,6871556531862108788017568747978974700191398617038593021⟩
def resval7Tail64 : Box := ⟨-53450804327134149336351043401208795498035457675669683656,6041268549494771773329505818397595750405749853048313598⟩
def resval7Tail68 : Box := ⟨-54293874233376169735409940208950827166134313607647700625,5197873219092816207151466118444026370438662101487920112⟩
def resval7Tail72 : Box := ⟨898091839254367719019767602701137271335730845741855770418,744906116770476257359524043211856793960920023669453241⟩
def resval7Tail76 : Box := ⟨-590518495067209841454468166581487092341463405394418676,243266387294533771395021365590882494323928801523708066⟩
def resval7Tail80 : Box := ⟨-599804251078652002097465438633636204460982360688138511,233949067860065855214849301457313917623415056248960577⟩
def resval7Tail84 : Box := ⟨-609268433533943030326069084524204645022156791375483411,224484883639546818304455739793368422311806687672245689⟩
def resval7Tail88 : Box := ⟨-618881951092734873202653027223714599047352684330924527,214871366079722975869035580502982781990945027793315282⟩
def resval7Tail92 : Box := ⟨-628647158309816474868807469671332101197154713959487508,205106158862638441658662172914972690588922719108624437⟩
def resval7Tail96 : Box := ⟨-638566448663150442432617955863640405538189768393367546,195186868509304444483380570107060788138475199679289143⟩
def resval7Tail100 : Box := ⟨-648642253397903551900951136305326288251703744249512517,185111063774551334137911728216965954545194773487302897⟩
def resval7Tail104 : Box := ⟨-658877042121347910903892766142439776510932061212277939,174876275051106975069550538615350855406036759023936581⟩
def resval7Tail108 : Box := ⟨-669273323408165697542281468408252436563494396126201669,164479993764289188421371680900990058793463594632312739⟩
def resval7Tail112 : Box := ⟨-679833645415307643997699987113684736406216625097401089,153919671757147241965969271100742610441328608085889607⟩
def resval7Tail116 : Box := ⟨-690560596506553267246843238182332196318027694942698656,143192720665901618732459682670516655000090443919294782⟩
def resval7Tail120 : Box := ⟨-701456805886925904097509681317593265996900483723532473,132296511285528982051229239424972804914062639062857666⟩
def resval7Tail124 : Box := ⟨-712524944247118050203639967241065296941956033525376285,121228372925336839820485269124719512395327149940792235⟩
def resval7Tail128 : Box := ⟨-723767724418085194639496967688415578361354645379300325,109985592754369941132081669723797772364915291028083935⟩
def resval7Tail132 : Box := ⟨-735187902036022764464479136321850536681586878424502489,98565415136485147283244439966403206838786001066704258⟩
def resval7Tail136 : Box := ⟨-746788276272648648429257918819429350597924549024504140,86965040952743620860695131181701510963956010865910225⟩
def resval7Tail140 : Box := ⟨-758572177716940056484406931694691397284792487947146105,75181611887039263142974501623675497302330551431343438⟩
def resval7Tail144 : Box := ⟨-959860685440061347317765212573241002102297481301988972,60023152323353176623033861331067340574075219716690316⟩
def resval7Tail148 : Box := ⟨533657743973670716657267731105375722147406088206,170211709884329247149536739234020188728626916269⟩
def resval7Tail152 : Box := ⟨541995375690298837900831502760954713626296851768,161791989528254887188576682974190079104604996284⟩
def resval7Tail156 : Box := ⟨550547404403398786790163908437968942923950152661,153239959305458205976817675945918634068778701799⟩
def resval7Tail160 : Box := ⟨559234375282138371011135527451163926019224773060,144552988426221644832416036646065957320278964541⟩
def resval7Tail164 : Box := ⟨568058416034827953325692015035040143265713151442,135728947673531164949555564160438346206299779877⟩
def resval7Tail168 : Box := ⟨577021689457480546378519797081867953316237206159,126765674250878565776390788294219043510338885379⟩
def resval7Tail172 : Box := ⟨586126392472902887286288893175418681712437628254,117660971235456224741138671564769018665020415753⟩
def resval7Tail176 : Box := ⟨595374756668682208744682908678308245498411723248,108412607039676903275774944501114205666163584157⟩
def resval7Tail180 : Box := ⟨604769048844153601697244109158792560114780246234,99018314864205510322365745567612868275963958373⟩
def resval7Tail184 : Box := ⟨614311571565998720827959234961730181603486180976,89475792142360391191515448965081616598224077397⟩
def resval7Tail188 : Box := ⟨624004663732611169787386006229883610738178272405,79782699975747942232343015855683215680039992680⟩
def resval7Tail192 : Box := ⟨633850701147366888388660726306902013103375858318,69936662560992223633553989425358923824913865732⟩
def resval7Tail196 : Box := ⟨643852097100940051851914897338004121603733028156,59935266607419060209568839320129829779203678671⟩
def resval7Tail200 : Box := ⟨654011302962807210773615931721027853390890389217,49776060745551902832111210218591538548994629089⟩
def resval7Tail204 : Box := ⟨664330808782084839080719538760644545439596088902,39456554926274459356554859524695104506225799953⟩
def resval7Tail208 : Box := ⟨674813143897937061828460621823218814646556398687,28974219810508436164149410566551180532543661785⟩
def resval7Tail212 : Box := ⟨685460877816244981541092098982987297419753706848,18326486139298727032750561779838469391419185549⟩
def resval7Tail216 : Box := ⟨696288753180864378744150857878803514553248653750,7510383101350398206519886909563907761050894732⟩
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
def polyval7Tail5 : Box := ⟨21811692881578703629370639192068267526422467181866871214102,6653080026971532682631321317359903569072485050578220009822⟩
def polyval7Tail9 : Box := ⟨22155852749836457773562428436842382124157118049976666787943,6308917970273292740524074600792769889462981110418627878154⟩
def polyval7Tail13 : Box := ⟨22505445257187188284639459464228975782339819506192922686788,5959325462702865282318451260605517943721099142067105990409⟩
def polyval7Tail17 : Box := ⟨22860553910882831764345667479499350822906696019337856931330,5604216809007043209070501759096153459386071277169149303924⟩
def polyval7Tail21 : Box := ⟨23221265748807559916248483344046013119202849164563103102807,5243504971082314414423887449201001031835162263181899976708⟩
def polyval7Tail25 : Box := ⟨23587669182418301139760532827874061676937743223905269017828,4877101537471573183134680855978304572684368313133252644255⟩
def polyval7Tail29 : Box := ⟨23959854018197812383951033150852738448986026312540547028897,4504916701692061938678681694274988070385119315143387649416⟩
def polyval7Tail33 : Box := ⟨24337911479666320169402865008399628377630771976124243524990,4126859240223554153204788834574107889318854681381351647523⟩
def polyval7Tail37 : Box := ⟨24721934229740654060741461388835206061188707068192453223884,3742836490149220261862709700421408871776340390896856897584⟩
def polyval7Tail41 : Box := ⟨25112016393446180771873879036052450187043950028652975213427,3352754326443693550730618671993853115779485383392298472396⟩
def polyval7Tail45 : Box := ⟨25508253580987105075244718147878294464202873872074977322732,2956517138902769247367773978898563702032927676013726504333⟩
def polyval7Tail49 : Box := ⟨25910742911180792102719509481174969558148769137442808748978,2554027808709082219981597597698942504071720267856538182768⟩
def polyval7Tail53 : Box := ⟨26319583035261854856208372161216533950813093515235765759125,2145187684628019468607651618895058449832042128540173952640⟩
def polyval7Tail57 : Box := ⟨26734874161061841512039231995051535633066382321827059192489,1729896558828032952377840410969999715776526652588325588874⟩
def polyval7Tail61 : Box := ⟨27156718077570480706860214953589264847323898546399790346447,1308052642319424655510586413238786523145244478770527259611⟩
def polyval7Tail65 : Box := ⟨27585218179916724822356809760234037675510046596724891427311,879552540004352719373805182176630148206616676262368482207⟩
def polyval7Tail69 : Box := ⟨28020479764110422033380219382447314051221420077357606878916,444291217698147487054991403116080107658626327666450957083⟩
def polyval7Tail73 : Box := ⟨28593750000000000000000000000000000000000000000000000000000,2⟩
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
def pend : Box := ⟨1032303147774350330501827042633206768729368913201713813319413,3628437899995825250790145383810874198271430957162745488⟩
def zend : Box := ⟨1003836706487289706235332031250000000000000000000000000000000,1884996402241040957031250000000000000000000000000000002⟩
def betaquot : Box := ⟨428769736177786553934126280773469518510423040552946294763137,394810602349410531051779373508712258486140804098638517⟩
def crit : Box := ⟨209800538272368087437987142048543147780278329312809621825,8816892361286040302555939614490353213405740188984067035⟩
def subsonic : Box := ⟨332340005347625639460869186545389084698530045452150180730,4163595727304205175062364286828176790313324317042700090⟩
def pendTail4 : Box := ⟨28463073950911444189851058204644433179211930850910232260174,1659293958099851756987052049335984202533204175416665505⟩
def pendTail8 : Box := ⟨28463111539319181474089373325853205142172678999239036498746,1659178868251102019925254465465597349376801024756275666⟩
def pendTail12 : Box := ⟨28463111541036287261028583687485215343972687979370028314545,1659178852705069008514398668567879705642062981896050591⟩
def pendTail16 : Box := ⟨28463111541037180504809958633812189417558918321903498037641,1659178852691578901183075990362701707835009707501847827⟩
def pendTail20 : Box := ⟨28463111541037182775476877542486945318835919108618454217602,1659178852691526842517531360643725822533743623159437120⟩
def pendTail24 : Box := ⟨28463111541037182795920708984412549716475757593717586308539,1659178852691526135017816020122885047517009917450857197⟩
def pendTail28 : Box := ⟨28463111541037182796456499393431038505449975394851311118862,1659178852691526105930778754129515488019768937400943318⟩
def pendTail32 : Box := ⟨28463111541037182796491357676626002215443763533027009733193,1659178852691526102633199363338769318960428374695471438⟩
def pendTail36 : Box := ⟨28463111541037182796495738477036039084422674111068051462497,1659178852691526101655802159080595729679212594987322273⟩
def pendTail40 : Box := ⟨28463111541037182796495475798959146291616379972738903480618,1659178852691526100917154352941590814859864275601259296⟩
def pendTail44 : Box := ⟨28463111541037182796489419052221616798327184457648653926412,1659178852691526099496644262738068428689749280781540634⟩
def pendTail48 : Box := ⟨28463111541037182796436508056950743873127452256380236667046,1659178852691526092400672915549662396823004535719811380⟩
def pendTail52 : Box := ⟨28463111541037182795463895346188003583671765072005864985840,1659178852691525996079905967056708550363293026048299041⟩
def pendTail56 : Box := ⟨28463111541037182747977515632165756313306510626165860344851,1659178852691522625142928088895996317267319934851862048⟩
def pendTail60 : Box := ⟨28463111541037175313060238996129954789896799758437251823217,1659178852691140373285899439166357563797758063813930800⟩
def pendTail64 : Box := ⟨28463111541032309657846623364224180665386450102784726343102,1659178852507044894757585019850560132973237590606127428⟩
def pendTail68 : Box := ⟨28463111519274499594675798318895235257640023464312545670325,1659178259184928559297987117794549872154403596714913730⟩
def pendTail72 : Box := ⟨28460624970495665461849435977514746857895791317080681378230,1617476901700517694928818255772391811727228436500665236⟩
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
end SepticProfile.ExteriorCertificates.C41

end
end

end OAI
