import OAI.MathematicalPhysics.Transonic.Certificates.BarrierData23

namespace OAI

section
noncomputable section
namespace SepticProfile.ExteriorCertificates.C23
open SepticProfile.ExteriorJet SepticProfile.FixedInterval
def cell0 : Box := ⟨250000000000000000000000000000000000000000000000000000000000,250000000000000000000000000000000000000000000000000000000002⟩
def resval0 : Box := ⟨116282612978987902210984402214696798636523053618474126937,313412788288670304682567805454272623843744966619560437⟩
def polyval0 : Box := ⟨3822196059715017391214407462629345749932400944784215578607,14891430454983960682255202222365708444917924467293162524⟩
theorem cell0_lo : Holds Q cell0 (0/1:ℝ) := by norm_num [Holds,Q,cell0]
theorem cell0_hi : Holds Q cell0 (1/2:ℝ) := by norm_num [Holds,Q,cell0]
def resval0Tail4 : Box := ⟨60757757413658316139014384358908088130665152820167,1782590407083108474698456776155647967321141215179⟩
def resval0Tail8 : Box := ⟨7474190581255386480983893073846932168812670010,398555739720610314104961656558264344612410304⟩
def resval0Tail12 : Box := ⟨6912837319271895995999541306947838523650926,559871397536967673907366347748397903593628⟩
def resval0Tail16 : Box := ⟨28140435776725534933080078254358158216796,27523652009677193227025973500117250512437⟩
def resval0Tail20 : Box := ⟨389560399724938336198998752473698043368,388643669554645708335439825575792705886343⟩
def resval0Tail24 : Box := ⟨15738922994250258296944287438856243519,6217308022232314980354030643048099187082223⟩
def resval0Tail28 : Box := ⟨1688656806103224526082662683389878672,99476873512671348052831900117919412138138991⟩
def resval0Tail32 : Box := ⟨452499549749015077795681810466993450,1591629968097862062234581118662597882731081448⟩
def resval0Tail36 : Box := ⟨-262038115691227493738205994177897600,25466079486413104102240846551583477319918155490⟩
def resval0Tail40 : Box := ⟨-143010539589818716747581422561957089123,407457271646985088162363101238262677497075786420⟩
def resval0Tail44 : Box := ⟨-36730337249320851633046997733543139751251,6519316311913370745289277017042050707880667792743⟩
def resval0Tail48 : Box := ⟨-9403423181586266943231803948931793789108105,104309052174879920005784387938023560571691721977371⟩
def resval0Tail52 : Box := ⟨-2407280587081791169014771600602938839450523527,1668942577972024021474434351960519453055489645399887⟩
def resval0Tail56 : Box := ⟨-616263917965828127546648575783347699734036960843,26702503500095034507728106709762692840942201593912511⟩
def resval0Tail60 : Box := ⟨-157763560201993834233293870402176795742800587034755,427092152654600455168553928602453005095375409870018426⟩
def resval0Tail64 : Box := ⟨-40387451024118641880518469549324342681955386142274043,6795611193276305999198683083655536669026559963791341159⟩
def resval0Tail68 : Box := ⟨-10338708330727661191888952953688707827428393198707311488,99036991088598554280644596453679697742455348022439774201⟩
def resval0Tail72 : Box := ⟨811515739639205753893235138406030291680648512907341810327,2489660149795271232620279128931470927899505502330596189⟩
def resval0Tail76 : Box := ⟨-28225187521417107280436537144462059818417658370510,614237749579535170848190801199508703415395857521⟩
def resval0Tail80 : Box := ⟨-1551356129651385510785549894773722198804386636,71033194697641068119674766359844505726906118⟩
def resval0Tail84 : Box := ⟨-892264494782810978494761371910867605624649,64323593862632580185009842380272099692698⟩
def resval0Tail88 : Box := ⟨-2509940370093187094187301101102397541947,428048845124110556357161841723464894328⟩
def resval0Tail92 : Box := ⟨-25409987855787113125878600301736106925,2663879072610485494466848286354099319393⟩
def resval0Tail96 : Box := ⟨-777153937565388882101827745956914680,42563012763294942881388038203203554482391⟩
def resval0Tail100 : Box := ⟨-64500990091484572453642023116406393,681005723569468947187090931467219271433592⟩
def resval0Tail104 : Box := ⟨-13617740983547151343511147922803926,10896091293995775985178031998764516966223523⟩
def resval0Tail108 : Box := ⟨-8949090979102688914769170353291739,174337460619902450955360238538957134357246905⟩
def resval0Tail112 : Box := ⟨-495947180802190621656364945357153378,2789399369469842536177605915034210636006686322⟩
def resval0Tail116 : Box := ⟨-124725296183539076792966651787874056182,44630389794618526561291035663863402961608457588⟩
def resval0Tail120 : Box := ⟨-31922926067492916872312606697881941198174,714086206786323120811895690347907177618412547323⟩
def resval0Tail124 : Box := ⟨-8172219317082073766297822290117317710511382,11425371647128415239607753156228425569802209557957⟩
def resval0Tail128 : Box := ⟨-2092087286387091666646167425033782872803822878,182803985022382477282398506434787531785265311099156⟩
def resval0Tail132 : Box := ⟨-535574336072079708466426206821601435599973176802,2924361659451525578263607696245406376136598489964632⟩
def resval0Tail136 : Box := ⟨-137107080839443003943405023840397721647660686993826,46661248696998086709381199415159339676846318894089186⟩
def resval0Tail140 : Box := ⟨-35100053140140244810592866456078303418604504017900610,713673993055415987178929118013094224618614018251649626⟩
def resval0Tail144 : Box := ⟨-9361190587375640227816909770918886947525862841396206102,2809569104752933299933778363560307171233472448772290899⟩
def resval0Tail148 : Box := ⟨65280584669116248487806982911107908862149494,1171909686496557051265318170309444881599481⟩
def resval0Tail152 : Box := ⟨1183588385847035132654722911220134381337,48338613523708465974946639756627888869⟩
def resval0Tail156 : Box := ⟨382416750698025672447402112793127356,25118721271845839732970154718498061⟩
def resval0Tail160 : Box := ⟨681071573177812828174715803768702,66847360322202337143828452400492⟩
def resval0Tail164 : Box := ⟨4622269882906776887906657493414,30924702546257297417337317741646⟩
def resval0Tail168 : Box := ⟨97826079672342185399527183532,484985800747438814692943884609081⟩
def resval0Tail172 : Box := ⟨5713322208107524805615406580,7759489212541970633591258892367129⟩
def resval0Tail176 : Box := ⟨853827402332993767867649587,124151804838508072508660686101129809⟩
def resval0Tail180 : Box := ⟨319528417505620938084957612,1986428872771430233090580200197827129⟩
def resval0Tail184 : Box := ⟨2079847485735864552758322159,31782861961000886031668508844072218018⟩
def resval0Tail188 : Box := ⟨462710478893341520069363122942,508525790942993348402834675343979764239⟩
def resval0Tail192 : Box := ⟨118308224545462607768457455868562,8136412544176626189650418956535352268139⟩
def resval0Tail196 : Box := ⟨30286171932717790622910449470286870,130182572313567635381058137784867051476647⟩
def resval0Tail200 : Box := ⟨7753251129597090366516273462501026594,2082913888345046855958771150324180334034523⟩
def resval0Tail204 : Box := ⟨1984832082113543908446335330123478333039,33324761433545605241201648133934233345894128⟩
def resval0Tail208 : Box := ⟨508117056626434331892712585320177032136661,532719823243665076271319139948527963421757468⟩
def resval0Tail212 : Box := ⟨130078223746949565338235666501867536680964579,8401568974813601088677963156705755149068415868⟩
def resval0Tail216 : Box := ⟨33315185608222777454548302068171227245809478863,103199061006614079217359366147923647791134986409⟩
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
def polyval0Tail5 : Box := ⟨2142427288214446794095550191739544448621364954437048,52905053139185884622394653943845840862621567657365⟩
def polyval0Tail9 : Box := ⟨211244238263162969197770926810604098272327083056,10308789063024231637991371230457111245902257069⟩
def polyval0Tail13 : Box := ⟨169051417793584260218512674751385464233282740,12796289562057877038179540675457057839945867⟩
def polyval0Tail17 : Box := ⟨603028042596350933895586978785928420965628,444685385924258390180075862444562043844604⟩
def polyval0Tail21 : Box := ⟨7335301156748493739704400467935273419462,6068562132013949010541359526993594382047510⟩
def polyval0Tail25 : Box := ⟨260116902052550396120284379930494892517,97079328812470088674226107582840075293348988⟩
def polyval0Tail29 : Box := ⟨24408343214615673883371286281919342810,1553268402868931592663746443219888784436881518⟩
def polyval0Tail33 : Box := ⟨5737718763003061179834019148745387435,24852294335329185353433518829332033661431666430⟩
def polyval0Tail37 : Box := ⟨8992952096421361226439369952225522436,397636709327330787244343775189912359099448240776⟩
def polyval0Tail41 : Box := ⟨1478066776644429219243228193680149395628,6362187347859481510704811132154267213840995217106⟩
def polyval0Tail45 : Box := ⟨377274996463877321885423370646047146157731,101794997212072592177412578061640849253356487212535⟩
def polyval0Tail49 : Box := ⟨96578815759851961595699248791961632474360122,1628719864850616929220940874258135643087364871256357⟩
def polyval0Tail53 : Box := ⟨24724148853548073501483983049972421420862342667,26059494658722019075334992440229073272998663629612117⟩
def polyval0Tail57 : Box := ⟨6329381602485074654468129336987624783028465102765,416945980744399281884863544368414723782402521852412589⟩
def polyval0Tail61 : Box := ⟨1620321685931950398285635167319621019392061937706495,6669616640351553979785679964449291138909326116797476318⟩
def polyval0Tail65 : Box := ⟨414802385390931034321825425778055887204347893842579562,106324989031896263726571639889926617735708962998408557694⟩
def polyval0Tail69 : Box := ⟨106189822968586617000998627656738812479386960625313498449,1601647068647348815374501859791337146800638693504894712102⟩
def polyval0Tail73 : Box := ⟨27468750000000000000000000000000000000000000000000000000000,2⟩
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
def resval1 : Box := ⟨116050678439091647756049242708528448209533750229391733151,234347082081627660741066580756041126209847020592243518⟩
def polyval1 : Box := ⟨3803859982889826450234705361296231653316163374792043211625,8643103901458399610403141089955669310645500098986685346⟩
theorem cell1_lo : Holds Q cell1 (1/2:ℝ) := by norm_num [Holds,Q,cell1]
theorem cell1_hi : Holds Q cell1 (3/4:ℝ) := by norm_num [Holds,Q,cell1]
def resval1Tail4 : Box := ⟨58988080418618392281104863231063383347914642046034,3134115994995926567942628511192249588983724089433⟩
def resval1Tail8 : Box := ⟨7045846781692171752019216532838153506276887595,6332595657354831313230959313030051271678724308248⟩
def resval1Tail12 : Box := ⟨-325212933954529859719622986197911741786161722,20013247431924416767473740106739045269689004791776⟩
def resval1Tail16 : Box := ⟨-2173305509768991091348937467305059565564831454,63250618854237677874614310325385667046409754012559⟩
def resval1Tail20 : Box := ⟨-14243141381754144088391012938510544711755778511,199895816105563476727659599503891139992718960248755⟩
def resval1Tail24 : Box := ⟨-93343853591503366646296494718489779304321987585,631721164384655483222001095774518073480288858533824⟩
def resval1Tail28 : Box := ⟨-611738278983935919857665684027073915748214676833,1996234114918475629404421847013668541363301254907642⟩
def resval1Tail32 : Box := ⟨-4009087985157906281669118411863771618296702548090,6307009904836446204956703084200183196695697073261941⟩
def resval1Tail36 : Box := ⟨-26273959019533002941155080587803328889545001439315,19919662610885784433551402934329649757317840437444473⟩
def resval1Tail40 : Box := ⟨-172189017830412640317752832058700374283833940562365,62866820388290097020015983136697164840542433594491145⟩
def resval1Tail44 : Box := ⟨-1128457947253393264093025854409585678646103038018457,198105942151102784939921599944105989274410768066978164⟩
def resval1Tail48 : Box := ⟨-7395462003119834235645814858666384636178028917990861,622283629665758941711583727146352939795658407038787618⟩
def resval1Tail52 : Box := ⟨-48466899783645904402160614592024128177153342358639662,1941629982527871909881757603762746452178057250350320082⟩
def resval1Tail56 : Box := ⟨-317632674422078198653693101023221355885237626401060320,5972056237574793543338396867338297519399983876383522944⟩
def resval1Tail60 : Box := ⟨-2081637495085066776164698546391632823041084197325481533,17796885486033806860254348744287856951025284354111259540⟩
def resval1Tail64 : Box := ⟨-13642219475842944218765694990308931190337704730899944647,49183729688254158634021913116546534509337694319860882439⟩
def resval1Tail68 : Box := ⟨-89405430046957763424802318970937155426736245771586143803,109155402019305029866221338957792718551481051994781301461⟩
def resval1Tail72 : Box := ⟨814462148730871783913164857133222256366812448861601457516,1507323814859954988531998762954488985454594764875961283⟩
def resval1Tail76 : Box := ⟨-27593131237100730797607412309586552356628420234733,405795341494860901725542151688337547368705270537⟩
def resval1Tail80 : Box := ⟨-1482472868017945876169157800837250074928586242,65018174895292341978390016855659952448123800764⟩
def resval1Tail84 : Box := ⟨-3660576167170686322453438622785744161725350,205349739290745614435362522261488752950560653494⟩
def resval1Tail88 : Box := ⟨-18533484515717487976977781262761990120494740,648996999468308875478699505296079887656864414469⟩
def resval1Tail92 : Box := ⟨-121446089106560076052738847376340208375089478,2051088132369102632324318187802499316229221113325⟩
def resval1Tail96 : Box := ⟨-795908942643931795182487527807082823183379444,6482039301916648849116432461751584787800810827353⟩
def resval1Tail100 : Box := ⟨-5216068842180858169914468117655544921876808733,20483744597575243741974131103197149648709317942076⟩
def resval1Tail104 : Box := ⟨-34184028763774912029133606023563119756936570465,64721049682382491465859463681194010898207301707421⟩
def resval1Tail108 : Box := ⟨-224028450906208866593779065902548972653651786696,204434487969506651624911168207616097706282625963543⟩
def resval1Tail112 : Box := ⟨-1468192855858901183912225050520492286072582502955,645353784966680497221697677443710501491402182889229⟩
def resval1Tail116 : Box := ⟨-9621948700156870985957458804369060611611495242281,2034654919479720727369594834988490113838721575209917⟩
def resval1Tail120 : Box := ⟨-63058403001348086061548469436455445419612143910295,6397866019888141655096297932280986771364210978598228⟩
def resval1Tail124 : Box := ⟨-413259549909636716454951831234413284930400731424535,20006452206383073345334040012341543189600363447299513⟩
def resval1Tail128 : Box := ⟨-2708337786287943540506899410846850391103835433625454,61828035171871855301293972924097758770286133126124977⟩
def resval1Tail132 : Box := ⟨-17749362516250161118126743483333083320568920341145313,186217445845368604858063271256334080239193715177286580⟩
def resval1Tail136 : Box := ⟨-116322222220423499133797130621008963403589925433334756,528313616579740816949795565505094988573664214695796942⟩
def resval1Tail140 : Box := ⟨-762329620526411631560599220520707490675518971548059615,1275038217173192180024900242249053545529549000103903364⟩
def resval1Tail144 : Box := ⟨-5153040385855222878285023431350241151927414027053786380,1414688435372703691310555486499229954307585654824146471⟩
def resval1Tail148 : Box := ⟨64308712626658997658452637061332035462631277,829617275530714216960510198871878946819230⟩
def resval1Tail152 : Box := ⟨1138157981466193939186006767543784215630,3154396834506870356315403066564354872735⟩
def resval1Tail156 : Box := ⟨480479953724101663409209515016920898,9870945481500734409777082630516473222520⟩
def resval1Tail160 : Box := ⟨792777204227848722183783022970890057,31196653496174717635227909940497556255495⟩
def resval1Tail164 : Box := ⟨5191450760641310259553347634227060900,98594142950143450857603698365653933721628⟩
def resval1Tail168 : Box := ⟨34022664687661673221551325719693581335,311588565058516485072702562142342139413256⟩
def resval1Tail172 : Box := ⟨222970934744106347134742478992510837137,984658293967956570739398619894300432529506⟩
def resval1Tail176 : Box := ⟨1461262317908069327776922196145248547995,3111249895893081752587475506710382626485960⟩
def resval1Tail180 : Box := ⟨9576528726637999541853742012646488796688,9828127872532784580071181637517183516673501⟩
def resval1Tail184 : Box := ⟨62760738662893388389309048015462718108411,31029243294947132893559463742987688243984719⟩
def resval1Tail188 : Box := ⟨411308776901137168008081086705369662497328,97854778045372525785301910591103290925722531⟩
def resval1Tail192 : Box := ⟨2695553200299291874411177067705666821463426,307873807620713766561599757749657880285075338⟩
def resval1Tail196 : Box := ⟨17665577453481452207216256078323859240365464,963886970326510449828117444336021978161892425⟩
def resval1Tail200 : Box := ⟨115773128399136819513773035981413573800645248,2986417639893183915552891977223853809329410940⟩
def resval1Tail204 : Box := ⟨758730774276684416582261908015655974315681226,9045723999585547376311308890340801321731818801⟩
def resval1Tail208 : Box := ⟨4972418002347710319507115825077393575421262861,26014500789157022764288996857163146885584931041⟩
def resval1Tail212 : Box := ⟨32587238756569535512005258902933079095604782562,65346726917285676522291051210919046017783128118⟩
def resval1Tail216 : Box := ⟨213570423570086735162420674466522596605353639607,95954697385693119919541948749768552224879354139⟩
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
def polyval1Tail5 : Box := ⟨2084446444762898945128782031417489446050107908046600,118937998997182903915379107919257416356389643403643⟩
def polyval1Tail9 : Box := ⟨203300034782956296396031711504608465376930104256,276205895492492541378273046758577796232201264334680⟩
def polyval1Tail13 : Box := ⟨15637080620430855958941108532373260684668106867,872922601036295090745203210803200519440974268595526⟩
def polyval1Tail17 : Box := ⟨101449913544271433599462755504789961264157202141,2758813970092463790369288281757242072928320638810670⟩
def polyval1Tail21 : Box := ⟨664858576755056628219578115667567423261631927697,8718870294299180937395246913036622956504778832501132⟩
def polyval1Tail25 : Box := ⟨4357217126416447082525044544382038489882257759420,27553679809226752751085854979026531868755701924631576⟩
def polyval1Tail29 : Box := ⟨28555458158241707706979519547471738086211943064190,87068450452290594431039698949267028678255687523870216⟩
def polyval1Tail33 : Box := ⟨187141050585724573650664738474037364312526461244000,275082408493548808094877248661834485441085345832141707⟩
def polyval1Tail37 : Box := ⟨1226447589118577007270819342604007417759338904325710,868761264550368328387054080587331362552480456917346706⟩
def polyval1Tail41 : Box := ⟨8037646920047493138332702225607438767551034999400599,2741553147002281486296150112778890265252591611428924812⟩
def polyval1Tail45 : Box := ⟨52675522855223239929251684176175773602628956489126029,8637389208553618964057281782979818095730511396120336604⟩
def polyval1Tail49 : Box := ⟨345214306583991038632762296401553213552286076549809961,27119681634658769536544868973537487184109233428049000244⟩
def polyval1Tail53 : Box := ⟨2262396479628844828929658473717084887922520796580854997,84540237606274201995614453156892668302363404581199496982⟩
def polyval1Tail57 : Box := ⟨14826841568895690366075662707538620818060073440212082051,259512347640872040675529023095158259172227015183751153949⟩
def polyval1Tail61 : Box := ⟨97169188905936478243365708357228270773219556520430253769,769878125139766900700835144059063734408080322013795700745⟩
def polyval1Tail65 : Box := ⟨636807996436364328145889880172286069931064562087783452533,2103489687479472423083948986491990588236596308056095522564⟩
def polyval1Tail69 : Box := ⟨4173385082250521286232513342967768671302814090806371490129,4487308993158035708919730645614512589372838590111543488684⟩
def polyval1Tail73 : Box := ⟨27468750000000000000000000000000000000000000000000000000000,2⟩
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
def resval2 : Box := ⟨115936503971478128054569870435575325926449092652583364693,215262070484514502271698149487338772879519261131878400⟩
def polyval2 : Box := ⟨3794800385609805992324652910450170305041952147515687873938,7346698685826685492856040631928585098048421455822039320⟩
theorem cell2_lo : Holds Q cell2 (3/4:ℝ) := by norm_num [Holds,Q,cell2]
theorem cell2_hi : Holds Q cell2 (7/8:ℝ) := by norm_num [Holds,Q,cell2]
def resval2Tail4 : Box := ⟨-136214413058366407923380064498055617579017710048178,34508648475315489395243481618800604743883708278490054⟩
def resval2Tail8 : Box := ⟨-445976163497072598299163759460420751860595717036211,58754528324450744461887354223567192739927762084913403⟩
def resval2Tail12 : Box := ⟨-1023351681258503289845917312032502064727371421825498,99970106909544827609968647599894090894225722236910969⟩
def resval2Tail16 : Box := ⟨-2348180252365563624519687759562736094081711674238168,169942201427094960202958429688177659248354742870642095⟩
def resval2Tail20 : Box := ⟨-5388128602661390821902899168613342784058670686812314,288531656219981058834280403809135393811278524461104559⟩
def resval2Tail24 : Box := ⟨-12363586572740371130387030891474758904344071677169203,489050590284212851524758932664879490889836640382531407⟩
def resval2Tail28 : Box := ⟨-28369455188232686064103094083437646959999755771651424,827020993960488864965559067730777864050381826617918983⟩
def resval2Tail32 : Box := ⟨-65096481748398774157046360407495392925406790756539345,1394161860489486888858621792851142305143279292257052009⟩
def resval2Tail36 : Box := ⟨-149370226107736496582651134757021035267579479074722970,2340060082016536588114251970941364688114375185632723617⟩
def resval2Tail40 : Box := ⟨-342744551598215015044509828448483279509367237038674257,3904113650016538235611815740142812620326681493918579002⟩
def resval2Tail44 : Box := ⟨-786460800866237849296074460102348097175829601150217631,6458491799639397016501971659747595944745706700180173874⟩
def resval2Tail48 : Box := ⟨-1804611009613450630648102801065225665570626102974828331,10554958274714362941507434547656908415691931910390769486⟩
def resval2Tail52 : Box := ⟨-4140855961837018782591430015601229054585320205901714595,16944023583605181857791412692759269646624994130707906453⟩
def resval2Tail56 : Box := ⟨-9501597854240057105479847171666718249728809128060554024,26468275789296470151486949307082652102408523916890524241⟩
def resval2Tail60 : Box := ⟨-21802342949311995886806997775447690139700952661987667888,39560673478805738200993395656277000189176586476691491477⟩
def resval2Tail64 : Box := ⟨-50027602228636964692204815489805836154022664650815122435,54654994717181461148498002938291648006330757447811349516⟩
def resval2Tail68 : Box := ⟨-114793039934907324501605839867077437562351235669198298337,63790682252042547218733225061871364693048522076747595243⟩
def resval2Tail72 : Box := ⟨815933601290499718269228134908096366743449128789629046199,1016595824026713755899606460991255816627438811438914978⟩
def resval2Tail76 : Box := ⟨-29445177976873010142176959289203717558905040609411,413085011338046007334251121120255982135023016295935⟩
def resval2Tail80 : Box := ⟨-4946290086329458761331851984064062683470989103570,703335569678779669869822753313327398273355136541373⟩
def resval2Tail84 : Box := ⟨-11346418887293278906888969529754984502492434529114,1196948679442984707077508358693562308172287669666101⟩
def resval2Tail88 : Box := ⟨-26035462883509738683411223061035577063822796685596,2035262629343115902310077455701082336563493849897859⟩
def resval2Tail92 : Box := ⟨-59740908770382427208974972306371303461810174470890,3456742633816552067133665365833995908173298294535043⟩
def resval2Tail96 : Box := ⟨-137081341590784758032585869348737597063237237061949,5861884335392137369306008108512872372232408989637757⟩
def resval2Tail100 : Box := ⟨-314546507562537387032279855947797515690474142819508,9919424093404579022970572481565582113531874462698912⟩
def resval2Tail104 : Box := ⟨-721757638724780197652238311802753673826588897384277,16736944394411958087976050971211711778041655712354003⟩
def resval2Tail108 : Box := ⟨-1656143293703553605209354485680323858965555101037927,28127631603309390994761110251469943640802880809765337⟩
def resval2Tail112 : Box := ⟨-3800182307907849477099875194641753179497696555439704,47009622764214191785501392107458567079132599774997381⟩
def resval2Tail116 : Box := ⟨-8719888930046175674217674912066017974228110025275289,77959395357922121293431508941995112143159523721665018⟩
def resval2Tail120 : Box := ⟨-20008635584170938391439583745019448185908887480680997,127862396670522166377862320444727243229184613370436557⟩
def resval2Tail124 : Box := ⟨-45911765752047431079340352106110078566796017724019895,206349687023972128046269647513609820861062365924972720⟩
def resval2Tail128 : Box := ⟨-105349024205251365916857801116840182414479548522196690,324997877323518475903138457930814979801535002554806639⟩
def resval2Tail132 : Box := ⟨-241733610528908441532299440731657448078038765445647839,492419204407326595062965264150434220752509424131541744⟩
def resval2Tail136 : Box := ⟨-554681345205195102479975019517743594792184922743613630,697750945522575799827097237014332483740922397824272578⟩
def resval2Tail140 : Box := ⟨-1272770684409276386673660791281923251663969561722546197,863823726983981742721799405518069302142396398377243446⟩
def resval2Tail144 : Box := ⟨-3042158723674748967563972351664273940990146995464957054,713472067988761633691937265392744867035482165375846472⟩
def resval2Tail148 : Box := ⟨64105673463611732859804362363566078365201739,48453480291987345425654898571281955487848340⟩
def resval2Tail152 : Box := ⟨615036025145244684470819627389712548965082,81450492948253199664770780820660081811330105⟩
def resval2Tail156 : Box := ⟨1408697756204967179037096105860669407518134,138589554323412935678737626509062328933878180⟩
def resval2Tail160 : Box := ⟨3232393588394259166839877473924571597138725,235598443177522802553317958539281759751071574⟩
def resval2Tail164 : Box := ⟨7417042336393594512453108265241280153489260,400017821216588209283175571692201779528329355⟩
def resval2Tail168 : Box := ⟨17019127010876206223521044769003874379354741,678046762665507473868147005122805942141145532⟩
def resval2Tail172 : Box := ⟨39052046769538109275271768971263863778610961,1146699675060727290934703021342256083920320978⟩
def resval2Tail176 : Box := ⟨89608729984540081032793385457674752308634762,1933231358568882268598936029662377267896165687⟩
def resval2Tail180 : Box := ⟨205615970318504909318215378773247611193024116,3245259915860094816533413988063951630236126882⟩
def resval2Tail184 : Box := ⟨471805897230262866418672857943112987778355474,5415236014384707761017984114033952671402449192⟩
def resval2Tail188 : Box := ⟨1082604645526504926719413958705663308369088133,8960428952963674036163688700702017657820691295⟩
def resval2Tail192 : Box := ⟨2484141943532265218478897938139802290471008571,14648829992917452829788472201035864731818343253⟩
def resval2Tail196 : Box := ⟨5700105963073090364139124206553897273328901293,23527987769412559433075512591012175361799103264⟩
def resval2Tail200 : Box := ⟨13079449052762790917414089749978263701983304121,36782388485038634773013909914419047018111525435⟩
def resval2Tail204 : Box := ⟨30012071465350119109718266108351327309774015300,55050022060195412100803935704198903090838986987⟩
def resval2Tail208 : Box := ⟨68865624997524926673744260308099720793149078445,76246551212686512821372554923654187649096965985⟩
def resval2Tail212 : Box := ⟨158018892999031352096611703580989941787251164464,89536073260662049450933977623174895419606679662⟩
def resval2Tail216 : Box := ⟨362594994226882108542245508687800290375987381586,59727542918681852027139426070414693153892469702⟩
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
def polyval2Tail5 : Box := ⟨22258221987712129129978089591754052910415958126135852,3099191867518954929361547474299433407642669701001983740⟩
def polyval2Tail9 : Box := ⟨46354235271504629503788153332614716214065565222034751,5275190726817975750796427534770887009411113478372989100⟩
def polyval2Tail13 : Box := ⟨106363863650799787525954240055232742568630514266666286,8971956568913547085587503002267152569882226758460684691⟩
def polyval2Tail17 : Box := ⟨244062258264195880737117075337450013237595693345058712,15243151607274622337692874508343100440965726138626135258⟩
def polyval2Tail21 : Box := ⟨560024654513787002935790248508796561770859078595266593,25860478466371197813881281669252745390754087358222918107⟩
def polyval2Tail25 : Box := ⟨1285031187921121460675812392160515545837964594059689735,43787180716762290762444335623957595849430549817427416672⟩
def polyval2Tail29 : Box := ⟨2948629387332327402165993693590090856037965739179445752,73942574261806887770080768294389227685076151420254213632⟩
def polyval2Tail33 : Box := ⟨6765917703449158206013364436672175891103324993265561348,124407081108243563690862458165851079230006156901070706543⟩
def polyval2Tail37 : Box := ⟨15525058037647282377357847831809967919472037538200771164,208250286873928473089565380368188923583130007453710615638⟩
def polyval2Tail41 : Box := ⟨35623759796759647695026807534051837534055979118854805809,346127099327694452425104904698233009989246521159879725842⟩
def polyval2Tail45 : Box := ⟨81742191171192894905914234408706709228887674112687593407,569507920854531384184949662892786881467110840124094220693⟩
def polyval2Tail49 : Box := ⟨187565429802713405061052488946643924090378000820629538232,923438509746377243525331604532875694943166909417880933533⟩
def polyval2Tail53 : Box := ⟨430387171581899294504552592363085687252376399068898179355,1464936500385229109995902298908436599081375208863369359011⟩
def polyval2Tail57 : Box := ⟨987565340036810845044926749368034195959390275532599013540,2245773169074958466687860167957639548900054507274186154363⟩
def polyval2Tail61 : Box := ⟨2266064988083503837698543494405656217671600499328188051639,3249867762154665829518519018214618142572149299446144694256⟩
def polyval2Tail65 : Box := ⟨5199707120183391678888657737135823501098219260083090828037,4210230632842145325808683086594250759825790754731723657398⟩
def polyval2Tail69 : Box := ⟨11931235260254782317867564655017656292964174022335075732796,4121703253850456917807992766433905713560324102139626097429⟩
def polyval2Tail73 : Box := ⟨27468750000000000000000000000000000000000000000000000000000,2⟩
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
def resval3 : Box := ⟨115753301640434120037680921007592043633930590906055500578,1727134623012536530852198938055929779941832413473178688⟩
def polyval3 : Box := ⟨3813158590968360201205966852171884026538689364957781214308,242268004408698329119104124424728665063362000267565054761⟩
theorem cell3_lo : Holds Q cell3 (7/8:ℝ) := by norm_num [Holds,Q,cell3]
theorem cell3_hi : Holds Q cell3 (15/16:ℝ) := by norm_num [Holds,Q,cell3]
def resval3Tail4 : Box := ⟨-187777452289714831106427939220277502764787530199593523,1986350498119515920735417116104318374530388047148888992⟩
def resval3Tail8 : Box := ⟨-278474139329969280897991533157804909287705789774021600,2536091631595442278163117339997657094221828227021385921⟩
def resval3Tail12 : Box := ⟨-412850488404797592510647496723210639353204936018564687,3230712628686014550217291941591628828629482840569987440⟩
def resval3Tail16 : Box := ⟨-612069479790791131550401940912143486740338178873704863,4104662420299080895543478069014499061051502589561769623⟩
def resval3Tail20 : Box := ⟨-907420624675529643535562831528672103442324130883625084,5198569336890718904399127832662017733043953022965126807⟩
def resval3Tail24 : Box := ⟨-1345292025290893566605831331098611428544759991749377105,6559145665992181667189732654748040775304514842626658075⟩
def resval3Tail28 : Box := ⟨-1994456136544632224434213608691971821376339762556727782,8238140970337888648509631143663667061940144129167968692⟩
def resval3Tail32 : Box := ⟨-2956871226334970514465357642630752110225161381652505982,10289617346438419865492014589106805389070889562043030616⟩
def resval3Tail36 : Box := ⟨-4383695027896151660186768939581577053564438823947100758,12764391393936478699284537487985785750228082230397960761⟩
def resval3Tail40 : Box := ⟨-6499025702049447282240627414146840733375375796565285253,15699828455801876435941619122460200585066449132839119741⟩
def resval3Tail44 : Box := ⟨-9635098885099700448582438474518395675182746395035317287,19102167408015249697617429914946045660460865286760567334⟩
def resval3Tail48 : Box := ⟨-14284468900680639649110643569807500531033693339917736023,22917022137059239309717742144710794849319624027039267552⟩
def resval3Tail52 : Box := ⟨-21177369761099339912139841526408577960764800736575699199,26981384148023044170848930869667876859009924085495228262⟩
def resval3Tail56 : Box := ⟨-31396406342902591461164783148285730666855738344974722109,30946943705260243585614195247325034597727210065541442294⟩
def resval3Tail60 : Box := ⟨-46546589230322056832854379485649536304969587749836477071,34159263387082428604053356129373539862166009798548404376⟩
def resval3Tail64 : Box := ⟨-69007419035149024293023734556706991230744121370884989812,35469395911709833914298825085944581670394714441400868622⟩
def resval3Tail68 : Box := ⟨-102306457033622290985033379581267835530642822822640726436,32942622231362277947680669180624288490499802671214152116⟩
def resval3Tail72 : Box := ⟨816667334475492180238217162589093102756783732537453573525,790726698637845730979860336940264234177823911347392623⟩
def resval3Tail76 : Box := ⟨-2349990998344645113710816794651668072470157535807748,25536181260081788071258582343008367745214908402775517⟩
def resval3Tail80 : Box := ⟨-3443730196281307454317738000760690240899339123473387,32620709986343297362136849818259825340011836055381612⟩
def resval3Tail84 : Box := ⟨-5105483295590712818243546811585298708106675043955403,41581312892276604830451204606421372361713787703498036⟩
def resval3Tail88 : Box := ⟨-7569109379902160331225271835786489766989620439162836,52868735062871727996933297208278907510804464759846569⟩
def resval3Tail92 : Box := ⟨-11221546227225184012946481727431672788690009700370642,67017556457248636467679569756371972384656448182102752⟩
def resval3Tail96 : Box := ⟨-16636448677058839704886098166811001125732992415849681,84647064084021158810419677479506303875511653455758244⟩
def resval3Tail100 : Box := ⟨-24664285917472191817037004155477009960858632454406787,106451097634333017929431173273282314608039286876281804⟩
def resval3Tail104 : Box := ⟨-36565916898940196277447884412552671961883976209193704,133167965105032272325879910595647623532249935831199101⟩
def resval3Tail108 : Box := ⟨-54210621914377899653869422628035637592411120626944123,165516384327841156186418497865990153368147109539134164⟩
def resval3Tail112 : Box := ⟨-80369693353123752096345211177177739961600283074427570,204075325532605987033558078155146502502236448783847657⟩
def resval3Tail116 : Box := ⟨-119151697242602433097501983106767968360556854416774560,249073265872364168066022794707917763559613606353388009⟩
def resval3Tail120 : Box := ⟨-176647768125906236633682492870799391864670137352585352,300033539186734774284234816619116820847587978258235645⟩
def resval3Tail124 : Box := ⟨-261888287838059073331658080595846555633825104970043485,355193907836829645321543874432968139607452031702889418⟩
def resval3Tail128 : Box := ⟨-388261204963912107728029092925132627926553106713978800,410575314063238759922192286287052243635249049773866617⟩
def resval3Tail132 : Box := ⟨-575614757439062210260788657328536943942722848226698961,458509689197274455126731562367600017820974386816983290⟩
def resval3Tail136 : Box := ⟨-853374853720238102099215231428417042918710680069205294,485338820075806064745438573111933312505176566198754120⟩
def resval3Tail140 : Box := ⟨-1265166948817354425493094636532446235725627067564698611,467849339575787733164248276771722422996578207682391175⟩
def resval3Tail144 : Box := ⟨-1985014847171031335288294739949862201374817845693596389,361918892640178007740478225873240634224295193514641514⟩
def resval3Tail148 : Box := ⟨623199421256296699164774559934732951734212397,5467214598050023063791484109357970300279399559⟩
def resval3Tail152 : Box := ⟨829622881015828987617910682096713994769917429,6971778351621029423154444464318658193314646570⟩
def resval3Tail156 : Box := ⟨1229951719373044553510410283444319497663292383,8869259302234154138163053749887135914059818618⟩
def resval3Tail160 : Box := ⟨1823458927544588779010019928257867905231935917,11250356252488431729113858122596341056405330152⟩
def resval3Tail164 : Box := ⟨2703360147393156841407028011286544699964044886,14221193959048418499713751237060931072940405733⟩
def resval3Tail168 : Box := ⟨4007853413159582770440931119629679004473962906,17901629607477549597524668207719314109790000791⟩
def resval3Tail172 : Box := ⟨5941823547581827568919619307218920250105038614,22420840733711507774455291809460673015845909399⟩
def resval3Tail176 : Box := ⟨8809021546215948711771151057353222727669243169,27907532850600644370513949326063376010729912640⟩
def resval3Tail180 : Box := ⟨13059771967358001467452198508644550191471291135,34471212900785647800824471653626354799078466319⟩
def resval3Tail184 : Box := ⟨19361701290497530326188360006537155027103441220,42168977708389624210859244453167365247173606893⟩
def resval3Tail188 : Box := ⟨28704595899486538390506590755520690321323789792,50949222942411112172299178234384807681305311171⟩
def resval3Tail192 : Box := ⟨42555858774518185106343666798094494278490630265,60559058195804865310081113203944267909249743184⟩
def resval3Tail196 : Box := ⟨63090981053286007229527388386571694007008903054,70395225338162712432515863633213925513651352226⟩
def resval3Tail200 : Box := ⟨93535226520902482629889048789579988085683579150,79267776384183607697730048634304432621535757991⟩
def resval3Tail204 : Box := ⟨138670194285413999101542657379500739505526700180,85029906423479347296492254102154120746303325383⟩
def resval3Tail208 : Box := ⟨205584820803963004935883886884887278388793899653,84003520925611227771566738824084122021880385253⟩
def resval3Tail212 : Box := ⟨304788774375689150759583063222302433950242530558,70094417095010815283993997999053631524589692789⟩
def resval3Tail216 : Box := ⟨451867829976922643593946881607924459143465981773,33437205597310357068771496825064930297550053887⟩
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
def polyval3Tail5 : Box := ⟨33918025681296783293335751556227816968374016407959210768,306222189440034478522406332743138544377234193387133125712⟩
def polyval3Tail9 : Box := ⟨50281974509211986898948033104221733673989647545533755463,390039898837944354400029066432586072448392531122367147655⟩
def polyval3Tail13 : Box := ⟨74545295999404066981490323901260094756285700768352757179,495468220620441270266755569656663751288294579448829510523⟩
def polyval3Tail17 : Box := ⟨110516765327663144536276052668309682283809936643652608076,627387547268648890337188200126790827861982326403357473498⟩
def polyval3Tail21 : Box := ⟨163846091893065383568336277964357226133977084214486811586,791399281545193809095539312516145685952970357819608501119⟩
def polyval3Tail25 : Box := ⟨242909225121080477970523419585719636029477016038862361380,993692469568297379966493673087421941192087495064051492704⟩
def polyval3Tail29 : Box := ⟨360123888017014571393488880886087447542359661132140685313,1240704332489910214479207185843226981736194304077439158290⟩
def polyval3Tail33 : Box := ⟨533899915311353014144938036146427016916804101885776236458,1538433482400090398514446062114994161253973559749396113894⟩
def polyval3Tail37 : Box := ⟨791530717773441246346731024806768951531951807684624652067,1891184177089119849788708627637788268266702279954100528670⟩
def polyval3Tail41 : Box := ⟨1173480008539751425994701902119841601967092355099705013120,2299397094664452109734625593472784637146880743550989431261⟩
def polyval3Tail45 : Box := ⟨1739737068342820450806559514645662200667719629607386103495,2756035254335514026580597678682664297889889715366314547745⟩
def polyval3Tail49 : Box := ⟨2579238713007476939239127783189599651367843065016313646390,3240710619121853002731659389170435147947742552901772462435⟩
def polyval3Tail53 : Box := ⟨3823837785449528744460309858893547350139421949851649553400,3710309363793488877881624900050796267337347990388307877289⟩
def polyval3Tail57 : Box := ⟨5669012075420554359482212039014348225046729809750429115834,4084229753177774655885556470043781949566722150884298447528⟩
def polyval3Tail61 : Box := ⟨8404566227561881358169913474677491666839227357815344163809,4221378591776802251237017315853580839187610909653269790287⟩
def polyval3Tail65 : Box := ⟨12460148705597363340948209611752438706954512859210739775019,3884620078223905725656605917916369278755103967488603942540⟩
def polyval3Tail69 : Box := ⟨18472732886379145850724124590201018287139955493370070670970,2686195976207985304293182925530951962986886165992076566785⟩
def polyval3Tail73 : Box := ⟨27468750000000000000000000000000000000000000000000000000000,2⟩
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
def resval4 : Box := ⟨112572437862357263892172991675258675546000488551925826051,8741025542104231121593141056614887751623978526022506878⟩
def polyval4 : Box := ⟨4651790560264909783295614509908624777576922276524051619690,1923337545072396895454538345539608512579712031710459017034⟩
theorem cell4_lo : Holds Q cell4 (15/16:ℝ) := by norm_num [Holds,Q,cell4]
theorem cell4_hi : Holds Q cell4 (31/32:ℝ) := by norm_num [Holds,Q,cell4]
def resval4Tail4 : Box := ⟨-3973616097454806575208536196639869186485647736996381993,9487020398013555456734084883908641667767081360116358144⟩
def resval4Tail8 : Box := ⟨-4814960735377751305003616810814564207031982042885585577,10468460123730845279354771277179540374781843849792622472⟩
def resval4Tail12 : Box := ⟨-5834361119915276484362064717303413051172510593100025807,11518604668367420564556809682914808468834628850593606520⟩
def resval4Tail16 : Box := ⟨-7069584052779557605516597449617093759461820405838156300,12633166024826104684068341392830792553524756632711548006⟩
def resval4Tail20 : Box := ⟨-8566322456226272432677363441815243148007056022257690072,13804398800112737065434415557648611408255817810791530852⟩
def resval4Tail24 : Box := ⟨-10379943130486528230232023677822587411858862140555163968,15020022232604222842029317995693007329134567137445500389⟩
def resval4Tail28 : Box := ⟨-12577534868982582523658770179430153673119865264729155874,16261867895619681427890357387502853958569154549364209885⟩
def resval4Tail32 : Box := ⟨-15240390182470858018182428656508007552856834845067391510,17504188006109134776897997575597879488340615018975865756⟩
def resval4Tail36 : Box := ⟨-18467012441901723317414747743931667613687527428040019093,18711545293838400107159146258397246854356728425724829122⟩
def resval4Tail40 : Box := ⟨-22376759679131998039539061467156811359697304937086884407,19836187678114275364018205873692724960091089081685867798⟩
def resval4Tail44 : Box := ⟨-27114259835634991302539405299182263027110187691810553660,20814789409668438050554820132204834004974694411781599763⟩
def resval4Tail48 : Box := ⟨-32854760786475357193904231267687508611878268465414462275,21564414025405789773502266538020221118160984958987421486⟩
def resval4Tail52 : Box := ⟨-39810613045681150253242887130634995784634439866582882384,21977522413656629099673245367913380286641922171414928359⟩
def resval4Tail56 : Box := ⟨-48239124958881895778522997802772357974484470512336634015,21915810259061770728672715372497097058282522418088484804⟩
def resval4Tail60 : Box := ⟨-58452080959623704111174708757208335666848143488545730014,21202611625694028494636080278039321671723500731324619407⟩
def resval4Tail64 : Box := ⟨-70827274976898966360266334657624838873185972081602610052,19613547618773658872201005983839289798484458808877396130⟩
def resval4Tail68 : Box := ⟨-85822337084069583926153874007805367535163041898741370055,16865025900550759507278158246575084986151600500833638465⟩
def resval4Tail72 : Box := ⟨816993812062853516924861667399239518766019379651355207719,760922723244741436098731662276280972368012469447408115⟩
def resval4Tail76 : Box := ⟨-51686156960393603878870694592679692106467128034025198,126332769457794891143450406131272448036022889885169443⟩
def resval4Tail80 : Box := ⟨-62596104321087814367359743219840886849909692278100727,139497676175233328414164500884958662900232543069144597⟩
def resval4Tail84 : Box := ⟨-75848649354488051360956248686350876582765752150720620,153610871832605249867614925932135155253214653759972009⟩
def resval4Tail88 : Box := ⟨-91906961340616513489321756561740725804506807794737721,168623927385724949230300378942775456137158926084139488⟩
def resval4Tail92 : Box := ⟨-111365062065578935975350212363251742931356935434018410,184444602443522604783471387073063440173618335561522911⟩
def resval4Tail96 : Box := ⟨-134942738482091744244620887573688296974910085651598916,200922839855916417394552280129921873326087632921943807⟩
def resval4Tail100 : Box := ⟨-163512167382650524128105856957012316145965718243078726,217833340376626466303863314318942718501823901996440989⟩
def resval4Tail104 : Box := ⟨-198130178644033431782976666570003016289037667759344671,234853746079055300876239955602234006763522017518598087⟩
def resval4Tail108 : Box := ⟨-240077349092015139864035035751744784231758875011340399,251537407746689655078187020550806000523831609834129415⟩
def resval4Tail112 : Box := ⟨-290905373131479834035863391663728140737421308199021483,267279481643778897558024663331238453115947733957799376⟩
def resval4Tail116 : Box := ⟨-352494462458974761835522587466235926818686000828098124,281274820839208711789683656659240267454609937298123717⟩
def resval4Tail120 : Box := ⟨-427122898166901578542627096379322407152469551056150864,292465784714891075995751770721192347680762081535687489⟩
def resval4Tail124 : Box := ⟨-517551308085374652358352102446301316526216908279190760,299477674191648410635361310781878763183237343756275509⟩
def resval4Tail128 : Box := ⟨-627124786918387887152022611640377193578251521831483966,300538993461388897255150998749098752256921922052985301⟩
def resval4Tail132 : Box := ⟨-759896636765084304488556267468942829681699519821069161,293383122087747314231492338170660653248825103601818607⟩
def resval4Tail136 : Box := ⟨-920778305414085277162068987305252227917563300820150785,275127230507192843173633207904429150271509717348280375⟩
def resval4Tail140 : Box := ⟨-1115721276727437883995188835817229371354848066534850827,242123347386694043704817388289279146913656701074302914⟩
def resval4Tail144 : Box := ⟨-1456016956867484329671138859521404379925662211084078770,185905963068605377449353125695912038230848096197308204⟩
def resval4Tail148 : Box := ⟨19176515311059264972950761905837510482305856563,40741621124113493879194370005548506922506255043⟩
def resval4Tail152 : Box := ⟨23159542495824365748620339635853588414395309185,44799575242775182401085207747912884777699194498⟩
def resval4Tail156 : Box := ⟨28062768338792187668848943883940549127086723934,49098767429164481931885356773185060162735214054⟩
def resval4Tail160 : Box := ⟨34004082956907366555472232563654651270942405813,53605981707628223126825044848668176853341721065⟩
def resval4Tail164 : Box := ⟨41203264189581827302806923269158815375096139453,58270176225611163499281346084987211072492834653⟩
def resval4Tail168 : Box := ⟨49926621518597476586246985031676532771255233705,63016627478232483396753245037311340970469173912⟩
def resval4Tail172 : Box := ⟨60496846191412849571066509634181019388851753146,67740173064348494284141233119742660651179724667⟩
def resval4Tail176 : Box := ⟨73304948097563067665326377384939962909109346654,72296787762400275767097316632759405200733967008⟩
def resval4Tail180 : Box := ⟨88824719863647477956491105501840948939023718644,76493108080813907114857709046684231347344525845⟩
def resval4Tail184 : Box := ⟨107630263217084775531524665977101689294420711877,80073434646517179716346148692190375524751273318⟩
def resval4Tail188 : Box := ⟨130417225947480270025181648904693219620710101217,82703637239197979658428650596297865184528688855⟩
def resval4Tail192 : Box := ⟨158028535055521809471012114759505870352758925016,83951259921348594495059745028449283209937760337⟩
def resval4Tail196 : Box := ⟨191485578000647370604844332541104117595394357658,83260968637346633563698082453985518750422697467⟩
def resval4Tail200 : Box := ⟨232025985492806763127629237512086724056250713619,79924294887911381314550855559755880032365804650⟩
def resval4Tail204 : Box := ⟨281149413475547392771540564068081188159761334150,73042399380350820783168196987753439325181501790⟩
def resval4Tail208 : Box := ⟨340673017850851243427018850303798374954981525710,61480300110749897652277887345830598291587283633⟩
def resval4Tail212 : Box := ⟨412798674140726227566770430802303968290351206085,43810669465634745154706950723246642378726140190⟩
def resval4Tail216 : Box := ⟨500198924520188248176534406245852851448926503389,18244657299192123842634213424646371101806076764⟩
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
def polyval4Tail5 : Box := ⟨1046630420694981177379158256057672935834161365054367416866,2115971455247760069789391185518529301195514365442277347828⟩
def polyval4Tail9 : Box := ⟨1268215522094175593578167110999925873920349435221931416205,2322635449880819477703178648191569440309104091538156983328⟩
def polyval4Tail13 : Box := ⟨1536716025086121101268481916454021232754518187595574527433,2540376048170079438075402050795550268929928849244828919364⟩
def polyval4Tail17 : Box := ⟨1862062166070576344105728858355054605115118293986611437224,2767113453981957833547688655881089376343232696582666314315⟩
def polyval4Tail21 : Box := ⟨2256289030445598946624271487215944698729169638875997779522,2999728380065050556563307594911691650633233912463143139277⟩
def polyval4Tail25 : Box := ⟨2733979714357285316294679944728609242689086244568224976591,3233760826727990283552666656503257900299421331493330258907⟩
def polyval4Tail29 : Box := ⟨3312804777072803083757759455982666744362493862751910893041,3463034110845321081455506970909676395016030466838557589185⟩
def polyval4Tail33 : Box := ⟨4014175903853168981315591156951995073443004988695650026720,3679186821778013162507976287983078547912480266907629165651⟩
def polyval4Tail37 : Box := ⟨4864037959192211457866291340313486612917388827199545061818,3871091521774049674949488330670547820611613262013447083903⟩
def polyval4Tail41 : Box := ⟨5893828729765632665166345648222499462510235775275248663353,4024134295042334055247319537072427936236960368303491419260⟩
def polyval4Tail45 : Box := ⟨7141641859550723469973410181571091257758763268862799870173,4119323507453425338584196502123825740803662875229551763123⟩
def polyval4Tail49 : Box := ⟨8653635995987831335976351334299964158135250045740933493609,4132189145694645122191219926481931748832630707369166075100⟩
def polyval4Tail53 : Box := ⟨10485742273803590530322018780660561062814844762253330728527,4031425591101316272638353810048417592352138423149481370968⟩
def polyval4Tail57 : Box := ⟨12705733299113718043401065611177787265296586322274538542006,3777220321984803396335843039232735454987897965834975390293⟩
def polyval4Tail61 : Box := ⟨15395730168909470959330033705650531536923244535058975717982,3319198431736336637901396953386345330219036749939014467108⟩
def polyval4Tail65 : Box := ⟨18655240264692457665810979872358193045378685096899648437262,2593897516001726662500078073514176174531678924929519445691⟩
def polyval4Tail69 : Box := ⟨22604838327399541967055599632652281956349457844412866219909,1521668828675422105791213519340112301609306139491306543942⟩
def polyval4Tail73 : Box := ⟨27468750000000000000000000000000000000000000000000000000000,2⟩
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
def resval5 : Box := ⟨100974323164318023250615979493028738394593056972215767984,13895147811920054771628808507347292736583993602768268342⟩
def polyval5 : Box := ⟨8753225255021214138694742780218792315954989059150936308564,3850840579776431760431351430020913494566419111866737727135⟩
theorem cell5_lo : Holds Q cell5 (31/32:ℝ) := by norm_num [Holds,Q,cell5]
theorem cell5_hi : Holds Q cell5 (63/64:ℝ) := by norm_num [Holds,Q,cell5]
def resval5Tail4 : Box := ⟨-16342457326976860789984944758783044050425961962352090392,14115072618113951904320502135194870461972780236379712035⟩
def resval5Tail8 : Box := ⟨-17968785001304248284920658219849652048791321136003661159,14469149266039454970934714503117326153717810819617804104⟩
def resval5Tail12 : Box := ⟨-19756888053387849316951976682905891740114349283341857490,14790155509329659857554102894933567810890902819973885685⟩
def resval5Tail16 : Box := ⟨-21722928143375262780678651901902187960401057666254448652,15070358656053692080496527144642581778687670766473456440⟩
def resval5Tail20 : Box := ⟨-23884612082983642069395621704528497495259170346692510245,15300968328468441495465505199192734393549377897015080344⟩
def resval5Tail24 : Box := ⟨-26261408710159662609510363799580640360313125631110368664,15472011860633376511317549822177557727132004196546006312⟩
def resval5Tail28 : Box := ⟨-28874724238598475236442355513423448730993173200538674546,15572196650435536133959605327901587099979808783522959291⟩
def resval5Tail32 : Box := ⟨-31748095049164531717108587423898961180573205621475825704,15588757513997126597210656869277911959677329733818595482⟩
def resval5Tail36 : Box := ⟨-34907399666294061017270239687192166694266174362991625401,15507287465370696132752530978585460830286616940911100226⟩
def resval5Tail40 : Box := ⟨-38381091828514382230507091339752688360781899047404487461,15311550182112068904062505935164369489646433626393331204⟩
def resval5Tail44 : Box := ⟨-42200456752189980657378975989971676351947377188032130350,14983272238375936822147589635190315487138337158579380795⟩
def resval5Tail48 : Box := ⟨-46399892896491095877046471722527581352189978899364305522,14501912990045813573934101594861118777870713974097431825⟩
def resval5Tail52 : Box := ⟨-51017221767252984077126292445742400746271772122208459452,13844409779254445087149211259627125588850999159400721873⟩
def resval5Tail56 : Box := ⟨-56094028549921489603697318251652447418710677876927766461,12984895886453924086487886501704695702967056858346237743⟩
def resval5Tail60 : Box := ⟨-61676036639432249926425134003825828872194188721355717927,11894388394734958609416005952482187936161706400926200670⟩
def resval5Tail64 : Box := ⟨-67813519432016328611252617053247659452116699855605818240,10540442840607296909057797404103503186956904832956157380⟩
def resval5Tail68 : Box := ⟨-74561607888983506112671834327639197145032513028494725286,8886767301945673130913967723597337242375928276322983221⟩
def resval5Tail72 : Box := ⟨817022611474306247524165557357944730023177231825875431489,769219337645194637304302237508142332537497694679756457⟩
def resval5Tail76 : Box := ⟨-217267714824316653632346578993219920051297335344960768,190782059070611326252002734114161351594601292449480373⟩
def resval5Tail80 : Box := ⟨-238858658414215669820853315310235075653340055844684379,195693501314810056343311804746851903433487954420412461⟩
def resval5Tail84 : Box := ⟨-262627870757583166735089371537696458908553128884225130,200178799232816171200422390538919080465916586730869649⟩
def resval5Tail88 : Box := ⟨-288762397675154752290607772050519719196484132398915864,204135887838043376207934375344760550790398127430404954⟩
def resval5Tail92 : Box := ⟨-317497613908307740021453261685614808690714474279091867,207448839148013531855494339852515337298134137621808070⟩
def resval5Tail96 : Box := ⟨-349092318283319398634770805952194670624757998570861359,209986069034452910799586985267735941941560774477676953⟩
def resval5Tail100 : Box := ⟨-383831063119789997336659767295972393861094731684713696,211598511355886458942976053341961394905869972756978050⟩
def resval5Tail104 : Box := ⟨-422026717001832900808957682318870657622368395781774568,212117592995919944031401117093877929369437968714750911⟩
def resval5Tail108 : Box := ⟨-464023282575646587138320065921062040899293434243413313,211352988844263548638255238147584663233774401344513007⟩
def resval5Tail112 : Box := ⟨-510198994750711996880498861360447251893759719396706601,209090133616104822414697616615263774095994978900396993⟩
def resval5Tail116 : Box := ⟨-560969727208034227034444320186646921586774066580322706,205087465027877041320581204162609078005424869442982448⟩
def resval5Tail120 : Box := ⟨-616792737895564388844978358421158912199253533560695126,199073370228197633244819999911069658632754611542950962⟩
def resval5Tail124 : Box := ⟨-678170787243967723872119957535758059796110267335287763,190742804497401419677092606003390386196436282481501091⟩
def resval5Tail128 : Box := ⟨-745656666192746448166917358072247570222593564701379680,179753548050834041472294561999512863079532096483687754⟩
def resval5Tail132 : Box := ⟨-819858174807636468208212883771491097215184713434344878,165722063280376439951116808696925782940382660419585152⟩
def resval5Tail136 : Box := ⟨-901443596351651222163208530596610103923839429826327693,148218910911723844097237634285946572391006792705833941⟩
def resval5Tail140 : Box := ⟨-991147919345661709888020953934046354311215391610610243,126763670004455804860020667756638855714921612755608657⟩
def resval5Tail144 : Box := ⟨-1191411433792833229529912102120487482504926809986729474,97840413519306448266911290252612059407516835664101174⟩
def resval5Tail148 : Box := ⟨104775657747720820426753241138515209106750733823,78779027848435106501918669939287612826534211048⟩
def resval5Tail152 : Box := ⟨115132308321589443216808115167486832924132761266,80289014899057395326342573056760542190989730393⟩
def resval5Tail156 : Box := ⟨126589310524309214984049233857577425035938073114,81538274633802838699569267751047524690581905139⟩
def resval5Tail160 : Box := ⟨139186418873250694305808404352752852118180207582,82473588521563760144305773710320709694336510823⟩
def resval5Tail164 : Box := ⟨153037085979639403520329645115972524612120015136,83035219577670706225838226194887386845032737299⟩
def resval5Tail168 : Box := ⟨168266055515568984092059117456518192110027682735,83155633521367755971904020618972345631152098080⟩
def resval5Tail172 : Box := ⟨185010484599370036530588920629055845638920600495,82758602371487040123627999874888889926818344559⟩
def resval5Tail176 : Box := ⟨203421179077479928085872731610451378673733334810,81758211021489711976651121949694126290951026618⟩
def resval5Tail180 : Box := ⟨223663951731593149753215843397000457991925321000,80057756615090056582603416887601264374012279628⟩
def resval5Tail184 : Box := ⟨245921115643216677930872931854665141132189660702,77548529512465929057557288298769318608980083446⟩
def resval5Tail188 : Box := ⟨270393126165363106804594183100690219816968685828,74108463486273860041787002188818647540213180539⟩
def resval5Tail192 : Box := ⟨297300386289519726514071862663119265385286056701,69600641519085788752701840628102256210934559724⟩
def resval5Tail196 : Box := ⟨326885231667623427327172119479158885418789826689,63871642177679775586297089678697250450992150233⟩
def resval5Tail200 : Box := ⟨359414113166803498255705669758557868755020994813,56749710001894908997551128883852009308569358152⟩
def resval5Tail204 : Box := ⟨395179996613699664974572700532679215942447603312,48042731652247207801248043726549594588528051814⟩
def resval5Tail208 : Box := ⟨434505001341276971292025090950314316625196984473,37535997695513209375764456178384624166570379668⟩
def resval5Tail212 : Box := ⟨477743301393976153088423790655410167945094051633,24989727848684105992648285158507616898009326815⟩
def resval5Tail216 : Box := ⟨525288708341736712852798578012470496763484668231,10136139538841633231088285554835488382370830172⟩
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
def polyval5Tail5 : Box := ⟨5460523555628965422589317515079002466995572844328534702266,3927742966127913297540508014938705248296434662769422541956⟩
def polyval5Tail9 : Box := ⟨6003906907613748275498392628471426217769445909600808994079,3994781023566210899097465125296512365323224687208960554764⟩
def polyval5Tail13 : Box := ⟨6601365456794753292769856228880470226531707046817229243052,4047435561295833936660011729450895075946182506346158611409⟩
def polyval5Tail17 : Box := ⟨7258278078944495336903843700281589407074745313600884310820,4082906275001609104102403179207667876138142146965751342280⟩
def polyval5Tail21 : Box := ⟨7980561145431119752467447150047515376240771407675023093309,4098025197921995765958454106083293620317625457508325783705⟩
def polyval5Tail25 : Box := ⟨8774719775578869538100115059908653572529654065924819527723,4089214316372820257032515486540662734508734029103227243607⟩
def polyval5Tail29 : Box := ⟨9647906423724980258307423675926193148959304383272716822705,4052438601596758382111231203156407862080987467274809227820⟩
def polyval5Tail33 : Box := ⟨10607985296580379829149673862833478216640707928042384263169,3983153966974470504421867624057598223468545767592203696702⟩
def polyval5Tail37 : Box := ⟨11663603180866967552370518772541638790325929000712610270164,3876249619551991898742154319946704338927400140324843895102⟩
def polyval5Tail41 : Box := ⟨12824267319128370832416239907383287810056399461056477526425,3725984220301820939565952677450210196590536019930346490870⟩
def polyval5Tail45 : Box := ⟨14100431035089394675458119011113608683953427159280687402254,3525915207458456758950287045203875158465433137961094744523⟩
def polyval5Tail49 : Box := ⟨15503587879734368913340457222150519843438597590404748460637,3268820571096791898375370075686522230882540001420997341184⟩
def polyval5Tail53 : Box := ⟨17046375146015000487591816535786123446778543274679124096456,2946612294239550036939786802757871161247417325862723601572⟩
def polyval5Tail57 : Box := ⟨18742687684475302940069979529344340572277648493207403001218,2550240595512039769193971088233937620917967256728350629977⟩
def polyval5Tail61 : Box := ⟨20607803044854644358358120988059568924238320216824340787939,2069588019965255603874216552699893438352229696552851916377⟩
def polyval5Tail65 : Box := ⟨22658519070750828671616808065613626745537860922747588073948,1493352327342769798631018857693987956128275935743417298618⟩
def polyval5Tail69 : Box := ⟨24913305317776108743186653620492181724770278953716543186296,808917014227075748950743558742826748407292625960848024545⟩
def polyval5Tail73 : Box := ⟨27468750000000000000000000000000000000000000000000000000000,2⟩
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
def resval6 : Box := ⟨85231742404591518247764409178187736737589354607485062381,12438287890572127736458136563715473280499911644419532434⟩
def polyval6 : Box := ⟨15509524977745470772871108755537947141446146106803934234839,3853963151251886241675502541418029176367347448432626647056⟩
theorem cell6_lo : Holds Q cell6 (63/64:ℝ) := by norm_num [Holds,Q,cell6]
theorem cell6_hi : Holds Q cell6 (127/128:ℝ) := by norm_num [Holds,Q,cell6]
def resval6Tail4 : Box := ⟨-32076283517215256682324957169092983431634589788664819523,12169360810535727799735231933260209484982179953856846756⟩
def resval6Tail8 : Box := ⟨-33625023528343961494574964498541823217957063939242075085,12030789068261520828002784272521322423631793706046351449⟩
def resval6Tail12 : Box := ⟨-35248478346760376884236451132550797828341512712351959839,11862385932802679308292522670394829983154098872617271732⟩
def resval6Tail16 : Box := ⟨-36950315424018943935064619962434936925569310161219158815,11661973058372608218022938796700175892683504051272918027⟩
def resval6Tail20 : Box := ⟨-38734319152808093162530016230275322933331404412663169267,11427243952289006388792205970394172575700867894549251608⟩
def resval6Tail24 : Box := ⟨-40604456633577714629161047140572848354153661462228758420,11155756507962709867351366191816097996947475035948230988⟩
def resval6Tail28 : Box := ⟨-42564886502944175152372513270646759557947309428682331408,10844925684217490787057603781851426387805201066644423011⟩
def resval6Tail32 : Box := ⟨-44619968181282905128517230075811538776273127379957099580,10492015806636719717327004962958404564293627277546817263⟩
def resval6Tail36 : Box := ⟨-46774271566799249805877451907105157807908880364872846355,10094132471790586018806547003458350109923582987876183176⟩
def resval6Tail40 : Box := ⟨-49032587197640188673592310729775952089055395411826525383,9648214034360220577685372198277456736275888765706423917⟩
def resval6Tail44 : Box := ⟨-51399936904644496823448737208195779957460933530916750168,9151022656184556154516362452889336220116124256609912379⟩
def resval6Tail48 : Box := ⟨-53881584978419936843186375809620433834369383063373303084,8599134895216462884579962917429388949289094592394683256⟩
def resval6Tail52 : Box := ⟨-56483049875579781672805835497555721620829563073843563883,7988931811284370464242444874437721842021785455254882654⟩
def resval6Tail56 : Box := ⟨-59210116490169884141877378959101566204020698343382194764,7316588564411742917699112582737553795840601988138231168⟩
def resval6Tail60 : Box := ⟨-62068849017569156101832175520193011209694116359419690719,6578063480246495916912952831341227850729523978764503952⟩
def resval6Tail64 : Box := ⟨-65065604431407583982509946925623762143065460321824429067,5769086555547104650683722416584801630985706736151008722⟩
def resval6Tail68 : Box := ⟨-68206903024109056314079548951029923151312705838191599504,4885142961866073538063547753510824767085308705796498834⟩
def resval6Tail72 : Box := ⟨816901804609508054062079272414888922772451562894930618965,719724467745854881594905802526892056317220715942805353⟩
def resval6Tail76 : Box := ⟨-430086851855386457670715793755398095504222249121898089,165373669230399673318611247527547861302831358326410515⟩
def resval6Tail80 : Box := ⟨-450823623325267172309483529363518728608491468522245520,163586205003033117639156134781651091125293642311236308⟩
def resval6Tail84 : Box := ⟨-472589904906138275984229144933662945051352769452083460,161401175664522501031224110811655018399973902287911632⟩
def resval6Tail88 : Box := ⟨-495407089085365958290457119341470962936887613650100438,158789300117609715041105951348073857996061517884853674⟩
def resval6Tail92 : Box := ⟨-519325913161824950651761621372724780896391809502595529,155719728271371728698665244957973341590154225617779457⟩
def resval6Tail96 : Box := ⟨-544399565576041411758314732992941088290916627057657869,152159794180028437989372610825467969507584902229052639⟩
def resval6Tail100 : Box := ⟨-570683802768439452101196643271943773851162516589075963,148074917951041595092954225065629466941174210662083895⟩
def resval6Tail104 : Box := ⟨-598237073164519837497673157998604365967624527377300202,143428502603810300718292224633754708814343291427128199⟩
def resval6Tail108 : Box := ⟨-627120647146993694807512364916173339230032054401169256,138181825606516730221203818473032616347102557430720459⟩
def resval6Tail112 : Box := ⟨-657398753303122414390750731477271358500347970872002338,132293924823259387735969094725588028588318109245748540⟩
def resval6Tail116 : Box := ⟨-689138721250235852431896759761641734216465394555595945,125721478590346389990037111843731528355849551184979289⟩
def resval6Tail120 : Box := ⟨-722411131357030829938530861632120660315818970330373020,118418679626689651816463268847982967014048843357277375⟩
def resval6Tail124 : Box := ⟨-757289971693586133790052307698336993995478760541316248,110337102468625097589293022099994492204598752784120666⟩
def resval6Tail128 : Box := ⟨-793852802559104874548368799398621690170392317491188913,101425564104150809232348816703834533060917050941017083⟩
def resval6Tail132 : Box := ⟨-832180928953269036098345794187074111628676910427378243,91629977465487722169812109978876435075190025443396072⟩
def resval6Tail136 : Box := ⟨-872359581397796029010834041320711425951862842148239797,80893197420750521788742502961022743074913136426569212⟩
def resval6Tail140 : Box := ⟨-914478306511296736158368869035668640537923479187363339,69154850411845091542120538508826545537113171865864595⟩
def resval6Tail144 : Box := ⟨-1059081947671585076556471272542127159342098578081931559,53792841590526004463527076938917093873259640849271421⟩
def resval6Tail148 : Box := ⟨241447593819534313893135649167980864028428345520,77759371825703233476221418341373195100455227500⟩
def resval6Tail152 : Box := ⟨253038495395367257311161281294729540164558314483,76275681999120523223055063704057884860763381739⟩
def resval6Tail156 : Box := ⟨265255483846650634421710348845313706072933954927,74553941932901478898675468506499473781586737023⟩
def resval6Tail160 : Box := ⟨278062323702297112243867932535500904212070921679,72576835388200054356501496975812875616435743057⟩
def resval6Tail164 : Box := ⟨291487492516909884855512992261858235990620868486,70326543705785139277722655381581536369646744673⟩
def resval6Tail168 : Box := ⟨305560843923472770551397678880239565381577576661,67784212992920349853140221555201569670802992354⟩
def resval6Tail172 : Box := ⟨320313672923061768074245419894677632609803891191,64929898551078039905232837347986899767733377512⟩
def resval6Tail176 : Box := ⟨335778785475400813673441554723972542142831815239,61742506457456306230298242465817687177480283200⟩
def resval6Tail180 : Box := ⟨351990571449682613628496212063618317095104869924,58199732142639406812736712899399717586105189719⟩
def resval6Tail184 : Box := ⟨368985081097539599754488095779808292350834605409,54277995813521580460099902270421891547500346377⟩
def resval6Tail188 : Box := ⟨386800105218217885090777305681194457946445960144,49952374563150278302696891880519368567980558851⟩
def resval6Tail192 : Box := ⟨405475259194218023920199113634397989397520171383,45196531001307638454192039443083506338533168653⟩
def resval6Tail196 : Box := ⟨425052071084273165184031357949368377865784163129,39982638231427327540250110263335283692724978601⟩
def resval6Tail200 : Box := ⟨445574073969557515957151492483892967816784491616,34281300990818892024849711317174443087634038157⟩
def resval6Tail204 : Box := ⟨467086902758476038341291604603254878030252268454,28061472762123830694448823504131369780038893259⟩
def resval6Tail208 : Box := ⟨489638395665333915615270592869693457119929881159,21290368654433952079607993820870810979074194891⟩
def resval6Tail212 : Box := ⟨513278700679777505994771368991981350827513905671,13933373837834371230463493296010911813909252676⟩
def resval6Tail216 : Box := ⟨538064730312846651802271541245591040733895426492,5953769918101887855478630518133935782303634154⟩
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
def polyval6Tail5 : Box := ⟨12289186685604391433240934922028394985439076406894555734917,3782091165059451145529555178064832939026913183180919390071⟩
def polyval6Tail9 : Box := ⟨12882520624119546308978249137486382046492067958454972219024,3700947071911963090468446545461374204696043967102508867682⟩
def polyval6Tail13 : Box := ⟨13504503537079012343191104281880643955265800830366308434505,3607479611531799374714827707420461010340564824737688228156⟩
def polyval6Tail17 : Box := ⟨14156516500679548803574839371425181160730257073296930363462,3500825898934283346178395314916258651945463681373007717994⟩
def polyval6Tail21 : Box := ⟨14840009400105795525138781387297977855248909883169594452043,3380072860933258975673481058109648697545221297154752890269⟩
def polyval6Tail25 : Box := ⟨15556502122867371955956086275365875503762247354674459392446,3244254530426630080237097055651639156268340285327464518831⟩
def polyval6Tail29 : Box := ⟨16307587938391183262383760163382927766026479651791854065577,3092349211849821850610449676048990289797549022423544922337⟩
def polyval6Tail33 : Box := ⟨17094937040984638755619999206400005530101551649722021755596,2923276500828374095952831803913909932833297265270420510832⟩
def polyval6Tail37 : Box := ⟨17920300263857360850002064153464169484519362961523630856758,2735894150702772916294318476392881138219269861975862464713⟩
def polyval6Tail41 : Box := ⟨18785512972460134476426700831256168703672232286628448030985,2528994778238072475976932659806072868122253686444922465556⟩
def polyval6Tail45 : Box := ⟨19692499145798739082742965757648871373994474049315269828458,2301302400450324343675569940127449209002578270855715870864⟩
def polyval6Tail49 : Box := ⟨20643275654798306755515134135563042377139254124090921925000,2051468794082623413080206009932379851156085573470383600999⟩
def polyval6Tail53 : Box := ⟨21639956747232032511895496535002350573081172830372183910238,1778069668844788304813866164370631640210923717602981331935⟩
def polyval6Tail57 : Box := ⟨22684758749187401341160212950917671666274731742777006865244,1479600645091365079321971601361877182038298052657869508310⟩
def polyval6Tail61 : Box := ⟨23780004993524627530462843374348452300219722007712995558292,1154473026151773316681816191597303165011410640712793697529⟩
def polyval6Tail65 : Box := ⟨24928130986301989526420707293232401811887672782540741859371,801009355042163546764852729646328346788433238116754847959⟩
def polyval6Tail69 : Box := ⟨26131689952426030459463079951725971688157915370551570801464,417438739665297060864188592153112850429166464666434801154⟩
def polyval6Tail73 : Box := ⟨27468750000000000000000000000000000000000000000000000000000,2⟩
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
def resval7 : Box := ⟨66972835561153489562219378234360013569480965063336282415,20083269880011226539221934594826196892510972546067010094⟩
def polyval7 : Box := ⟨24452619661589932258757827796773968699250218421382388204563,6731405723923425769414919275615301285184600220327293236434⟩
theorem cell7_lo : Holds Q cell7 (127/128:ℝ) := by norm_num [Holds,Q,cell7]
theorem cell7_hi : Holds Q cell7 (1/1:ℝ) := by norm_num [Holds,Q,cell7]
def resval7Tail4 : Box := ⟨-49624000044422765178882750489093472521632689142071330360,19154256937045788985249919156011675090033903414817219165⟩
def resval7Tail8 : Box := ⟨-50407064879822152697095048658124302061161987148931847446,18371248939359679458262027668680513409100535216421408381⟩
def resval7Tail12 : Box := ⟨-51202427286391445089994258039250042736949474991969847830,17575886539437915653015873008595030404466966277484049956⟩
def resval7Tail16 : Box := ⟨-52010339541047165590247501995867521440627860799622054061,16767974284788014721689761407646221001195998518095172136⟩
def resval7Tail20 : Box := ⟨-52830999672034181842036131881014914832392513725433601595,15947314153801020619778815523688223228361460896358992570⟩
def resval7Tail24 : Box := ⟨-53664608825398929154591429627869616274239725746915099273,15113705000436273586638806581407347966196255907482231457⟩
def resval7Tail28 : Box := ⟨-54511371321022716083160437223880081993881250680340644423,14266942504812486667760576069188004124020902901711283401⟩
def resval7Tail32 : Box := ⟨-55371494702706957644950488936071448468583153220374936240,13406819123128245106725716982664865966177429455959896677⟩
def resval7Tail36 : Box := ⟨-56245189789042749980609532538651836047857813557688250620,12533124036792452771127903922847608243178891480392064886⟩
def resval7Tail40 : Box := ⟨-57132670725083083340702249583383094803676718688640158045,11645643100752119410886727004552938775389309157562840512⟩
def resval7Tail44 : Box := ⟨-58034155034830379721893411478317037724388924278604664031,10744158791004823028806359212724532796765777061731437358⟩
def resval7Tail48 : Box := ⟨-58949863674552220228811191044728237970231308904895540201,9828450151282982512399263258611055931938863589202043148⟩
def resval7Tail52 : Box := ⟨-59880021086938329812839112563164383695406964540014514873,8898292738896872677267619961771483029624984079401159682⟩
def resval7Tail56 : Box := ⟨-60824855256112076586521021630905614577665284508002124480,7953458569723106370694878802059363455169774252660116196⟩
def resval7Tail60 : Box := ⟨-61784597763504815318427612352279632242938205153198655387,6993716062324800418323931420068640908324001786384933724⟩
def resval7Tail64 : Box := ⟨-62759483836601260006801571717032701227075295933152680535,6018829980845967945967985289121267966691004506113467256⟩
def resval7Tail68 : Box := ⟨-63749609870837478981897595611046214739353378858600485902,5028556996571580028260617413632742429383808575669497092⟩
def resval7Tail72 : Box := ⟨816716065028744817987154186012776847548420967663115421862,821428393274560559982683639014361361619735418389205000⟩
def resval7Tail76 : Box := ⟨-667631070481777568077261533777802537020438924095397451,259957116142070085618611371568679538522272941215575505⟩
def resval7Tail80 : Box := ⟨-678138053633084844143168738689554446532741601924399995,249422979153367939211556738512663915272968126541956377⟩
def resval7Tail84 : Box := ⟨-688838248899257250527167899220854370283751242791011104,238722782450732762797309831064276049555990365220584809⟩
def resval7Tail88 : Box := ⟨-699707281720763215318895602822338703064704823286164527,227853749628431796344647517879187978091725960016657895⟩
def resval7Tail92 : Box := ⟨-710747814709712879184574226530905701880157659746058404,216813216639479991407821540974505999532561664654956931⟩
def resval7Tail96 : Box := ⟨-721962553930133804474697318013618607545674317006098010,205598477419059045588630643429816163168831850989409667⟩
def resval7Tail100 : Box := ⟨-733354248145250603916142459842766118421892195606527812,194206783203942245567669680836856903780109751770211788⟩
def resval7Tail104 : Box := ⟨-744925689490442634626068847817917530851325827892820985,182635341858750214816199339203162152728517176045032817⟩
def resval7Tail108 : Box := ⟨-756679714157602003609337037585578465686903597451595602,170881317191590845826762617179944860265261160203895966⟩
def resval7Tail112 : Box := ⟨-768619203090291932562343515495880128409398156750318153,158941828258900916873345390776087070334206197261812385⟩
def resval7Tail116 : Box := ⟨-780747082689873896840967677265218732143293107431353467,146813948659318952601962174386545952254896069560180307⟩
def resval7Tail120 : Box := ⟨-793066325532776595448486617266558856835361531865491117,134494705816416254073328919762312753527941056397093096⟩
def resval7Tail124 : Box := ⟨-805579951099082557793253789899608699103454519572926595,121981080250110293480405602353426927047016055061656862⟩
def resval7Tail128 : Box := ⟨-818291026512611072768174055344479795205563348966617705,109270004836581885186522297286241600430200793717859823⟩
def resval7Tail132 : Box := ⟨-831202667292702134273837220657520160514236194113618241,96358364056513119675552674292169160749502829857041810⟩
def resval7Tail136 : Box := ⟨-844318038140792430465537744930844398042703726538027775,83242993230230053713745806551401579583912609067894883⟩
def resval7Tail140 : Box := ⟨-857640553300968064671170869196126259281176135570572170,69920669339205480224772900590010942884550928830240729⟩
def resval7Tail144 : Box := ⟨-970852334899274960307798735441159000802399091440217808,53853149859743118399444421929818119268881456889740039⟩
def resval7Tail148 : Box := ⟨418986781556687123982105068315928122288937696301,133753790303449195852044740337074120812522875291⟩
def resval7Tail152 : Box := ⟨425533499428320445995653990748427510703693204476,127143206572035947714674482820250310625220937926⟩
def resval7Tail156 : Box := ⟨432247901267090919419544465502970174661791363633,120428803622777759418402472723664725248446466313⟩
def resval7Tail160 : Box := ⟨439068249343742651885061107900760648760114123273,113608455545780139730263878401298225373423971250⟩
def resval7Tail164 : Box := ⟨445996214248379773298832723268586908014585086445,106680490641142426668755214385677860329896948439⟩
def resval7Tail168 : Box := ⟨453033494043792716645108367741736369380621823481,99643210845729479495689309408927837535886168494⟩
def resval7Tail172 : Box := ⟨460181813586487794698114682944059114032230649554,92494891303034401366866162834380176752111414041⟩
def resval7Tail176 : Box := ⟨467442924949117354110507091634484250804391407601,85233779940404841950507965858238969812928134900⟩
def resval7Tail180 : Box := ⟨474818607849917009110358039542840859507161062188,77858097039605186950187362898460017115602587590⟩
def resval7Tail184 : Box := ⟨482310670088919440635796541183728254177394100766,70366034800602755424666478211463677020774569253⟩
def resval7Tail188 : Box := ⟨489920947991051124011846164813499770749861026268,62755756898471072048713260670832738090363752136⟩
def resval7Tail192 : Box := ⟨497651306856220586096473697475995762951193808602,55025398033301609965106572306480254747253347969⟩
def resval7Tail196 : Box := ⟨505503641416508509715818669252581832596781002094,47173063473013686361546800426122541894177110402⟩
def resval7Tail200 : Box := ⟨513479876300571744506500314696705561317424915088,39196828588950452166205007156623786421317663227⟩
def resval7Tail204 : Box := ⟨521581966505375122377633841749907733285303248729,31094738384147143214175709493218051683035048482⟩
def resval7Tail208 : Box := ⟨529811897875399590281599458090303320876922156570,22864807014153836686369633914226297712925286761⟩
def resval7Tail212 : Box := ⟨538171687680032882069693219140353875938763484599,14505017295625207500240636907937025635623977564⟩
def resval7Tail216 : Box := ⟨546667695778921259073776258343031687275460039421,6013144381336424974032738326647505826352915683⟩
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
def polyval7Tail5 : Box := ⟨20992741480334896956423314964735141706179259575192947075250,6403074462865077094217778961803243630079764445759771884224⟩
def polyval7Tail9 : Box := ⟨21323979439059745952613458411373396799333186295815052907888,6071834463677085099475879133460565201821520354445936784696⟩
def polyval7Tail13 : Box := ⟨21660445993670258586512433911024656590593025077351504119780,5735367908872749826450605994027618027578164469965369162585⟩
def polyval7Tail17 : Box := ⟨22002221582971410184104994322790217120110263032684350717645,5393592319571449026494718400644289160867197902665583635284⟩
def polyval7Tail21 : Box := ⟨22349389976902694862564353024369219350606034768184604793340,5046423925640163838916854622028794152644553566171609755735⟩
def polyval7Tail25 : Box := ⟨22702036267385940440763506487422905414005624670887670909261,4693777635156918254864877018525542509215860728115059364826⟩
def polyval7Tail29 : Box := ⟨23060246888990532722387138246428302230148410037162395275474,4335567013552325973050664758464474533630187633494619702839⟩
def polyval7Tail33 : Box := ⟨23424109640118620096274963099511723926668065485950773521831,3971704262424238599147591090443762858273412299598227787029⟩
def polyval7Tail37 : Box := ⟨23793713704524741334163814760179425804865888792073146429615,3602100198018117361256332355145783892917058324930623800730⟩
def polyval7Tail41 : Box := ⟨24169149673175007513443032197835671710305179477987849535137,3226664229367851181977112304751115923369678991747763928399⟩
def polyval7Tail45 : Box := ⟨24550509566451195346258514148882646258815139779382104132646,2845304336091663349165707454095607899876087003130216596661⟩
def polyval7Tail49 : Box := ⟨24937886856705194194232920043775366299940974231783885123773,2457927045837664501236458025305390970925289108986189052705⟩
def polyval7Tail53 : Box := ⟨25331376491169334926203541875169140177047303441945995306782,2064437411373523770312891116997456740952896243208082530346⟩
def polyval7Tail57 : Box := ⟨25731074915228216070044506150463118672588737947607165235679,1664738987314642693095297641861118854864138562214027712915⟩
def polyval7Tail61 : Box := ⟨26137080096057746318152879470548338004740390243243312549078,1258733806485126886702078386714828078923124359689447626251⟩
def polyval7Tail65 : Box := ⟨26549491546652332206303085642818098090285832576851100864423,846322355904976910937348639948059635591599910269961346554⟩
def polyval7Tail69 : Box := ⟨26968410479072446410976310832011322356486481363996453134774,427403547327374266310945394572605516509951164923295542203⟩
def polyval7Tail73 : Box := ⟨27468750000000000000000000000000000000000000000000000000000,2⟩
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
def pend : Box := ⟨1031180014393884997364184635666488574324134673061137833626435,4010991628360663988111405900695660300145580571847814631⟩
def zend : Box := ⟨1003781802029446654003945312500000000000000000000000000000000,2322282242280212187500000000000000000000000000000000002⟩
def betaquot : Box := ⟨428755523512387197632738052069877491013102212248852921199940,394781920366610081604205930830165446289212480402045837⟩
def crit : Box := ⟨141481125307912884713995081576176421282676941407453447703,9981573989961352001140497612522093103426228150146849684⟩
def subsonic : Box := ⟨456420863087444839098377978445120633184755621493146650962,5034138745461010242862405234589763612874394138761024373⟩
def pendTail4 : Box := ⟨27394190977085089270677653467852022820975781624918323434761,1587535454077118897266369947146735774534821200143980008⟩
def pendTail8 : Box := ⟨27394226493999132630638376710838012459620091691602692179624,1587407024835894117323506018865389502872846797288675956⟩
def pendTail12 : Box := ⟨27394226495533096217422398075558597423796245278661367504252,1587407009018933634689072923152438179463912051053672869⟩
def pendTail16 : Box := ⟨27394226495533851013107766279512258514757716771922382137349,1587407009005898492461073264997473329837205120092363369⟩
def pendTail20 : Box := ⟨27394226495533852829487640659405040030416630858141880921749,1587407009005850658586985740104397964867724100955504350⟩
def pendTail24 : Box := ⟨27394226495533852844989031441240140624621201246175465194736,1587407009005850041421252229620962801426752227474511475⟩
def pendTail28 : Box := ⟨27394226495533852845375040981888447720650922716886007141408,1587407009005850017358514686128035935187038194427772590⟩
def pendTail32 : Box := ⟨27394226495533852845399037416843308055390923504427981976546,1587407009005850014772547731173256310978561236384984262⟩
def pendTail36 : Box := ⟨27394226495533852845401982486207815140260403432006026352860,1587407009005850014045849821533151580298682910531996158⟩
def pendTail40 : Box := ⟨27394226495533852845401934380334394496297796034672007428170,1587407009005850013524746329104840152239720601808959409⟩
def pendTail44 : Box := ⟨27394226495533852845398658862279446004852684677937749037266,1587407009005850012572407042088265371838647615229104458⟩
def pendTail48 : Box := ⟨27394226495533852845370670069258212636696739901962566312636,1587407009005850008041015369911681976231978928217744654⟩
def pendTail52 : Box := ⟨27394226495533852844874052522639710658954601836953036178188,1587407009005849949152790068717948044881604100778086054⟩
def pendTail56 : Box := ⟨27394226495533852821466484678807640159059438042790188492896,1587407009005847730814137065510966844747725874079260173⟩
def pendTail60 : Box := ⟨27394226495533849261325953378338892726976002462941077121351,1587407009005598834180129056051965997221296604933307762⟩
def pendTail64 : Box := ⟨27394226495531560194240120363207404678159486780771792041592,1587407008885810100793804514600193734928331174358371423⟩
def pendTail68 : Box := ⟨27394226485224326113002741460018053789839135949691960671914,1587406607747397339066935320015969079792619420016455302⟩
def pendTail72 : Box := ⟨27392931927763191422139363642088793539582333493557129100904,1553569019841857759788404522388787184664316339682663480⟩
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
end SepticProfile.ExteriorCertificates.C23

end
end

end OAI
