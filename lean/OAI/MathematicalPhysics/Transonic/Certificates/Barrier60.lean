import OAI.MathematicalPhysics.Transonic.Certificates.BarrierData60

namespace OAI

section
noncomputable section
namespace SepticProfile.ExteriorCertificates.C60
open SepticProfile.ExteriorJet SepticProfile.FixedInterval
def cell0 : Box := ⟨250000000000000000000000000000000000000000000000000000000000,250000000000000000000000000000000000000000000000000000000002⟩
def resval0 : Box := ⟨132945879876379992244561249422314789030444366367212313078,312436130447502679951510642947048890882027750639029438⟩
def polyval0 : Box := ⟨3924687973416829428877709976437352745710209753270887558253,14926321337896992683631886521167021257388225557052115901⟩
theorem cell0_lo : Holds Q cell0 (0/1:ℝ) := by norm_num [Holds,Q,cell0]
theorem cell0_hi : Holds Q cell0 (1/2:ℝ) := by norm_num [Holds,Q,cell0]
def resval0Tail4 : Box := ⟨77150586029872096724978789223910233928949024849334,2183707934213084010230282262295202527850299375286⟩
def resval0Tail8 : Box := ⟨10531972083565956411118918140498856346304378620,548817742574999698230798080778233137150088983⟩
def resval0Tail12 : Box := ⟨10797930001953001522435214258830574169841183,858295732280229130808848288043955633559340⟩
def resval0Tail16 : Box := ⟨48663203815925354558623564687229933774205,33748091155519265568457541989644279676208⟩
def resval0Tail20 : Box := ⟨744724417058589286807847483671005626774,451744402728390055190221620585405044630300⟩
def resval0Tail24 : Box := ⟨33205751134827435043426024883734283255,7226035135462659012252577920336252952080955⟩
def resval0Tail28 : Box := ⟨3924104501736313362947143242214897024,115616447107954418194736011743184627091161042⟩
def resval0Tail32 : Box := ⟨1158593564453122544660466168465060673,1849863134911813122830393746578114910043833341⟩
def resval0Tail36 : Box := ⟨203189936457070664569171466477032926,29597810150926835411477140886427952132839292490⟩
def resval0Tail40 : Box := ⟨-160315873446254999018670674411108028618,473564962260292287176018108855487859901627219992⟩
def resval0Tail44 : Box := ⟨-41405921841132307716396981927927848863085,7577039357335467104531839888357865840627724676227⟩
def resval0Tail48 : Box := ⟨-10601428660456724158008543841892890397374783,121232619778445755483539335769380221975221932908798⟩
def resval0Tail52 : Box := ⟨-2713980874206195475570488647759267397190481146,1939719372096251857701364794297636065004662634738794⟩
def resval0Tail56 : Box := ⟨-694779431043266789013244520795885678112718848615,31034858597691527631421864753934032573331267235411796⟩
def resval0Tail60 : Box := ⟨-177863520238834294840452945908174313227851227768912,496390990474880050447374275190007667990468580200491102⟩
def resval0Tail64 : Box := ⟨-45532971478307853945071366988928743982300497167180195,7899568627715349078771186238545542298261029032140101150⟩
def resval0Tail68 : Box := ⟨-11654425538074797591665093582372029403199434285888699722,115466043851413661992159408193992198550851337886430939672⟩
def resval0Tail72 : Box := ⟨979622804574474291626655949506221347771438523148175446951,2887154674115333531543845716559051394712783063223424321⟩
def resval0Tail76 : Box := ⟨-37866043844666023867839786869547030660503480798201,792486500288949514342373329668223709151299330093⟩
def resval0Tail80 : Box := ⟨-2310693358852936203456946290445896191640353368,103506165578246284354618276464716046291254840⟩
def resval0Tail84 : Box := ⟨-1474052856918841551909984341298150076589300,104413362065558258414401184197983276265382⟩
def resval0Tail88 : Box := ⟨-4593656456502078025882840071803581532257,681303950526894994771848665630275958553⟩
def resval0Tail92 : Box := ⟨-51450030396448447651457759247234767866,3347064371990243153446441053592445140950⟩
def resval0Tail96 : Box := ⟨-1738187624335247109249730702101354482,53434659928681120644591422537655235245698⟩
def resval0Tail100 : Box := ⟨-159065981191126023613889404819199220,854949044186919675262807021435368694071728⟩
def resval0Tail104 : Box := ⟨-36938623376988737785479273898440158,13679184009974368349682969079999004423662650⟩
def resval0Tail108 : Box := ⟨-23275350060412556424043808746615696,218866943931765665796342317934623553746764305⟩
def resval0Tail112 : Box := ⟨-615679656498332318893001895829919733,3501871102293540959992342477757297011751076677⟩
def resval0Tail116 : Box := ⟨-150333029849175161786371037370056132256,56029937495876913108314386811576424751911050745⟩
def resval0Tail120 : Box := ⟨-38461349402714286461321800356543219478166,896478963877213447346375235087112980617518031644⟩
def resval0Tail124 : Box := ⟨-9845915078267200436385511024722892839995199,14343654191502701269917552572570829290991359772673⟩
def resval0Tail128 : Box := ⟨-2520550775588538018198515176129398897622113708,229496104048448866376915270679507316637654539058488⟩
def resval0Tail132 : Box := ⟨-645260973601222741676305514085825352038134629494,3671332732777462288388369019677183871535997875557865⟩
def resval0Tail136 : Box := ⟨-165187062875097764022359757063252292412362765668391,58586461025997295864560616768185435037565572631708920⟩
def resval0Tail140 : Box := ⟨-42291123169567369162768910366691254408725620028604050,897737068924813930116343033275869669919439870030969765⟩
def resval0Tail144 : Box := ⟨-11947660945947347245704288959671353939046157293812518809,3675957002928014778175336571534038433906969618360997913⟩
def resval0Tail148 : Box := ⟨107202660391414311918771134005757239328268610,1793177614476514042757710351037688799979093⟩
def resval0Tail152 : Box := ⟨2159607194163459853336856214520026330611,85637769145763773499184834101919679728⟩
def resval0Tail156 : Box := ⟨774559848528671181728339298147128183,49740881630129199096205492893845995⟩
def resval0Tail160 : Box := ⟨1529656892317851495768057341383956,146320422897018634357112360224744⟩
def resval0Tail164 : Box := ⟨11497701571558972545952764250641,49865858515416888827283863866762⟩
def resval0Tail168 : Box := ⟨269129216894825032384766320254,773784605254190310558695465101905⟩
def resval0Tail172 : Box := ⟨17356028958245727685905373291,12379780777119200393973592696548609⟩
def resval0Tail176 : Box := ⟨2858722039738962369183059352,198076424229013737979402374292914738⟩
def resval0Tail180 : Box := ⟨1161547612422128767288735133,3169222772116896566679921267311437119⟩
def resval0Tail184 : Box := ⟨3911050278518025399328326094,50707564344117344213986524505369999205⟩
def resval0Tail188 : Box := ⟨719805015827906377431355239464,811321028834710763614496187819820305592⟩
def resval0Tail192 : Box := ⟨183627972067159079299764317139526,12981136289218074806924994015924992680625⟩
def resval0Tail196 : Box := ⟨47005248115145489174937450358055570,207698136560224079955276447949705730705718⟩
def resval0Tail200 : Box := ⟨12033297824063715484451506717581592721,3323158903752343201248604687685657363762588⟩
def resval0Tail204 : Box := ⟨3080523152561440163855743893421161649015,53167654470232377495864958160909432767672652⟩
def resval0Tail208 : Box := ⟨788614224821234409778282013427578701454537,849943146004246995341298491192176722944379014⟩
def resval0Tail212 : Box := ⟨201887018815785465956728322376090633934401339,13409822225766518854125251781559370970497360654⟩
def resval0Tail216 : Box := ⟨51781514952632822371736730632716558394302416626,166058297976164992968140041012311480491749055973⟩
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
def polyval0Tail5 : Box := ⟨2443673623105763316026977436839996923154168734286790,59392213868294243425993362769267312314354462314658⟩
def polyval0Tail9 : Box := ⟨267375004599156294738810148365194539557684037767,12867994756255340039404556942471803841308666457⟩
def polyval0Tail13 : Box := ⟨237189252685040078002942137783466676130427744,17726516162996264430498645269991093235888744⟩
def polyval0Tail17 : Box := ⟨936702680320657500494613771108757968290349,508778944601250756249583647890049423696393⟩
def polyval0Tail21 : Box := ⟨12596055378420442458051289820722138165021,6531381350487197649311238248400762863847979⟩
def polyval0Tail25 : Box := ⟨492949466875374716453144864704896887084,104471986583632031651976128523027996207237690⟩
def polyval0Tail29 : Box := ⟨50948105412203239308704089948095823434,1671550165466030666597111381184128788837274542⟩
def polyval0Tail33 : Box := ⟨13132736413978289118293535281124094980,26744802416681009150926453322125461429062239953⟩
def polyval0Tail37 : Box := ⟨14285689568259390032506223850959626115,427916838581733724219081470933100252595841250949⟩
def polyval0Tail41 : Box := ⟨1586936544663707859136107696945199685700,6846669415842811842205061839133627401876105719499⟩
def polyval0Tail45 : Box := ⟨403212848648745137549458620645899061057164,109546710275524374761846530746132408909148029161239⟩
def polyval0Tail49 : Box := ⟨103211827749437870591190257879350611865268313,1752747267647628424221054307324899809908336633251127⟩
def polyval0Tail53 : Box := ⟨26422138263416784868826392300509751059677675146,28043931511613713184833678777902625001902382146661479⟩
def polyval0Tail57 : Box := ⟨6764065689507918128989908970722014075438855752405,448696562874626674835799062490094384204631121747258388⟩
def polyval0Tail61 : Box := ⟨1731600807136156925399093753345781934024898819085398,7177521630324597350397554208956046356044081764691128473⟩
def polyval0Tail65 : Box := ⟨443289938377483824407459046238443917342865838972432695,114424761858526181861518634720392574217657052690829246969⟩
def polyval0Tail69 : Box := ⟨113483743116302363424631447196974787942043145528199821819,1724405948979279095373625526925712744715386603436976753258⟩
def polyval0Tail73 : Box := ⟨29781250000000000000000000000000000000000000000000000000000,2⟩
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
def resval1 : Box := ⟨132673774864991474756934851040483186388937988093069725931,219201958894689534029712729542198045033739393059279589⟩
def polyval1 : Box := ⟨3905361447230842257606436493958180066912628220116596419002,8331313354741240539898880943913255925789250446134179798⟩
theorem cell1_lo : Holds Q cell1 (1/2:ℝ) := by norm_num [Holds,Q,cell1]
theorem cell1_hi : Holds Q cell1 (3/4:ℝ) := by norm_num [Holds,Q,cell1]
def resval1Tail4 : Box := ⟨74847454593535531610385508301268287293838624499216,3600789043076570127957455623698200139442949261130⟩
def resval1Tail8 : Box := ⟨9931010259297090115269055705269865055334535904,7179218211144107053225794244964852289420426032925⟩
def resval1Tail12 : Box := ⟨-357336661653694686099425124193565957150415864,22688724124923985366837264794064990850078008759824⟩
def resval1Tail16 : Box := ⟨-2407310811556170712310742043646049602710665776,71706324873453344090002096605965559409385894662098⟩
def resval1Tail20 : Box := ⟨-15776839169580159013320649887065140118302404592,226619228713389578836037908899905846917414582586014⟩
def resval1Tail24 : Box := ⟨-103395097434554127755782910970349228089294223610,716175140971807707886160956164219987964437713824105⟩
def resval1Tail28 : Box := ⟨-677610110729055403430015341034221051105080057643,2263116281663744595389595399819553742604456892417193⟩
def resval1Tail32 : Box := ⟨-4440785621694194441699031005243068445069485945689,7150265835295168987648615561895486613114467579676341⟩
def resval1Tail36 : Box := ⟨-29103132650340481667817304871760822649006057815808,22583302977901722820168247858406305914034443023439592⟩
def resval1Tail40 : Box := ⟨-190730290137274502095504136673105016391783226018278,71275639639508753348581445331118760191213245934894649⟩
def resval1Tail44 : Box := ⟨-1249970029443644826084733436239861965342982729323534,224619050982770960124815829523071069156162349445732454⟩
def resval1Tail48 : Box := ⟨-8191803584961854623839094508363717860237779179608041,705665843070926246422644930082447348906365620045152200⟩
def resval1Tail52 : Box := ⟨-53685803974405062980750221162050320234763098688819032,2202456881752845136875462650023065059096565944729154114⟩
def resval1Tail56 : Box := ⟨-351835284926564145450061944922336905653541066372577598,6778689746507613265791032724597231983132803744676842086⟩
def resval1Tail60 : Box := ⟨-2305787723262771970369552605349645800605369755866118520,20230192622969006924770022537644409187163882745104123703⟩
def resval1Tail64 : Box := ⟨-15111210370832701858721633988497048635139622461672072210,56113616356087415974332195536470333300088689472381407292⟩
def resval1Tail68 : Box := ⟨-99031902000050770121518975616233879521628460970924837077,126072923548526363472700888106965978936747859931493354166⟩
def resval1Tail72 : Box := ⟨983275027782298061598824996144772943612720233338386233006,1668511695043811645892648513179347284816602307180119013⟩
def resval1Tail76 : Box := ⟨-36996642716463412657283706774221222819516260248256,500991822450678360556804947590609112027419580729⟩
def resval1Tail80 : Box := ⟨-2205476744079711716305778368655458455721609399,79715336114059168634146226509151848230983225069⟩
def resval1Tail84 : Box := ⟨-4749081473241996609339032497396413148343714,251743117725569316757017759070510316917981428380⟩
def resval1Tail88 : Box := ⟨-22124401058677878261707141873730392407377853,795621150592004862612894285580150346890948610214⟩
def resval1Tail92 : Box := ⟨-144967166761199697561784948286119992292139913,2514480679049505870975293278461935011701581220605⟩
def resval1Tail96 : Box := ⟨-950056527506755676384953153514012312848322421,7946508775817568336707043391979155876184987944710⟩
def resval1Tail100 : Box := ⟨-6226290449024589344058028280872341178481490142,25111668290785176915151453341116715395164235946974⟩
def resval1Tail104 : Box := ⟨-40804617085890828086781528342744262595617113587,79344146158172430204126040126862129409907473658701⟩
def resval1Tail108 : Box := ⟨-267417138533916094780598770117909404198380709931,250628229756109586364743444374438812227283115538534⟩
def resval1Tail112 : Box := ⟨-1752544959095787624496285780086930772014714132592,791201598312863889824406627069369167731179893253364⟩
def resval1Tail116 : Box := ⟨-11485478643930082163839014286672299550198080254822,2494641196388436292925584150146739111871757054970827⟩
def resval1Tail120 : Box := ⟨-75271232840860287294501444885853523984838720972735,7845326653681186751265080336605139087768835417052085⟩
def resval1Tail124 : Box := ⟨-493297551545870114573638853175808517113055204208526,24539703176227520896561672126768665475752017624835996⟩
def resval1Tail128 : Box := ⟨-3232874833811676641261915212535822035627908167260989,75883769441620847537735133527092727192382062559895007⟩
def resval1Tail132 : Box := ⟨-21186968511025570331757516125051478225710726963997160,228860697347263960109511554569632372420275256283759003⟩
def resval1Tail136 : Box := ⟨-138850917000624618590384456869485536428831104693449896,651423187579454779825450298807858841580347100229628428⟩
def resval1Tail140 : Box := ⟨-909974909541044370673204825448217198919833564817130569,1587682796754942820157277769287154261458351624580973232⟩
def resval1Tail144 : Box := ⟨-6439777863869590944230666239301046364330686544717973461,1849786560838876338254571058430748742218167254859795091⟩
def resval1Tail148 : Box := ⟨105565482422790842870940921940803524530337813,1213573587202323784612663394508022295771220⟩
def resval1Tail152 : Box := ⟨2074671139720383146661214914630553817240,5084501299757125848833176090715338577466⟩
def resval1Tail156 : Box := ⟨921305659969113035117575384772994986,15901202740440613614191830746754503306501⟩
def resval1Tail160 : Box := ⟨1272971009966095369446754030525937339,50255005960997331636327574287967513728529⟩
def resval1Tail164 : Box := ⟨8333367190360453695879911165676276443,158826321583038845963965342211324880757175⟩
def resval1Tail168 : Box := ⟨54613488201619184281465844126853213620,501941332989188273880520633617462836700496⟩
def resval1Tail172 : Box := ⟨357914954762704170166987830612298718978,1586197175145897590356452137062447478442425⟩
def resval1Tail176 : Box := ⟨2345631447439499336086731921288189268361,5011951937265714484815330745714910265284887⟩
def resval1Tail180 : Box := ⟨15372330253925162110651114131550057650814,15832284183209863536521465205730010962803947⟩
def resval1Tail184 : Box := ⟨100744103552118862064421428517008214158949,49985676482209976559305507518990779810495181⟩
def resval1Tail188 : Box := ⟨660236557039162543508831060888326115787061,157637586528826224261794722571263963350991770⟩
def resval1Tail192 : Box := ⟨4326926300211853520469320555083540812896564,495972366415609617931898775751825495420441440⟩
def resval1Tail196 : Box := ⟨28356944201068476063939081738242508072971316,1552835882160046376565833672773261813269269145⟩
def resval1Tail200 : Box := ⟨185840069516126770316870126600177112605842054,4811510097748635169603991625264120526876165044⟩
def resval1Tail204 : Box := ⟨1217921479581498474872719200086977531240882962,14576172876218757799365151965564363364872342588⟩
def resval1Tail208 : Box := ⟨7981770208892238755042233384533650770978462361,41935367508460506721822661877388392901525421719⟩
def resval1Tail212 : Box := ⟨52309330175013123228547759700629240848776071541,105453476223384079157176558376455252743262583946⟩
def resval1Tail216 : Box := ⟨342858173015921190352017432988213691032548153625,155786306999410787865172425842627375535262162941⟩
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
def polyval1Tail5 : Box := ⟨2375887973722116682188354683933426665504005992688129,128564754619882545708908984883949800755980642991717⟩
def polyval1Tail9 : Box := ⟨256565235341254446585979424648780043558724043531,297960501826887281612454751007702853323915354895187⟩
def polyval1Tail13 : Box := ⟨16902916241562632597449639420665219665619657502,941673495823885817921313558315943425905409594523675⟩
def polyval1Tail17 : Box := ⟨109333395231074449147403044258612150229163337446,2976096670898196504758642231730617203262494130922480⟩
def polyval1Tail21 : Box := ⟨716521796488376816207532481593543713166711265828,9405564180493861926195210278610697501635656450300420⟩
def polyval1Tail25 : Box := ⟨4695797173223113336067833664940982331781110023788,29723796298920066150560236532869051369131721076819382⟩
def polyval1Tail29 : Box := ⟨30774376351716198061886297384856443366253372140040,93925941384139374974183385909327152020323080172794805⟩
def polyval1Tail33 : Box := ⟨201682952858341377301788793132422686033980796373836,296747937228446712378400130990774649475895690931604730⟩
def polyval1Tail37 : Box := ⟨1321749399852363626414372069741458700419267767231316,937185692160815432785572575982731615090090223405927616⟩
def polyval1Tail41 : Box := ⟨8662216866872418129293798949023909157827199366945470,2957484758929806036991946978728488862887870829497785829⟩
def polyval1Tail45 : Box := ⟨56768704458735051554244359591670008575389718793208621,9317720502997433889361950171840903121334140022606037920⟩
def polyval1Tail49 : Box := ⟨372039381540766093208762668000461725179100850452133807,29255975891407125980181882699509752888022905453898250357⟩
def polyval1Tail53 : Box := ⟨2438197290865568781463613596348723491535173194863041069,91200962090303081682205858810144447434528378912241081822⟩
def polyval1Tail57 : Box := ⟨15978969765416934001385861789234664827716131910999714160,279967015439264529063237399621771940897658130282185502407⟩
def polyval1Tail61 : Box := ⟨104719776254719460336459120835154864079885442510587562306,830615683157677129290703940896150065153601204548162303924⟩
def polyval1Tail65 : Box := ⟨686291525750010032804657601070418021116710441310563964829,2269830420119964108148410949770014522698564207036165222985⟩
def polyval1Tail69 : Box := ⟨4497680871354736230707314213012709529284746066990247417254,4845124896646820504903460782861204318721968095899911419654⟩
def polyval1Tail73 : Box := ⟨29781250000000000000000000000000000000000000000000000000000,2⟩
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
def resval2 : Box := ⟨132539891997859101238720279304678780290396403077068523260,194742513474588002247635618586484759523907323090816985⟩
def polyval2 : Box := ⟨3895815396101473240998110155823771148653171460021634684574,7006888279442102957407941306784399311326019731016526700⟩
theorem cell2_lo : Holds Q cell2 (3/4:ℝ) := by norm_num [Holds,Q,cell2]
theorem cell2_hi : Holds Q cell2 (7/8:ℝ) := by norm_num [Holds,Q,cell2]
def resval2Tail4 : Box := ⟨-130192725806478477269244373573948039421034093054885,37357672297185226080148642014027170352902273495210780⟩
def resval2Tail8 : Box := ⟨-467968861677873877212545949393822027480151909650855,63609054965559877957379164055114562307985667850213593⟩
def resval2Tail12 : Box := ⟨-1073822526307044303147119967991433847484161100151059,108238767497334588551722327070378090339321279308648129⟩
def resval2Tail16 : Box := ⟨-2463990536561383041868642957910681063357138164088346,184018462097790028578108358987825019021212664832910969⟩
def resval2Tail20 : Box := ⟨-5653866594545458133768238932189947801159287180246095,312476964721767161551080445223733692712510517061557166⟩
def resval2Tail24 : Box := ⟨-12973348312039870616745992661042529362724387557162335,529743804987259927846705061334948048614047282322921625⟩
def resval2Tail28 : Box := ⟨-29768612967957935659506557510830769351231014216967777,896082890536386948801346638164867667266762075216604590⟩
def resval2Tail32 : Box := ⟨-68306985731175079381614629930303043450071129684394020,1511154804503642353256286514840628858001942328154810065⟩
def resval2Tail36 : Box := ⟨-156737040610563006929536531839796202195181029047531845,2537755043022011839258447084106190931978755999566583208⟩
def resval2Tail40 : Box := ⟨-359648425946355422877612119124598676972348596684626897,4237036111562610245445845706273499760692593479761462734⟩
def resval2Tail44 : Box := ⟨-825248389160755889079359358411830449559863719682183676,7016492496152331729099351944739525358606918461626252835⟩
def resval2Tail48 : Box := ⟨-1893612913834925146407992515722127251361424330600826223,11484050837203145158386275115076441800963933677286960053⟩
def resval2Tail52 : Box := ⟨-4345079511259606703402381658927665368054511925809264470,18476624247279307723604657903194907664576878739405404405⟩
def resval2Tail56 : Box := ⟨-9970208705924413201560281738050189116661116117358244627,28962610367368043437899365384395198300898575954891080602⟩
def resval2Tail60 : Box := ⟨-22877616251206458888591869728202660829321719132280409266,43540054271135727109044411008376081615009426261622840060⟩
def resval2Tail64 : Box := ⟨-52494921656759876681746047959783610155579152968645319221,60810691988442738193404598910302576260011564189559944360⟩
def resval2Tail68 : Box := ⟨-120453989304431923021568847262546834905071672312161899713,72839692456415605023818932700685500111236226460064163821⟩
def resval2Tail72 : Box := ⟨985098912769591860420107050260984761719405083983076173987,1059723064135516364215293390226952169388503148141957697⟩
def resval2Tail76 : Box := ⟨-39020454587583821580524267736656989337212492807042,483665296751109922761298459375890387681338278573703⟩
def resval2Tail80 : Box := ⟨-5601154445673114695171917461731747985483854388348,823630747026302285026591949253539267900123884688493⟩
def resval2Tail84 : Box := ⟨-12847449291421685234693237177439704116220170746517,1401781879178436833600569537318905043077554376207807⟩
def resval2Tail88 : Box := ⟨-29479722341014504924411520383887048664696169000951,2383815456315421280072846123328070535695367689476650⟩
def resval2Tail92 : Box := ⟨-67644098003581207243160178879369052866645635176748,4049330933966591500239199501469755672986258045883769⟩
def resval2Tail96 : Box := ⟨-155215980069322476226374450351525150631331356706744,6868161667140028722277558560153795275075304748283161⟩
def resval2Tail100 : Box := ⟨-356158204188334790473530766148407813493303268259186,11625413991967224125039934862496070585472701302699548⟩
def resval2Tail104 : Box := ⟨-817239734942288491494830285846416259215497325994323,19622793465996140855157106840929795395440189648710216⟩
def resval2Tail108 : Box := ⟨-1875236275661840174554447240101670303913472406603979,32994557973002802274136733805641798549226118827883802⟩
def resval2Tail112 : Box := ⟨-4302912522732900012792321647062150724844432085821628,55183417024343474600393109607324567857841103574772217⟩
def resval2Tail116 : Box := ⟨-9873452438283790333092697922307300013079549369610704,91607599550397938303617652022567249919045572706689048⟩
def resval2Tail120 : Box := ⟨-22655599558676744261210085667527384816731300701953121,150466594920973551954827055495097220795616939762918760⟩
def resval2Tail124 : Box := ⟨-51985482744912270746547721761537771249327258933825245,243353337991717313644794601721653453882399294791421187⟩
def resval2Tail128 : Box := ⟨-119285760203444820359920678051250935850462351794370672,384549229274787604718600894239109143763776792684463726⟩
def resval2Tail132 : Box := ⟨-273712810500217564744982122849485146334383971400387109,585807438105832065809043592149622856931926352070642495⟩
def resval2Tail136 : Box := ⟨-628060738517175102812877222182997701690071740521240329,838242859393887886287661597068373445806125554543544365⟩
def resval2Tail140 : Box := ⟨-1441147834013240827128991045651282112165890112507095793,1060302479705064173044791774170100999924010882274577873⟩
def resval2Tail144 : Box := ⟨-3676688111535234714673824096124071242978737423630174900,931624847901158468242767877618239889231856007353943828⟩
def resval2Tail148 : Box := ⟨105205203318289691721985933544046205755644179,78134005782480091897425872307774483739246180⟩
def resval2Tail152 : Box := ⟨992872707592479189336484061086648304870088,131578993001246209317979042457929957335971113⟩
def resval2Tail156 : Box := ⟨2273574651715418246924615500527146158200625,223884690412088738409608113639812808115802264⟩
def resval2Tail160 : Box := ⟨5216937157363610737118854426647500533978372,380599077334674695598023048994572552825410834⟩
def resval2Tail164 : Box := ⟨11970771102449581930350872418140722290069796,646214316508483341933613531952967819765779123⟩
def resval2Tail168 : Box := ⟨27468101781082721191355084635511526212148027,1095366599949171884990794748287276499119859390⟩
def resval2Tail172 : Box := ⟨63028238448409483069551965051367507412068027,1852478191492082803909433240647761852713229034⟩
def resval2Tail176 : Box := ⟨144624440144076294816706152554838351587976998,3123144963036371999609275671031809830313493876⟩
def resval2Tail180 : Box := ⟨331854882857119286469874089591691286091834664,5242815452597739608402515363196017727029064395⟩
def resval2Tail184 : Box := ⟨761473393891116190817125613191965521389956824,8748668086335082072994392426412754221289085151⟩
def resval2Tail188 : Box := ⟨1747274967334763862575241542028470573223911427,14476606541622548960688020048303879723360200680⟩
def resval2Tail192 : Box := ⟨4009292820953435966484299756048014336530605675,23667932777001230145449790682240469995943628272⟩
def resval2Tail196 : Box := ⟨9199713396379832019339108038963549646590967436,38016411572059281933544268164576211172611599574⟩
def resval2Tail200 : Box := ⟨21109639618540975136170511854973432828793330582,59438985067309345421642402375512454632317456701⟩
def resval2Tail204 : Box := ⟨48438126887739093866981119983490408533018170253,88974270743766127349510286529391124642487018866⟩
def resval2Tail208 : Box := ⟨111146006222542738330651170624782286625947047245,123273477617186597375410526072976898520799581406⟩
def resval2Tail212 : Box := ⟨255035351880828096912724389739982786983047864881,144873939010866848491461953583569824446291925734⟩
def resval2Tail216 : Box := ⟨585237711625923245219398435057269512266208411290,97021116780359194339435935342014307910857212812⟩
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
def polyval2Tail5 : Box := ⟨24144284673435119491608240876308977953466153761584379,3345635509193546392527235797331138828633182248043573622⟩
def polyval2Tail9 : Box := ⟨50023922963143233060821967858516815105479437278282523,5694675459886448126123658155027996865689868549615898574⟩
def polyval2Tail13 : Box := ⟨114784201414153007535174193108203855017037174744223662,9685418903924982684936570303386547748286494930026311090⟩
def polyval2Tail17 : Box := ⟨263383544342810311305628246516436111875390338716727014,16455330290974892306011828936118546086046214900256890363⟩
def polyval2Tail21 : Box := ⟨604359229788791963883383696723453776429099609432030298,27917028470943402565245684253663901850242282735017696786⟩
def polyval2Tail25 : Box := ⟨1386761194756401927981233270984674036649304996072856926,47269467052723409120038757699028710636589713232991945412⟩
def polyval2Tail29 : Box := ⟨3182058809549929348024729135156145414251027821448252817,79823318492273187894138302061825857778895492854076745106⟩
def polyval2Tail33 : Box := ⟨7301544278654954920281169017251804207599866637392973906,134301964854317759815516930904475330608493055579313602139⟩
def polyval2Tail37 : Box := ⟨16754105453097970140797804852569386131897192366230482067,224815229577579347447307557996121648481034638834260300345⟩
def polyval2Tail41 : Box := ⟨38443928958167731207034804667319045666374196838331863863,373662691735565835154095933104747390853664575570310990166⟩
def polyval2Tail45 : Box := ⟨88213344357777403894355701810819574282671342390952579649,614822356750732670173153114643146422709324983658192815712⟩
def polyval2Tail49 : Box := ⟨202414121908592134247277753407799082535737155802384311877,996933746371481694877130997255553908580700124391691465260⟩
def polyval2Tail53 : Box := ⟨464458943783533287906813038649281069195850049915084335436,1581575570366896705217739650986203844540295039970483736950⟩
def polyval2Tail57 : Box := ⟨1065746344308590255421468277467393686525723233974411611167,2424698207944705000855874607277849970910415643365583201543⟩
def polyval2Tail61 : Box := ⟨2445458927229780145607834398164391523414564567639924364847,3509085381820468922620431950121853148356866323494312371865⟩
def polyval2Tail65 : Box := ⟨5611344009556397118782617546812608417073959259602761598191,4546845698908293082539177818798995154002332769897159020782⟩
def polyval2Tail69 : Box := ⟨12875776669139618146325856683043067439600129546948499611261,4453647033942475300460755703882223779840691797836910041258⟩
def polyval2Tail73 : Box := ⟨29781250000000000000000000000000000000000000000000000000000,2⟩
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
def resval3 : Box := ⟨132350984617092755004251541910151321928789912116080312041,1718029157508677149954263020086685429509997614310573279⟩
def polyval3 : Box := ⟨3915753968608062780483909518943652326740404483957521139659,260722170191636452493184085357808645546103693477941359251⟩
theorem cell3_lo : Holds Q cell3 (7/8:ℝ) := by norm_num [Holds,Q,cell3]
theorem cell3_hi : Holds Q cell3 (15/16:ℝ) := by norm_num [Holds,Q,cell3]
def resval3Tail4 : Box := ⟨-181756438225061556838055125305788378287602411711260633,2008883499325328539753608028864380872205308015829073812⟩
def resval3Tail8 : Box := ⟨-269570668634094979554055172281514578197349008599979732,2566390492319567424760777678981353696202867478998532129⟩
def resval3Tail12 : Box := ⟨-399650695425561053496588992895446972521187059008586637,3271609576449778131497558477418857846769148394398424248⟩
def resval3Tail16 : Box := ⟨-592500191036459694387524098172922745565370195857959842,4160086735940848272581044875093752179259627012711134069⟩
def resval3Tail20 : Box := ⟨-878408270993126133041184179131601459873255653186892653,5273997395108353715696698313180363228968187072798464700⟩
def resval3Tail24 : Box := ⟨-1302279901715002718512905746039044969554348180482544305,6662244695492436679243389964277882593180961365079080395⟩
def resval3Tail28 : Box := ⟨-1930688722333430016109273371895857605204850151135912107,8379693183890505782162848390994483544616608183150355198⟩
def resval3Tail32 : Box := ⟨-2862333157132029158144324187520744757203704788364717748,10484850815337933441464051531506281506228623953729329703⟩
def resval3Tail36 : Box := ⟨-4243538074079290419204830691613533469704034834856687770,13034902396435108967378560582017510999209641971093945733⟩
def resval3Tail40 : Box := ⟨-6291236693147088682646672374448365830546264658418723376,16076365769581438293794330299830898332616501596853197604⟩
def resval3Tail44 : Box := ⟨-9327042302498443561938588752762827042738141139982046147,19628675129548504463487313019965487953356310951820627030⟩
def resval3Tail48 : Box := ⟨-13827761115291670403976567664210795505291856076211053262,23656523282271367306265965174922520232930522363555866191⟩
def resval3Tail52 : Box := ⟨-20500279859388387271149432955343227741707677971551107240,28024560876980821422611838765444296840580290168966184768⟩
def resval3Tail56 : Box := ⟨-30392590008551031068089927932138565403041981216359351407,32424673448213183218005379241305609485013334649650007216⟩
def resval3Tail60 : Box := ⟨-45058386215364542401392974711596656534640337620243045300,36260965446882521115335508924851147374083731708508490618⟩
def resval3Tail64 : Box := ⟨-66801090877760168347670374067823479340020315320306479067,38469922032948479251478946091939419604821483665091691743⟩
def resval3Tail68 : Box := ⟨-99034973940584618154718888010163719119122044454357373255,37241731653074605364029689475212563976111056861013062643⟩
def resval3Tail72 : Box := ⟨986008676200058977111087891299813403926675548566588775779,776623293229843776162024377750886698886821753361098652⟩
def resval3Tail76 : Box := ⟨-2463864243202950372116035291741764072480553984713050,27937360662472431429473621583448112769788622793383485⟩
def resval3Tail80 : Box := ⟨-3598862131788746256061937911248128153892974760186317,35709474117261691113046831880909769547050925497216827⟩
def resval3Tail84 : Box := ⟨-5335472356270188878659746891953863540445736695678515,45550670534069948129789395171995922189010272170664888⟩
def resval3Tail88 : Box := ⟨-7910078540325437582590713895509813043733456094067699,57963980923870741287597294437244096913966779460372620⟩
def resval3Tail92 : Box := ⟨-11727048394480012144836788876254484329984138444784737,73549442687896337387626032165680722239949290555659058⟩
def resval3Tail96 : Box := ⟨-17385878451832058633946497725845086863801258261735015,93007802922481298407992771400866812040999682848110584⟩
def resval3Tail100 : Box := ⟨-25775349378123053471257120197474313676430120256027617,117133496104286824676304885097553826909324092044776687⟩
def resval3Tail104 : Box := ⟨-38213118618363505893415714269646094685509014352587263,146787851209492568524570205047952451478503366703942541⟩
def resval3Tail108 : Box := ⟨-56652672796765545148816519926744203763941634469771734,182838162929424591974860680575922329844292352264154278⟩
def resval3Tail112 : Box := ⟨-83990143988798268676935661883368994470086981660624847,226039908557406113078377749260109373840844297549325972⟩
def resval3Tail116 : Box := ⟨-124519178690220907103590784314747643956217416736622685,276826589678530705023982548089004656697335635263560481⟩
def resval3Tail120 : Box := ⟨-184605301590565953475963530532795189063029141437375875,334952155709473664662582043801578578797514308327224518⟩
def resval3Tail124 : Box := ⟨-273685690299370817679810218516978463119624607553619789,398901322473278995745045299014082522864621103131344685⟩
def resval3Tail128 : Box := ⟨-405751386494693688862988767925400991746807393474879938,464938242523941451693512899905083455121129863496232193⟩
def resval3Tail132 : Box := ⟨-601544740838712635594361180290391947555695268885113107,525596306615529008069851881370005093973839451789315537⟩
def resval3Tail136 : Box := ⟨-891817224351483853864509000220404548319055224678691929,567309999190474585515398120879556247213603368739655145⟩
def resval3Tail140 : Box := ⟨-1322160380335251236090273294170983842403223375062058012,566736696132013889546693599749596250620739675687702274⟩
def resval3Tail144 : Box := ⟨-2292854243294044595855772522220953698206567805482660447,471273511820632696088728052651702640403669173297802086⟩
def resval3Tail148 : Box := ⟨1009252327205606201063825001652080085684397184,8841895768750880309010879654609944498676787231⟩
def resval3Tail152 : Box := ⟨1341510655414409030947390536728275018647208983,11275394163979366729118952144441915755885247123⟩
def resval3Tail156 : Box := ⟨1988847097409865380907975092573342847379032810,14344216432272917192321781166210428128612815353⟩
def resval3Tail160 : Box := ⟨2948555571668231143195892226388265593790710307,18195220259151288371064019947693931590366824670⟩
def resval3Tail164 : Box := ⟨4371366694589859175652337062380811106276441163,23000060324639782180253309978842433385731979695⟩
def resval3Tail168 : Box := ⟨6480748391581629311924532332702674608891366589,28952611433252605724556119072949824194989049808⟩
def resval3Tail172 : Box := ⟨9608001947530187186934706655887784992565923131,36261838437266581476198036743428309317608180783⟩
def resval3Tail176 : Box := ⟨14244296467929173196337204664314073553500187721,45135967422600032340560998675867098880688673098⟩
def resval3Tail180 : Box := ⟨21117812316682196626136817770623092912548734496,55752211867608608587870600969175870562741031087⟩
def resval3Tail184 : Box := ⟨31308109743902849092697623328224999690738718143,68203078501858774818053601896483811992999523103⟩
def resval3Tail188 : Box := ⟨46415685537746205384519713669248886743114192730,82405356099275696534150184567826323504264582864⟩
def resval3Tail192 : Box := ⟨68813348412339317840318800744034560964860734867,97950420174798802937837178966477039907817759113⟩
def resval3Tail196 : Box := ⟨102018894364216079059142910808933935990677564716,113863186388903602672912629233739099181028496512⟩
def resval3Tail200 : Box := ⟨151247614705968691539346551001399298512947156598,128220000982652575501458468637270070164334424281⟩
def resval3Tail204 : Box := ⟨224231414159190150381805823046652166376736080239,137550110023911201704685956967685773404477597022⟩
def resval3Tail208 : Box := ⟨332433190391866301568618454137795195213801951662,135906838622940586311213971761352367925807833034⟩
def resval3Tail212 : Box := ⟨492847207158762928785128802424332262622173345023,113436885161645470917777254993432115625450592051⟩
def resval3Tail216 : Box := ⟨730699090028469406780627539311866817386051684212,54188130703848331747764660554494629430376689664⟩
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
def polyval3Tail5 : Box := ⟨36620517959438880629149973761024481834583832010222821749,330670453429015978293923692747696918696433431954492062581⟩
def polyval3Tail9 : Box := ⟨54288119443478306091744306360360954571129950866439075787,421181080831629954290237535204083043219254071871477554804⟩
def polyval3Tail13 : Box := ⟨80484586574347222965413497221483766107850331538162546110,535028489832519768386428709806943462391615933289033596745⟩
def polyval3Tail17 : Box := ⟨119322031627548634114168120895643375359132712697960203518,677483202454163047663880786360985658432848367308761873494⟩
def polyval3Tail21 : Box := ⟨176900296538274906277786225188112396475715589489059281467,854594573995631358374453323944589872504965409691226128239⟩
def polyval3Tail25 : Box := ⟨262262672605256097248383629625005075571877672860759071104,1073046914265066476506602901500244875221134333771025755140⟩
def polyval3Tail29 : Box := ⟨388816247276159004774737782516698398881567970945173268469,1339793117368452554131558894291434311504994054041414803411⟩
def polyval3Tail33 : Box := ⟨576437632714360635388091602678418279365521168120942775992,1661313346472785302830985719577026680080805284312632256062⟩
def polyval3Tail37 : Box := ⟨854594803424796392956859897804868902126941492421740593017,2042259481454389704953935403210623788097920353486118694723⟩
def polyval3Tail41 : Box := ⟨1266975361413581451418599669822000151468186567275494271770,2483113377625279587843440834663716590129573228744688099989⟩
def polyval3Tail45 : Box := ⟨1878348148147069671053747035698970722615551156873127050685,2976285246453439900692832570972523360082232094092636158747⟩
def polyval3Tail49 : Box := ⟨2784735893925415397155855712499690830769204265355984197889,3499772829996342534727552757689304673571994709266929530856⟩
def polyval3Tail53 : Box := ⟨4128496629640463095291469822592329686486288091006287573192,4007040431711365606307204248858567235281071270472577988304⟩
def polyval3Tail57 : Box := ⟨6120682560286333766487813126088322590499762159334931683204,4411081525693981475280410275541254727765921481902462768180⟩
def polyval3Tail61 : Box := ⟨9074188103928774900955926266918829710333737774226282161707,4559583572887204478012025846005396867863040798493643245966⟩
def polyval3Tail65 : Box := ⟨13452893355414029335063891953237965045176692421691398364744,4196545866608169832729126042607553024878616495195917205351⟩
def polyval3Tail69 : Box := ⟨19944522009573975879857391975589965426456301066960565521364,2903353030472047561977381040655068463552343750990291732735⟩
def polyval3Tail73 : Box := ⟨29781250000000000000000000000000000000000000000000000000000,2⟩
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
def resval4 : Box := ⟨129556946870541513571595028637789399538423343099069484424,8147689186869682875062889531949781500394687146709150662⟩
def polyval4 : Box := ⟨4821449349289549647714437121924304316304126771610309505139,2076357165681162211860133178149677315860283804074961048249⟩
theorem cell4_lo : Holds Q cell4 (15/16:ℝ) := by norm_num [Holds,Q,cell4]
theorem cell4_hi : Holds Q cell4 (31/32:ℝ) := by norm_num [Holds,Q,cell4]
def resval4Tail4 : Box := ⟨-3494083471356553827755460694030064419880423646337445251,8874839352463233913160111272550311379434090723240044685⟩
def resval4Tail8 : Box := ⟨-4233922450688377907046546035011097804658262393639337598,9809972068560204495853698800936853224631578228940714232⟩
def resval4Tail12 : Box := ⟨-5130308201768413228888161015622965796277586014141869066,10815285617196036625595571399767232388641029170013939489⟩
def resval4Tail16 : Box := ⟨-6216472430081875707925870103822343633684425384693024889,11888331883327422160941433993565840955689453789577550472⟩
def resval4Tail20 : Box := ⟨-7532594135490158895616317692755666084965519802675066214,13023801753436577504979086176586707573905730344546872593⟩
def resval4Tail24 : Box := ⟨-9127358811317540857548709537013955125910141015944533527,14212601379763378923994252399033259835361113633266857756⟩
def resval4Tail28 : Box := ⟨-11059759409845716698392750911471718514484946781770473627,15440690604093182972429765022782760308977891910175631241⟩
def resval4Tail32 : Box := ⟨-13401278588062228633127069397473451074122484552850223243,16687626671066687399297958818521166234583000376082088360⟩
def resval4Tail36 : Box := ⟨-16238532967993423528780986547313729249273628092003519478,17924744229814057035095988564194563197230248576856302036⟩
def resval4Tail40 : Box := ⟨-19676477227143281012601156794037523181119093088690094140,19112887119707712889409414955413910355664638026924738047⟩
def resval4Tail44 : Box := ⟨-23842286543581129413823280650432314414823224411106380333,20199588529496394301578084150256206670783465930720149589⟩
def resval4Tail48 : Box := ⟨-28890061013668582593245328574630160776353066870063760170,21115573072212883530907838818651256001788999909281581890⟩
def resval4Tail52 : Box := ⟨-35006526066527612891976145786034355893306888359950921274,21770426235842602124015323548868957912375536790136844163⟩
def resval4Tail56 : Box := ⟨-42417939742899190988249231791531612334130303710270736727,22047242464554756856962231016439605349150520806314628176⟩
def resval4Tail60 : Box := ⟨-51398462349905768047985765850362287915508767857641847948,21796021477036098392627064063744504781933341569383730617⟩
def resval4Tail64 : Box := ⟨-62280298062468758998604538161329373234783387913029469067,20825531733579308019157517269018059759713463431167372183⟩
def resval4Tail68 : Box := ⟨-75465356326261608436833673372078379398659678527176979923,18893295990824854138946696769665346838264274332771896370⟩
def resval4Tail72 : Box := ⟨986425401848358430238718418994213942928835675006516866102,716712909095493078947173110497034376125695361283981754⟩
def resval4Tail76 : Box := ⟨-49083325845523834931945278066157230337276614500948218,127853935968193651275261510818347975684892765948777595⟩
def resval4Tail80 : Box := ⟨-59431058257345340216480535316630136734745693029173285,141424140272173575702906641122179765028927483117567812⟩
def resval4Tail84 : Box := ⟨-72013514089041673343102992034833928326052740818689204,156039706586875652811681353770661844552500122853971402⟩
def resval4Tail88 : Box := ⟨-87259869643829026119375452314872264849758433459725864,171674289863205140124875525293409567231751365388519568⟩
def resval4Tail92 : Box := ⟨-105734110419605304206008095226855650016301368861156755,188262610000659919816684238298590249356419614180484230⟩
def resval4Tail96 : Box := ⟨-128119628780770207344990000712909129785687988491145646,205687512704263683761805469598501732108814625990878012⟩
def resval4Tail100 : Box := ⟨-155244501644558708589891453873807196924236743090994711,223763834050905602510485547589110864746084429945576223⟩
def resval4Tail104 : Box := ⟨-188112122398568398778335168279013100987748487324819093,242218151206695786194433704285758831650498480619810177⟩
def resval4Tail108 : Box := ⟨-227938318062385673563719325457199802628106082094437208,260663453825761426507488984510953786519537309530472174⟩
def resval4Tail112 : Box := ⟨-276196324716522883709145529050134898061588411169297683,278567553483740817498808673835596062772793761089522679⟩
def resval4Tail116 : Box := ⟨-334671284913299465839158813566854658303256442600910522,295213783588358548199420132603233774402709833463333377⟩
def resval4Tail120 : Box := ⟨-405526283017981097433774391278981525796178052742286185,309652219245848911869314927737050281331654586484764201⟩
def resval4Tail124 : Box := ⟨-491382361235391975962476686896576526024393592721948017,320639252988646051194282983769364769120558366482899248⟩
def resval4Tail128 : Box := ⟨-595415476245625343847849436436317836949568596950070030,326562882835094379767583132620747463923320988340721392⟩
def resval4Tail132 : Box := ⟨-721473983033413153042356488176602384862222810932727445,325350485334416459358426732054915993091746529834138666⟩
def resval4Tail136 : Box := ⟨-874220991946971471156380319451648008953076014556296158,314355135555333725775808633406849766451863921837988689⟩
def resval4Tail140 : Box := ⟨-1059307914494715891071257757886153884452028443602103976,290215632446175935446287114081211648452062800053790576⟩
def resval4Tail144 : Box := ⟨-1600364794366076568190750928454607475980868838945121981,240780101147673430738860829779300378210099377766164801⟩
def resval4Tail148 : Box := ⟨31035227688142546201277234163983610983364077801,65918910991371992322419876975753254564449781640⟩
def resval4Tail152 : Box := ⟨37479610133181672602452728823831835742824695523,72484248155446704959079307900513276304197417348⟩
def resval4Tail156 : Box := ⟨45414610867689229243637810215502198911472533166,79439572790887461591422354800607442778993800315⟩
def resval4Tail160 : Box := ⟨55029574301163735900966350579923154377867724978,86731252451278681226474562597683542844865262946⟩
def resval4Tail164 : Box := ⟨66680171644225240848814655440210517134122013467,94276645442519587270086480283870795378440532159⟩
def resval4Tail168 : Box := ⟨80797377536853258952233099866012745218175097781,101954780165625119937891703515884113624989073395⟩
def resval4Tail172 : Box := ⟨97903410502065933185993663358554955148474485561,109595418993997468085723483810797185464751174517⟩
def resval4Tail176 : Box := ⟨118631050662060080504708052942938779110225169249,116965424824327534979290127911198962543067996250⟩
def resval4Tail180 : Box := ⟨143747047309320176042886325566658202180809561912,123751807486200857363102299948095246351704876554⟩
def resval4Tail184 : Box := ⟨174180482216333656195121232000784717785573375154,129540688353765197132975432542892010309853552112⟩
def resval4Tail188 : Box := ⟨211057137889102473303310541196901302517650842520,133791252295540837707257332271525017420276247247⟩
def resval4Tail192 : Box := ⟨255741142102329229465222153179227257842955729147,135803549990490039929823457646555225752288991722⟩
def resval4Tail196 : Box := ⟨309885429215709727360911239715984876595949164795,134678762671556570107814197067177814808386424573⟩
def resval4Tail200 : Box := ⟨375492884917909482174347376941930814237170007677,129270235869145872710161638008795418072440806923⟩
def resval4Tail204 : Box := ⟨454990436242256147811566344188122451436943990352,118123216985345345322175930870665532184535575292⟩
def resval4Tail208 : Box := ⟨551318827565159345509467070234654703841491165338,99400779294867144176298345465341679233152407592⟩
def resval4Tail212 : Box := ⟨668041404193108174587581420835217314689544944601,70792864928551069237261244520493080668301953962⟩
def resval4Tail216 : Box := ⟨809505344841998229394155297306338141168523956295,29403653388307078609073283425397705162849707046⟩
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
def polyval4Tail5 : Box := ⟨1130246831526487810171230001395093970312382608529783140634,2285236166438623450997425240122066063111252355996065479471⟩
def polyval4Tail9 : Box := ⟨1369534454678579702338658180606398574873179113425723196803,2508440231422878547475331725112459743448654840667034399553⟩
def polyval4Tail13 : Box := ⟨1659485715710786109835988159529190561275647921520243969942,2743609811295557608115382559782461864145257546097397626678⟩
def polyval4Tail17 : Box := ⟨2010824066330892252131626574056117362206998224340352556763,2988499495695293004350809766195908870052198561071361810986⟩
def polyval4Tail21 : Box := ⟨2436546086209692411868779411667808399814824687298693845859,3239741408471173972526257445293673357206956111190085363727⟩
def polyval4Tail25 : Box := ⟨2952399928779669701835621415830922530913861438295239250331,3492519933381000320164025892517681918575199927406762732210⟩
def polyval4Tail29 : Box := ⟨3577467870931143510212389724372097989931623224812092739345,3740165717677005875250557230700166779904126774894313630959⟩
def polyval4Tail33 : Box := ⟨4334872197627570314966022809920870850805065775084474631304,3973650248324799853095342025745099356970727234521470277619⟩
def polyval4Tail37 : Box := ⟨5252630533023774773182464783114649325317233196186343097488,4180958126342880128373055581642460835517320579908854231788⟩
def polyval4Tail41 : Box := ⟨6364692258183161463795961866925696403081368849413659358429,4346309074849925526162650180244917937957236413285669892167⟩
def polyval4Tail45 : Box := ⟨7712194354179472914732676129547873864991799329524349865415,4449195515446125445883544497713051755598792548395748206622⟩
def polyval4Tail49 : Box := ⟨9344983126272323931713634401796557946165166163256900501416,4463193995777452334036432328827316633620154350008965817802⟩
def polyval4Tail53 : Box := ⟨11323458100221290529193957094840809784317518745679308348512,4354499557406923881894289389201690819219703248456579033190⟩
def polyval4Tail57 : Box := ⟨13720806299477384063039868923139974111442744855847801264053,4080120943980168924364596625965418382032370925712724842949⟩
def polyval4Tail61 : Box := ⟨16625709552817601242017353757035860323747108091659355686106,3585660936035170645373692802042016712746772942532293130314⟩
def polyval4Tail65 : Box := ⟨20145624980218602842859101115935835205516330264269221286804,2802589539834112301034938062688453473971095930768111323617⟩
def polyval4Tail69 : Box := ⟨24410760504423765865657904703215231227407440743878100018945,1644897604022033974310427528481951610524171236020515618462⟩
def polyval4Tail73 : Box := ⟨29781250000000000000000000000000000000000000000000000000000,2⟩
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
def resval5 : Box := ⟨120491341871280852414259432011153210641853760429931470604,12087045251826196453683401891091550957011781609759058901⟩
def polyval5 : Box := ⟨9251082850904603382889698246968866671808903586377833609379,4158332961644356754452570044350298168775864145044399764784⟩
theorem cell5_lo : Holds Q cell5 (31/32:ℝ) := by norm_num [Holds,Q,cell5]
theorem cell5_hi : Holds Q cell5 (63/64:ℝ) := by norm_num [Holds,Q,cell5]
def resval5Tail4 : Box := ⟨-13120139457525026740922728387995579982843049444923579008,12320727893949418564522261938165366365780842843065908366⟩
def resval5Tail8 : Box := ⟨-14425825959147708962042743616516062593738471870131262223,12669279498445297186851911390205384869663072095612693634⟩
def resval5Tail12 : Box := ⟨-15861363392823992676286004847550607293592314693553586650,12995461489962780226498374995687084035458049303222903346⟩
def resval5Tail16 : Box := ⟨-17439753482800808859908252717992685223231978481125991129,13293337529920005410504107251704031348788128159401064476⟩
def resval5Tail20 : Box := ⟨-19175211739886526226995010828692842287339368311244725417,13556139925878182721432650985484491197906723292044714075⟩
def resval5Tail24 : Box := ⟨-21083368273072100177272934135404179872990499087158495319,13776170633200462564900361198173765642523332865603606818⟩
def resval5Tail28 : Box := ⟨-23181408568926378958642682278789261672949542977452998858,13944691971215791160785832082359990429860904103991203196⟩
def resval5Tail32 : Box := ⟨-25488228269760757623800887720542180291429619465000976804,14051805378496345204838317254942734162596127474918282003⟩
def resval5Tail36 : Box := ⟨-28024603354010910653360681748750331916091639110100233703,14086316946247398733247218179111546490124660910320026728⟩
def resval5Tail40 : Box := ⟨-30813377251545285550665661595435148661618703561372543507,14035588338874097342950268706948867646979247772716485973⟩
def resval5Tail44 : Box := ⟨-33879666579122525924756235522509182617994555780831756041,13885371567485817570019667971044467427556129514215389243⟩
def resval5Tail48 : Box := ⟨-37251087348919153947177579893160443823508640261558220869,13619625924216470884805331148715355948471986528607797824⟩
def resval5Tail52 : Box := ⟨-40958003687436058548953480319257111140465213758488274809,13220315211307064107561903326934433621256684029828172245⟩
def resval5Tail56 : Box := ⟨-45033801304828156236975876785643609435450779095716201290,12667183207295898629453756452448970082084753070162308258⟩
def resval5Tail60 : Box := ⟨-49515188177589715515321822442128028233413760384901078805,11937505101609585805898805391464588025279389824256068038⟩
def resval5Tail64 : Box := ⟨-54442525116954236430843150435019590121847487642846454672,11005812395657263200367352749341899350986275883373923650⟩
def resval5Tail68 : Box := ⟨-59859576029498860204855001359067402635800236047488109041,9843581506990942720956946641992404226413783246488520641⟩
def resval5Tail72 : Box := ⟨986522373066273678150139763825047608476312064046330385665,698638289472755499310180221900639636486537755677762247⟩
def resval5Tail76 : Box := ⟨-188333768735186121706200385788427458895098915124772509,180217665320098820220684513899618170487871375962171244⟩
def resval5Tail80 : Box := ⟨-207035340293064477856092798052664894620590206790359420,185440513318411712161416830089618803444639972469884271⟩
def resval5Tail84 : Box := ⟨-227637761688492199637058480881977697575615508720203264,190356806762810064541811731514125902529184982428841811⟩
def resval5Tail88 : Box := ⟨-250290365895982271005944733562867943618182597329813778,194882142416095870332858463034639413156905127166706351⟩
def resval5Tail92 : Box := ⟨-275197167622937914291657500533691986887966472555791552,198920385846118796364466136530862946465032093731624171⟩
def resval5Tail96 : Box := ⟨-302582485732441146909256135468691874018279291129794133,202362115091614283718631358404830852175866440949551234⟩
def resval5Tail100 : Box := ⟨-332692961424184659713257895287077385096351278529991959,205083056434232937729308794181164284893742513761515253⟩
def resval5Tail104 : Box := ⟨-365799779565123250314333241502439280945651128493919603,206942348802396319424171987846671773126757909522140626⟩
def resval5Tail108 : Box := ⟨-402201111069750646337021330161738152605921088857502794,207780618709279670913746305821163119013597676678580431⟩
def resval5Tail112 : Box := ⟨-442224798325617305830947471401318830862660034818075927,207417845781507945292560736171118578982419782364347143⟩
def resval5Tail116 : Box := ⟨-486231307849912803249069720678630560530870203073369224,205650996879741988481755248729419970215090012764812814⟩
def resval5Tail120 : Box := ⟨-534616976769710993361897686866678688579438123034905025,202251404547759420696958846969747057609897178739388067⟩
def resval5Tail124 : Box := ⟨-587817582364748920908504788052087433481143732522671236,196961863031806420636441740202132363182309329462977680⟩
def resval5Tail128 : Box := ⟨-646312266821218565318565526613425730239338690884827506,189493412363680223788205967223078485407361258998948878⟩
def resval5Tail132 : Box := ⟨-710627852544308588415746909592146755527586791973600498,179521777973627874554124307724527505109524066581170299⟩
def resval5Tail136 : Box := ⟨-781343587009106700422351545110061020548626918779345637,166683429960337922509315445274193437106401173378572976⟩
def resval5Tail140 : Box := ⟨-859097386047790898159632420964489339859747287266505638,150571192328290005917062320554106256316812835401378308⟩
def resval5Tail144 : Box := ⟨-1253976800867257796438000850886934527410688445030074785,125453964961866958467579631006717591118150456023737660⟩
def resval5Tail148 : Box := ⟨169626060502625469273560460375488467697726156558,127455318178436099863599286980085042377382173024⟩
def resval5Tail152 : Box := ⟨186391375282418664602039040666110622366480019455,129894681687527261341836301980778317494474726816⟩
def resval5Tail156 : Box := ⟨204939482240163323749573622703850796342285074297,131911441320709163750028259710843957345229214980⟩
def resval5Tail160 : Box := ⟨225333343712697160385374792675312635507469978513,133419572921105293883253640917345269568109169920⟩
def resval5Tail164 : Box := ⟨247756631537755129391242601738275118302546154946,134322342249793415838457139881682532438402473565⟩
def resval5Tail168 : Box := ⟨272411297234375790266855402206671884051502176112,134510390205340457082413770643276734848165225255⟩
def resval5Tail172 : Box := ⟨299519388846740291923745660556911631391561044356,133860281506065536582951632486731562135747795526⟩
def resval5Tail176 : Box := ⟨329325050781352117752594965977953460880313618094,132232896293983090067612799615904416237026746842⟩
def resval5Tail180 : Box := ⟨362096722652018327654952687420981473177744413540,129471648183119717438883462812052309723566290791⟩
def resval5Tail184 : Box := ⟨398129556935475483051536219495783638538732741590,125400510603523145355709661849641598311773877767⟩
def resval5Tail188 : Box := ⟨437748077211862318571257791955188085606108479470,119821831429209567057112763247184377781282245712⟩
def resval5Tail192 : Box := ⟨481309100931028869514827729367623842231037185253,112513913826103424331190546000102843861421605562⟩
def resval5Tail196 : Box := ⟨529204953028078629522830695992581217527113490373,103228338995661925397716042865301314773630379552⟩
def resval5Tail200 : Box := ⟨581866999331024357976959453501514420431513445274,91687004000372988404948289433000994583415261854⟩
def resval5Tail204 : Box := ⟨639769531583591752588784100742035966504712032885,77578845115593857898536851972382641911734657759⟩
def resval5Tail208 : Box := ⟨703434039073180152200214263656669454792905586749,60556214132858662037506877170929374198584872023⟩
def resval5Tail212 : Box := ⟨773433905966654288422853273383534517439469769837,40230871691866305988604833434006833321161556393⟩
def resval5Tail216 : Box := ⟨850428321569060258446776047153136386189997419942,16168745344272552155806787133135746914737384349⟩
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
def polyval5Tail5 : Box := ⟨5897321622077874492779120604154468470076052781426665486162,4242246015232229761227061780452351573035617386592671669581⟩
def polyval5Tail9 : Box := ⟨6484171149663898857519415201466819505137187418254304888700,4314667075159362809336626695759554644869740035907401639263⟩
def polyval5Tail13 : Box := ⟨7129421575278419379672441199062269217657236397494612886104,4371555380280026356921898665875384954620310923056741551845⟩
def polyval5Tail17 : Box := ⟨7838881921335482974694930278398813431489043038213652283728,4409886712981769955566402723519106457073668859380257832464⟩
def polyval5Tail21 : Box := ⟨8618941821271434423289609856370811853357136162229979116493,4426239786933242256510081666827330064076777074494399515541⟩
def polyval5Tail25 : Box := ⟨9476626751612796914081387240882161353675789061578737061426,4416750474425992409414066585958544352084419150627006007181⟩
def polyval5Tail29 : Box := ⟨10419661305491373567901957677998689916248010511482530738759,4377061081540092634091371824052078038940882346316768646970⟩
def polyval5Tail33 : Box := ⟨11456538762875421359138842228943044747424847192449477284829,4302264142766413675368283224116593236053670722492076590908⟩
def polyval5Tail37 : Box := ⟨12596597583847995816884070652773533911098458190167772288541,4186840161562577154775545006017677306951035096665402698889⟩
def polyval5Tail41 : Box := ⟨13850105513855938526378935500647653369072434536544641668023,4024588664419891105225109127708137531683568753989619042077⟩
def polyval5Tail45 : Box := ⟨15228352058409095891519133179944666651787253843063958400318,3808551871136346473813327164940887873215001962278066496357⟩
def polyval5Tail49 : Box := ⟨16743750160087385252780689756510554513308810148197992908531,3530930212525272671093645354794825513053321340926326480031⟩
def polyval5Tail53 : Box := ⟨18409947993592341549807184765468937985121332913401131396447,3182988848077173558013365644035661417819430226223111111880⟩
def polyval5Tail57 : Box := ⟨20241951885706220946959160614169683039090256602777032862039,2754954249403696458416228910995984354860491244952373321648⟩
def polyval5Tail61 : Box := ⟨22256261467216379871377883452710249347039939627722588402753,2235899819824524516430905730901111845472655593162490397416⟩
def polyval5Tail65 : Box := ⟨24471018274087509379526999021797043547803828303887688109456,1613619415324483627353209492225522463208548772113399328022⟩
def polyval5Tail69 : Box := ⟨26906169622138107901381474945346304210963578308052650977024,874487503192843373795055015192993018642576478512424876928⟩
def polyval5Tail73 : Box := ⟨29781250000000000000000000000000000000000000000000000000000,2⟩
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
def resval6 : Box := ⟨109500032354546993398933895753566555903981413262004679480,10307104986014507922970926824900495499647762367717499075⟩
def polyval6 : Box := ⟨16548418518980437200262530999252594502543094707110798837738,4161855741670789376088481210227390781817188112236628224555⟩
theorem cell6_lo : Holds Q cell6 (63/64:ℝ) := by norm_num [Holds,Q,cell6]
theorem cell6_hi : Holds Q cell6 (127/128:ℝ) := by norm_num [Holds,Q,cell6]
def resval6Tail4 : Box := ⟨-24022168479193599640486146533255138381325317221833646592,10126063918798769207193186545830465500835747581299632534⟩
def resval6Tail8 : Box := ⟨-25182062671828085038410253228740116017886268047619929991,10054549132997312981239054126258269982651419258103549155⟩
def resval6Tail12 : Box := ⟨-26397881631905089575814577475766860509209583007857258109,9961721717530912220617965868077507581707668430421941000⟩
def resval6Tail16 : Box := ⟨-27672401719849995213680621091170026481111408820253424496,9845982927894589384677984574675668152512109633626550906⟩
def resval6Tail20 : Box := ⟨-29008457103579517683634417529999373912657322721286005456,9705639226010939870373665780766357742494094011526006872⟩
def resval6Tail24 : Box := ⟨-30409018777961470401978277360984974197288724839704939075,9538896589095969427703676510987976707446927884765608272⟩
def resval6Tail28 : Box := ⟨-31877201180903492320093332610959763602532908853439975021,9343855061440824295663118356356538004734620427454616269⟩
def resval6Tail32 : Box := ⟨-33416269118957578488700655725005517513260684205983319558,9118503024264634342632844679980056060781248176684069941⟩
def resval6Tail36 : Box := ⟨-35029645027291222295611978480801373338636079048491161819,8860711169290786136955913523222168589474678640666160863⟩
def resval6Tail40 : Box := ⟨-36720916580178276088329614684838477047602850260009753611,8568226161116621756124961207092684338867051097658954695⟩
def resval6Tail44 : Box := ⟨-38493844668933063614768788373101952712811975609153787395,8238663972705977231752268602299773648559697418996681149⟩
def resval6Tail48 : Box := ⟨-40352371765028327567094816219650598630974045854669930713,7869502877556819933176316808781463761145442058372084481⟩
def resval6Tail52 : Box := ⟨-42300630686994130112557303803878406846404104539622742943,7458076081280911323514503103058615571988536843846594784⟩
def resval6Tail56 : Box := ⟨-44342953790592645920238443411864706552036363881798876359,7001563974477044011069564058834730390949255836842626410⟩
def resval6Tail60 : Box := ⟨-46483882602682904217850646366440689473006777360762466170,6496985987881271711982195162248670727917116125442914352⟩
def resval6Tail64 : Box := ⟨-48728177884883767118466547865086536562949618079924257545,5941192028989794653015201177829743154788514851173315923⟩
def resval6Tail68 : Box := ⟨-51080223807124359923034140229724136553347584446401245427,5330844244523080062512676017432174319435842450923605378⟩
def resval6Tail72 : Box := ⟨986475859946303248400840896803235108314285356884769059260,635701581376698464888293599355704797946792964737923640⟩
def resval6Tail76 : Box := ⟨-347683079653555524566288704770859105950923938374453172,149084018410961075102529525930946941525563157237082880⟩
def resval6Tail80 : Box := ⟨-364431672383565153946382076295572304066880437346091639,148129890394287408921348820815072740811884191117133104⟩
def resval6Tail84 : Box := ⟨-382026850481275466762151805880714269037000823112769633,146870057527969679945103143180383620480422121458301869⟩
def resval6Tail88 : Box := ⟨-400471546227047804772272107897813892822784125915599237,145281316996843060086750970330838638690487941292588226⟩
def resval6Tail92 : Box := ⟨-419806773099791654560160534031271148479453569863870948,143339244975628670345773935989831680144773333366015316⟩
def resval6Tail96 : Box := ⟨-440075526965262662003924239523241888310223182094236371,141017966160585301524994461703744391428394873634586496⟩
def resval6Tail100 : Box := ⟨-461322879580405122917180479956889495743989579142229469,138290074990778463893396679895257381354082167980205359⟩
def resval6Tail104 : Box := ⟨-483596078818433834204954848360764481522617742689644893,135126552811033215084688979941758036840137077893779988⟩
def resval6Tail108 : Box := ⟨-506944653734226771993154245448361192378390744239056964,131496680750061183832823585856324397874440037566895235⟩
def resval6Tail112 : Box := ⟨-531420524702399559664083417982229415576602981007408194,127367948097769951640841035915609508569300847431632382⟩
def resval6Tail116 : Box := ⟨-557078118872972887731905682817440130233176988225527457,122705955955065179183044077621834234651949971840003546⟩
def resval6Tail120 : Box := ⟨-583974491201372354570750292996183986882119407699643204,117474315918212016036020256353996215923697590143483754⟩
def resval6Tail124 : Box := ⟨-612169451321895914516254963991130429433690487162191896,111634543548026003346566460095181356348955284049592354⟩
def resval6Tail128 : Box := ⟨-641725696546778749390878038387990787242519168552677170,105145946361787945795921645290033443244782945575065146⟩
def resval6Tail132 : Box := ⟨-672708951286716479882185649984167101053419951796261683,97965506072789022561303615113336085861210919482110396⟩
def resval6Tail136 : Box := ⟨-705188113316179536378791181893193106117606511296661469,90047754784969769602910856452659627184359479564493255⟩
def resval6Tail140 : Box := ⟨-739236422095225430959628068459226364924047264247168152,81344618728493988865758291862850979424363669185647077⟩
def resval6Tail144 : Box := ⟨-1080746857773238419480166674236493183830862318862990144,67770997542716497725784281382178720116216130721966142⟩
def resval6Tail148 : Box := ⟨390959644105089699048064605419517900194588760831,125734126124837002140087663980261068955288484925⟩
def resval6Tail152 : Box := ⟨409726557940346415751014890560077058193988339825,123326251467532933283656521239191003371877772477⟩
def resval6Tail156 : Box := ⟨429508625328665763324155862894703572094345378321,120532585873631556302459830189939260732491393558⟩
def resval6Tail160 : Box := ⟨450245795778062841159382304453532112418144185937,117325240012345477832355458306084142177844858176⟩
def resval6Tail164 : Box := ⟨471984180669291890606020541126239232791514659421,113675355576124072460728016108684309971989216495⟩
def resval6Tail168 : Box := ⟨494772119786481516873456176828084911184686158501,109552397791363799685561691251594526038368313230⟩
def resval6Tail172 : Box := ⟨518660286814853191934088463498498335143647448065,104924065430130870578295562801645135170906154649⟩
def resval6Tail176 : Box := ⟨543701802023436890418856196029227872866459431845,99756196211271778940630540459649025374690959724⟩
def resval6Tail180 : Box := ⟨569952350388950102011972114503654520332978294290,94012667337404740278522711097891133830281590869⟩
def resval6Tail184 : Box := ⟨597470305422834893278847738915613646609185350044,87655290923476716146137696758985645041094096383⟩
def resval6Tail188 : Box := ⟨626316858976806752866878707055676160640849690314,80643704060484839060357081630312558706544247676⟩
def resval6Tail192 : Box := ⟨656556157315564636981923606250327684786055263510,72935253245270684954700287849988031626817030377⟩
def resval6Tail196 : Box := ⟨688255443759247966271372277893738894919641649028,64484872893982823930655659714782391757160625557⟩
def resval6Tail200 : Box := ⟨721485208212835516693485678561240465736406368509,55244957642837066424227482344295289930661634533⟩
def resval6Tail204 : Box := ⟨756319343914996112668326599159385113398306821453,45165228125152934872876910536671102634405727243⟩
def resval6Tail208 : Box := ⟨792835311755165892895262950641160744987274117893,34192589898266939819349456013786036442395845687⟩
def resval6Tail212 : Box := ⟨831114313148487509482359719897043192482811544018,22270985157218266799030807222165581673757796478⟩
def resval6Tail216 : Box := ⟨871269892002319887695504210961772331398868442254,9340539811071508405292477955841490654903121262⟩
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
def polyval6Tail5 : Box := ⟨13272821885383119429684184875521808936225848624144786868192,4085084571618522312556968290941048960249019923530053599524⟩
def polyval6Tail9 : Box := ⟨13913646566497731229853516936428379213978349962548805722395,3997454325199494861338818793913720176719687965216188462802⟩
def polyval6Tail13 : Box := ⟨14585413425899670156230448371373601918025057774982428303701,3896514615274654559967373105248162627782507227962129111746⟩
def polyval6Tail17 : Box := ⟨15289613962191002623609874670402505294349406376762197652703,3781333501576896972365589745382408536369321178061547913396⟩
def polyval6Tail21 : Box := ⟨16027814110343572936052055303480581297409369966506227833010,3650924836996800666760477939321617149240782879503493147912⟩
def polyval6Tail25 : Box := ⟨16801655410724057290109164128498929179158228984014312348292,3504245347132696609421595152108242288673286782806303763840⟩
def polyval6Tail29 : Box := ⟨17612858659156341367941894331409439539023739359512974272883,3340191568874392179267636730030715716162591442045815830429⟩
def polyval6Tail33 : Box := ⟨18463227733465941882425064117760148238229210562044211009186,3157596631516206420800975662007248841241896590206746033431⟩
def polyval6Tail37 : Box := ⟨19354653604774605171614958464411815098985568705449072425607,2955226872486094623599282343297368186826943855458157297915⟩
def polyval6Tail41 : Box := ⟨20289118542464823546638040970984457647933256024228509107594,2731778279388114720914488688090392442136835333555008202636⟩
def polyval6Tail45 : Box := ⟨21268700522164875032201139130412560866370557338323775425402,2485872749644496004559176298623875805149585447084049527318⟩
def polyval6Tail49 : Box := ⟨22295577846556450874378728316556511666122197059541778621787,2216054158592409598844027416973524407390893423328293282657⟩
def polyval6Tail53 : Box := ⟨23372033989280190143877066827944874744877963355682639463559,1920784226438229018133064175869675195728094255033892976918⟩
def polyval6Tail57 : Box := ⟨24500462672710545242981082855135892769100700190399644006635,1598438173997576187880134445796316583814847902453328784312⟩
def polyval6Tail61 : Box := ⟨25683373190891516652178238179175970148745075105472348761129,1247300156651689189607347322966663683110448187677096027171⟩
def polyval6Tail65 : Box := ⟨26923395989529096320872599530085404930675043082161655774350,865558465426594262043898426227223730015811923637103738316⟩
def polyval6Tail69 : Box := ⟨28223288996027827636108829813527097396161764552379860923843,451300472302777300652409347061388323029088365110505592010⟩
def polyval6Tail73 : Box := ⟨29781250000000000000000000000000000000000000000000000000000,2⟩
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
def resval7 : Box := ⟨98018622754690129556668836577686206390020144551231129256,16067647804887018574293892393576862917729684295111493864⟩
def polyval7 : Box := ⟨26207993368376573808247630882381014295521856748581078097176,7270018259957157974037438280621789735366872813601710061456⟩
theorem cell7_lo : Holds Q cell7 (127/128:ℝ) := by norm_num [Holds,Q,cell7]
theorem cell7_hi : Holds Q cell7 (1/1:ℝ) := by norm_num [Holds,Q,cell7]
def resval7Tail4 : Box := ⟨-34934348582469724825878482170471602618029360714003060983,15395624799720174717830992133622413432869997924234787694⟩
def resval7Tail8 : Box := ⟨-35485644128334268564667045679287184952554177834105676240,14844401453186754481936258418151293291253569391679014260⟩
def resval7Tail12 : Box := ⟨-36045564600247701666374896940936353120548662126266076028,14284480990644037897254989239584077038323553030779282509⟩
def resval7Tail16 : Box := ⟨-36614319929050810994034530129120965453582433841938788200,13715725661850025546180784613729135088093417288312861770⟩
def resval7Tail20 : Box := ⟨-37192049527706140435381997331140109658834412951085461982,13137996063194734452732165351325374525303499373790430338⟩
def resval7Tail24 : Box := ⟨-37778894999326138920243061038842440725313438945893164275,12551150591574736502605871087371564061131262895331535423⟩
def resval7Tail28 : Box := ⟨-38375000181339465608109738757565889207795780408833974656,11955045409561409835161687370637766540352516878733721276⟩
def resval7Tail32 : Box := ⟨-38980511180755060911162155695496285985526272131772921066,11349534410145814533842843664178372528718517032540878856⟩
def resval7Tail36 : Box := ⟨-39595576409973410977982408117276758881765186085324615996,10734469180927464467158452877151282343830876612110839117⟩
def resval7Tail40 : Box := ⟨-40220346623162833063773389009293003167829614678225419803,10109698967738042380913290926065973968428234115849458699⟩
def resval7Tail44 : Box := ⟨-40854974953209734127609379610168428473483171610319384669,9475070637691141314197544648991672133606420788136627084⟩
def resval7Tail48 : Box := ⟨-41499616949251899697918994675614481252456660648230512065,8830428641648975710740247128096972032006104628349165955⟩
def resval7Tail52 : Box := ⟨-42154430614804011808351041370778765791853050375638846856,8175614976096862665468022974689966313081156828664490529⟩
def resval7Tail56 : Box := ⟨-42819576446484671731205865209862697532758860181027683117,7510469144416125348060288189109118112883804404911058948⟩
def resval7Tail60 : Box := ⟨-43495217473332370315002773344945705470608959198026522477,6834828117545170816264986403976876912834745625092137483⟩
def resval7Tail64 : Box := ⟨-44181519261650410760550229646315987124127001590826448542,6148526293179177778364985321505128671885775598068904190⟩
def resval7Tail68 : Box := ⟨-44878048011522942108995087968935530372181756830991176582,5451386282705470522006670390532056281645558254102556116⟩
def resval7Tail72 : Box := ⟨986384154514385358439754902200770412330110971191436127778,719057897272488003923797815606169839749779543039208809⟩
def resval7Tail76 : Box := ⟨-507162171729129128209063096716105739710269063629691311,226457269903292518223450062632772017112665503705230070⟩
def resval7Tail80 : Box := ⟨-515127823470444254272212061491557691702511212433510038,218455280555993328022899432023615117133915901233908537⟩
def resval7Tail84 : Box := ⟨-523255914142216971325081646898305844218540673653329658,210327187754253015741713953901543923746839204490281364⟩
def resval7Tail88 : Box := ⟨-531512258376096174644901806756049721333339153845719317,202070843519069546385247270117121089438557196435019324⟩
def resval7Tail92 : Box := ⟨-539898877718115126552042431230529225312442906880498097,193684224177046716263795812948582171494633394745867278⟩
def resval7Tail96 : Box := ⟨-548417827750313974217021352685848472576074222927407274,185165274144847827682660340542203623933176967307545064⟩
def resval7Tail100 : Box := ⟨-557071196490619514269742348767619903155044965070238085,176511905404542286367095607017594512192436923406710458⟩
def resval7Tail104 : Box := ⟨-565861104903354867755929793509710009411108439620591766,167721996991806932783399012504659976235054375197621155⟩
def resval7Tail108 : Box := ⟨-574789707419089992482059730461065566958298875280177294,158793394476071808042528915825623837715118300071592574⟩
def resval7Tail112 : Box := ⟨-583859192462698467361173436717890639046611013386157526,149723909432463333164297511473499118052445292622110122⟩
def resval7Tail116 : Box := ⟨-593071782989746407801249773307196958301079452347357405,140511318905415392753490502468264635525252390436078979⟩
def resval7Tail120 : Box := ⟨-602429737031344949276482615561156518501676653114666672,131153364863816851597893686512959226700379972289896058⟩
def resval7Tail124 : Box := ⟨-611935348247599849597069123717954909225918415767705089,121647753647561958811702103460785825607771411174566986⟩
def resval7Tail128 : Box := ⟨-621590946489794338169417608856789123131588304183760034,111992155405367959933861712249023411331984012260239923⟩
def resval7Tail132 : Box := ⟨-631398898371552350252602104621405204270642551789352352,102184203523717310317112716110931589888163931502626493⟩
def resval7Tail136 : Box := ⟨-641361607961650365171565566375459842694936687492568461,92221494042995180440273065624167720971712485215322049⟩
def resval7Tail140 : Box := ⟨-651482525103165495951862023061633233609073475400468316,82101559195097285669513721005282200376892364130399555⟩
def resval7Tail144 : Box := ⟨-965246822776984705541903920445805559337172986033628535,67828725606302751344255638636474995986598792466742407⟩
def resval7Tail148 : Box := ⟨678516352758106153773334359926678359025123350458,216297459538990236165105244024789527412414390926⟩
def resval7Tail152 : Box := ⟨689116865345124712461517453863858540777883708436,205592312675689261266163649695078688432345654487⟩
def resval7Tail156 : Box := ⟨699990292368837123342646048631696636506272877614,194718883634201550186916688339685804698348586164⟩
def resval7Tail160 : Box := ⟨711035290922162861667265591818575085209723074569,183673885080179765118928639497170009182249983764⟩
def resval7Tail164 : Box := ⟨722254566168846636857582309756628347188322504237,172454609833494673683558953400583766844497164110⟩
def resval7Tail168 : Box := ⟨733650867983225161905589920496401763207627996215,161058308019116139249611468358176493326198042012⟩
def resval7Tail172 : Box := ⟨745226989630011713450582012747622410603040981425,149482186372329587500602821412198256811803441287⟩
def resval7Tail176 : Box := ⟨756985768448253099784316378533666155609889262272,137723407554088201155280516863440365595657234246⟩
def resval7Tail180 : Box := ⟨768930086546767963145270798299278965915980701071,125779089455573337792880455239711968186987870417⟩
def resval7Tail184 : Box := ⟨781062871510559518029780959855552247885206067814,113646304491781782908158498398269301594960836874⟩
def resval7Tail188 : Box := ⟨793387097118374634806017654626649255931600713922,101322078883966666132479275771190714697428053311⟩
def resval7Tail192 : Box := ⟨805905784071585136274642464354901891760489650628,88803391930756164669146330197081267914405483548⟩
def resval7Tail196 : Box := ⟨818622000734569957896717597416531621956545912260,76087175267771343132614682791076677334537828521⟩
def resval7Tail200 : Box := ⟨831538863886779644630942522921780011338123800291,63170312115561659872049853324859195498104658494⟩
def resval7Tail204 : Box := ⟨844659539486667947233122591141110577877817503971,50049636515673783549304082827387904774657717760⟩
def resval7Tail208 : Box := ⟨857987243447887711702826485171930851230495848030,36721932554657709041350006359353609741988250901⟩
def resval7Tail212 : Box := ⟨871525243047767852330290515766562572045216244835,23183933555422946577720318594802045988483408227⟩
def resval7Tail216 : Box := ⟨885305066658011443390710338677076034249441092839,9431630646863248524678104231208992388608142288⟩
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
def polyval7Tail5 : Box := ⟨22673684352611688379299049971728291249174446244075595575509,6916242005083580541241516289734615029328112325167929414358⟩
def polyval7Tail9 : Box := ⟨23031445266019479167094393811397367430063983276498581976862,6558478769844333261404730068385245854480703161632019880220⟩
def polyval7Tail13 : Box := ⟨23394853562193573913207353393494810400257656379542816585532,6195070473426010878764247689205005273276265429924154272748⟩
def polyval7Tail17 : Box := ⟨23763996001142818329952987739495396980995175896631026285632,5825928034476558580828091018438233939851965100267485070322⟩
def polyval7Tail21 : Box := ⟨24138963060446110633677919511601681289025564799246945561393,5450960975173265494544606550462716033275812877158029741963⟩
def polyval7Tail25 : Box := ⟨24519846645554062042143647276812459200750739816002022750116,5070077390065314076190644890386164443715415012841538084893⟩
def polyval7Tail29 : Box := ⟨24906740112074127646946341412060285062346032819261126266221,4683183923545248471036497982670330564537239650344373188502⟩
def polyval7Tail33 : Box := ⟨25299738288652119095056252880834324582255216229293995976050,4290185746967257022896399108163242027388911984036124828927⟩
def polyval7Tail37 : Box := ⟨25698937500214964063145547757173186275168126705284000669449,3890986535404412054802320767471680366207730146796824221201⟩
def polyval7Tail41 : Box := ⟨26104435591580209042370432323271454349587745779475761316527,3485488444039167075578276635069565533666695517381455007678⟩
def polyval7Tail45 : Box := ⟨26516331951438051474986532903918048730519816770318709702144,3073592084181324642975810892442305555676785766260582432094⟩
def polyval7Tail49 : Box := ⟨26934727536711779296611106478706899592152298529946368416957,2655196498907596821503893083431552893752386827202614492294⟩
def polyval7Tail53 : Box := ⟨27359724897302588697460718265054824209509375618264392894170,2230199138316787424404229883929194092778026972112711946960⟩
def polyval7Tail57 : Box := ⟨27791428201224845370927631555934557495792414141888839149902,1798495834394531003586854392103601003085989171212455773825⟩
def polyval7Tail61 : Box := ⟨28229943260138007654881529489896498775504672940640997712906,1359980775481425420765505572021389400984463692045460381747⟩
def polyval7Tail65 : Box := ⟨28675377555340258766336179986671037760057751698527079993273,914546480336417458757674790246307999829443757464005688237⟩
def polyval7Tail69 : Box := ⟨29127840741322944025819690746034927154520911599673124305822,462083760643251454995917460630690322207842760915874306698⟩
def polyval7Tail73 : Box := ⟨29781250000000000000000000000000000000000000000000000000000,2⟩
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
def pend : Box := ⟨1033474504394942197368374513995698540637231659011195634065280,3507233391534413910555167304263393657070550987154093420⟩
def zend : Box := ⟨1003883568284858398613339843750000000000000000000000000000000,1690408226252497871093750000000000000000000000000000002⟩
def betaquot : Box := ⟨428784739555963416704468957587590480659647640303267020408521,394840881233678122056761237776173532083726186386245667⟩
def crit : Box := ⟨290400887157818796762155429552189720378942027366182457582,8394423414316800304453925022952591693455815805666431628⟩
def subsonic : Box := ⟨223449674925683396667511123454921911010957236781487475896,3776317155781451952448196763581147910825324748447092595⟩
def pendTail4 : Box := ⟨29588144708151419590383305585118973925181648152986055659863,1740011780633743309867688903950469353349546619510837481⟩
def pendTail8 : Box := ⟨29588184132808728694561815100882431769894249260135041225782,1739900937841473020326961181364064486109896354716165535⟩
def pendTail12 : Box := ⟨29588184134696553933359910844560193585591000671712267773767,1739900921805143940092508924094864930872722984420637664⟩
def pendTail16 : Box := ⟨29588184134697582824263949764711815593303100873651518926802,1739900921790588697881526617264508020774838635264712406⟩
def pendTail20 : Box := ⟨29588184134697585562278693930824172687076680511928699187990,1739900921790530001801456062919562905518921741000343743⟩
def pendTail24 : Box := ⟨29588184134697585588053063017000543418055644212078895158972,1739900921790529167645071695580602941349423871974835205⟩
def pendTail28 : Box := ⟨29588184134697585588757759460043142608590437695633351914000,1739900921790529131772815769645659636290461354814716030⟩
def pendTail32 : Box := ⟨29588184134697585588805347322642477194361089983219655448175,1739900921790529127519494166508722194178129626704072094⟩
def pendTail36 : Box := ⟨29588184134697585588811433263753602778468958178195958928290,1739900921790529126201833957082304680636203856656838541⟩
def pendTail40 : Box := ⟨29588184134697585588810805669462207562087556946376441809331,1739900921790529125162263645413203793369295220405979569⟩
def pendTail44 : Box := ⟨29588184134697585588800762340994040370941620144266987924639,1739900921790529123078990386595164038549035900613642472⟩
def pendTail48 : Box := ⟨29588184134697585588711405387619416566181778013051929734462,1739900921790529112263136106973187773840477164680001964⟩
def pendTail52 : Box := ⟨29588184134697585587023812484379025068810485680720076209314,1739900921790528966611061137145197318827490877261165147⟩
def pendTail56 : Box := ⟨29588184134697585502494759398708571121284469141791656695291,1739900921790523913447229403605889197372816587047602311⟩
def pendTail60 : Box := ⟨29588184134697572013740146115741131770483926272746063389082,1739900921789943909392854265628574427142998125258125735⟩
def pendTail64 : Box := ⟨29588184134688682457176545824680275731652075677480651144477,1739900921512119367275833280755207463332632688059617054⟩
def pendTail68 : Box := ⟨29588184095658359462437521743407230897360033774526065956517,1739900063047192397778576796972736793752486364779500054⟩
def pendTail72 : Box := ⟨29584168837643565034409025275999870775893959665978689194476,1689251675855190024436605926918131680388107023872166049⟩
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
end SepticProfile.ExteriorCertificates.C60

end
end

end OAI
