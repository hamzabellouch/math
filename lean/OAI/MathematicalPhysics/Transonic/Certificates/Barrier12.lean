import OAI.MathematicalPhysics.Transonic.Certificates.BarrierData12

namespace OAI

section
noncomputable section
namespace SepticProfile.ExteriorCertificates.C12
open SepticProfile.ExteriorJet SepticProfile.FixedInterval
def cell0 : Box := ⟨250000000000000000000000000000000000000000000000000000000000,250000000000000000000000000000000000000000000000000000000002⟩
def resval0 : Box := ⟨110624338851347349075617124285458272977762089033044987136,348150195448651393015103432199329684684342808300555450⟩
def polyval0 : Box := ⟨3775724102588306733102575581871311716669062392265020758734,15398451532827631672596566442475744390223633533934328559⟩
theorem cell0_lo : Holds Q cell0 (0/1:ℝ) := by norm_num [Holds,Q,cell0]
theorem cell0_hi : Holds Q cell0 (1/2:ℝ) := by norm_num [Holds,Q,cell0]
def resval0Tail4 : Box := ⟨55057176021768593957328534246645104045377122802737,1711659902220713185979698009104561306786439819055⟩
def resval0Tail8 : Box := ⟨6452926930729928745229585768421915969608666045,359746233718639833597796164338933401194859839⟩
def resval0Tail12 : Box := ⟨5688153205882974762209967123953498321104617,479588604802748283512594295090945225607803⟩
def resval0Tail16 : Box := ⟨22076804669202639334863431990341935666785,25802178336340414283561060507569543674153⟩
def resval0Tail20 : Box := ⟨291516815701589645087641625845515828505,370748718301463932391966758282241475406635⟩
def resval0Tail24 : Box := ⟨11240101879596362583302116150162478953,5931213425631407762257468159055848446964950⟩
def resval0Tail28 : Box := ⟨1151603988878959583107069883178314402,94899374480144609149947868070954874325438440⟩
def resval0Tail32 : Box := ⟨294204949009601397406640624427206341,1518389986012054786885234459199651007595464924⟩
def resval0Tail36 : Box := ⟨-354244338175471460711613928471974138,24294239773965848458324954335748579898056534782⟩
def resval0Tail40 : Box := ⟨-138024767602619566395504921025850306270,388707836253036955142200027769391923740958166907⟩
def resval0Tail44 : Box := ⟨-35405781833527789629825370337635303655458,6219325346853363122552864426791202900055281324921⟩
def resval0Tail48 : Box := ⟨-9064141938506768471933359559439113573692107,99509197052006080658050404431008761814631537552615⟩
def resval0Tail52 : Box := ⟨-2320422683283743858328472716521002735365436086,1592144977435548604107995145482722359945160673637768⟩
def resval0Tail56 : Box := ⟨-594028254065914802416986094561046891011927846454,25473762737462072729179955128232565426986373002957698⟩
def resval0Tail60 : Box := ⟨-152071231827287459034873112777460511131897065589550,407437637014760387829934093686278561881887239677434907⟩
def resval0Tail64 : Box := ⟨-38930225523047294714067819892049382224859246117511564,6482505098875551567039590832089480863287932492572480250⟩
def resval0Tail68 : Box := ⟨-9965907458598355225371172702169205744311352071516003350,94376920906087904563915281451489939072879269632710245949⟩
def resval0Tail72 : Box := ⟨761972838657526214924884985371967195311682834984005444719,2488806469510790434904780649805417698005076804080167368⟩
def resval0Tail76 : Box := ⟨-25239018348532961784270084734638939291222815528960,584044110982430016528334118833401900853542340822⟩
def resval0Tail80 : Box := ⟨-1321496103956171525355035283825175665580129277,63179360814942304188105652050393722790505418⟩
def resval0Tail84 : Box := ⟨-724261211243361506592110186331080658601484,54299215477595607857930090994306853104391⟩
def resval0Tail88 : Box := ⟨-1942084749660552152755707221292821594839,364800168896487193351765000593849251547⟩
def resval0Tail92 : Box := ⟨-18749587827290942671079174348034751730,2480031909688566558810659497231460792323⟩
def resval0Tail96 : Box := ⟨-547120514830286532104069464842983642,39635482347572781639104134505275181822254⟩
def resval0Tail100 : Box := ⟨-43348164973395599930144228320925911,634165918781691478273132613502308079143335⟩
def resval0Tail104 : Box := ⟨-8744420545777337075036037040115000,10146654505211848893505220714372851154044583⟩
def resval0Tail108 : Box := ⟨-6120554309885154922400960765644560,162346472028058211131533446000327823874119102⟩
def resval0Tail112 : Box := ⟨-465011990535589152108327427764702775,2597543552021419551410168122239844208365752718⟩
def resval0Tail116 : Box := ⟨-117728639320686960954361805303441457668,41560696721987489818187236081179357414493004335⟩
def resval0Tail120 : Box := ⟨-30134729670205452753078674225776665571732,664971119300572849493936453728941391105291406825⟩
def resval0Tail124 : Box := ⟨-7714463848582805595244458109986918143491323,10639530676500664552672429955954702621313368993437⟩
def resval0Tail128 : Box := ⟨-1974902294532764625687383614053044172161495660,170230639353183349101535172858917707059192899340463⟩
def resval0Tail132 : Box := ⟨-505574981718701076880778746441239832367444179877,2723216253120743078761641730565159025713919577906691⟩
def resval0Tail136 : Box := ⟨-129427218908349699837045070364221326530324728382649,43450122047529369476113441124113844495478200616843148⟩
def resval0Tail140 : Box := ⟨-33133659966158282861133238825263001593067868234283331,664139285702872297339990207335497626982990908689425140⟩
def resval0Tail144 : Box := ⟨-8682840608106559282555649112542802434811002777028636216,2573120062095418320617657959796239579502131322581908805⟩
def resval0Tail148 : Box := ⟨54886560806020837002046354226533758406321430,1059485483619478105881334100970895405817743⟩
def resval0Tail152 : Box := ⟨947770100475838886679727658140967981084,40440340517397584588030415526380117631⟩
def resval0Tail156 : Box := ⟨291728947627047705382023330053212090,19938459309595010075194460645787713⟩
def resval0Tail160 : Box := ⟨495125877180179801342008097289109,50616058102003289219365874214462⟩
def resval0Tail164 : Box := ⟨3203460289337879101493869425703,26461207199966635771099695695570⟩
def resval0Tail168 : Box := ⟨64661197775485577108545669927,416346281693964151468071648973332⟩
def resval0Tail172 : Box := ⟨3603417632606862437477099948,6661347174534591422434214812780554⟩
def resval0Tail176 : Box := ⟨514144502390137691561722291,106581540164169637765502764791447510⟩
def resval0Tail180 : Box := ⟨185867160636910905478917558,1705304639761283236241214085501951332⟩
def resval0Tail184 : Box := ⟨1713796388767486277698747003,27284874233793999970012487385762286169⟩
def resval0Tail188 : Box := ⟨400363094333344036386815512584,436557987365716647058777813173900894727⟩
def resval0Tail192 : Box := ⟨102416207709272395106689753258484,6984927701837468924850101798127311293730⟩
def resval0Tail196 : Box := ⟨26218178333881925168190869493167468,111758818649869451816864946985779712221470⟩
def resval0Tail200 : Box := ⟨6711849324411168118369505018896611188,1788134806039556420897722414958673754001396⟩
def resval0Tail204 : Box := ⟨1718233327382858424577267223053941116482,28608546052930748925287575654579980806417941⟩
def resval0Tail208 : Box := ⟨439867749938709714967190196134051108194429,457324360850854028798983813501036810285273406⟩
def resval0Tail212 : Box := ⟨112606250775630973626159058215204631333085635,7211621468961832393832658493528958025943489459⟩
def resval0Tail216 : Box := ⟨28833394574022568167940975780467742588297139620,88357401328361296116151245543168115328205731774⟩
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
def polyval0Tail5 : Box := ⟨2015781725159877094090571508556688184632393061979441,51623153132382468970038652451354596242569298549899⟩
def polyval0Tail9 : Box := ⟨189367605364877526473089551047318521627401180721,9565339992476527338826838079294253591758354961⟩
def polyval0Tail13 : Box := ⟨144431157732887501886077730680432670538549284,11307618950114491033095452326317291325210174⟩
def polyval0Tail17 : Box := ⟨491211442660051738136426147909069412499671,425625239378865423221339334791587127900233⟩
def polyval0Tail21 : Box := ⟨5699422712547922927026992310139886346986,5930019783833514778113364176843509888698523⟩
def polyval0Tail25 : Box := ⟨192879820156020781241728285166801466425,94866177072520020328055018232652755014696649⟩
def polyval0Tail29 : Box := ⟨17283194853850165385609285028542289652,1517858179353406991677451534832252933567528467⟩
def polyval0Tail33 : Box := ⟨3889220947830450747310260432146659702,24285730789442960868988819775494871238374058641⟩
def polyval0Tail37 : Box := ⟨7731932785131650413870563531162613232,388571692604359626125346606082709869798505824700⟩
def polyval0Tail41 : Box := ⟨1445906189606050672060896875194929542338,6217147080318534867954790928788549133017827738776⟩
def polyval0Tail45 : Box := ⟨369463770184322130981717852726832082179082,99474352938732805392105382829495693737111571033731⟩
def polyval0Tail49 : Box := ⟨94580593671892184332308095448143979262489580,1591589558350467182382497334725509466234012762281336⟩
def polyval0Tail53 : Box := ⟨24212615959863767196259768304790926636086401181,25465410234280869788841365417304638172820629179532963⟩
def polyval0Tail57 : Box := ⟨6198429405690685782790410206836217511437351678850,407440752720975101446635980918576503246032310606618637⟩
def polyval0Tail61 : Box := ⟨1586797924927642924088738399797963152040265444707497,6517564420491488140371850075481437632276961944887118322⟩
def polyval0Tail65 : Box := ⟨406220285720077850006929653426573114697709544210137975,103900199220932694611002358916877762424170851053345761502⟩
def polyval0Tail69 : Box := ⟨103992601031608094039507015137994398202267656164634129978,1564910223632348066263921116001051126548655985152481627223⟩
def polyval0Tail73 : Box := ⟨26781250000000000000000000000000000000000000000000000000000,2⟩
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
def resval1 : Box := ⟨110406311726682262096101000050308083222488845885598237882,274235448185927747259951768191179487571173766823792806⟩
def polyval1 : Box := ⟨3757828712415452526364129335923123368048385782609786476845,9307628997220080292965425398637884875934852333513143327⟩
theorem cell1_lo : Holds Q cell1 (1/2:ℝ) := by norm_num [Holds,Q,cell1]
theorem cell1_hi : Holds Q cell1 (3/4:ℝ) := by norm_num [Holds,Q,cell1]
def resval1Tail4 : Box := ⟨53471778485521781110032690381212052152202678012978,3063398059327675011206279486410105828177591400727⟩
def resval1Tail8 : Box := ⟨6081126198847983900611155925813630441213560340,6107605363045310131344534977788092546972275644591⟩
def resval1Tail12 : Box := ⟨-317309092880751099446890860423583128191676402,19302219498844988648619451922042941425004383682229⟩
def resval1Tail16 : Box := ⟨-2114096923998978075434880870341597138077495162,61003450198614083644005760171107800953601686637655⟩
def resval1Tail20 : Box := ⟨-13855076288526184194636360070671815932386398201,192793854361021146997268189551243190821176655211679⟩
def resval1Tail24 : Box := ⟨-90800629637344861755476132416479827066409675810,609276774876667374905637902110710468280067367821361⟩
def resval1Tail28 : Box := ⟨-595071006453328530420262476123673964863802103277,1925307389853004987776597417202062028963635393459007⟩
def resval1Tail32 : Box := ⟨-3899857347898545177985354136897017713662641335054,6082902981911626388365061368055617036785194540322130⟩
def resval1Tail36 : Box := ⟨-25558105115189314826642252310042685843223986795106,19211744695507507240287029646609007404964128009364344⟩
def resval1Tail40 : Box := ⟨-167497597682905422534707908532604129079850315327772,60631879154902407281230811637815332599069480452786720⟩
def resval1Tail44 : Box := ⟨-1097712256174689598044112265229275967351571489359431,191058342665576421857194782326005393358365870547377960⟩
def resval1Tail48 : Box := ⟨-7193967042066443818839659331462444066859769888747274,600114058389640767156342085773362418636535318195490335⟩
def resval1Tail52 : Box := ⟨-47146382406886520053976464858810732608706394825532009,1872246883155052159090668341204255996992116917999088299⟩
def resval1Tail56 : Box := ⟨-308978531741759456246163916030986612095187138401040875,5757252035960157415514762950976452101104764524352170425⟩
def resval1Tail60 : Box := ⟨-2024921705619094382067337606206149028892049531096914888,17147362557731505014492773396862906025569611976747162890⟩
def resval1Tail64 : Box := ⟨-13270526884160165780606791961326342438729385628258982136,47323359177367414300099693051830629890667800155401359567⟩
def resval1Tail68 : Box := ⟨-86969619508220961528369400061427631974416003328694019885,104536889100236947667020637860922249600744569042057858563⟩
def resval1Tail72 : Box := ⟨764705726554723259410781307459786345525956923230914361743,1578512898448393926576827116334983427917825737723082120⟩
def resval1Tail76 : Box := ⟨-24680347262351055669000325805115465048341323086199,401936775136079465124983576489712485463712232693⟩
def resval1Tail80 : Box := ⟨-1263513236349925331716725009751841978027910190,61190556466526470254737838247195965053007874531⟩
def resval1Tail84 : Box := ⟨-3363384881516190889907835352671204530301898,193263476653072874118552084947650675625742521425⟩
def resval1Tail88 : Box := ⟨-17609793964883419579900233285947304853046001,610798907722730839198625505121046738226345555942⟩
def resval1Tail92 : Box := ⟨-115395962004534028834013784921163110953996970,1930366431587916442617843202885653217145217788040⟩
def resval1Tail96 : Box := ⟨-756258868025861299686426226353737535350354783,6100519640496553089275349958143530915411079129361⟩
def resval1Tail100 : Box := ⟨-4956218114439577760172396835287356974689347115,19278088599628924581039448772442146560768777911124⟩
def resval1Tail104 : Box := ⟨-32481071034560965121997380931626890872408489125,60911463044302379911163435385949898031951483914450⟩
def resval1Tail108 : Box := ⟨-212867947132055884196238448699935944876713682507,192400091232204428135477731338612926189467520738346⟩
def resval1Tail112 : Box := ⟨-1395051378324623285508865290506470462439567773531,607357017139084503140020888147054563907692127641203⟩
def resval1Tail116 : Box := ⟨-9142608712988236673156175105285887072142460429936,1914814546107465293728883026680451648200969818256993⟩
def resval1Tail120 : Box := ⟨-59917000461439713813241458177638117646963279587657,6020737711069870229776530877928197327152959662711697⟩
def resval1Tail124 : Box := ⟨-392672054224092276292761932795849146328318820129794,18825199626664986904914680074875623315022658841645850⟩
def resval1Tail128 : Box := ⟨-2573415574563085136826416558887581941908516112586454,58164549244049371680595780000108207125068847604603643⟩
def resval1Tail132 : Box := ⟨-16865136309472828971508930308771254174856050836629479,175096826574055749078872583252546152794619273484437541⟩
def resval1Tail136 : Box := ⟨-110527357333683329910702342701726258505682587542903278,496167241421913628921232536084008285794861740416074514⟩
def resval1Tail140 : Box := ⟨-724352228235264663767197782816844321307959348256360105,1193102416989163530970718214366211124956602017876989094⟩
def resval1Tail144 : Box := ⟨-4830605482921949464354537610867004452589288351824094606,1296729134413134438268866335592866268795557835731950319⟩
def resval1Tail148 : Box := ⟨54079004843870070162743112592031043430285401,776246319104429893596781504946651769336202⟩
def resval1Tail152 : Box := ⟨911800485012613120476219923121563840842,2700196583943026362261039897249472315234⟩
def resval1Tail156 : Box := ⟨378068203369075497343073383062249768,8448810967753649571936094874384294147610⟩
def resval1Tail160 : Box := ⟨679100098720014541908435075096130837,26702061199815416781362123914255563823977⟩
def resval1Tail164 : Box := ⟨4447571352752907867287643743367523644,84389396873608177224071192968850545014107⟩
def resval1Tail168 : Box := ⟨29147584869069107369366884951227398488,266697076824688295502196800400454478236367⟩
def resval1Tail172 : Box := ⟨191021611831797183665057139561190665761,842795564176221076377637924840587164884756⟩
def resval1Tail176 : Box := ⟨1251879235281322979860996828721981974360,2663002021526950353157781211183075005522972⟩
def resval1Tail180 : Box := ⟨8204315756337063593680907279069912867361,8412153691590961781950539595224300286822428⟩
def resval1Tail184 : Box := ⟨53767803740729764645879043083626404965644,26558721700961843978820230534961848870064721⟩
def resval1Tail188 : Box := ⟨352372678595246056330761104833657408199737,83756236126390665798020710760408052351201376⟩
def resval1Tail192 : Box := ⟨2309309586441804155295713768129025889224131,263515429352772929620416035523105579628412815⟩
def resval1Tail196 : Box := ⟨15134291305705013728286018398855127570458232,825003155218232916213571407221096311906692482⟩
def resval1Tail200 : Box := ⟨99184091501068735902505303802045283432176422,2556065122204216859974494548992986495735929837⟩
def resval1Tail204 : Box := ⟨650012862061449478408462894502690542197081075,7741885887426895679366101726897025627047774602⟩
def resval1Tail208 : Box := ⟨4259924292826726402129501436497716643334180239,22262619903103331955743707439896952627854356045⟩
def resval1Tail212 : Box := ⟨27917839902370481499420683074588995326385504714,55906497354408961777069352420387245629657608686⟩
def resval1Tail216 : Box := ⟨182965089604079466544249875919378870730835488604,81963381463515525552252266194580951919238915053⟩
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
def polyval1Tail5 : Box := ⟨1961850524258241367534422352981862421864000493165115,117176674450466760784615673934889154254603614965361⟩
def polyval1Tail9 : Box := ⟨182536755312339043569686213850579732509770255199,269707815339559513927279261914274418771688220580862⟩
def polyval1Tail13 : Box := ⟨15254664685064234631479800563649918575764865503,852386338438511972224840549838214128309273178774203⟩
def polyval1Tail17 : Box := ⟨99092895150311794752911276186759140913595726379,2693910457020983206125233097468009948066791347802501⟩
def polyval1Tail21 : Box := ⟨649412281004004612769664679176432882852371070007,8513751139136529655262103271445283192469220393095105⟩
def polyval1Tail25 : Box := ⟨4255988291946273394189943702959136353168198258211,26905454396419247978559572388336936493018395793821578⟩
def polyval1Tail29 : Box := ⟨27892044869028262132298873648349369881631956305444,85020081516686822280987798918171729797083015152169052⟩
def polyval1Tail33 : Box := ⟨182793305253572490373943976389131104135980572246879,268610802148552528584857076452407028254003865032617414⟩
def polyval1Tail37 : Box := ⟨1197954205309793917667850816579422787374894153496277,848322545006719356139751838829741133813540660291122062⟩
def polyval1Tail41 : Box := ⟨7850912679918256810798327642936739206956528086469392,2677053381126001028410879793188102561265299219701267215⟩
def polyval1Tail45 : Box := ⟨51451741339112280679326624653682038741973534135385032,8434171705751200519747988691468355100480208179092492043⟩
def polyval1Tail49 : Box := ⟨337194132040006248755230235679188475755686750249180177,26481566392097278665029294584853233627366072283099953871⟩
def polyval1Tail53 : Box := ⟨2209835463737385577879146458720686887781511285762043529,82550691624894033950292588438128076513924009179190835327⟩
def polyval1Tail57 : Box := ⟨14482377695149379305604068850349009319476151973361445847,253402744955340084266501336012519340289191157515997670067⟩
def polyval1Tail61 : Box := ⟨94911710462942141868769424085917071553852913661610064065,751737566062070355531559447143807766903551687277840030537⟩
def polyval1Tail65 : Box := ⟨622013385701252988744280508329559949029017189502078492931,2053816426534919235529206334112221317428949654719201487918⟩
def polyval1Tail69 : Box := ⟨4076427023720418827208674568743924674202201207375073638066,4380516659660090461199388302994132591325429552260687743973⟩
def polyval1Tail73 : Box := ⟨26781250000000000000000000000000000000000000000000000000000,2⟩
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
def resval2 : Box := ⟨110298958550078277984976210281886130052380867108611891782,257365708055884740763393741987674328546130552031562872⟩
def polyval2 : Box := ⟨3748985721925719475429469482072303715569052678588501541342,8046497574497028397578218186880427812642976408462750139⟩
theorem cell2_lo : Holds Q cell2 (3/4:ℝ) := by norm_num [Holds,Q,cell2]
theorem cell2_hi : Holds Q cell2 (7/8:ℝ) := by norm_num [Holds,Q,cell2]
def resval2Tail4 : Box := ⟨-140425668704101741230868006677498656319919795858313,33915529687753026824877379185290238524838057830010902⟩
def resval2Tail8 : Box := ⟨-443182320293846167141934376161419685599453015711399,57743339838057812591548386869316250257278205155236759⟩
def resval2Tail12 : Box := ⟨-1016938777702757452932845829353316085012307191553383,98246709123283411969136770276808692937891263963257485⟩
def resval2Tail16 : Box := ⟨-2333465217221923093126959937277079073689653691674917,167005935791725615204011702084057324871376111987930152⟩
def resval2Tail20 : Box := ⟨-5354363519383059527240650326341819160735683172722789,283531178560051593647947138782372985450120763521976838⟩
def resval2Tail24 : Box := ⟨-12286109296113715118140291389263254614464983313385110,480539871694042569759852761760686526434457362828746814⟩
def resval2Tail28 : Box := ⟨-28191676020801407388262945922569875055084337267915448,812547690133167844552157263140035877614077313153101002⟩
def resval2Tail32 : Box := ⟨-64688550110263684255194397377255426198222456600606483,1369575691358565161452789889261589823334261814036368059⟩
def resval2Tail36 : Box := ⟨-148434187179238850943559486960570363486125192381920824,2298357288479371291673868741842589347295433569032618521⟩
def resval2Tail40 : Box := ⟨-340596718986681045431690103321229659188194727626240247,3833521516872405645152439616782460044470816533429985364⟩
def resval2Tail44 : Box := ⟨-781532389465044255694985039948041643674678694373475105,6339329040805184433801741628915214281079814114295247140⟩
def resval2Tail48 : Box := ⟨-1793302288994823017977843430540166074635724779572031856,10354572937322068568325244349988925871691940317583504651⟩
def resval2Tail52 : Box := ⟨-4114906999459567857095435079641904004853228315316217111,16608831828942759331711451555231001746411659108905391119⟩
def resval2Tail56 : Box := ⟨-9442055429312066674404774936477005365915432746995466437,25911728094692891555751892313790251404968771624300965917⟩
def resval2Tail60 : Box := ⟨-21665717048258396318484038835348658710585684058339693876,38646276835255421530449074476102565593927051778391479685⟩
def resval2Tail64 : Box := ⟨-49714100778752177348988509348225375611203149831468363507,53175498111560109839945710833732442924850912087789647463⟩
def resval2Tail68 : Box := ⟨-114073769882907750938435436941748192577538891685113588599,61451261849923768787140836930417090626873189865051265310⟩
def resval2Tail72 : Box := ⟨766070564142002242031170693959732866922879471337925594851,1123781921940403013580419458293412032837263990780507499⟩
def resval2Tail76 : Box := ⟨-26503392230112443919449916623848434522849835928889,396176558480728298552057434087792067826310431192457⟩
def resval2Tail80 : Box := ⟨-4799114680015427110194724971716421020348110747393,674467218573591436165342525368211264136734772369969⟩
def resval2Tail84 : Box := ⟨-11009201215783734678153162349951076208815040239477,1147787050389589611023119074593244902881670187364951⟩
def resval2Tail88 : Box := ⟨-25261684394287096625403910757646109580984749475525,1951593560862583108988725734888078540224456222261095⟩
def resval2Tail92 : Box := ⟨-57965398562841925971925178157166067670515103081490,3314462375100255357422957749720429251211479655537829⟩
def resval2Tail96 : Box := ⟨-133007260257462566837701177433930442645275627719673,5620205634754607825919868382104792501061824779089358⟩
def resval2Tail100 : Box := ⟨-305198130605827485269438149738608178850485568337563,9509529073879569646448964909690173062143636131110827⟩
def resval2Tail104 : Box := ⟨-700306876068187670760333910500831728931342363478777,16043184431542052445447160312172491531459301113025432⟩
def resval2Tail108 : Box := ⟨-1606922426735924752479822605314157532946543900343159,26956734547846142508394768079101108181678570382030578⟩
def resval2Tail112 : Box := ⟨-3687240228233099838184351764502798881594770854262508,45041097534319231479368070342625076550976345627792421⟩
def resval2Tail116 : Box := ⟨-8460732313206275376992029366450940435735607997041345,74667660637820109079110075270556083739952476288538756⟩
def resval2Tail120 : Box := ⟨-19413975451779925926502277050430628369551920336216708,122399392947805276412720096632807052194880480825343835⟩
def resval2Tail124 : Box := ⟨-44547260082204728717134598307446769859262155841355148,197380085592389603193981079010603442350697657416342199⟩
def resval2Tail128 : Box := ⟨-102218032868154861974482882634168356024396110451321776,310499338178550059432943894253929112150142458037489302⟩
def resval2Tail132 : Box := ⟨-234549245546296855974747773576478479882184686593362075,469528368700821383589333479835279316420385308556802267⟩
def resval2Tail136 : Box := ⟨-538196119060598360788170877378996692847678017096912594,662929207046413242073116574778184042353039939351868085⟩
def resval2Tail140 : Box := ⟨-1234943594370050571244940177353414569448679605274006114,814123280921110717046522780267420276984952707582029151⟩
def resval2Tail144 : Box := ⟨-2898332903122720921558729917962868566562532010877129879,655120273830821871100123372919798484587401470318160552⟩
def resval2Tail148 : Box := ⟨53916664038186068556265503477433372254817900,41508307501432994243062109465157912813614355⟩
def resval2Tail152 : Box := ⟨525966131596993080511413448386768394901633,69655403992432875006454516329152018491975760⟩
def resval2Tail156 : Box := ⟨1204827368806938379967742753458576198957134,118519951527392091290186616465742343142294688⟩
def resval2Tail160 : Box := ⟨2764593290705857165521286295601098093216853,201480593403339221400601564913273820945828732⟩
def resval2Tail164 : Box := ⟨6343628930048329489136766299637283284529541,342089642497268343234641439652595608398323422⟩
def resval2Tail168 : Box := ⟨14556075262052100348939338682291355335130908,579855703066260147863664468129937926912834411⟩
def resval2Tail172 : Box := ⟨33400334315109522047119060190565128027403026,980639917260386833080282697605336899589404861⟩
def resval2Tail176 : Box := ⟨76640324557088948653185864888383204879549607,1653267576506315074298595831183056170245439631⟩
def resval2Tail180 : Box := ⟨175858699281306022804508158950423973970275321,2775287807489082513869230287988042539969641212⟩
def resval2Tail184 : Box := ⟨403524936665371363223321242449870686550842408,4631000715867536360987367736665562236465146494⟩
def resval2Tail188 : Box := ⟨925927322198164548127911053024262089708255567,7662751175417324847234222285586083267922301581⟩
def resval2Tail192 : Box := ⟨2124630544714082554514287213716533491346424297,12527275796907343752953415621288881438742705154⟩
def resval2Tail196 : Box := ⟨4875171996021922010728818195561403985485205772,20120333366444284641652199114699726426224222206⟩
def resval2Tail200 : Box := ⟨11186557611123304184114264771018174574261182336,31454671028885685039048094959103643732350561552⟩
def resval2Tail204 : Box := ⟨25668647442406707723592737694183705944452448257,47075406080907285447964804814318470189976149756⟩
def resval2Tail208 : Box := ⟨58899214970976274128140208457504956886048786134,65198928815583085786680513303651539238235522624⟩
def resval2Tail212 : Box := ⟨135149993124711829073120600280404503314945957860,76555961496028530654417379170896757569541331867⟩
def resval2Tail216 : Box := ⟨310116976682240164404662524759694835895778035579,51045913442734267232787043776495306782176380512⟩
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
def polyval2Tail5 : Box := ⟨21659996058782021013900177218436717593426435280946894,3025627711235383141036019289880755880950828880263947551⟩
def polyval2Tail9 : Box := ⟨45258444019593916530382777496729037142234947668536746,5149970451854113217750757879015048281215578223223726349⟩
def polyval2Tail13 : Box := ⟨103849510021360683422586029459220412995864767800572768,8758981323947480695052928344990538088538017367788329337⟩
def polyval2Tail17 : Box := ⟨238292828691622742551078100723186218784335082075181417,14881305295173263695827525948831956721373915839982107689⟩
def polyval2Tail21 : Box := ⟨546786135678246143801680513381482941315616972521760686,25246580759510761983295811619796190434487198252720392810⟩
def polyval2Tail25 : Box := ⟨1254654115325416884367975784411862337994928425409670943,42747691075301054411555055750148618146548744118098504809⟩
def polyval2Tail29 : Box := ⟨2878926231643377723908132850106282421311454447994118832,72187132036080914569233207922320666888814168287694394532⟩
def polyval2Tail33 : Box := ⟨6605977014704681269041323552068977183877624530240252260,121453404353308105561790165081021201713120530850814201084⟩
def polyval2Tail37 : Box := ⟨15158058528611953065503287038878903151356828305442270236,203305592484874250536913176736298086416768406835694929299⟩
def polyval2Tail41 : Box := ⟨34781643630514091105229582857605558608533614786873391567,337907700205903855563812110521855407706279162611743890893⟩
def polyval2Tail45 : Box := ⟨79809873497754682073705949806745195173084150509690037918,555981693496817541815678459511923402172333876971252050420⟩
def polyval2Tail49 : Box := ⟨183131538445742475584413913368979457042627437100276345017,901500805748246624416870441575006630738374047822410895314⟩
def polyval2Tail53 : Box := ⟨420213175434339795517319192806602436956975345235380325152,1430121719117338403135688249815872031457933106189921606923⟩
def polyval2Tail57 : Box := ⟨964220113625744690437578775122844540706871078739236361924,2192369527392028733057640137274911589202836319154503792063⟩
def polyval2Tail61 : Box := ⟨2212497089267780222089300341368236296400819337494043032864,3172505480331894483253600064519743240463155913447587752400⟩
def polyval2Tail65 : Box := ⟨5076790351966472477059228287414527827563964342305732813416,4109786293222744806764670282651835771223838450083532842279⟩
def polyval2Tail69 : Box := ⟨11649190670632996707723186192058631962741868032531668928967,4022703583610077533886239518322104081013796362079743191241⟩
def polyval2Tail73 : Box := ⟨26781250000000000000000000000000000000000000000000000000000,2⟩
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
def resval3 : Box := ⟨110116266994227316089230226972685748680254373153879530432,1784185216982711829709349738566565094668499015339187291⟩
def polyval3 : Box := ⟨3766907664428817175649377122386623264123025251884820917662,237372637884336883615220362016770835354431234976589136247⟩
theorem cell3_lo : Holds Q cell3 (7/8:ℝ) := by norm_num [Holds,Q,cell3]
theorem cell3_hi : Holds Q cell3 (15/16:ℝ) := by norm_num [Holds,Q,cell3]
def resval3Tail4 : Box := ⟨-192033226308119202832468358260385788389947755278859502,2002956253924209983937668679686705522854262812024662131⟩
def resval3Tail8 : Box := ⟨-284775530987801914376001573844598667470156125801855249,2556789243158532962196302727636715576299510322702182718⟩
def resval3Tail12 : Box := ⟨-422192584524794209887022306643833287481958843626594723,3256321774326174480020187236199551392137399422087308008⟩
def resval3Tail16 : Box := ⟨-625919558868275495241495688128760981577921417655734064,4136058061318859544627020947582884882447926824202976465⟩
def resval3Tail20 : Box := ⟨-927953991921004874601278308783596058456561910058234278,5236608285937468920472211089162538131874009039078531304⟩
def resval3Tail24 : Box := ⟨-1375733668842454199273742824265592069322897954555279790,6604528127537455976204877850281598864853869080463025756⟩
def resval3Tail28 : Box := ⟨-2039587246851174091988761229840750918423182620861959148,8291167065989394673105988965199237810823160198732076086⟩
def resval3Tail32 : Box := ⟨-3023780133997967887475789433281140587854082602664951537,10349776698521923759471360284001353461271348666038129840⟩
def resval3Tail36 : Box := ⟨-4482890502907688988828426749464384964041482410693773779,12829690644273024472482738884611105956425449278311499151⟩
def resval3Tail40 : Box := ⟨-6646087470152503586487204144499218596074345732385999327,15765711405139056658392131593742818158796740586396917636⟩
def resval3Tail44 : Box := ⟨-9853124592775193452749810663233447889994974121305978811,19159806786802242442210989310425452673782614821417741652⟩
def resval3Tail48 : Box := ⟨-14607701851165012557497091607666530098274850184839647804,22950648191145838574010682420344258626515694027220881846⟩
def resval3Tail52 : Box := ⟨-21656577196739632647348527004216538912285281242785531915,26964144351366716637255277636132924264518895916096328888⟩
def resval3Tail56 : Box := ⟨-32106852991453821116866708971023019974780667781865716692,30834531845616740020051527329976091187051723021539870449⟩
def resval3Tail60 : Box := ⟨-47599858447158471197286397382308999668151413090014932319,33880173092241122229791194733125896717853587236658425165⟩
def resval3Tail64 : Box := ⟨-70568938184535543185386098296570155832270932475196497803,34910081010395276334278711955485890966771340636981301529⟩
def resval3Tail68 : Box := ⟨-104621560570500236587951065705314316043643335962085912299,31924990190873859459970809146578768673197575220668875839⟩
def resval3Tail72 : Box := ⟨766751027833600933260981217915160014973475162945762093570,915608498527647941573624740234842415157570438268419800⟩
def resval3Tail76 : Box := ⟨-2343307184311347102200989084392686632585916184911087,25125328428132070169625370630519785869703525677674801⟩
def resval3Tail80 : Box := ⟨-3438061902519332782545223029357324566233545577517261,32089525170629888858927131692299675602975945746553147⟩
def resval3Tail84 : Box := ⟨-5097080107657501943522429543001759798239845667136139,40894739455226400915134601042029319879410342552007406⟩
def resval3Tail88 : Box := ⟨-7556651274800043963159048191283393064734119030464548,51981519329252831225562076806324387949290608306437197⟩
def resval3Tail92 : Box := ⟨-11203076524214563022617531081836468677300398296850032,65871363944073794495326453971214913226233001705070341⟩
def resval3Tail96 : Box := ⟨-16609066508862522589908048973164337544122540569331489,83166746439873176594835864795792179271860107448797689⟩
def resval3Tail100 : Box := ⟨-24623690617444874189323177088999258327574104005734087,104539917825189056745267243804500808639194898023303058⟩
def resval3Tail104 : Box := ⟨-36505732534703853727836237525718582203116269904925502,130701501892880487915890855800701483567499830660381218⟩
def resval3Tail108 : Box := ⟨-54121395878455137522557228902274756423725871276831093,162334768377271626203630968725392810961392941595131707⟩
def resval3Tail112 : Box := ⟨-80237411728361110056870537391888557592634315278769964,199973377025482034387206574359624301220961763684873068⟩
def resval3Tail116 : Box := ⟨-118955583764413266215166613665291555515042668755360356,243788006394043312835006522791616385846620253152198943⟩
def resval3Tail120 : Box := ⟨-176357021044469461316742388481051240854904849819796788,293228439195029015059996752874551414584463152389044237⟩
def resval3Tail124 : Box := ⟨-261457242169273047949968153760548985276343687337796711,346439107899976773141095384470508562349986842802081193⟩
def resval3Tail128 : Box := ⟨-387622160308120393319611527166062257984141032204815174,399322930025476821134804859295361757788365254054135343⟩
def resval3Tail132 : Box := ⟨-574667344898642108648092903101758691078970511572118593,444063192189815774939747682395568434655122806670207463⟩
def resval3Tail136 : Box := ⟨-851970271861878419295839981443567612964849956056113716,466815396862307653403824111914936993479205552869061695⟩
def resval3Tail140 : Box := ⟨-1263084474414802575749543353874120991936172002677930482,444134136489313847532557661498021582360226947784702934⟩
def resval3Tail144 : Box := ⟨-1930656603843885494305685163912361490973214114273210106,333461615923934168333187414023224816507232699776921938⟩
def resval3Tail148 : Box := ⟨531823433642714764191202460833514017539963379,4674009017318697013602862995104819438913579129⟩
def resval3Tail152 : Box := ⟨709143992558347999414241795581910557246171253,5960198207522212840868471116894404562725057646⟩
def resval3Tail156 : Box := ⟨1051336656157110404370416711803835906067730984,7582380906447921373712551199747677203826190107⟩
def resval3Tail160 : Box := ⟨1558654036077812121849193987424026278879876211,9618023774595572110396864241344685521353656169⟩
def resval3Tail164 : Box := ⟨2310774945932210548727059654490485743414160595,12157862229381609340640000200251267483840233197⟩
def resval3Tail168 : Box := ⟨3425828135784519663947997485600829403441750481,15304376425625185446917799801107652357552042777⟩
def resval3Tail172 : Box := ⟨5078944808793659718228973580074453695301793372,19168021830940590764958855337122659239358883763⟩
def resval3Tail176 : Box := ⟨7529764876796662896499153086136954952635920778,23858861408667511710699927929526075672252904575⟩
def resval3Tail180 : Box := ⟨11163216225873362345457803016567197312720380347,29470561793764764015743166583738083459564494302⟩
def resval3Tail184 : Box := ⟨16549971817794323323673172990855833657352092222,36052008948526748265514065371557957872061363824⟩
def resval3Tail188 : Box := ⟨24536080071167612834888273474079828108379795249,43559197193061873538824667800305190646600371869⟩
def resval3Tail192 : Box := ⟨36375845946242937101902567730432629481940738696,51776096587851751668648023131560000345995681878⟩
def resval3Tail196 : Box := ⟨53928833149664184420273514109841681802278855640,60187230177040596293482485023565124640222397213⟩
def resval3Tail200 : Box := ⟨79951928793142007315014898537531972385996352600,67775682588170082024344484154903956924923063364⟩
def resval3Tail204 : Box := ⟨118532342429950329640604080098370206670762451068,72706704275939461147140906391634858399913612299⟩
def resval3Tail208 : Box := ⟨175729546666513946727765222177734118504161703935,71836718319518476373359963761497748096615572095⟩
def resval3Tail212 : Box := ⟨260526983129129851360671700720699109505532895809,59957021690709976451080597232325835464141206337⟩
def resval3Tail216 : Box := ⟨386244935415657998230440327448218627467608282984,28635633656738121054827986102161671233396771545⟩
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
def polyval3Tail5 : Box := ⟨33111368273606970938964887313651561508022452482014400226,298926157737525956537807813905071386660500383516013391046⟩
def polyval3Tail9 : Box := ⟨49086246016337580064946121581793307579150803453557094873,380746538404691513920486808106555817218961836293382063359⟩
def polyval3Tail13 : Box := ⟨72772574578533637598092864406557259910208499808905373847,483662415017543882306679153750010554991783222064957068590⟩
def polyval3Tail17 : Box := ⟨107888625823579094551463256089036049083456866318184781097,612437763868471091031385760337823945567148910870351614589⟩
def polyval3Tail21 : Box := ⟨159949756478096878764945838100651124242682918018520702694,772540323025274442101581429753215948426725413007146634832⟩
def polyval3Tail25 : Box := ⟨237132732038294409142808544566844859399685140839736544835,970011363770751370126108262853065804591826134080154542144⟩
def polyval3Tail29 : Box := ⟨351559976345733305734578701663566130051987368284156817645,1211134255021014826223254477768387063966493071417871204502⟩
def polyval3Tail33 : Box := ⟨521203529794669511527182078508618756795340405371626389107,1501763959525848129464480423781930387685845554004717802488⟩
def polyval3Tail37 : Box := ⟨772707753294624594351132339893132778927869998007286620443,1846101083843339733943034335080300424612378282579679933541⟩
def polyval3Tail41 : Box := ⟨1145574114275180979902015974680123179936905361002031531088,2244574151417137641708943975656743609699147687246040060813⟩
def polyval3Tail45 : Box := ⟨1698365320785108282540470220863803301742497646843574692915,2690311355568704916194899308521152995071773525611232454004⟩
def polyval3Tail49 : Box := ⟨2517903230268543482002413696819356887879647413913609600915,3163406688971426923795273403082340306198884321013650959307⟩
def polyval3Tail53 : Box := ⟨3732905164400101587151947755888015156342694229942491986795,3621767958904801139620750223706081409726834954258747468523⟩
def polyval3Tail57 : Box := ⟨5534200361194491229339665493104589857363445439540129352809,3986705472067930635281493976464765062122768286654387492877⟩
def polyval3Tail61 : Box := ⟨8204701777567728981909466414446708152291232303003922111366,4120475203937188775529541942581460274545300229046150225356⟩
def polyval3Tail65 : Box := ⟨12163840639181254245047880063542873582151954007956510094982,3791572667688585819925758553695093865310355276234953856732⟩
def polyval3Tail69 : Box := ⟨18033442736632325069841491027855830421708421339999168871338,2621450493223358591287066768166919925518954967939269142890⟩
def polyval3Tail73 : Box := ⟨26781250000000000000000000000000000000000000000000000000000,2⟩
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
def resval4 : Box := ⟨106762590724674390272841190263558423616997315106803427044,9097309977014622784703303085296175441125122123648329317⟩
def polyval4 : Box := ⟨4585544505536391057282071351630242992372591857892098514822,1878309130590623609861013771849962703246180236344603105147⟩
theorem cell4_lo : Holds Q cell4 (15/16:ℝ) := by norm_num [Holds,Q,cell4]
theorem cell4_hi : Holds Q cell4 (31/32:ℝ) := by norm_num [Holds,Q,cell4]
def resval4Tail4 : Box := ⟨-4188532091154951875083967162698519774849282559470800148,9827595332881122358833829864529223741901144319925242019⟩
def resval4Tail8 : Box := ⟨-5075371210586689513748305989631572198201236106769180348,10838754054240532900160333438751509535102593507957318166⟩
def resval4Tail12 : Box := ⟨-6149904449914106873620366306180855222926869263763384659,11919170124156187602048040057127916531023967638740733552⟩
def resval4Tail16 : Box := ⟨-7451932702076622181157371055253902236573494785868027705,13063895243996468518471638278856444203760554956616923236⟩
def resval4Tail20 : Box := ⟨-9029620126376104231470886370854774741046576528091814041,14264278771842296260511733040505021465584287223036593491⟩
def resval4Tail24 : Box := ⟨-10941327959649341756494263821422266532178108415149835069,15506823550817943486546756004305465746328441503458920859⟩
def resval4Tail28 : Box := ⟨-13257773399671156922736523389941076170040994720070129126,16771751557790280444005306050274347634463149335762102463⟩
def resval4Tail32 : Box := ⟨-16064645549904648527581065956028367657364203542451020541,18031210593913504117386250690046872522507279427866391169⟩
def resval4Tail36 : Box := ⟨-19465775199512190538158259483115070123798917185395576512,19247038533862863443186280602486592024751736258519847096⟩
def resval4Tail40 : Box := ⟨-23586975693976199444402311559880730936337960899201876396,20367982962391636916076570580656921481297127877982333319⟩
def resval4Tail44 : Box := ⟨-28580696976412526832601705686126207849798445840479766845,21326251244645316333976634115980435528870422322181866490⟩
def resval4Tail48 : Box := ⟨-34631664960172507232526841331049855376756747815946527436,22033238315274341243245303986134246424461910690963498587⟩
def resval4Tail52 : Box := ⟨-41963714842344755323960370819127473475184426609771537919,22374245655526927570480999005737143204967574223872315546⟩
def resval4Tail56 : Box := ⟨-50848071133593385505623218104883444961839831023641504467,22201963751391674928712780467507920205031673369280023517⟩
def resval4Tail60 : Box := ⟨-61613380696168881347191427703031796219403474217938953287,21328440204011406859493760943877118022409232174674550612⟩
def resval4Tail64 : Box := ⟨-74657869924537044743121540463683976436609078608092083406,19515194670942784753790473665858136173133193365920738188⟩
def resval4Tail68 : Box := ⟨-90464004405151761372669244903025713855260460172750135502,16461064915776229575422976788373522571137266113748432979⟩
def resval4Tail72 : Box := ⟨767049638652741494361164029781585585615182913318577482909,896363204293582724870966312217849945975304356919290573⟩
def resval4Tail76 : Box := ⟨-53182095906558180962697740975206717508057436494202303,127696166087524838354512015207532169867300951959478747⟩
def resval4Tail80 : Box := ⟨-64412212039108371761639145797653326080715273543321797,140931297021729346909392022255506348067644806044583524⟩
def resval4Tail84 : Box := ⟨-78049254936360565376858712196126891049667374812036799,155100044391461926860097736949185923245083861795057234⟩
def resval4Tail88 : Box := ⟨-94573468574113410970544739669807110994981700787242106,170146835231957648756106241638034883945004895320319266⟩
def resval4Tail92 : Box := ⟨-114596109411994932960252480675382783900658982186758968,185970263506166107188664870336260815226439834665905453⟩
def resval4Tail96 : Box := ⟨-138857847664484355460687749676858572936946338803889871,202408550229048779753041803793393720284316469014312554⟩
def resval4Tail100 : Box := ⟨-168256164689609649103710659348989445749333181231377077,219221493574370704722010956794494923514209155647668798⟩
def resval4Tail104 : Box := ⟨-203878552290839829682371237250945223716303325614861661,236067884218791747143491183328898287396795237158170699⟩
def resval4Tail108 : Box := ⟨-247042740816589952457347710832147750931861611031907441,252477329230028847003495769092108207327654124774621132⟩
def resval4Tail112 : Box := ⟨-299345444159870535549508289801901810537178572426065240,267815191027854870004365629717715493908681248885121104⟩
def resval4Tail116 : Box := ⟨-362721424815299157849447397155061842954608160911646345,281239059247980783653676542243967153728900276455144834⟩
def resval4Tail120 : Box := ⟨-439515063906485281504332585313437972338565843678783618,291644821507206262031689917971261355761382002381493417⟩
def resval4Tail124 : Box := ⟨-532567083676095036998227203383314508934958394065401329,297599970465117804690736446284852453621547621077256802⟩
def resval4Tail128 : Box := ⟨-645319630445266655398802394344679386172044607190204566,297261262640192630532963421292950261468555593183903697⟩
def resval4Tail132 : Box := ⟨-781943605232833547435044977125105379005135558517724699,288273209055080225343042577854663133775071669077778847⟩
def resval4Tail136 : Box := ⟨-947492952213278299978894380581053000730199243432691973,267643104539325089937448112483247419553406153827809642⟩
def resval4Tail140 : Box := ⟨-1148091707293010820258189921916370149372982072446027229,231587354836552804743688295148267521283150883873842837⟩
def resval4Tail144 : Box := ⟨-1446433282100230658305059710261230809426326865239530227,172418645011718864827467388444697230787980446923409955⟩
def resval4Tail148 : Box := ⟨16386730188621186885264060293530670818578474159,34827844483228100483701487900372180596306221002⟩
def resval4Tail152 : Box := ⟨19791345700546389760052138674748858497384029622,38297096308568498864831918601654187241129478508⟩
def resval4Tail156 : Box := ⟨23981473349483566567787567231788777514243212880,41972787820357154379967835074922591133164527384⟩
def resval4Tail160 : Box := ⟨29058715781739349638933609840554432710795879790,45826484836489660616556540490802553471339617257⟩
def resval4Tail164 : Box := ⟨35210887612593762152841783523358762449337512935,49814600842416622136617182659985878552920551634⟩
def resval4Tail168 : Box := ⟨42665567734615024428182496056889664098028000732,53873316148048137402541926493128104201177083101⟩
def resval4Tail172 : Box := ⟨51698516951499510998566445713482350835223996277,57912803967188215133885013833958306689361685357⟩
def resval4Tail176 : Box := ⟨62643878820720880723481425925344853046655329137,61810032290811938903028193621911339971449409717⟩
def resval4Tail180 : Box := ⟨75906540169936914023759888739112127030412358385,65399812687969552502021467995739838334851628334⟩
def resval4Tail184 : Box := ⟨91977108522603163863383154485726461652879435295,68463693856911899728745762031601929731973139757⟩
def resval4Tail188 : Box := ⟨111450060472249693060917745388440603754591411268,70716208400794219661371026520566207239809444600⟩
def resval4Tail192 : Box := ⟨135045732343452095573339408539121962501461971934,71787872468805442508744417755203233579856808691⟩
def resval4Tail196 : Box := ⟨163636966609993715312104000797966219361941465455,71204205382432835095183610728132718199150048817⟩
def resval4Tail200 : Box := ⟨198281399764785131135895393664317036503243450615,68359875055311718606570306245197298944178941818⟩
def resval4Tail204 : Box := ⟨240260586022629454038222227914210963820372606811,62486878719112100719627224358519042467011610518⟩
def resval4Tail208 : Box := ⟨291127404105568080731803115182556316612350799494,52615429667620407362232266443621111777397504352⟩
def resval4Tail212 : Box := ⟨352763500804631700409950611326279093002517780625,37525930296423561381062996277029123753276384646⟩
def resval4Tail216 : Box := ⟨427450731743895589208160464431528314090355729014,15689928413149178241435906488754300573681936616⟩
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
def polyval4Tail5 : Box := ⟨1021677795280805191636843830286383189935997657223395368431,2065465207918640530866651362697867722480623652704260846912⟩
def polyval4Tail9 : Box := ⟨1237980191121041286886467264768082233993275278721769540185,2267194071859978799288242318868691661637190475401519142971⟩
def polyval4Tail13 : Box := ⟨1500079414985224474839361448574550795146353815784364517451,2479734371378088840938520525387997203471032403715815657993⟩
def polyval4Tail17 : Box := ⟨1817669028725566612142710434175624772635626530979671670508,2701055744018704960617684958487127761812188315180248080464⟩
def polyval4Tail21 : Box := ⟨2202497191137687404679969858335325124820805557633158897929,2928113100674948005356853363429834476064709715433141940135⟩
def polyval4Tail25 : Box := ⟨2668799325018268464449222910032311420273734837643064930948,3156552580729111381624855060700031085850359192892717360083⟩
def polyval4Tail29 : Box := ⟨3233824708552242797801306364486067469957033675144542679564,3380344541438785635036425479734158197037701716401035276622⟩
def polyval4Tail33 : Box := ⟨3918474554309703881691480998024873413818946580936649902349,3591326668920295901723369539145539204128175973949665919207⟩
def polyval4Tail37 : Box := ⟨4748075179265573894655486657545995897193148180341839231652,3778636533245154343134411976457743639869422153511445156062⟩
def polyval4Tail41 : Box := ⟨5753314866664816864110781883332576172322114852684221973461,3928008309156468599531558084385299605219727440363313655775⟩
def polyval4Tail45 : Box := ⟨6971379075785055752819132194245211255377738562311426076890,4020902778563659897746466478131418583889142585021168114989⟩
def polyval4Tail49 : Box := ⟨8447325992861412314174724855534699879406429263181350553185,4033432904560041948402539921823958158874555292932208357305⟩
def polyval4Tail53 : Box := ⟨10235753307050858988568860567295454055503657237636401294011,3935038956062377012943624772226074277260776387996632759520⟩
def polyval4Tail57 : Box := ⟨12402817868203642147295626213128349263433709565511058169532,3686857047782268931800269222802249277356833102790802328543⟩
def polyval4Tail61 : Box := ⟨15028682936884234830520374866126996520491229851309326979732,3239712654233725133443583850077478911177406230811822870172⟩
def polyval4Tail65 : Box := ⟨18210483554428492163497889577371383890377511396106067983464,2531655688056345988224302036671527028796345421635443186658⟩
def polyval4Tail69 : Box := ⟨22065919794546235726473285178353379514498602327767889218341,1484935525951911523934287489474906923978775595404501692068⟩
def polyval4Tail73 : Box := ⟨26781250000000000000000000000000000000000000000000000000000,2⟩
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
def resval5 : Box := ⟨94135973171909010574780717424971966997400706877584623659,14766594103821050444530320765408935313929897067181681495⟩
def polyval5 : Box := ⟨8589058165904878756711069296531756574305075433783232639484,3759723782377606081971055940374306311644213605848512413587⟩
theorem cell5_lo : Holds Q cell5 (31/32:ℝ) := by norm_num [Holds,Q,cell5]
theorem cell5_hi : Holds Q cell5 (63/64:ℝ) := by norm_num [Holds,Q,cell5]
def resval5Tail4 : Box := ⟨-17669245770919446693944739865424617816694742608231424617,14953944855265621099449012939278940484052716316634574202⟩
def resval5Tail8 : Box := ⟨-19427598435372468636010116057279901496362576921432881764,15316801649127119332203114291711511051140802467465840692⟩
def resval5Tail12 : Box := ⟨-21360870385891252787281426193218714652606474115413271500,15642605030845998103209997141457663772596818249830442502⟩
def resval5Tail16 : Box := ⟨-23486525368708868192745050344989715214094643389559810634,15922910090273805264822973974108629677698761669574343033⟩
def resval5Tail20 : Box := ⟨-25823707738951426199910085960616224822374683416242738134,16148122898692616977032072147086760787150365726162256606⟩
def resval5Tail24 : Box := ⟨-28393466931266171346107118695579280723899432276336693015,16307365408963189152939909545791939339328106126369911204⟩
def resval5Tail28 : Box := ⟨-31218947043800495573971751741042089251370061837497294024,16388326252427018145548220612234066685210871486138124062⟩
def resval5Tail32 : Box := ⟨-34325595281581826058637362467627317964751805400181005949,16377095295881101883867367563876148692227221747287666270⟩
def resval5Tail36 : Box := ⟨-37741391142432218641972555699050818122351085594685725887,16257980251889158404831175216467862123657820208219154106⟩
def resval5Tail40 : Box := ⟨-41497098409546356982744066912854702074104426169423917427,16013303460092685234796379131953705330333035870190084206⟩
def resval5Tail44 : Box := ⟨-45626542220261175663426112085911731392451150792111048810,15623176763600845788190748305767810989894948937537013963⟩
def resval5Tail48 : Box := ⟨-50166913706389754376974467293503516081095839734624855223,15065252191282032406785275023083753725543466019106011941⟩
def resval5Tail52 : Box := ⟨-55159104949810724045893616767517550066757052800012664987,14314445921868159803326315042231257957683771591698515950⟩
def resval5Tail56 : Box := ⟨-60648077270033598594186931611964338340008246414162456084,13342632747032066234483567170671637630788114249595677132⟩
def resval5Tail60 : Box := ⟨-66683266160656616317690668722728644370978362155171864347,12118307965606312877369520719703826937682395056512119386⟩
def resval5Tail64 : Box := ⟨-73319026517762166591605076234307899826126647195424267217,10606213326987475325213578160015296806416531731051982648⟩
def resval5Tail68 : Box := ⟨-80615052402860768937184535193039872707217814119221073037,8766920098256075203673160931888575847486424016836175403⟩
def resval5Tail72 : Box := ⟨767055399024566066915510105204735874549225277193400195753,914131050729915199908411088544428973039504631005133887⟩
def resval5Tail76 : Box := ⟨-229320455245539070605426680122131522353046234537194620,197210878127495818117387776538314507012758908970225144⟩
def resval5Tail80 : Box := ⟨-252113917760485499569333970369910347562542888879389098,202124474819977382710631640352782174958882057503617201⟩
def resval5Tail84 : Box := ⟨-277202182768399782652196515285106066099637630694361147,206570716001003004204266306054420015026460560652916715⟩
def resval5Tail88 : Box := ⟨-304787023198044024489002048063105636485415514267441844,210440711929941404476310198395460303541999655192016528⟩
def resval5Tail92 : Box := ⟨-335116876001481075310013664211940984246845255809684023,213610883905559324101603091669935931951799417164894084⟩
def resval5Tail96 : Box := ⟨-368464901827596391156988177157936945415191457154714730,215941049101664237537476781991414957423003782273113018⟩
def resval5Tail100 : Box := ⟨-405131443986784544930276165894418497635444846490297111,217272488227965829989658432739821435439630963784958102⟩
def resval5Tail104 : Box := ⟨-445446733441150841999934898845906222953790125574369021,217425802713558448883109328595337961958941172719972804⟩
def resval5Tail108 : Box := ⟨-489773862973381736186310636851585160613801528231364113,216198539264862057490085236844667331218369769011899032⟩
def resval5Tail112 : Box := ⟨-538512057320002528113711250510373176105539748359387532,213362557388298951662441896081739887082247846956167949⟩
def resval5Tail116 : Box := ⟨-592100268720918595815900457316912639787138425121831943,208661112956973637864895822659747776951934330237166526⟩
def resval5Tail120 : Box := ⟨-651021130267944222797618385036500213803062863401672886,201805628134392990492738814752740851214505371582672054⟩
def resval5Tail124 : Box := ⟨-715805302657478696481119700023388969867132132779536217,192472114921084872999937737084904727387378239196642207⟩
def resval5Tail128 : Box := ⟨-787036253495616799914907859551922971112838631593491478,180297216233519125397713046480587245758081613869815416⟩
def resval5Tail132 : Box := ⟨-865355512199701990756330157676617911481857614265709718,164873824727834435127809712402346129383673701105992475⟩
def resval5Tail136 : Box := ⟨-951468447834639075263247436620832690909113103162267375,145746235508336128266121130730375727862495238685785333⟩
def resval5Tail140 : Box := ⟨-1046150714710338074576275069660646210954113023172760316,122404778273373752496439781951432033659822951596240026⟩
def resval5Tail144 : Box := ⟨-1204225250528349318454118016853021586300530615964160643,91843749094754055555130623678030859692349314963918629⟩
def resval5Tail148 : Box := ⟨89526422634636222069320509534423674934146829125,67355419688628760086339233046573968768163021429⟩
def resval5Tail152 : Box := ⟨98376682295222722032607582523574837282579495489,68648262218263048309511950132735129719321875441⟩
def resval5Tail156 : Box := ⟨108166305117511920518230490013191136549391932114,69718573572894639447946492032612604980592996742⟩
def resval5Tail160 : Box := ⟨118930110209985283145313346064635237413783683130,70520814788704623528791400119753129507945294648⟩
def resval5Tail164 : Box := ⟨130765039068559533182546249829846798405964467729,71003954716343062813431227083215580911050029379⟩
def resval5Tail168 : Box := ⟨143777680962464124367055676391010588680666244467,71110300467310782506045807688799570253641098811⟩
def resval5Tail172 : Box := ⟨158085232032897335686165393376082360136908318566,70774731516261609297426476012811538914571226670⟩
def resval5Tail176 : Box := ⟨173816550799837607139220191561673907550218263393,69923850907267884855462596518707116307646721357⟩
def resval5Tail180 : Box := ⟨191113318704339242181827814062219160865659643915,68475044865333632268625891006404973062716115718⟩
def resval5Tail184 : Box := ⟨210131316138281507445818977671557510361145982063,66335441234820150331095829565212531231326763438⟩
def resval5Tail188 : Box := ⟨231041825453915158559145748175743988594856562174,63400756183157332287613286877609629658097621620⟩
def resval5Tail192 : Box := ⟨254033173589172726060194995039818477673369751965,59554017525107236075266611261690258192840121696⟩
def resval5Tail196 : Box := ⟨279312428202134476328577939359016770034471710123,54664151829870656505393403465250236603529742345⟩
def resval5Tail200 : Box := ⟨307107262590596007541718660931901452706314153810,48584421159413722750809540744962764824616740582⟩
def resval5Tail204 : Box := ⟨337668006192817721249469262399861606010085318382,41150693839360592475174813511461395426648326538⟩
def resval5Tail208 : Box := ⟨371269899136956158172349071990596734970781972149,32179532070248100831796050469349756202379530484⟩
def resval5Tail212 : Box := ⟨408215571182885335439300891980472004828606856792,21466077429136864617855516117844939064167779734⟩
def resval5Tail216 : Box := ⟨448839560793764591068345637591939647434624104969,8781599590370803094904736593000745817460393414⟩
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
def polyval5Tail5 : Box := ⟨5330186800771193539986867823855546570529229859562332114443,3833906810909855671075220393477829361746871357724128994064⟩
def polyval5Tail9 : Box := ⟨5860600261012770943268386090050756415240660401974835794966,3899339198140973382216327117380866185481044463173974603019⟩
def polyval5Tail13 : Box := ⟨6443798132541064480420681507378130646536320063963538074582,3950731026149431381062351501067036141782708578664110953244⟩
def polyval5Tail17 : Box := ⟨7085030973770036472755803305114511823686467709204619996106,3985348805221771411921843383002624754739440345673057274145⟩
def polyval5Tail21 : Box := ⟨7790073938813270714762119678508524501878698876171892771215,4000100159515152498098341510750174966814276758669721031393⟩
def polyval5Tail25 : Box := ⟨8565276876959975104447079323558872322706202347615901809840,3991492452010063931628711976940789912093309525157188870152⟩
def polyval5Tail29 : Box := ⟨9417621521338395897342553144475987922242147247178474724503,3955586937332034533750925762203297576849296307933127434184⟩
def polyval5Tail33 : Box := ⟨10354784368705069191204784298527219108102708879779518970835,3887947961054452473023069975528193955910988533935838589109⟩
def polyval5Tail37 : Box := ⟨11385205816504391179682729010791701272532277915412050238512,3783586687111832019079633138055666245170623069691473149374⟩
def polyval5Tail41 : Box := ⟨12518166179869526312224973144914321832767460119854725674304,3636898781717705301554999000485447273462928135129738133086⟩
def polyval5Tail45 : Box := ⟨13763869273198814478855555196030011919339406697877957144238,3441595423538560013879311117730236782734038633557696105315⟩
def polyval5Tail49 : Box := ⟨15133534309070898558150029125670170912426720163357031779261,3190626945282326028509221241358945830488636151721553924888⟩
def polyval5Tail53 : Box := ⟨16639496942170487156518052927358430524619515770732105950889,2876098340717281637911711083658246609224586912845961159276⟩
def polyval5Tail57 : Box := ⟨18295320368259646911447803912849906728262496393402447841177,2489175792785200553466969819324348511717070354369653775226⟩
def polyval5Tail61 : Box := ⟨20115917478788580258580883677959256599929641408394735203124,2019983292185226277676307067595091086999297712358134268492⟩
def polyval5Tail65 : Box := ⟨22117685171318342488652904914207654220681757027960394170074,1457488320783074187045619437807716734086522824020995436626⟩
def polyval5Tail69 : Box := ⟨24318652091521070506410456283431765109174509450200075710995,789375465414962294495586641595966636171995930808231612039⟩
def polyval5Tail73 : Box := ⟨26781250000000000000000000000000000000000000000000000000000,2⟩
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
def resval6 : Box := ⟨76532444851195901733472456119032655514683554806509393850,13434880163099686156275825314553082129011296627667241956⟩
def polyval6 : Box := ⟨15183933738658576056427526666760095127324240795740145418200,3762730425603361994169254690101825022352193567043756783919⟩
theorem cell6_lo : Holds Q cell6 (63/64:ℝ) := by norm_num [Holds,Q,cell6]
theorem cell6_hi : Holds Q cell6 (127/128:ℝ) := by norm_num [Holds,Q,cell6]
def resval6Tail4 : Box := ⟨-35292487339825921705992059994811004822204876876944547155,13101077797883993282404256247838114101732087599090381342⟩
def resval6Tail8 : Box := ⟨-36996503762920605265708199233153856365227445956174539301,12939418373090112844330338645544032062922513976536976245⟩
def resval6Tail12 : Box := ⟨-38782737523964812577551663682539609793497003850448285439,12744643472128641326615631728074202889321907327777389318⟩
def resval6Tail16 : Box := ⟨-40655212699389672663119756528342301959391518409078588734,12514346977118762336835947076413013945318159667477548709⟩
def resval6Tail20 : Box := ⟨-42618093129992994506098610145318477971672054595122673150,12245981494872173809709581060348082132689067740335447392⟩
def resval6Tail24 : Box := ⟨-44675743685483709304273528276418825832827090806971458600,11936850113608659664458998014276617643676044625922197798⟩
def resval6Tail28 : Box := ⟨-46832739976495649499788757642710272583702396590915583941,11584098338471340160734944366500192331939903733970625738⟩
def resval6Tail32 : Box := ⟨-49093878529406881269871098804152489311297014040718832644,11184705610853903477977714616901734970942473794205266785⟩
def resval6Tail36 : Box := ⟨-51464187452405950691344238376256832339214531254977169241,10735476390468566615039981761178575808573367548817361433⟩
def resval6Tail40 : Box := ⟨-53948937616528058465040878991896356158911403083045131657,10233030778157163606842187764055380267925655320508947326⟩
def resval6Tail44 : Box := ⟨-56553654376524521343990190707623059979566680006597416538,9673794656357595813247541209056885973620906447203496164⟩
def resval6Tail48 : Box := ⟨-59284129857629292451879145916700035753641160281353133192,9053989322994036675014462569128924911801779485010298343⟩
def resval6Tail52 : Box := ⟨-62146435835544701294695346861972265312914468364024941131,8369620593359285555673385176805683650701739533790720394⟩
def resval6Tail56 : Box := ⟨-65146937238287711068471569935011554659025329039980333274,7616467343298771010353600166407049063974200500314275041⟩
def resval6Tail60 : Box := ⟨-68292306299918261906785010083079012487997764357286794716,6790069465684815434437938616690843587520620105710283329⟩
def resval6Tail64 : Box := ⟨-71589537393718625163940855586978618808547482256764672767,5885715210525005069334674054519365948432264478078777024⟩
def resval6Tail68 : Box := ⟨-75045893588706508459346030008404912963948737499144789373,4898424446061895563798315792726161367664516316289352368⟩
def resval6Tail72 : Box := ⟨766908463011182485572037396211108386901667995078927336677,868947036381887806567111347288893873829456520226162375⟩
def resval6Tail76 : Box := ⟨-461992062004661968455319601120506458289626900582175430,173663865050625921892399465329100200467487009231225746⟩
def resval6Tail80 : Box := ⟨-484272236721940861285192545183667579803753739282489212,171616936312371470508156070366258061621864137811197405⟩
def resval6Tail84 : Box := ⟨-507653456049432552242627701687492623474436553531852013,169138917001635286352082352766575945942855623498237582⟩
def resval6Tail88 : Box := ⟨-532163548807979762309569192230723566854596552431440374,166198210937480467839960647305576320138023304372637264⟩
def resval6Tail92 : Box := ⟨-557857017036992412630106001141707593492775785916987604,162761546196199891414566068608080411084800753952253619⟩
def resval6Tail96 : Box := ⟨-584790995464636542413979360647087399701912368385963779,158793696036145925515284278687398629418394679284527984⟩
def resval6Tail100 : Box := ⟨-613025377350130702295924424232442611688164466433615564,154257373393260033256431237958052712727561354100817423⟩
def resval6Tail104 : Box := ⟨-642622947668139172395193520335829932374289238975443500,149113119947939188705160559525888355685866580638001048⟩
def resval6Tail108 : Box := ⟨-673649522724118086403942463563459250277268137400852974,143319189470759792293249600061997703312146232655244247⟩
def resval6Tail112 : Box := ⟨-706174096510452674004097090090387767691393801386133472,136831425159181889916127549335764616569777879099875475⟩
def resval6Tail116 : Box := ⟨-740268994128837161176634311593857304920045005724781661,129603130663102087420761264622890089802230093533763848⟩
def resval6Tail120 : Box := ⟨-776010032620063638289084996482132097594352571176419782,121584934482153613735459902686715687895781447845117159⟩
def resval6Tail124 : Box := ⟨-813476689558858121412099608512004343312815180822209639,112724647401947028852269580605725839983735346910766836⟩
def resval6Tail128 : Box := ⟨-852752279788669270409898085595931569125990558372092088,102967112619969268960764072195850975975999736388693484⟩
def resval6Tail132 : Box := ⟨-893924140689427382147696268823627722770438716593742071,92254048194573322666042541247026196639191593783303472⟩
def resval6Tail136 : Box := ⟨-937083826401083796751288937151260852006662374441257944,80523881431507257420337441824018934793160748974783290⟩
def resval6Tail140 : Box := ⟨-982327403204778374709157556061200098776140252285022371,67711569094168011315665460858882984267630007043367212⟩
def resval6Tail144 : Box := ⟨-1083097073525119028413644391144928714867692072535537424,51542926276778841166293129743296016100528990540033154⟩
def resval6Tail148 : Box := ⟨206296442367735506204987083541752792886954497106,66516246709269036312863817549283780136070362938⟩
def resval6Tail152 : Box := ⟨216200769654009561884954309389143205538512042445,65250935943289837952742203814239579840075378059⟩
def resval6Tail156 : Box := ⟨226639190564290083295537961762308887662156509410,63782385693771589750236494199562101615678515561⟩
def resval6Tail160 : Box := ⟨237581591364029128234542088515318214999569320902,62095726436264385072211797055729130934583328504⟩
def resval6Tail164 : Box := ⟨249052303860560389577477667405060954587481379327,60175736153450852721313431904170191409766923685⟩
def resval6Tail168 : Box := ⟨261076835549996125826199677653099983305619340060,58006308388945724194250169666231328414109011483⟩
def resval6Tail172 : Box := ⟨273681925459970138010056061034581877001108475267,55570404766442220236343870571455702919920211923⟩
def resval6Tail176 : Box := ⟨286895603609125950792323360358605206507569960926,52850005078579380908940270544363685409356742137⟩
def resval6Tail180 : Box := ⟨300747253337647225547759595149666477621857421801,49826054809345286624644662483449307390885289147⟩
def resval6Tail184 : Box := ⟨315267676647178301144598812624889013205841909096,46478409961103781566336759411045768626303069379⟩
def resval6Tail188 : Box := ⟨330489162695431254629381859279698150577710859297,42785779050955495844361054603893183323693421702⟩
def resval6Tail192 : Box := ⟨346445559597791373088167366395324135917708632781,38725662134447822705604132726361030279930722219⟩
def resval6Tail196 : Box := ⟨363172349695586723640829156725982818620580843002,34274286707623821164790618543298373875534639337⟩
def resval6Tail200 : Box := ⟨380706728458396351837744827250286380222987185888,29406540331030767396735096756750185069681663828⟩
def resval6Tail204 : Box := ⟨399087687195852705559348037702990864514389653427,24095899811578458538035318614145905357831569131⟩
def resval6Tail208 : Box := ⟨418356099762879399803260136657301378607482294076,18314356770026428493234332134857559817106897521⟩
def resval6Tail212 : Box := ⟨438554813489254161458176971157771659801829445501,12032339410545668347071314123812076858981674775⟩
def resval6Tail216 : Box := ⟨459730517620807648323159162309208754405442777725,5218524270818616298088870073487784682129481863⟩
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
def polyval6Tail5 : Box := ⟨11995690926023493809165046192599658100890544160511733180313,3691693905536778716813772460256435638838247044888406476800⟩
def polyval6Tail9 : Box := ⟨12574854676361236207533016459406108593719777494776755030888,3612485443018467064140229022400587589242451141781460746968⟩
def polyval6Tail13 : Box := ⟨13181983123507313212977861382817578022957932565035802892767,3521247854546650363072410424633844522988497918347662551877⟩
def polyval6Tail17 : Box := ⟨13818424430578831590151110669441331238819211081924463145554,3417138858488527038383397588911098258020529487314503684680⟩
def polyval6Tail21 : Box := ⟨14485593855988354826543641633689130074241417783407682654594,3299267185672142479684071619070363279263022472963084852987⟩
def polyval6Tail25 : Box := ⟨15184974988632480229865763371608863933196468501962162786181,3166689936168990465595132033943722114456372768599908647639⟩
def polyval6Tail29 : Box := ⟨15918123046786281680634675103652595492033594225305242286182,3018409812440630072537702214402781844426697977720667027004⟩
def polyval6Tail33 : Box := ⟨16686668336451960402523164589209330335256429164302723183007,2853372210166718026956922925912244713042368801684084193727⟩
def polyval6Tail37 : Box := ⟨17492319876680675892127864294600290331719451179623520844610,2670462159602263345257227492980438829935669488722140642694⟩
def polyval6Tail41 : Box := ⟨18336869199929085080956194035469518254721215876949565420401,2468501109960248135051529670322301884389877526346972199991⟩
def polyval6Tail45 : Box := ⟨19222194335901466368321747029129856193034268069457202448613,2246243548944312451221655414272793099609569207606714040089⟩
def polyval6Tail49 : Box := ⟨20150263987736323603290049895323611939916196478568559421252,2002373449166526634957181418010579647224248925036215390862⟩
def polyval6Tail53 : Box := ⟨21123141909824082741944591295553284451766949844789742988168,1735500532776485115027786714847138937315560339492104993567⟩
def polyval6Tail57 : Box := ⟨22142991496990862285321348180832941893992202041282853194554,1444156345199118739429628513696018330107076609320579014261⟩
def polyval6Tail61 : Box := ⟨23212080595253322469475107005430179210888399130245252046325,1126790128428759759288009982432655790450196031365258880283⟩
def polyval6Tail65 : Box := ⟨24332786544849992540549010965555703384388291784055677214252,781764483854493118829549817277240045375132606304090681490⟩
def polyval6Tail69 : Box := ⟨25507601532158779176201292740645180803889428486683011002762,407350810224515383603949288422136038498371065245030764877⟩
def polyval6Tail73 : Box := ⟨26781250000000000000000000000000000000000000000000000000000,2⟩
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
def resval7 : Box := ⟨55667931072287420675640318346646106524242889780227298640,21885077518503908931551453317930338033016138814977302863⟩
def polyval7 : Box := ⟨23913262638034914602633839631645399425425494805594131717024,6571342460000424151556516500293091136056974876380069693766⟩
theorem cell7_lo : Holds Q cell7 (127/128:ℝ) := by norm_num [Holds,Q,cell7]
theorem cell7_hi : Holds Q cell7 (1/1:ℝ) := by norm_num [Holds,Q,cell7]
def resval7Tail4 : Box := ⟨-55387488093434145211923187296595607866943104936955978501,20821669981872788489221339751940094780362003976282479153⟩
def resval7Tail8 : Box := ⟨-56261488355499741727602225749192008348428853427726687347,19947721142489965998752739299211819557957074037188719887⟩
def resval7Tail12 : Box := ⟨-57149226469099209487485943564607592600911502067504637116,19059983034615534860568932311160247866675404369278453985⟩
def resval7Tail16 : Box := ⟨-58050972008429553847209996154157970653404888458964712848,18158237495289960290907124086241760793777065656214496810⟩
def resval7Tail20 : Box := ⟨-58966945999615727043862123804797897374668561426681436270,17242263504103804366997157561205154989095431595511849720⟩
def resval7Tail24 : Box := ⟨-59897372950390701396104613834295346868329185164871840508,16311836553328830221962671399119395481356845572388087155⟩
def resval7Tail28 : Box := ⟨-60842480910942475873567663744875705093301654092118496829,15366728592777055751325608464171234133971114915293488848⟩
def resval7Tail32 : Box := ⟨-61802501529814643477267666916666774346147287619140170793,14406707973904888148128732054891064416655899909880147775⟩
def resval7Tail36 : Box := ⟨-62777670110684099450022805427834207576911008760987616409,13431539393035432175410141343484004524344472716248072622⟩
def resval7Tail40 : Box := ⟨-63768225670034615633707513136546768733054279193051932075,12440983833684915991631157419133516249330783868195273760⟩
def resval7Tail44 : Box := ⟨-64774410995740433748051094798866976857330767136715331973,11434798507979097876757136033352139004260682413615312452⟩
def resval7Tail48 : Box := ⟨-65796472706574236770422958331407481330751969972124850505,10412736797145294848990494906877637828999090946124269946⟩
def resval7Tail52 : Box := ⟨-66834661312654083890098396778759768134166835654398950490,9374548191065447592585816093007739582311350932290531737⟩
def resval7Tail56 : Box := ⟨-67889231276844116151127824483641935271984618709765874543,8319978226875405018582827554000458647878781282719510517⟩
def resval7Tail60 : Box := ⟨-68960441077121526154691632941222819540526773972779989278,7248768426595154820486875423125792881198046112588552502⟩
def resval7Tail64 : Box := ⟨-70048553266047328820422865612893574435032362753234789869,6160656233517475213526199364954031780960935272316456502⟩
def resval7Tail68 : Box := ⟨-71153766047455989968067287753114316432305837751593508288,5055371542742949555707736029352116814947148483057943062⟩
def resval7Tail72 : Box := ⟨766689705036599303330321617168827679649068395863778046075,978557322014362094971710757167329071354374899090372433⟩
def resval7Tail76 : Box := ⟨-727579747459759514880817101873489707253671673797637827,275652451621277358387587303961555649239857371868557153⟩
def resval7Tail80 : Box := ⟨-739035537174887265486746651820971465571055068756893024,264172327095926219115221869616917954390074023115635469⟩
def resval7Tail84 : Box := ⟨-750696621147146341093628053691802935455068160861899745,252511241895292472776357525278746964779640774940523036⟩
def resval7Tail88 : Box := ⟨-762541704121896131279756688249266745345542258141609582,240666158919893427357183123972575082595615464061901747⟩
def resval7Tail92 : Box := ⟨-774573688152566724770028173423400776082636836520188832,228634174889221161981886415086809173878492300221774881⟩
def resval7Tail96 : Box := ⟨-786795522310690057248758476238291056939646464702333598,216412340731097814144573489791176885382940709256137798⟩
def resval7Tail100 : Box := ⟨-799210202201212267407433378698659676995691317838926807,203997660840575603568870905806027553571137903766827135⟩
def resval7Tail104 : Box := ⟨-811820770696097017654931033145499103369702742963132721,191387092345690853292346444764400701669209924186686527⟩
def resval7Tail108 : Box := ⟨-824630318680140169235416670966679558521560073104229972,178577544361647701707534631315627772115018989348729249⟩
def resval7Tail112 : Box := ⟨-837641985808554078216043262326428485256822716279197805,165565877233233792726338242162437411929380056661235017⟩
def resval7Tail116 : Box := ⟨-850858961276505666692350988802862906409412591935000291,152348901765282204253566056737208843805031140814806940⟩
def resval7Tail120 : Box := ⟨-864284484600796872539789531729719846807711528297952275,138923378440990998446241219649716172908061207887264013⟩
def resval7Tail124 : Box := ⟨-877921846413879070248816289499396303529180550736632224,125286016627908801612625276449723213652003515648414816⟩
def resval7Tail128 : Box := ⟨-891774389270396131394025102542564830984630410009899568,111433473771391792072313772515610806066451123295054571⟩
def resval7Tail132 : Box := ⟨-905845508466465082387686638354817621524392571037544492,97362354575333272604384119063811913813628954014040001⟩
def resval7Tail136 : Box := ⟨-920138652882650378657914588776406922426127873784713491,83069210169120604671108091151707595071054389886349411⟩
def resval7Tail140 : Box := ⟨-934657416953580478945984223193002264452912346728124181,68550531601343212478252352669138267902144954326587861⟩
def resval7Tail144 : Box := ⟨-1002335957898108759960332507695463943571686721722686098,51616402946638253556908381708534622309408517499255907⟩
def resval7Tail148 : Box := ⟨357976100309055998652087732947181121463200197141,114411395447899784378997455973234804707400151976⟩
def resval7Tail152 : Box := ⟨363570376502704767554643370154892864254958353500,108763320550671016047707806590391155097863229438⟩
def resval7Tail156 : Box := ⟨369307075570770977756321492971416356747534590610,103026620590376245002697212393377373167246888001⟩
def resval7Tail160 : Box := ⟨375134293690726786737841177643394824967022713624,97199402470155146424997066160317567854607649964⟩
def resval7Tail164 : Box := ⟨381053458251361078685499560617809952543102093855,91280237909520420864640750706185999906602331687⟩
def resval7Tail168 : Box := ⟨387066020055823244742458344408372044034944926907,85267676105058252123396227124561231402888630467⟩
def resval7Tail172 : Box := ⟨393173452799440177537209088106827495576656235471,79160243361441319277594550875410290769124854480⟩
def resval7Tail176 : Box := ⟨399377253430665598168248223115303464340080692656,72956442730215898643975544114757220469696492648⟩
def resval7Tail180 : Box := ⟨405678942517985803560040308557619373602862821456,66654753642895693251882801779875871702471072450⟩
def resval7Tail184 : Box := ⟨412080064622615154957268056701249364305316613812,60253631538266341854597077939168790313328585414⟩
def resval7Tail188 : Box := ⟨418582188677072251963725890184841652183804926119,53751507483809244848176153199191799152041262717⟩
def resval7Tail192 : Box := ⟨425186908369729579881740505883324914301921740367,47146787791151916930635502832716434620524635760⟩
def resval7Tail196 : Box := ⟨431895842535430884490994978075885864828422049238,40437853625450612328677376397421382693899115907⟩
def resval7Tail200 : Box := ⟨438710635552272015918570446081552515363715729700,33623060608609481169281037525626490512705620598⟩
def resval7Tail204 : Box := ⟨445632957744642525746027621980762997097519122587,26700738416239001115648786872161664873527083104⟩
def resval7Tail208 : Box := ⟨452664505792641063120298692297085825631613394859,19669190368253572781693817063835991562078510376⟩
def resval7Tail212 : Box := ⟨459807003185779146102026042761662977936071474498,12526693010205991003512184866176542325787721481⟩
def resval7Tail216 : Box := ⟨467063960509588747072751353082748824695820009603,5271390570350752338055027749131784165294988895⟩
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
def polyval7Tail5 : Box := ⟨20491197880170574602664206152909286447436646232564113304136,6249976461856443010536354626486390213947604114310649605018⟩
def polyval7Tail9 : Box := ⟨20814522209393400134262503858137314756622701475985688163229,5926650209141569731882714211683156151534053353139919655219⟩
def polyval7Tail13 : Box := ⟨21142950146308256832346497742879470175778071035852711252044,5598222272052316842660384341782986809016848003486311130239⟩
def polyval7Tail17 : Box := ⟨21476560278247895918789779388770207504567776567632536893445,5264612140112549519556138376775594413634036772194747547143⟩
def polyval7Tail21 : Box := ⟨21815434373795515353439724704298893939982709535385415347469,4925738044564929666394382225869833556500474875451763492939⟩
def polyval7Tail25 : Box := ⟨22159655491917766302153854125285873830248420483783024456283,4581516926442678713068692328236932615507857892276162588393⟩
def polyval7Tail29 : Box := ⟨22509308002151267603383667839258741784597756746757687734551,4231864416209177411694332623197147833395418549333663321994⟩
def polyval7Tail33 : Box := ⟨22864477605281685969462879486940430931953658345358283765613,3876694813078759045603872099006740095858232677508804578933⟩
def polyval7Tail37 : Box := ⟨23225251354349232339220558011218791117673957416071782338387,3515921064011212675844397875561804105302666369095675862803⟩
def polyval7Tail41 : Box := ⟨23591717675985599897985943835298509212020805437280141175939,3149454742374845117078851262053945524588890161566392808115⟩
def polyval7Tail45 : Box := ⟨23963966392087573126960448145814649063327140248823041992471,2777206026272871888106485045889332399390533175707518236126⟩
def polyval7Tail49 : Box := ⟨24342088741832620139074887756976605578343980127677447999923,2399083676527824876016404556031768800504389406283520851661⟩
def polyval7Tail53 : Box := ⟨24726177404041864383586170009141894903959563844122183120137,2014995014318580632059766107967141011338635534600554087752⟩
def polyval7Tail57 : Box := ⟨25116326519895916980335423837528318758594054034256035831921,1624845898464528069501848847010842754421520940791815321748⟩
def polyval7Tail61 : Box := ⟨25512631716009145164840697395051058333853401406412490834170,1228540702351307087368704729517579995050472933799797430046⟩
def polyval7Tail65 : Box := ⟨25915190127875673080071548190526577531488049010127043037258,825982290491879727448138984207011876619611703554754506381⟩
def polyval7Tail69 : Box := ⟨26324100488613023718682217200476786210080161979788608482570,417071990878899884151559525110288073961303953706843792207⟩
def polyval7Tail73 : Box := ⟨26781250000000000000000000000000000000000000000000000000000,2⟩
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
def pend : Box := ⟨1030479811449996354131030983226517654076529543525822829521159,4793648038984623159372905420836484952926156151371889702⟩
def zend : Box := ⟨1003735668402242189400214843750000000000000000000000000000000,3112114428004877910156250000000000000000000000000000002⟩
def betaquot : Box := ⟨428746838502930700158115089356111603871828828403002408475499,394764394057149838064315654513004413925921709591777395⟩
def crit : Box := ⟨110459218640502946708839250336317309966260191566732893336,12264525244867658130847739174231504909056015775126935093⟩
def subsonic : Box := ⟨557297288950945863686743990508181065921495471902847806788,6606739984472919012535399438272348550265701837243397988⟩
def pendTail4 : Box := ⟨26739589623042006142734125999643818027671607274669178007891,1549108616509574167624939964726748374893608946839546490⟩
def pendTail8 : Box := ⟨26739623464391293106665590737078333202627225635154764067406,1548952592881614962112053444276781957984656530840814550⟩
def pendTail12 : Box := ⟨26739623465784459954215757305576538024771393140077746728068,1548952575343853233902144568338376178802436408344057486⟩
def pendTail16 : Box := ⟨26739623465785113563392083763616461205434313462080512959017,1548952575329988134490180635870794601111245236273398746⟩
def pendTail20 : Box := ⟨26739623465785115063887937394444466494476910449308527135233,1548952575329939265600427936573403145278280535177528569⟩
def pendTail24 : Box := ⟨26739623465785115076115551163037174289704515579027303659046,1548952575329938661444073009902711371861733836179576326⟩
def pendTail28 : Box := ⟨26739623465785115076406825817108788611884515248307983468567,1548952575329938638911975678703735630884030401326861066⟩
def pendTail32 : Box := ⟨26739623465785115076424224552229147074117946322376149914598,1548952575329938636598083684899289686687946972453732037⟩
def pendTail36 : Box := ⟨26739623465785115076426311939676720118018329643920558309612,1548952575329938635977019059162408943097362877486526133⟩
def pendTail40 : Box := ⟨26739623465785115076426343504427893384638396747163377003429,1548952575329938635551616904245033687060517489152970047⟩
def pendTail44 : Box := ⟨26739623465785115076424429619115753616201264457332980294839,1548952575329938634808549353144840460806766345615714768⟩
def pendTail48 : Box := ⟨26739623465785115076408383050127129086938581761947958213937,1548952575329938631425159222585308579819590827204516325⟩
def pendTail52 : Box := ⟨26739623465785115076132994516275150740617493547363159708300,1548952575329938589270665553752296725098511102618164505⟩
def pendTail56 : Box := ⟨26739623465785115063581173513010895119395490416612664291554,1548952575329937024114755119906071217320316529147930571⟩
def pendTail60 : Box := ⟨26739623465785113214175115190805157537619247552466353205466,1548952575329746708378683976658298880141252556856939541⟩
def pendTail64 : Box := ⟨26739623465783952566776456979024760208713327837599376191283,1548952575238835649414582569488319979470931535726889160⟩
def pendTail68 : Box := ⟨26739623460604032738707679440265071697469279327831670262202,1548952265396706804782727887969105335980638155691570285⟩
def pendTail72 : Box := ⟨26738941379476801660368404769647695221800519770378328866950,1519547062429182743565214451132948736942844928602284055⟩
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
end SepticProfile.ExteriorCertificates.C12

end
end

end OAI
