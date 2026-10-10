import OAI.MathematicalPhysics.Transonic.Certificates.BarrierData25

namespace OAI

section
noncomputable section
namespace SepticProfile.ExteriorCertificates.C25
open SepticProfile.ExteriorJet SepticProfile.FixedInterval
def cell0 : Box := ⟨250000000000000000000000000000000000000000000000000000000000,250000000000000000000000000000000000000000000000000000000002⟩
def resval0 : Box := ⟨117242292938522824388314777341070809986563079340067237278,310972999058301496417470528538585131454322780987602145⟩
def polyval0 : Box := ⟨3829212247355383436485235999226513559419362516050166618604,14859461038675310928675094259796800094425090007056851328⟩
theorem cell0_lo : Holds Q cell0 (0/1:ℝ) := by norm_num [Holds,Q,cell0]
theorem cell0_hi : Holds Q cell0 (1/2:ℝ) := by norm_num [Holds,Q,cell0]
def resval0Tail4 : Box := ⟨61707084023285890052805510059228275191059388525023,1800925777006580174809361676089543999509473086517⟩
def resval0Tail8 : Box := ⟨7646131858087029370448197474243887244609132512,406155519167840330940199318973130836395917115⟩
def resval0Tail12 : Box := ⟨7122831600077398088412166584826975293656892,574920298072959826227073522236950141003226⟩
def resval0Tail16 : Box := ⟨29202205018234996138190770698535842342671,27841926258823352501034809273884411753068⟩
def resval0Tail20 : Box := ⟨407111527226916963375548348631421902541,391941920901480748598261723826135894606617⟩
def resval0Tail24 : Box := ⟨16562551995132939580657992767987516935,6270038046356383369386836541536521385068156⟩
def resval0Tail28 : Box := ⟨1789206421551448119974312896611924396,100320551152387606062378886399364630976183383⟩
def resval0Tail32 : Box := ⟨482798868669334692305689105419079933,1605128809865422471235231677997954879710910663⟩
def resval0Tail36 : Box := ⟨-243801747601927321290381011160401266,25682060954513179751459190917723720989558669834⟩
def resval0Tail40 : Box := ⟨-143933030678358813413710440805868930565,410912975135614310569200749848558684372871873405⟩
def resval0Tail44 : Box := ⟨-36976116799785403950388708261815904338608,6574607567500735743010735003888459666756505800799⟩
def resval0Tail48 : Box := ⟨-9466382447665866787146576078750926712829232,105193712205251346462753754526498838424156878384588⟩
def resval0Tail52 : Box := ⟨-2423398553780610051719279998225830211053789726,1683097123347326380217773618396164128619847264992096⟩
def resval0Tail56 : Box := ⟨-620390125875628193828999033942857252866357244779,26928972357776622775625833021232742094751259618344640⟩
def resval0Tail60 : Box := ⟨-158819869071874087629138548997369971618769129945366,430714664086980898881424698973521384139502081888752845⟩
def resval0Tail64 : Box := ⟨-40657863795263432711986791348580424152160727646658402,6853317862715296422054365552001122259333805395605360515⟩
def resval0Tail68 : Box := ⟨-10407880428457181800260762583726814209561996897748805420,99895421726838749880544529253899672342510453701068143337⟩
def resval0Tail72 : Box := ⟨820429691089933404310674891631280971747444688799589786640,2502549914751952368048775156826134400259885375729583536⟩
def resval0Tail76 : Box := ⟨-28744846347055813133189777602770095548049861277445,622033048589191201746016564148831705947162043941⟩
def resval0Tail80 : Box := ⟨-1591439957966773844011453538366136215315233406,72597517589153276016524188161340893310002279⟩
def resval0Tail84 : Box := ⟨-921944290683063055446013394325361173150038,66245211806230809352434768029721179614570⟩
def resval0Tail88 : Box := ⟨-2612033461612827788483609340371597489458,440041147174116456690300716377101717686⟩
def resval0Tail92 : Box := ⟨-26631265276013603104411653974569917962,2698245332939648929882631619592047242136⟩
def resval0Tail96 : Box := ⟨-820218054039475548709302687641996688,43110193087040829312858780629200614010814⟩
def resval0Tail100 : Box := ⟨-68545742869059221933709426315490608,689760477003346376298876326708818415372686⟩
def resval0Tail104 : Box := ⟨-14569585050664039922350376907734471,11036167331718432076769223207494863149111578⟩
def resval0Tail108 : Box := ⟨-9511932764843713772402912379052812,176578677217742884480016192816633737024406784⟩
def resval0Tail112 : Box := ⟨-501789339586069157694868277669382514,2825258835031364311399607139284995870272138715⟩
def resval0Tail116 : Box := ⟨-126033070292470524491371523242212933867,45204141242379997365642555145082038033092143022⟩
def resval0Tail120 : Box := ⟨-32257104480990269621855533895412725471108,723266229637232668720237089063458203192454966521⟩
def resval0Tail124 : Box := ⟨-8257764172386660237997678345461631464362509,11572251932544986059486509734269574790426810619928⟩
def resval0Tail128 : Box := ⟨-2113986681706241747275903424563926466541600383,185154049058383335160423791768870270466535248134510⟩
def resval0Tail132 : Box := ⟨-541180580582223230023617930256929822177585537665,2961957428177366844803343033572858171414112629520588⟩
def resval0Tail136 : Box := ⟨-138542285552523813739934780489532942010776712979322,47261435496393670167735178648073001797000421975232993⟩
def resval0Tail140 : Box := ⟨-35467544219373563055613255132476027237516505110846653,722932498406037205174101985141587702402067332388715511⟩
def resval0Tail144 : Box := ⟨-9489227671681652018484415552829192053514250158557237298,2853241663591011856638851077682284860767597318211341630⟩
def resval0Tail148 : Box := ⟨67236402389870767445245618454285227902624702,1197907386130435968371065787481696732816338⟩
def resval0Tail152 : Box := ⟨1227989691962540294922613790650940907249,49949214122526143468556715714188764112⟩
def resval0Tail156 : Box := ⟨399652540466150893554156530156080242,26158833777971948996046386267251448⟩
def resval0Tail160 : Box := ⟨716910406773062069490812654115841,70103063833283353887004797105372⟩
def resval0Tail164 : Box := ⟨4900325828349393562255311012623,31785354735963066164980343549618⟩
def resval0Tail168 : Box := ⟨104445270284124450847127253493,498194958810874035104009445100998⟩
def resval0Tail172 : Box := ⟨6142557882301471635871801488,7970817279105252591342499351357110⟩
def resval0Tail176 : Box := ⟨924298073275136570920045573,127533052257071549500214641893942287⟩
def resval0Tail180 : Box := ⟨347790270582061856800375879,2040528831093118445075378172197719407⟩
def resval0Tail184 : Box := ⟨2152860490082072232360279551,32648461293947424282062510782198709788⟩
def resval0Tail188 : Box := ⟨474636024918037395967544582533,522375380259047426785516443613695323256⟩
def resval0Tail192 : Box := ⟨121346012635758640493726919424438,8358005970385895614356971907901255953832⟩
def resval0Tail196 : Box := ⟨31063764489676009422311310623297774,133728066403926473645909677973236072807182⟩
def resval0Tail200 : Box := ⟨7952313786752461327050161484175521701,2139641607169665942770837536877646856804237⟩
def resval0Tail204 : Box := ⟨2035792097766902363889292749474784130371,34232357159738935716343018834820094351696411⟩
def resval0Tail208 : Box := ⟨521162826806790038866588070127238531772887,547229124459911271336634698559966165018613130⟩
def resval0Tail212 : Box := ⟨133417977491164200938127440815734223153078505,8630586795133256846536106808578916726740725221⟩
def resval0Tail216 : Box := ⟨34172324219378092095866550517562591694754781426,106060789739949082042227057106164246915019600702⟩
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
def polyval0Tail5 : Box := ⟨2162073980714198137684587385874947604034363825910749,53228496413627296451162648609953306987814980908673⟩
def polyval0Tail9 : Box := ⟨214730202859672160243033412674651425570353813287,10449346667639384902554526559295126602927196671⟩
def polyval0Tail13 : Box := ⟨173079626524286117724754159582724608485305845,13065489377097142891507904904788564317777372⟩
def polyval0Tail17 : Box := ⟨621803746029908745520525010757907970312643,448124816680295504988636857683638438072323⟩
def polyval0Tail21 : Box := ⟨7617065974612786510538699922578182541732,6093706221197198311598038796171313085467226⟩
def polyval0Tail25 : Box := ⟨271989466713650027784353857769741015827,97480996746562799555266304468710275651251763⟩
def polyval0Tail29 : Box := ⟨25697354068788983762962655200826821799,1559695052382259177008262382878766879478328309⟩
def polyval0Tail33 : Box := ⟨6080090494472790340626846638594851566,24955120721887683295585108337593331145022427074⟩
def polyval0Tail37 : Box := ⟨9230894236176001178780921054152581968,399281931510141145844289947411898381600751291172⟩
def polyval0Tail41 : Box := ⟨1483914957582028563593269887920478189802,6388510902779625045434383453273305074414271487495⟩
def polyval0Tail45 : Box := ⟨378690461930610492070969632736182754412568,102216174089469359582611537060117848174783007317847⟩
def polyval0Tail49 : Box := ⟨96940888141114881543060721162284572396900362,1635458694549531515674371337655891952190651605008266⟩
def polyval0Tail53 : Box := ⟨24816836977525768313051923552466156616162484723,26167315847009706885331091824079583966235110859952033⟩
def polyval0Tail57 : Box := ⟨6353109716285099650047821221955688469707415033889,418671097511906183657323860855743851632141270088576644⟩
def polyval0Tail61 : Box := ⟨1626396082815323388132117555480915512559868697235685,6697212813886939629637891130498187076217567216272499654⟩
def polyval0Tail65 : Box := ⟨416357434545574784265108960664395761113995815770891307,106765069952332778451220486250531923832890154014145476940⟩
def polyval0Tail69 : Box := ⟨106587957948879383693222103784290171913784090797241603835,1608315133354177429935726492082687672800286342722204626838⟩
def polyval0Tail73 : Box := ⟨27593750000000000000000000000000000000000000000000000000000,2⟩
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
def resval1 : Box := ⟨117008025086200020320389008442503645115902935674229998881,231067275078107383898254076067334655877376873644770584⟩
def polyval1 : Box := ⟨3810809181532946102906345085728728231361611837344899341639,8587475657786546627436468584698309634973768354801076925⟩
theorem cell1_lo : Holds Q cell1 (1/2:ℝ) := by norm_num [Holds,Q,cell1]
theorem cell1_hi : Holds Q cell1 (3/4:ℝ) := by norm_num [Holds,Q,cell1]
def resval1Tail4 : Box := ⟨59906677670479803292099151974776010760558968465988,3154327285259090069534579254449796119063658438954⟩
def resval1Tail8 : Box := ⟨7208193185211582404767724001179741033210152668,6375682985497018078079063850224279197371481486066⟩
def resval1Tail12 : Box := ⟨-326806160131859499622804900089907830367579862,20149412292402165680952741365837109171406347489624⟩
def resval1Tail16 : Box := ⟨-2185016972116746451411408556527329138790509751,63680960973366681721741947624955782400878078118437⟩
def resval1Tail20 : Box := ⟨-14319899870154334081986903630831487505966151041,201255869975034318352405006892844812640456610111328⟩
def resval1Tail24 : Box := ⟨-93846898121105914574898235204316846719093367043,636019345793968169538856111685204778144924026651377⟩
def resval1Tail28 : Box := ⟨-615035031617643989426391661584050047892443488377,2009816783847123224695192618966998761664525303118799⟩
def resval1Tail32 : Box := ⟨-4030693583218693613177890716696709027327674200250,6349926659910089503533873642768401372922124681277168⟩
def resval1Tail36 : Box := ⟨-26415553466984319795636479002514826152954136094353,20055227440289644846257787092437773480336107808794614⟩
def resval1Tail40 : Box := ⟨-173116971201229672598597351251974695766527460662940,63294791749807376335991077965935568009199751098837941⟩
def resval1Tail44 : Box := ⟨-1134539382464379837158658660559046522120844515450713,199455394353068991725456376431424413833725610115354025⟩
def resval1Tail48 : Box := ⟨-7435317296918555427072130332417486682455358235462064,626527930064767151773964764824717993226941639565323787⟩
def resval1Tail52 : Box := ⟨-48728095437085179209635224242590131939450401514462570,1954908834496143402219215784731873367883411630780587030⟩
def resval1Tail56 : Box := ⟨-319344446256455351804023420594830526052778860262820356,6013137702668289990640742697699185710604859275060867758⟩
def resval1Tail60 : Box := ⟨-2092855762978026440137407958943552958282598173613902435,17920914979294865146188004020725459461560338478905088593⟩
def resval1Tail64 : Box := ⟨-13715739514966156654630828985377259689557540181838980979,49537659362213158923693984651566600301706696561703788062⟩
def resval1Tail68 : Box := ⟨-89887226407712518890767926832023780660424750290303961821,110024536694882470527242768149945116790154061248424998046⟩
def resval1Tail72 : Box := ⟨823413934988928587567147921417515021046640673131721666712,1507507218655794441247953611137799866352591426995746662⟩
def resval1Tail76 : Box := ⟨-28100034928807740954392660183258629441470623122445,409079051967909389007650168608803743435870124280⟩
def resval1Tail80 : Box := ⟨-1520651821423642245778689980546016488630741553,65748769706432364303168369057008830726084651468⟩
def resval1Tail84 : Box := ⟨-3715402524257288956312417965263049864248038,207656246180136207531920879716767159240940687256⟩
def resval1Tail88 : Box := ⟨-18711945464227255529627647419625682193565565,656286609421244472091566684922596782185464466558⟩
def resval1Tail92 : Box := ⟨-122615044931734892732442957572386753046354541,2074126294410865432314488951729002945804003254453⟩
def resval1Tail96 : Box := ⟨-803569804510908344256223389849905007958063021,6554847304451265919056400547576211657231507846880⟩
def resval1Tail100 : Box := ⟨-5266275066273680724126053809077202527823273355,20713827846036223880947704701504190054377461967822⟩
def resval1Tail104 : Box := ⟨-34513060273968382321243423106410396612811104428,65448056013827580570096642219765663674173005947198⟩
def resval1Tail108 : Box := ⟨-226184791811408208344508933554414626501494146421,206731070553497158152004759581164816171063978683104⟩
def resval1Tail112 : Box := ⟨-1482324651615213391807811573704648365445372735447,652604803353310612584196574101390598620832908842404⟩
def resval1Tail116 : Box := ⟨-9714562836825436809807859910157256597722199301903,2057523767647878401470406846339133879448050167260685⟩
def resval1Tail120 : Box := ⟨-63665359007419201464398536860712842978562087764868,6469828623759052242040771146674150074053436388401720⟩
def resval1Tail124 : Box := ⟨-417237296791024580424203616063884648734189609705528,20231830105532640191822346324159592718665781376793016⟩
def resval1Tail128 : Box := ⟨-2734406348249823330180650910060180902218479796014017,62526843713415229281288513745562808697494201460009303⟩
def resval1Tail132 : Box := ⟨-17920205443927370583729838266917298170275206875250709,188337572528772972159024810719882234722147004924069481⟩
def resval1Tail136 : Box := ⟨-117441858435281764299362967848411385614192981651495229,534434575682290891142122732478451959647626853764274401⟩
def resval1Tail140 : Box := ⟨-769667305835844435409887382087779101254395593378129982,1290584419737450056689255511289376235322332815432130251⟩
def resval1Tail144 : Box := ⟨-5215474770512414094867824518977130484200045140279984983,1436564357926754341667566563033808248717820362442697111⟩
def resval1Tail148 : Box := ⟨66233643062042544789429494560856774799814144,844569523892471911021072829942100426011283⟩
def resval1Tail152 : Box := ⟨1180775158362303007351884686785245637419,3242095729181545672684196332862591162366⟩
def resval1Tail156 : Box := ⟨499984829047003319387445202452164713,10145202484069577204517203938021928207361⟩
def resval1Tail160 : Box := ⟨814670061972379731767364277836014916,32063430275133225727819183730784039723433⟩
def resval1Tail164 : Box := ⟨5334712985541388573801009771705614687,101333511437453079105365336352250858080352⟩
def resval1Tail168 : Box := ⟨34961546385039652671950215702690850198,320245836149889236268580814400039393724659⟩
def resval1Tail172 : Box := ⟨229123989798783981283170618573995389886,1012016360087031895673973979107279948696878⟩
def resval1Tail176 : Box := ⟨1501586979512095648600787629348405075034,3197694017016381347489263959032643570052262⟩
def resval1Tail180 : Box := ⟨9840800428925792605396102724163261220395,10101197157879080909951981011642344288713342⟩
def resval1Tail184 : Box := ⟨64492669691006544650077037459643208911388,31891380383726890492568277680551159036221975⟩
def resval1Tail188 : Box := ⟨422659160086979460701577769324292811985406,100573680366764645357277471191593853105164621⟩
def resval1Tail192 : Box := ⟨2769939071546027868658554138120387859303258,316428368568873922433012497817985286360782842⟩
def resval1Tail196 : Box := ⟨18153072699284062833047062159742447326307101,990671208238339499217036638810638875714548788⟩
def resval1Tail200 : Box := ⟨118967977242028904801889599539985876896298511,3069414935350954938975064710978500210143724670⟩
def resval1Tail204 : Box := ⟨779668535653475160153505012637757173013258834,9297195978220740064940515190255596339211038848⟩
def resval1Tail208 : Box := ⟨5109635715313144362614028478388590808113347684,26738232377963269709491656369138085304347394700⟩
def resval1Tail212 : Box := ⟨33486508779542686359603644476131834654448450774,67168481864008334997084463608540392172522152625⟩
def resval1Tail216 : Box := ⟨219464835882766071926022404752405941973887705751,98660855442513460553364383068771882792449955148⟩
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
def polyval1Tail5 : Box := ⟨2103460936875831294132142966445903284912071352064405,119391479164245536101267949920524026229481696970814⟩
def polyval1Tail9 : Box := ⟨206608687855957129702305941737492792690160481354,277385936698592117430580856896695103658879543455685⟩
def polyval1Tail13 : Box := ⟨15706098627466819722589410301157200706828917180,876651900360678019961901201526227036192817260309174⟩
def polyval1Tail17 : Box := ⟨101877833292176091581397485557174340883216241254,2770600176320522981449355415444655091112732854310029⟩
def polyval1Tail21 : Box := ⟨667662880861605468384319918479909730586918390067,8756119074410315848124105160564612495116206643557610⟩
def polyval1Tail25 : Box := ⟨4375595412197630772188844337806562075625248799794,27671394833536538961431398956841766094483445055978263⟩
def polyval1Tail29 : Box := ⟨28675902091871966037192676312206699710817511379510,87440425700510826003924081597249545934813868699621845⟩
def polyval1Tail33 : Box := ⟨187930391949157125416174551636506721219124037435022,276257625290350664213752955435726228262419212280817441⟩
def polyval1Tail37 : Box := ⟨1231620616677966953272317739941002654735100385549673,872472851663183183413080530321868377822242269655627803⟩
def polyval1Tail41 : Box := ⟨8071548873460710236426786357692062939541421488533494,2753266042529557240644536496983750109082599538921525045⟩
def polyval1Tail45 : Box := ⟨52897702697112098756667307154059921414221796471372256,8674292709638352039609719184698762632314002804091077224⟩
def polyval1Tail49 : Box := ⟨346670384395793865424642310186871897781064949046717440,27235561042244685419081695295498625864377650056639181958⟩
def polyval1Tail53 : Box := ⟨2271939031176275944347442561178137629217615337626603237,84901533132033141227302196928034406614540058835728964122⟩
def polyval1Tail57 : Box := ⟨14889379634716944010229328048723358931014743714541607231,260621841029253644497069549142666198326667816968544985912⟩
def polyval1Tail61 : Box := ⟨97579038374104854198630665180200254360622943190212056197,773172473847846470993207389698184993735264649225921120982⟩
def polyval1Tail65 : Box := ⟨639493985913291539478794709769998487708958966729121543963,2112510793475122091931775670193124990434196478859234589714⟩
def polyval1Tail69 : Box := ⟨4190988003157628007881803825598439952581543165163613207861,4506706292165969221567854146525461192758598845365004230901⟩
def polyval1Tail73 : Box := ⟨27593750000000000000000000000000000000000000000000000000000,2⟩
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
def resval2 : Box := ⟨116892705980338204025527739937384369485940947582595245744,211642177161317712300504453969235466631947606017491819⟩
def polyval2 : Box := ⟨3801716667384058550143112490155514610071546251140123112136,7287129427417494627453632457856199748287638813256094560⟩
theorem cell2_lo : Holds Q cell2 (3/4:ℝ) := by norm_num [Holds,Q,cell2]
theorem cell2_hi : Holds Q cell2 (7/8:ℝ) := by norm_num [Holds,Q,cell2]
def resval2Tail4 : Box := ⟨-135698687304243531031901691115817952809185101968268,34641204544652124198541907418798669701398697011616386⟩
def resval2Tail8 : Box := ⟨-446867124464997773309153344716951824049038121730313,58980434875235822010737551562723330570137147967610166⟩
def resval2Tail12 : Box := ⟨-1025396441275600846337813146095286059974077462180294,100354968959447484491872301549904326433423201600761225⟩
def resval2Tail16 : Box := ⟨-2352872154074211549968429940783227740745698657911297,170597555462155018639615145365283708532336781487239441⟩
def resval2Tail20 : Box := ⟨-5398894628726207317663141744880534786748243540153567,289646899422157899899604157011717443734755021514854364⟩
def resval2Tail24 : Box := ⟨-12388290269536167635551749726070983680869510283810579,490946808619436165754311196350779774908862725369268033⟩
def resval2Tail28 : Box := ⟨-28426140229835198591228306728219792542584014464195598,830241317100123453610806231506367782106193393803259226⟩
def resval2Tail32 : Box := ⟨-65226551104740017997867611503928392405806395990266189,1399622222416089071356084084921429281421904583969544765⟩
def resval2Tail36 : Box := ⟨-149668682931278380877818303460123167795131827017545270,2349298654153817808494524524806539950191348572480666939⟩
def resval2Tail40 : Box := ⟨-343429389887758130812449904941961895049461102848227607,3919698562090814960220269921932137694387039088150972467⟩
def resval2Tail44 : Box := ⟨-788032229112570177778082993049231443178715531955417187,6484675847232384165747688549946832703697253914029907970⟩
def resval2Tail48 : Box := ⟨-1808216804983067781923014222518670302014278476989051238,10598702095770340366935599488091177148189454728827881125⟩
def resval2Tail52 : Box := ⟨-4149129810978968606499945982223134116121274054141789162,17016526089681572443477132229182811672932205932611108721⟩
def resval2Tail56 : Box := ⟨-9520583008029026740397578250970982878995987626720361323,26587091531373521804005574737325501244906487439639753729⟩
def resval2Tail60 : Box := ⟨-21845906236266047927197610349105795510903465344882396023,39752192436527089490504833723601633030360357218008095166⟩
def resval2Tail64 : Box := ⟨-50127562438121642425969104409623079517481470927153470514,54956074437603599742618171986513499829161974830547973115⟩
def resval2Tail68 : Box := ⟨-115022389077955968833481335872063364700486982866626858008,64245471206261434457271040751524151876723352626019075002⟩
def resval2Tail72 : Box := ⟨824904279379475784059811629597704538878824194477356672342,1010430720643778314451177363798790739468122115837008181⟩
def resval2Tail76 : Box := ⟨-29959553832844461156763449496162096697803010221268,416496921614552844369404290102466386301520458200898⟩
def resval2Tail80 : Box := ⟨-4977449821875433090370415111736260365178673585189,709154290358173330885225951312440469832560970463052⟩
def resval2Tail84 : Box := ⟨-11417832392519591216770248990490308819833861377167,1206856840462581276453996631507226527481478742689271⟩
def resval2Tail88 : Box := ⟨-26199328074929854558774602139165172056559911011129,2052123477664887425563068866964771321920898636561947⟩
def resval2Tail92 : Box := ⟨-60116913433354169355989024669280555742602668817185,3485410038795260471892057471532765182308014751847083⟩
def resval2Tail96 : Box := ⟨-137944120960990643738932379048088503417672911656068,5910568330654300407785586806102599656283233407799533⟩
def resval2Tail100 : Box := ⟨-316526238972705474792908304225482262856623435402264,10001968972112771192730176190921801684200473920537101⟩
def resval2Tail104 : Box := ⟨-726300325524849369469091852112204652604637072139996,16876596960858371050037366084332776970055270514640979⟩
def resval2Tail108 : Box := ⟨-1666566931605914629311383446725445026245426997240191,28363198701474331435986206973329932881344601283118281⟩
def resval2Tail112 : Box := ⟨-3824100361672393157811110633210571537479351186403008,47405354046114648855064946459671598113225239682194627⟩
def resval2Tail116 : Box := ⟨-8774771237091206824063344034664642769928421499527487,78620416290728753231564921027547072272956801084874993⟩
def resval2Tail120 : Box := ⟨-20134568390252768918292287592860560901681831626362766,128957763185736634071262156111324567301100588757744579⟩
def resval2Tail124 : Box := ⟨-46200730857589213640029197940642410418786359843337143,208144204642307745727401806485512061358334524195357767⟩
def resval2Tail128 : Box := ⟨-106012082822134061868562261930902807926264406233389893,327889148251409567124138382963748114325748605962151672⟩
def resval2Tail132 : Box := ⟨-243255063192194596003772819483719824233472515669992872,496961281029921496330153094298671702681694177401756869⟩
def resval2Tail136 : Box := ⟨-558172466728746653369200077148872870240798287390795790,704603937269370006710851223511809729681649259220885153⟩
def resval2Tail140 : Box := ⟨-1280781432764226145408616062197858486228386317595024411,873459606206063995151604384442754884455836009400042281⟩
def resval2Tail144 : Box := ⟨-3071672938369479518023203234545319341756774808574798722,724383627442699587274458785878565022608980574153232203⟩
def resval2Tail148 : Box := ⟨66023141053417159955195047489158764418633310,49798503046636594518173561698164770600361103⟩
def resval2Tail152 : Box := ⟨632209288918513969367183554441865372657923,83726566213525876577389613567272092360399174⟩
def resval2Tail156 : Box := ⟨1448007624474879884226583115879937627034377,142462350569880462826184158354393385979448208⟩
def resval2Tail160 : Box := ⟨3322593878990966006960383514879837382124330,242182123179202419682739064128621853727614826⟩
def resval2Tail164 : Box := ⟨7624015700158461206549882250593521028879779,411196192991113665192716410969245466326858546⟩
def resval2Tail168 : Box := ⟨17494047579752612140034469223390616827371074,696994738259245063627061347483217058407434529⟩
def resval2Tail172 : Box := ⟨40141798332924678189275565040140850027414212,1178744526863466046762114069594141881952138485⟩
def resval2Tail176 : Box := ⟨92109271228127566061737415535087370295035562,1987256987832437361185518885858309470951263976⟩
def resval2Tail180 : Box := ⟨211353706074947240328500989048977457318311319,3335953331456112292992265056268198002142742302⟩
def resval2Tail184 : Box := ⟨484971691513873545466916573007921869240233089,5566577507039737386570210769345023701950726232⟩
def resval2Tail188 : Box := ⟨1112814844545121552958961012333320658039195880,9210860922750001469751456285410511719095009839⟩
def resval2Tail192 : Box := ⟨2553462191523724173713045048872554886745455611,15058272895040550671430380361551518008771820848⟩
def resval2Tail196 : Box := ⟨5859168032761415498181271497914631711034637307,24185674497254107120636616429245201270319115228⟩
def resval2Tail200 : Box := ⟨13444432484683734813359795749698068880842176637,37810742443655949632424320998904205923840386159⟩
def resval2Tail204 : Box := ⟨30849561546032563755904129474686552164610345945,56589504054333763859214158861077943132813505906⟩
def resval2Tail208 : Box := ⟨70787327666470574154581900106492608625549377931,78379857964181314290958699940552289926798477522⟩
def resval2Tail212 : Box := ⟨162428427208309784641392982528290640907121986029,92044206114947093977532427302292440139095570800⟩
def resval2Tail216 : Box := ⟨372713848104779040703990038695625907359875857476,61410604873969483857465996981245679534780419718⟩
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
def polyval2Tail5 : Box := ⟨22363665060855003893919476351492329005108236677981399,3112553261609157471541490328738613423523687341042299252⟩
def polyval2Tail9 : Box := ⟨46553242641981911151636687110390650294549359463125351,5297934058051869639739839302090843541057604396965553078⟩
def polyval2Tail13 : Box := ⟨106820498102183679852887451576659050531432478350931946,9010638545846239125617344560031381513860097206789589332⟩
def polyval2Tail17 : Box := ⟨245110050539361492780585022721252611002814817411261258,15308872558112604660960936893173003783595774647677953880⟩
def polyval2Tail21 : Box := ⟨562428916078305109231307481743055206930473159156031419,25971978732833080762701556396786577882542668020573072859⟩
def polyval2Tail25 : Box := ⟨1290548000563964624141868488548567582812457486572327064,43975980000244452927145521447094680521385987896440986643⟩
def polyval2Tail29 : Box := ⟨2961288251985573751044095153038584246374301881244042802,74261410078423121549357557915542110048382478563282641907⟩
def polyval2Tail33 : Box := ⟨6794964702991021329254130836284227091042767600315229122,124943549400030226432434645515886690188536397385100916790⟩
def polyval2Tail37 : Box := ⟨15591709210994698141255556363206755382189336995003581715,209148379821064873211364802915870388441271000333046334678⟩
def polyval2Tail41 : Box := ⟨35776697414367442922751703231687750880270483910678422492,347619972587846636317594804177204517828781294820072352098⟩
def polyval2Tail45 : Box := ⟨82093121450508901630144281136174471607641718801730875046,571964671272968344756434424749764129252289863951341378198⟩
def polyval2Tail49 : Box := ⟨188370673554166569054012231770242825866274465897627278108,927423045311040761770107406524544960093940799934774799047⟩
def polyval2Tail53 : Box := ⟨432234881903499888279475388613732274290181054350128390498,1471259942116445646874128464941927286768850012825218748883⟩
def polyval2Tail57 : Box := ⟨991805091573396284824906254086650526789406101378078202504,2255473042198239326309688949767611676668331012223721976707⟩
def polyval2Tail61 : Box := ⟨2275793511479103292260509798346199203050844270104752811357,3263919623018465125876244345317662519128774217441586194948⟩
def polyval2Tail65 : Box := ⟨5222030165920864680562744441225192968201432764551128817594,4228475872790075622732501279261364915145147417239213192823⟩
def polyval2Tail69 : Box := ⟨11982457681838818789973657531271731547536478069321990830655,4139688551357756409763159162139795257906468242704522222963⟩
def polyval2Tail73 : Box := ⟨27593750000000000000000000000000000000000000000000000000000,2⟩
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
def resval3 : Box := ⟨116709278350296709471689960862072202149536246280630562714,1722730480009932737192425404505423695485176733594372885⟩
def polyval3 : Box := ⟨3820157300313633334332919395367655246577266927652488066866,243225972923028999895398092764701880563900572591447000390⟩
theorem cell3_lo : Holds Q cell3 (7/8:ℝ) := by norm_num [Holds,Q,cell3]
theorem cell3_hi : Holds Q cell3 (15/16:ℝ) := by norm_num [Holds,Q,cell3]
def resval3Tail4 : Box := ⟨-187270406591791673570816871646128076639949543807831988,1985786401577507403491307706637519709105047495675600870⟩
def resval3Tail8 : Box := ⟨-277723750917573549295152788490312822077454172590295833,2535456549848409592557352419382496711470410703787418758⟩
def resval3Tail12 : Box := ⟨-411738003952175702696527754176953956298748292525101425,3230031569194361663916623044849736951460977029281916968⟩
def resval3Tail16 : Box := ⟨-610420171386916795901712164849425628645464373191639384,4103989917425520346253174423433704261226252772369313954⟩
def resval3Tail20 : Box := ⟨-904975450538376217573796694421014197007984486569688863,5198008837469790036720582903476456605411751133597764336⟩
def resval3Tail24 : Box := ⟨-1341666944289085549036880337647836845073291499001625446,6558879787541101184351905409552087220381048941712160445⟩
def resval3Tail28 : Box := ⟨-1989081790370266105138282971597155941697331709990426655,8238478320587227592952491491558038598098148852293514656⟩
def resval3Tail32 : Box := ⟨-2948903515603122595682067856756372267973221108904485809,10291064473171401988171350385576800097653863756426724240⟩
def resval3Tail36 : Box := ⟨-4371882537176963440406623648973122682642453531497835141,12767762739115920374610987063365507516047641638252215064⟩
def resval3Tail40 : Box := ⟨-6481513151495475796019859625634350778919084475387323220,15706413620398458696725891508316494105552338571841880883⟩
def resval3Tail44 : Box := ⟨-9609135738613818309550900507955528254608557218060646777,19113984635170693115033049362817808450911961265828883548⟩
def resval3Tail48 : Box := ⟨-14245977364375295167392550532943335464617553938169866906,22937201239404294762224246549265872535616602200436735660⟩
def resval3Tail52 : Box := ⟨-21120304321517458153708466015618640333512827553581270674,27014743440997093769458657638908789884733554475993228647⟩
def resval3Tail56 : Box := ⟨-31311804253527911985849999507567738899274830877139378167,31000857280578804683205030412972247827482934717730166367⟩
def resval3Tail60 : Box := ⟨-46421162814981363133723481046100607430935139505310079783,34244962346478168888487916514231514334101004451977548198⟩
def resval3Tail64 : Box := ⟨-68821468713304220736685673422505243319143429935659305980,35603917520426615453919484218525471452631028575920279546⟩
def resval3Tail68 : Box := ⟨-102030759850722388761900127152868577321187811717055949469,33151725805972789951104873454509726975775328480552758110⟩
def resval3Tail72 : Box := ⟨825647449745221195806625538179937069454335784903396266229,781465984654591780669960148729868052570885005380242523⟩
def resval3Tail76 : Box := ⟨-2354219799032279680087126485136111810234824448154577,25641550048501061282585491991578556698725214022793580⟩
def resval3Tail80 : Box := ⟨-3449261559414499135560176047754930423667247159619879,32756415826413699620475921258929760134258194905116208⟩
def resval3Tail84 : Box := ⟨-5113683736415383133460128350916894638409401230504178,41755949368780636355183226216913219339747044906447323⟩
def resval3Tail88 : Box := ⟨-7581266903447550799942038046835786088746138480352177,53093266926236705311018879177623447020620654736842715⟩
def resval3Tail92 : Box := ⟨-11239570304514184030669476476081173741603575693152287,67305935849797704815729842609764948781272775891159096⟩
def resval3Tail96 : Box := ⟨-16663170185013089099741826697636391812270932994962627,85016993594324837008336754461928861124565667576007919⟩
def resval3Tail100 : Box := ⟨-24703901758877001193465188150962246370002964069988004,106924961716534164911194112402009466675478773490561309⟩
def resval3Tail104 : Box := ⟨-36624649171568599124463554966907072277232891788767522,133773952245212559962224046343426689728491077518772752⟩
def resval3Tail108 : Box := ⟨-54297695158963290952756205142721060303956646814594595,166289815803015376531747597714149451058274200197147796⟩
def resval3Tail112 : Box := ⟨-80498783367579634930144129282605487021496663354555009,205060191810775603631097701436709710497521049384921665⟩
def resval3Tail116 : Box := ⟨-119343079014483894353871023269187645635103338606484249,250323943154181565688964563441825233764956516404711917⟩
def resval3Tail120 : Box := ⟨-176931500239213924984922857331454235760831743546111506,301616607708354659580825426389234038310018860249215957⟩
def resval3Tail124 : Box := ⟨-262308933500028959094226119306764291912369687859163112,357189907042229902301484991009447061219836136935931120⟩
def resval3Tail128 : Box := ⟨-388884831140277292996383212499855343310494174022979530,413080127156561877170003864642240488849004326134788106⟩
def resval3Tail132 : Box := ⟨-576539311387931735251903266452750552109849569141222267,461635019613411002461649868638876514813334382736693544⟩
def resval3Tail136 : Box := ⟨-854745546674792640259022423453280081720096447445385253,489210857430128590301766756421560422130188614766230612⟩
def resval3Tail140 : Box := ⟨-1267199089701294088177536284370787336021493971355407086,472604139081512151657560201394176076109495939743600918⟩
def resval3Tail144 : Box := ⟨-1998039244690871415829514908428497293723950331145963529,367331740306199673852667879692427324069549183049839571⟩
def resval3Tail148 : Box := ⟨640777871776077646450859442773502777459693452,5620328969483798772728459562270437155898871834⟩
def resval3Tail152 : Box := ⟨852862989796569453255378310076833841633851696,7167041603146607592524279740812285575526482045⟩
def resval3Tail156 : Box := ⟨1264406168065263156372946089127830351257908214,9117665762232474865591761682777112451793089639⟩
def resval3Tail160 : Box := ⟨1874539202535299127496912016082702615142945792,11565450249318479926314632650648416551462387206⟩
def resval3Tail164 : Box := ⟨2779088960168598114080215248558081271532193080,14619491755221978713337656792830010697888286807⟩
def resval3Tail168 : Box := ⟨4120124795516553862385739633673835210094790340,18403003812164168557461059253931120344832239728⟩
def resval3Tail172 : Box := ⟨6108270938401520610945430241549718373432300219,23048781040521221494002409691969507038200082433⟩
def resval3Tail176 : Box := ⟨9055787314384682851288880964102565784333246466,28689132359505308779279653487940643873102656396⟩
def resval3Tail180 : Box := ⟨13425613354477545989416674746772518587886903430,35436629722027234088888636848531932516465594347⟩
def resval3Tail184 : Box := ⟨19904077656242211035348551912863144023646479671,43349966042756648563733124954428625146106736504⟩
def resval3Tail188 : Box := ⟨29508693337544529937425215899669455623254577803,52376087064580690066286898269387432303848906185⟩
def resval3Tail192 : Box := ⟨43747969512978707224704946490546590407482868699,62255012579538397332659700041430896356307787463⟩
def resval3Tail196 : Box := ⟨64858339019486117853658502491782378440683289679,72366578203530197507731551091835271190252711973⟩
def resval3Tail200 : Box := ⟨96155414461432833734287030816042810784929334615,81487492701581433496564027660115878816997967739⟩
def resval3Tail204 : Box := ⟨142554741148583744698370096564148850715405670544,87410800853101334845305346541996844177863499567⟩
def resval3Tail208 : Box := ⟨211343836826729803252284533788710709181417561375,86355358444861796330008712712997988195082684235⟩
def resval3Tail212 : Box := ⟨313326775530764136205031653207632189570826610836,72056226278585134593152377490173816992883824157⟩
def resval3Tail216 : Box := ⟨464526476023832494025818018003323512331723378127,34371603962545903915932464339861442719788128216⟩
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
def polyval3Tail5 : Box := ⟨34064537123644237053091448678466488949839216989877856777,307547437814612192684761145461588912081455572808602270587⟩
def polyval3Tail9 : Box := ⟨50499156805662055616101902609622524889133712322345832851,391727942180692093551568578751830604598265768991747047090⟩
def polyval3Tail13 : Box := ⟨74867278549987048049403315512152220946128201357281156773,497612625571773123516495592475652435497113365181726859436⟩
def polyval3Tail17 : Box := ⟨110994118989017559325774390995888504150636137975276807254,630103026621126798682536747356395912360168058624415666959⟩
def polyval3Tail21 : Box := ⟨164553790237582414914799707497554941612785512918493997999,794824827731926439116479218260417257708192227034848637886⟩
def polyval3Tail25 : Box := ⟨243958419853160500521239290054563126356999537840197984636,997993918067821857028222374401675695719948182157908113525⟩
def polyval3Tail29 : Box := ⟨361679366554378846295873196288287640448798024441384115130,1246075466393561889918358567868379453405122686142734939574⟩
def polyval3Tail33 : Box := ⟨536205982437142172795065909624443039015839142770297236385,1545094180171771290659987206829444202697626317901464865191⟩
def polyval3Tail37 : Box := ⟨794949566353413694101679377503228364925073483408039976089,1899373148841406113123842177195473046148343568635451290034⟩
def polyval3Tail41 : Box := ⟨1178548605842086974916679434009679419816583434391120407814,2309355265032139412960776807607805888394108463623971548326⟩
def polyval3Tail45 : Box := ⟨1747251492574340597037940148778534526264346719880253459837,2767973555951354228761989666985946527533859338674943486516⟩
def polyval3Tail49 : Box := ⟨2590379186034449908763207267425322008980397705085395877146,3254752444191326606912037905135614170935485677869835078117⟩
def polyval3Tail53 : Box := ⟨3840354039448619924022867881810510076852397315613836866983,3726392558447211973074956420884022172236008886246237847240⟩
def polyval3Tail57 : Box := ⟨5693498167303909119573359629921146669487527747280903996080,4101944895208708027520716268391141511099059392096018173657⟩
def polyval3Tail61 : Box := ⟨8440867963763874343631878185504929365320900779540735315075,4239707967985809124319196032114268018450781121088514907594⟩
def polyval3Tail65 : Box := ⟨12513967667708545915269658853321790327655686811283279565629,3901523181950746941412954454763061000688260663283665372871⟩
def polyval3Tail69 : Box := ⟨18552521940892942011038407435451798225409357956325807509997,2697959356398571063833304752379938936960263207196755611719⟩
def polyval3Tail73 : Box := ⟨27593750000000000000000000000000000000000000000000000000000,2⟩
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
def resval4 : Box := ⟨113553396887880290417877473795944208909887829933275856873,8696004946561068826189967210929613212715248009655027565⟩
def polyval4 : Box := ⟨4662422791299528941716142523506535284569351310344412704839,1931587262775875702514265791910292640359241496366266103986⟩
theorem cell4_lo : Holds Q cell4 (15/16:ℝ) := by norm_num [Holds,Q,cell4]
theorem cell4_hi : Holds Q cell4 (31/32:ℝ) := by norm_num [Holds,Q,cell4]
def resval4Tail4 : Box := ⟨-3942588218944633777053179823614762344037866235199055904,9442417852766450534362331475111741363944364118004187674⟩
def resval4Tail8 : Box := ⟨-4777364865912190256781486184706267487488254294238112539,10420185388807638232739742249520481139164903432820974927⟩
def resval4Tail12 : Box := ⟨-5788805633605111246420626775715592743815370164801698240,11466661716953655869653277959371098107759006253705600334⟩
def resval4Tail16 : Box := ⟨-7014383777562787050842907097318081835452022714737933515,12577665491036237411540714655392122610279431216424558609⟩
def resval4Tail20 : Box := ⟨-8499435443687908612772367466964703088952619716614258240,13745594884664684365477493894193793345562934539554021979⟩
def resval4Tail24 : Box := ⟨-10298895120694213132222630722559528226185327704503776802,14958359366840611572225247942226703533779762387414108050⟩
def resval4Tail28 : Box := ⟨-12479327763566899537701792377102332382955459736419802895,16198039487985925314465798255211276068668509252797339750⟩
def resval4Tail32 : Box := ⟨-15121391140065728330357408403340517865385108075226662953,17439210127435773934435406337756247199249553499911283832⟩
def resval4Tail36 : Box := ⟨-18322819493403757734789373074349217076263676123643059224,18646848802900988165850951844811941202561264063416616946⟩
def resval4Tail40 : Box := ⟨-22202038891667571419274364566763895987914114062329358053,19773733076123139606659372745866631029783843108486455524⟩
def resval4Tail44 : Box := ⟨-26902548001663997577767286014299492334661318488295978792,20757209672387932593666548859999347713718542128545426102⟩
def resval4Tail48 : Box := ⟨-32598226339179053598764767246715787942717442730421190740,21515191831958014991750816608007851347814181888593512905⟩
def resval4Tail52 : Box := ⟨-39499766356503461318603330732338866840581739047120791016,21941209617208259990277464825276420778939073388857633622⟩
def resval4Tail56 : Box := ⟨-47862467300656658567315108465680211857750392448653885578,21898299181763039021773820913319849553346182672910022144⟩
def resval4Tail60 : Box := ⟨-57995679149859515539144544467136332229350513356503616957,21211469875516060426679963274031746069914165664738785088⟩
def resval4Tail64 : Box := ⟨-70274245965647482813926270230589707227558987280838450014,19658430700713829192152174176383552682224036647587354755⟩
def resval4Tail68 : Box := ⟨-85152206789926485554944987414394210320760127252264228450,16958185013459872702283800882888168588951052083939430303⟩
def resval4Tail72 : Box := ⟨825978798254690405790731868508546052500940524877615269268,749953667042207118232259556832548616497545981086019458⟩
def resval4Tail76 : Box := ⟨-51504779008415154330099631444860323848096532920718212,126293384749542205336361057371555554215800569874225452⟩
def resval4Tail80 : Box := ⟨-62375724487841813366086542377514273970305871123384680,139466838481172563109431133014282173525481920953252824⟩
def resval4Tail84 : Box := ⟨-75581611716317376191039583021854441349171953821199760,153592674258673017696772953552115686064728854435861491⟩
def resval4Tail88 : Box := ⟨-91583387775373717792301484270380556664482210165945541,168623641723301751551196659152798192802071102225095751⟩
def resval4Tail92 : Box := ⟨-110972983058173759196518689310933170814867706742252908,184468968087063628632202901207758038649591258477526873⟩
def resval4Tail96 : Box := ⟨-134467650389118390997069964562478884133035396608505795,200980422111743437169025196269255466888447108754898156⟩
def resval4Tail100 : Box := ⟨-162936495918935027887094277048763364172469905834722881,217934971076037140239134774337489015892107983510228700⟩
def resval4Tail104 : Box := ⟨-197432628781096897770867644037408145619981655192098759,235013064793515846408724641704031637186111572300046094⟩
def resval4Tail108 : Box := ⟨-239232117320159849497882086114700325340423108156250353,251771525894984292144162329939583894598908062626761568⟩
def resval4Tail112 : Box := ⟨-289881192945785160291212289708941890318802100872434639,267609796634270933144040305936573228938508623448013956⟩
def resval4Tail116 : Box := ⟨-351253447760169564559910739942202309095119745171553169,281728013289332177400105514831157712013011886810288673⟩
def resval4Tail120 : Box := ⟨-425619141792620685349563557869529762089263494785273287,293075038958485503526367773201108951596049113764070529⟩
def resval4Tail124 : Box := ⟨-515729183629179655834147639522160976430235005516436297,300284170994344795603965616709522424319926293172461999⟩
def resval4Tail128 : Box := ⟨-624916891018061875051840963324799094063300172162776436,301593734444398520590367839926453953576666625773309259⟩
def resval4Tail132 : Box := ⟨-757221295742083627734998388205334123907403888447251775,294749158210721394820227390388528986211172139027764250⟩
def resval4Tail136 : Box := ⟨-917536554033496321578306805718868341820069848726532614,276882382565910833221729882547971710199050005144667782⟩
def resval4Tail140 : Box := ⟨-1111793222812843339925080720155834102566416403432707973,244363524524285420175489799395453342609291926398696107⟩
def resval4Tail144 : Box := ⟨-1460789008933801281228877491853786660807255713168490277,188565320718048698525230892379285323802993465395096400⟩
def resval4Tail148 : Box := ⟨19714705787440569399387937239717192048874416520,41883483240429725871005806342238331135862840775⟩
def resval4Tail152 : Box := ⟨23809375048244430848629860843054941450231613375,46055133783969450059108759095077957149012996598⟩
def resval4Tail156 : Box := ⟨28850180270294029633782413930263412452420255288,50474757659626270633341695362432795509793430656⟩
def resval4Tail160 : Box := ⟨34958201963150942926557937504386685263520586790,55108213542748274771461009517209969824458978285⟩
def resval4Tail164 : Box := ⟨42359384692298370090671577322484657838441504233,59903023748346857668147363647498719659312609466⟩
def resval4Tail168 : Box := ⟨51327510305064403470031939612062331899192742496,64782363962069755963810530760734545493142996269⟩
def resval4Tail172 : Box := ⟨62194324427840200506520299811181471467781284528,69638116328281715807873649419716567120920078360⟩
def resval4Tail176 : Box := ⟨75361808278742436614259781348277240418526258331,74322209083387167928261465141615228200894696452⟩
def resval4Tail180 : Box := ⟨91317048609979709245249760912505419643841247129,78635847089752524469218560306164231744100219219⟩
def resval4Tail184 : Box := ⟨110650255843045528084827882150362084211145359756,82316149426831850663754318914028738386646685023⟩
def resval4Tail188 : Box := ⟨134076596917011897111577431862012978897396456944,85019602706241870045584750640528296470631131200⟩
def resval4Tail192 : Box := ⟨162462650482671487591817144383546419597626777789,86301607846216477220686550242523613958405189959⟩
def resval4Tail196 : Box := ⟨196858463063405379612277485889916062192032248762,85591238612541379159468527379840583439491220993⟩
def resval4Tail200 : Box := ⟨238536391992568292529895740991903648994063816852,82160136169279190262059829011277151592322840164⟩
def resval4Tail204 : Box := ⟨289038171991140867144901529812780010287384774564,75084227731050030394444476095165630686618167536⟩
def resval4Tail208 : Box := ⟨350231946455333685287808433176153673147210640208,63196670123097832374944494358260012499580767598⟩
def resval4Tail212 : Box := ⟨424381373242265723971761632217259271921918607749,45030069649563868993765377907398407613034140685⟩
def resval4Tail216 : Box := ⟨514234499524179365947083265194898976602016502450,18745346503521834783554915953462336779869933315⟩
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
def polyval4Tail5 : Box := ⟨1051162828836076598098020727747177339774600986643617839362,2125145726625093160555370416928830971942666420055966387052⟩
def polyval4Tail9 : Box := ⟨1273707487520316040128166840559115538606669581493951787476,2332706179812269997255777466925221998394372127151778445801⟩
def polyval4Tail13 : Box := ⟨1543370723068429246812378463677575615212712152515395924014,2551391407332112598849269218398853876744642544181005880589⟩
def polyval4Tail17 : Box := ⟨1870125764768834505537682075414517535778635340301587242043,2779112634408571965160237278895392392367714080140123222836⟩
def polyval4Tail21 : Box := ⟨2266059815557026684330959654915130772285062466576038840258,3012737097188701472551473914742787899640105990785766864075⟩
def polyval4Tail25 : Box := ⟨2745819123195217748153892766205299464542025643787835821132,3247785517716320420869267804133264412858575711261219017924⟩
def polyval4Tail29 : Box := ⟨3327150768723747320555611319890248111560005466213616803950,3478054505383129563575051061034728053180922684747911524918⟩
def polyval4Tail33 : Box := ⟨4031559159999335044084937748273137927698581315660257825146,3695146486652871603773434638628063669615573733790999660087⟩
def polyval4Tail37 : Box := ⟨4885101514894429590152289811506928437690755349577066777813,3887885888904708965421242964428210179875300866284541395948⟩
def polyval4Tail41 : Box := ⟨5919351760381407126571697562981297589675598882239980121196,4041595570460106504465163575826804512368238868669449482930⟩
def polyval4Tail45 : Box := ⟨7172568503704405514010101135400766388742716083296653897214,4137201721752807691950446012461523843207050263899414647471⟩
def polyval4Tail49 : Box := ⟨8691110280801694274904292749187384952668241735645797531202,4150128439193869220347465026031153894988325471244135647244⟩
def polyval4Tail53 : Box := ⟨10531150434331195774548837628253304233285706708241654569559,4048934622812137174748992461329319171933838752035127253687⟩
def polyval4Tail57 : Box := ⟨12760755057440590874514583737603061177192505308613197629470,3793635442482126161449136311052012885333264888962128813706⟩
def polyval4Tail61 : Box := ⟨15462400869818846321428100196944785836836799424405778231283,3333637956420056786889473720691534066846315567716916871404⟩
def polyval4Tail65 : Box := ⟨18736026166397585394673953841767944010705497573428016599796,2605205065244625239138173034553726107712565975816741920540⟩
def polyval4Tail69 : Box := ⟨22702727846297836451160436724146670122474669582706476555748,1528343250190379790146504135025097415630586003313234009930⟩
def polyval4Tail73 : Box := ⟨27593750000000000000000000000000000000000000000000000000000,2⟩
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
def resval5 : Box := ⟨102111095835220928529312410309735286668688187848944579540,13773851080903506079839252831187401864027220132852628408⟩
def polyval5 : Box := ⟨8781645209422703237557960547994704897853865788952966870767,3867462198538748606552633951192127323947719052182318319094⟩
theorem cell5_lo : Holds Q cell5 (31/32:ℝ) := by norm_num [Holds,Q,cell5]
theorem cell5_hi : Holds Q cell5 (63/64:ℝ) := by norm_num [Holds,Q,cell5]
def resval5Tail4 : Box := ⟨-16142828865000310304896681808006852061460189215351575872,13996481193996615305426348048477399064291562577071525848⟩
def resval5Tail8 : Box := ⟨-17749292166523266113206594117991008523538042696001418394,14349732563033751751208926133422492270364904185260185998⟩
def resval5Tail12 : Box := ⟨-19515553129502693042278851419236676952033280347426267091,14670545051751862714797709661299721209614861777249176229⟩
def resval5Tail16 : Box := ⟨-21457577588375295786995554495820598969678928533639769564,14951295218725273241992726220286327013146788663602995055⟩
def resval5Tail20 : Box := ⟨-23592856062324364292613126211042979263851631168146395075,15183315820615799654111660937386680291461003360609819360⟩
def resval5Tail24 : Box := ⟨-25940619572971131831019268608709887047640455165879183748,15356772792388869412538877250506595786201029118924044079⟩
def resval5Tail28 : Box := ⟨-28522012852195455184590218765023380149803230398276811339,15460529347356467707692782063129331131601541698377027670⟩
def resval5Tail32 : Box := ⟨-31360284778565417426392175668309793515300862452497754160,15481995267135052065856230723049723954080011969068137981⟩
def resval5Tail36 : Box := ⟨-34480997764399377828749215406872276093415230809591019969,15406959823968081976058030370736185478495884983655703074⟩
def resval5Tail40 : Box := ⟨-37912257979275376859369247466088398357648075973861371028,15219406617550576084601460163013357227077831319595778638⟩
def resval5Tail44 : Box := ⟨-41684968483456714082824183763375185913515528490228087103,14901308431753190069909835860389354993859884514734164080⟩
def resval5Tail48 : Box := ⟨-45833107551036749819312648420671683298660787497357245080,14432400021938911527518769251110269323684476081959342143⟩
def resval5Tail52 : Box := ⟨-50394034689472893538134594117027689292252499860456366466,13789926529084584562511560705046742738130653730482819991⟩
def resval5Tail56 : Box := ⟨-55408827111622531619660279673472061201037680289906175460,12948364980668033671105184292849484871039427336582906880⟩
def resval5Tail60 : Box := ⟨-60922649690653124000587866361215527263534131295386389012,11879116078065053253638409359059256783043488736803225609⟩
def resval5Tail64 : Box := ⟨-66985161720701994249920890976398911496684400729270361863,10550163183268757815465439607976350588337109604627961255⟩
def resval5Tail68 : Box := ⟨-73650802693372952923671398307586503141653608259330627100,8925691057655720270837129933268133115858056487987521912⟩
def resval5Tail72 : Box := ⟨826011377260277430489094173211506254773526713300944695636,756750988029942172833852341861825522031274187862859715⟩
def resval5Tail76 : Box := ⟨-215540967849079022175872528296084887587731335097272190,190015239153969585721526125512164126834332257982812940⟩
def resval5Tail80 : Box := ⟨-236959535123580929623555679945602188908376071052551668,194936400554444596155845551836018274321777896406041058⟩
def resval5Tail84 : Box := ⟨-260539762576779769463340637336593481561878790647730224,199437976061519597537439055202898734165160703056043017⟩
def resval5Tail88 : Box := ⟨-286466498450278801604699153817064125675150377679014068,203418919047579928009598090117970988131606719656282071⟩
def resval5Tail92 : Box := ⟨-314973246014354634042603488535162951120754104294443963,206764442831045158505789897725886195449289384585089425⟩
def resval5Tail96 : Box := ⟨-346316746431133545096022715091382873123026930020941106,209344243340888525139570647006701317142868369487073893⟩
def resval5Tail100 : Box := ⟨-380779289594583882215648480063219997420262520554004362,211010688694513959058958459142037914824373758241347760⟩
def resval5Tail104 : Box := ⟨-418671256525529823403799133511254589718464559504781431,211596811324793993651786991559803231330636375847560221⟩
def resval5Tail108 : Box := ⟨-460333914765408558225493001548218242917629896009714219,210914081863767274087654213571151858988505960389592398⟩
def resval5Tail112 : Box := ⟨-506142491944212805032602136604562404356803374414424127,208749941866481885361538107916918443446074764972560769⟩
def resval5Tail116 : Box := ⟨-556509555204182388254623167664018079411531912476793435,204865070100084405201928206619217476240855058177112997⟩
def resval5Tail120 : Box := ⟨-611888726915448309855387290988271554783579049985293127,198990354525097992316758566759789168755893420752446721⟩
def resval5Tail124 : Box := ⟨-672778770148588916900183351941537184393228676312700568,190823539233732063915108612363299967250155196707814900⟩
def resval5Tail128 : Box := ⟨-739728080699210489674736570455658100291930157430955933,180025512457404801015961457351634971881416752699262778⟩
def resval5Tail132 : Box := ⟨-813339626121232348037186347779408246759708107892852148,166216198283148129650546286944789047095658017422518960⟩
def resval5Tail136 : Box := ⟨-894276376277510968185074454623398452732428327646043851,148970010892548842629644895737646332942480963047675091⟩
def resval5Tail140 : Box := ⟨-983267502477135324263380620725510638115388227116420880,127810815922075076566144720991539633532329642566443569⟩
def resval5Tail144 : Box := ⟨-1192055451582709136024434716691134111153619125922648171,99121992782509802904481813439971223738901745392178585⟩
def resval5Tail148 : Box := ⟨107717914832575540949313988926845221952753318127,80985805300804678196530449817941263112834937758⟩
def resval5Tail152 : Box := ⟨118365268240009551157708575343256626498236027366,82537854791124533700254150291763108668059185714⟩
def resval5Tail156 : Box := ⟨130143987501589330591136076019035963430426821673,83821823168327271017285192252053709602472742443⟩
def resval5Tail160 : Box := ⟨143094827542741043699364583440398853030071653062,84783005851134598958742099345222475203246011897⟩
def resval5Tail164 : Box := ⟨157334426757844534736758165317668330199489660518,85359986848654856760324691293457366703807470832⟩
def resval5Tail168 : Box := ⟨172991031669721490256724834588017969496272140221,85483333820650715116231365102609886395941903427⟩
def resval5Tail172 : Box := ⟨190205650821825042880146191223466170332043720630,85074676495364430805051868213407620481342843947⟩
def resval5Tail176 : Box := ⟨209133324747298325039897761032782470176987787971,84045685341737527513199366508373636384873933120⟩
def resval5Tail180 : Box := ⟨229944522315108805222411433060327892838404895776,82296940031553116305785755947817004268509603416⟩
def resval5Tail184 : Box := ⟨252826676028860038428583957559459595552444125414,79716676166693161788948139583768907701785860631⟩
def resval5Tail188 : Box := ⟨277985870105687300406455963603137990487723640444,76179397563601684663862394376341882923134220879⟩
def resval5Tail192 : Box := ⟨305648696538631940826550813749338371860739195427,71544340083846707407468887205011676160309607361⟩
def resval5Tail196 : Box := ⟨336064295858803862146940046860734607036350624945,65653771564281533486919180988616224276655914165⟩
def resval5Tail200 : Box := ⟨369506600977108691090806800545936198259202039240,58331110819401633517538819265808670989073696022⟩
def resval5Tail204 : Box := ⟨406276804314317775353560658416497997258394606690,49378846947422986065835356384089782156841155143⟩
def resval5Tail208 : Box := ⟨446706070439305420324396924406100704318949392402,38576238254245162542607808761694722368815663467⟩
def resval5Tail212 : Box := ⟨491158518751614641477065184393004981967800944891,25676767992498501267484663043753669214997371233⟩
def resval5Tail216 : Box := ⟨540039523545658888601196230294331468710087405961,10405117511116182769061609098048323959819990052⟩
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
def polyval5Tail5 : Box := ⟨5484198544540934809609848043296076999847196430900271229548,3944788329259840600397891632121473062529899392718340072004⟩
def polyval5Tail9 : Box := ⟨6029937812912512169977591332422452464211625603052740813981,4012118081597401214234558153346330287521897064737396177432⟩
def polyval5Tail13 : Box := ⟨6629986739848829007332350949778451108348796281668699619902,4065002019594912232995079625925707379784965675356995014151⟩
def polyval5Tail17 : Box := ⟨7289747512464315957503973821168532835286811301626784083197,4100627702376698271570143462275088131306284107856609759042⟩
def polyval5Tail21 : Box := ⟨8015162153505686323334581496614462949370984034201027104283,4115813432635490090860483319963392306693742424632967616186⟩
def polyval5Tail25 : Box := ⟨8812763986289626747784408377445118285949745862859157790036,4106965688621466036147228278761034592139591770784660032721⟩
def polyval5Tail29 : Box := ⟨9689736475771018051832048116647424030484090523279999767234,4070031952373581838226434924692950194538611515241670769434⟩
def polyval5Tail33 : Box := ⟨10653977925195473642798370407113378617996099482153052036423,4000448441311904340859068955096616624341045059885360753797⟩
def polyval5Tail37 : Box := ⟨11714172610821246387978228552429241625023655069977227876340,3893082209843227168797594255538132687386131857884917442750⟩
def polyval5Tail41 : Box := ⟨12879868995373104368211500274109323916554544355061934229782,3742167032858612601589555051571776038662760397709239322637⟩
def polyval5Tail45 : Box := ⟨14161565724644315796348173638591117948466808187947454670676,3541232422664346597552587154206316653968830970487733427894⟩
def polyval5Tail49 : Box := ⟨15570806181760480659926178864307911459031257822003703997825,3283025064428553113110135176317861684008940383816554790994⟩
def polyval5Tail53 : Box := ⟨17120282450692069413046423668816380582000730752229568638881,2959421882027512414122750315013178381633009439827399417485⟩
def polyval5Tail57 : Box := ⟨18823949625345323779541179273310170197395907498261920132344,2561333865559801479884219679851589215591719674436835880239⟩
def polyval5Tail61 : Box := ⟨20697151493736879633070523545904689955723884937464316744385,2078599703015881732885995986624814960103505722141393000271⟩
def polyval5Tail65 : Box := ⟨22756758729222211329046792701530144183755891197330195717646,1499868160823077210093840319211831134779862347653326299823⟩
def polyval5Tail69 : Box := ⟨25021320978103277013130734745069563627793295638384951722530,812468044375584963950466698390428624442036260765906523202⟩
def polyval5Tail73 : Box := ⟨27593750000000000000000000000000000000000000000000000000000,2⟩
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
def resval6 : Box := ⟨86655618668222424121351650602013188741006592372958235507,12297751818985643857112959672246505251645097569658011347⟩
def polyval6 : Box := ⟨15567267741589384120725229750912052395772521518468953066716,3870606008002302100988021493686469529178576531490123766091⟩
theorem cell6_lo : Holds Q cell6 (63/64:ℝ) := by norm_num [Holds,Q,cell6]
theorem cell6_hi : Holds Q cell6 (127/128:ℝ) := by norm_num [Holds,Q,cell6]
def resval6Tail4 : Box := ⟨-31584917510031385528817602874644744685973343739868975598,12036258298226630968146201209555624780831687308848059526⟩
def resval6Tail8 : Box := ⟨-33109934738972014162682202524655877797070253416743162054,11901508437734553262991200998205914081916184183267584525⟩
def resval6Tail12 : Box := ⟨-34708520478346173556760198166024200674389686349524199562,11737438314958549720659458773614669033720980330819630409⟩
def resval6Tail16 : Box := ⟨-36384287768660328471753150133001656935308818429021146925,11541904676101875245678232283229200927041019703552317101⟩
def resval6Tail20 : Box := ⟨-38140963031205828216887109554249830208300869040986855422,11312638141587514676506851061458110004508609383070503628⟩
def resval6Tail24 : Box := ⟨-39982452595948454119269398322800809073722051772264766489,11047235852105779956191534634639752211125079600113204114⟩
def resval6Tail28 : Box := ⟨-41912851394951407612164983863060435798915287357668598052,10743154261883824444514788230585291032646238481022679577⟩
def resval6Tail32 : Box := ⟨-43936452068307853278226788861572263046496501492401703546,10397701559831444175989837430924802996516357232731471891⟩
def resval6Tail36 : Box := ⟨-46057754509712032310210486273147694237231547011219133352,10008029699710243444690558358223979263845594546532472913⟩
def resval6Tail40 : Box := ⟨-48281475872901505105170221254771619264675580697779789048,9571126019650523628661252949179481555743106698530671889⟩
def resval6Tail44 : Box := ⟨-50612561061221934429985647598309461512371425113293609508,9083804430364981775762191367722277722003838299327983752⟩
def resval6Tail48 : Box := ⟨-53056193723640121362950131544788376259322325267110143213,8542696150384990738533747499889245160258194599201892934⟩
def resval6Tail52 : Box := ⟨-55617807781657197972363247176780060686553704862499067605,7944239965571673255615438866116151070440874224161749352⟩
def resval6Tail56 : Box := ⟨-58303099512754428245338572032567523522696676745151000055,7284671989027725158950228218630273838862832863935626893⟩
def resval6Tail60 : Box := ⟨-61118040217235899434684291943173090254044243231837993128,6560014896354100886375377420328684085928291279916451409⟩
def resval6Tail64 : Box := ⟨-64068889487670014660394637418933822923405575353694248250,5766066609591135198120858565459186103597249019165946632⟩
def resval6Tail68 : Box := ⟨-67162049457619080125972365473757637987288853559302842215,4898383788368212632015811106000973309745544931587404095⟩
def resval6Tail72 : Box := ⟨825894724286848767658039575067282597117502839757494368540,706523794940495537064422833086722190621735490829581614⟩
def resval6Tail76 : Box := ⟨-425322366138724132230685629948416723169733562672313244,164295342518006326730717109064024637118709877260996983⟩
def resval6Tail80 : Box := ⟨-445828583619074198608431547444891166097345414175161978,162551712509792430584823704148125327193764084787927296⟩
def resval6Tail84 : Box := ⟨-467353698899410274024061381315379643640617219144850898,160415688120296875465202968164106210179552861022175541⟩
def resval6Tail88 : Box := ⟨-489918073029941111907249240995952037641765167025807436,157858337122036323301205487415271754841622297722959885⟩
def resval6Tail92 : Box := ⟨-513571881097797938069073532953940137167464006080970477,154849176421463023758776709635760291966667965834676898⟩
def resval6Tail96 : Box := ⟨-538367722225696564958640890086800237155536806810662481,151355927992356703679662262312240069284017859178989399⟩
def resval6Tail100 : Box := ⟨-564360735083335822809197128654652645170969996212302530,147344421896114038065343102612833349892153550021958215⟩
def resval6Tail104 : Box := ⟨-591608720498810108332795253966601624880467919604001856,142778494309624888493043472596281510256722253547521335⟩
def resval6Tail108 : Box := ⟨-620172269990676536515160941183255427250176679765362772,137619880291105362722616872255006164454269053527828997⟩
def resval6Tail112 : Box := ⟨-650114900505700303110089504767118399465011891511911283,131828101019019372411868357199052261534045212153254848⟩
def resval6Tail116 : Box := ⟨-681503195661893387129592199692113909929155496264005295,125360345226103692052780151922944777363074860836667693⟩
def resval6Tail120 : Box := ⟨-714406953810929619622250612712721124363228243798160127,118171344536735135461365933641968329413275529694964545⟩
def resval6Tail124 : Box := ⟨-748899343249183454618468188400187429063027642094958785,110213242401425567813965610183462270572549122968005826⟩
def resval6Tail128 : Box := ⟨-785057064922536336239526075775091648683412750865297955,101435456307068084761707298280756000438700272511493320⟩
def resval6Tail132 : Box := ⟨-822960522986784504430718552436473538146135547482042520,91784532925649478742132412300419477644724345669463663⟩
def resval6Tail136 : Box := ⟨-862694003628728897106516513078461688983551264678648818,81203995846129342459525944003735587933766226909287823⟩
def resval6Tail140 : Box := ⟨-904346088197949738348366143024669590360257787864468390,69634176440038210889529310484431695335267196778626557⟩
def resval6Tail144 : Box := ⟨-1057661480708416542282421676765303889565628636963373255,54385272601730822361454435815951074992876881018994571⟩
def resval6Tail148 : Box := ⟨248230148954040669600708667588559198366886839168,79933221072322868639425231962976301295097343889⟩
def resval6Tail152 : Box := ⟨260146532277870793505600914967681784056314066865,78407529784596956522334689829775789871907331088⟩
def resval6Tail156 : Box := ⟨272706704882478949007787660792106790017340354016,76637080834793882131139857920008099349113386706⟩
def resval6Tail160 : Box := ⟨285873298260086397518223627337638163964516584064,74604081013259207218380174320840012669158675960⟩
def resval6Tail164 : Box := ⟨299675589910503538195065896609805707809574743194,72290210772376216972003815073195735764737261624⟩
def resval6Tail168 : Box := ⟨314144272077148762951577657012759209908747197756,69676086239261596550377498877803487728633079215⟩
def resval6Tail172 : Box := ⟨329311518860624867655593933839033436700002089190,66741202082217876178860443825395890507184496138⟩
def resval6Tail176 : Box := ⟨345211057764118907425143009362372122842049246867,63463871450866312571547647491176997157461965067⟩
def resval6Tail180 : Box := ⟨361878244693465062920225484640359945980924933437,59821162828030948073652832098646335881654052493⟩
def resval6Tail184 : Box := ⟨379350142578297422531226717504592261454320071781,55788833638255166431379960905204814964806206402⟩
def resval6Tail188 : Box := ⟨397665603789122454381606087911517088067791818544,51341260450158373110761053500586232081098180725⟩
def resval6Tail192 : Box := ⟨416865356533582533158111752463940076842636775030,46451365601783084618600740824478130831672226071⟩
def resval6Tail196 : Box := ⟨436992095424030442699838233363162574338558385292,41090540069630037276097218914063577203736059571⟩
def resval6Tail200 : Box := ⟨458090576417810546730601037233975410789209135289,35228562393211650058902586912677955801915391361⟩
def resval6Tail204 : Box := ⟨480207716341366016423953765072276755470011497813,28833513457652067757195160045920197230214231265⟩
def resval6Tail208 : Box := ⟨503392697219522090621445478892884102880903155827,21871686927101537893004743290729477812124783949⟩
def resval6Tail212 : Box := ⟨527697075746067725954695528865102284892343275647,14307495106347777350631692690181197476277131476⟩
def resval6Tail216 : Box := ⟨553179861734987802898921864109860541573207943096,6103176572681758942501092861564238466399140277⟩
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
def polyval6Tail5 : Box := ⟨12342499242143183014013779567695899317033530314834454213893,3798512153310461013849004873683509835717013783540894887847⟩
def polyval6Tail9 : Box := ⟨12938407152874995258393899466946095290292999683956189065533,3717016478576939854127480135680345739416081719116205108455⟩
def polyval6Tail13 : Box := ⟨13563088331719970152311660981032078468238762144676760676036,3623143989433477426951564902217275382523112163672037628108⟩
def polyval6Tail17 : Box := ⟨14217929836589784690445308416541045604026456572142813107473,3516028058205838300923266976737498539174887514958086155501⟩
def polyval6Tail21 : Box := ⟨14904387842511171656004297825901270486884694603284828780519,3394751651099472983167927403218646796668787859070144352922⟩
def polyval6Tail25 : Box := ⟨15623988830519928350220729403588255309571713793127381521281,3258344610955740866184468478768476211593875113032630559639⟩
def polyval6Tail29 : Box := ⟨16378332981912169088374129138616954716430092833738597593074,3105780810409121047128902405197236392346577961445766266240⟩
def polyval6Tail33 : Box := ⟨17169097736577507770311864882852588783845525433298996485798,2935975158611037805100269558938107244894614780889305664429⟩
def polyval6Tail37 : Box := ⟨17998041523132814078879384141657510091897153805725857235325,2747780454161645880846805861307314657577003089645773588542⟩
def polyval6Tail41 : Box := ⟨18867007669151118321213566873460047528291668144624123778766,2539984076528778292773683270500300195508629180452745547768⟩
def polyval6Tail45 : Box := ⟨19777928500180865332018926294874818807524468326789565054162,2311304507851074398039405959198529001072641094709039981673⟩
def polyval6Tail49 : Box := ⟨20732829636670532632405225962952031714963054839820021426485,2060387676621365638970399165490865915737219070560236793874⟩
def polyval6Tail53 : Box := ⟨21733834498353711461458546548066838192457411755375161366148,1785803114325788532092060939678194676907994645926677102711⟩
def polyval6Tail57 : Box := ⟨22783169026111080522094329014276110124286661177594155045519,1486039915672859519982589503463131096946142709717607494064⟩
def polyval6Tail61 : Box := ⟨23883166631809323671130809993374401199503501901699487264925,1159502492583877169947461585292114733075601251157549626678⟩
def polyval6Tail65 : Box := ⟨25036273387140808220065924934797643285757835187741678742186,804506111629627085337923881322777860083322243725677107498⟩
def polyval6Tail69 : Box := ⟨26245053606143115882376016525021851071805820267067280775322,419272198719455252932905464388146947428137670706706469404⟩
def polyval6Tail73 : Box := ⟨27593750000000000000000000000000000000000000000000000000000,2⟩
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
def resval7 : Box := ⟨68802472559011379940032041351041352035302798836788592299,19824085887113341018588748096965987125044086084032948571⟩
def polyval7 : Box := ⟨24549193199398195901483989656418363758413274043255913324697,6760552092285479106341358534585972514012600767993998248567⟩
theorem cell7_lo : Holds Q cell7 (127/128:ℝ) := by norm_num [Holds,Q,cell7]
theorem cell7_hi : Holds Q cell7 (1/1:ℝ) := by norm_num [Holds,Q,cell7]
def resval7Tail4 : Box := ⟨-48735658290777213781013076045709154659876170973125467286,18912962687745085358612476900875846068128365255469381827⟩
def resval7Tail8 : Box := ⟨-49504707074076781442960489683267645155334725013085668746,18143971637056765577389808358174394534102256975343689534⟩
def resval7Tail12 : Box := ⟨-50285831368119867623182859666469715713854717714797113958,17362847349815326541280405659623651879122379261695162319⟩
def resval7Tail16 : Box := ⟨-51079280849931204889429189101645641130462451493649978286,16569397868009987328929908000050346182192404245067510592⟩
def resval7Tail20 : Box := ⟨-51885250003044394068542453355016509544514408714293600327,15763428714896821145435435138160493266525231905417139110⟩
def resval7Tail24 : Box := ⟨-52703936372707229076175722971792164537387240941864933335,14944742345233986429989570594801282351848575768820269319⟩
def resval7Tail28 : Box := ⟨-53535540621185958179266525931435610284340617981343726862,14113138096755257337105310742480731942186085017049469325⟩
def resval7Tail32 : Box := ⟨-54380266576954201980029179374963511008102828477153038944,13268412140987013537143638729639711142538572938464736377⟩
def resval7Tail36 : Box := ⟨-55238321284651891890761224321173642653965128699729547369,12410357433289323626476927551840954249709195680185945320⟩
def resval7Tail40 : Box := ⟨-56109915055832477388906124285706616949411784610633626579,11538763662108738128172235850799793921990545982759285299⟩
def resval7Tail44 : Box := ⟨-56995261520510862441287167085417555779544289032203711785,10653417197430353074828056514243356722373083280040317178⟩
def resval7Tail48 : Box := ⟨-57894577679524705884622979161985276220359375299440325609,9754101038416509621150049936831717228284263230635846666⟩
def resval7Tail52 : Box := ⟨-58808083957721919462603965921133208868466911480876931089,8840594760219295767908188783531471702393827287621128381⟩
def resval7Tail56 : Box := ⟨-59736004257987381330788587595914241595284610201008950616,7912674459953812400649002218180867337005373131863550191⟩
def resval7Tail60 : Box := ⟨-60678566016116391335829677060992823877093220332767125875,6970112701818645371800500368262911557149453719368243242⟩
def resval7Tail64 : Box := ⟨-61636000247645062978511748424656129027991916745621096140,6012678460987918170064844196431120196327301719120452908⟩
def resval7Tail68 : Box := ⟨-62608383112031624356108933610861057748410508297341235379,5040132487433290943855220611867220958234788079650290563⟩
def resval7Tail72 : Box := ⟨825714223756062333231089447377399012688559825041292987650,807107868832790702961617081523812930513584810075493404⟩
def resval7Tail76 : Box := ⟨-658491172376061179809752131987959814850271961661517355,257829029289528176536618262204649997862802712724241146⟩
def resval7Tail80 : Box := ⟨-668853436216248280501889447172207610744899093314171818,247439118364717098550710678534464817340459562484855073⟩
def resval7Tail84 : Box := ⟨-679407131433810100790646335834980832717943782203495030,236885421674207504383161335933461469981690128844359904⟩
def resval7Tail88 : Box := ⟨-690127352650465837936247776220201657196897365338479942,226165200456730870164395844208090287292562847416883542⟩
def resval7Tail92 : Box := ⟨-701016725967799128190289081772540308020200217847860081,215275827139395353977527173476716287663017321438686427⟩
def resval7Tail96 : Box := ⟨-712077920400163392895811509954726633762389170577480333,204214632707031067788860470116108749749049225743434734⟩
def resval7Tail100 : Box := ⟨-723313647076536056346977948709365641772026045586128307,192978906030658403727561055589955897133560748139340313⟩
def resval7Tail104 : Box := ⟨-734726659904226554878273333307902525101047185581588568,181565893202967905152313526552546025677188177871972200⟩
def resval7Tail108 : Box := ⟨-746319756243864457621885845315646704485759370263837572,169972796863330002402171575571243155854245050786918817⟩
def resval7Tail112 : Box := ⟨-758095777595040181930127046730235255405684493978547822,158196775512154278093554071424168967859694158150795386⟩
def resval7Tail116 : Box := ⟨-770057610292764306808505603293019538754381597228220918,146234942814430153223185333447770511916447521258397266⟩
def resval7Tail120 : Box := ⟨-782208186214916170824589139337167866051497926834514892,134084366892278289294171924162038379181441890677168095⟩
def resval7Tail124 : Box := ⟨-794550483500855153384352111970027801291207415691764335,121742069606339308674564302298520130841650408077648763⟩
def resval7Tail128 : Box := ⟨-807087527281370891671872432311730821783555185036480620,109205025825823689208455961180040175374256736238680027⟩
def resval7Tail132 : Box := ⟨-819822390420177308422944108386215839696909981281523569,96470162687042196763293833208024151104726357469532667⟩
def resval7Tail136 : Box := ⟨-832758194292760463681260283034240202354477388233787691,83534358838918326296813475074499838362304226254265726⟩
def resval7Tail140 : Box := ⟨-845898333613734472843094520334124157062233983873389250,70394434679855865576292179391454717940581402437325419⟩
def resval7Tail144 : Box := ⟨-968055369968320804344993188898869517673000517673092087,54444559990111046545926772796327876074850993976888493⟩
def resval7Tail148 : Box := ⟨430759376521551321452195476076680002861923960734,137493764804166811686276654015519293643235629772⟩
def resval7Tail152 : Box := ⟨437489926106552618068997945923980739820978670817,130697450009549044200872188852783095916709355482⟩
def resval7Tail156 : Box := ⟨444392985827680666853309444858671657772624439504,123794389136714078655442398811154491411763404634⟩
def resval7Tail160 : Box := ⟨451404968621073131213434708065545928529372774893,116782406342960356011474315634708831236216664486⟩
def resval7Tail164 : Box := ⟨458527592006070528366520034396101073553065423900,109659782957962336636609607740682147849990092318⟩
def resval7Tail168 : Box := ⟨465762601756773567811047139956967152928403555878,102424773207259293140497870016230768278488717525⟩
def resval7Tail172 : Box := ⟨473111771193840861762689499014021997646213101931,95075603770191999108076214152033643869375814631⟩
def resval7Tail176 : Box := ⟨480576901618782679866003579902799515089714273690,87610473345250181000513452488168965579164415067⟩
def resval7Tail180 : Box := ⟨488159822755464281248445306600815316938750294371,80027552208568579617566992754586397202715900000⟩
def resval7Tail184 : Box := ⟨495862393198576229917318187974945610272561422788,72324981765456630948606686863195422815235135878⟩
def resval7Tail188 : Box := ⟨503686500869181031873817927127560719399344283997,64500874094851828992216592857422558174717866824⟩
def resval7Tail192 : Box := ⟨511634063477447746184048756206036602678602570938,56553311486585114683129306517817801596356840422⟩
def resval7Tail196 : Box := ⟨519707028992687987480859642114032387390893475473,48480345971344873404039258988035277211987509069⟩
def resval7Tail200 : Box := ⟨527907376120808527650353765800274182241979879886,40279998843224333905819231293661486415859641425⟩
def resval7Tail204 : Box := ⟨536237114789297602448344367901695014912530005191,31950260174735337253531985070574880972678918347⟩
def resval7Tail208 : Box := ⟨544698286639901131070026111244641301630424518866,23489088324167284079390243481750187200874964881⟩
def resval7Tail212 : Box := ⟨553292965632498946976492458631364578708333113659,14894409430067205065662833828306747243648242720⟩
def resval7Tail216 : Box := ⟨562028185148134083623937223185662769477813535640,6163925181050981776244409858708228870516833578⟩
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
def polyval7Tail5 : Box := ⟨21083845910965268783161214893122763943949874229191243470054,6430885461643455830219373869871918230660188241560281967786⟩
def polyval7Tail9 : Box := ⟨21416521368482209282432673685210823240653259460445994887016,6098207945397673388631790879205791693794555560043564479637⟩
def polyval7Tail13 : Box := ⟨21754448122592021792434296520215516745252955813939391595873,5760281191090921841316000134076728422670889424205638792984⟩
def polyval7Tail17 : Box := ⟨22097706951574254977934665764144711225415079225068037862646,5417022362108535999363739792469968035571070856008565875439⟩
def polyval7Tail21 : Box := ⟨22446381988911378367842734183715613022796796452908613638004,5068347324771412085012627704898080542600045867131680144769⟩
def polyval7Tail25 : Box := ⟨22800558695807631958227259766079265707479682189568659734918,4714170617875158488559851813142675460905794256064435197010⟩
def polyval7Tail29 : Box := ⟨23160323881941646154664644688469924319720207253210039830168,4354405431741144291923693131583814939448830449764659012893⟩
def polyval7Tail33 : Box := ⟨23525765726743583279107876435573946164448789437435340199358,3988963586939207167464483272176266620620189278844029235315⟩
def polyval7Tail37 : Box := ⟨23896973801008156360554551647545578931733922677710364704031,3617755512674634086015287167288830167131179572666114176102⟩
def polyval7Tail41 : Box := ⟨24274039088848675661897078190521768325312257585474087209113,3240690224834114784672789011100250637381733699497105762514⟩
def polyval7Tail45 : Box := ⟨24657054009997503461797164785557545028346034617834082962503,2857675303685286984777161353907599485231130879377756784581⟩
def polyval7Tail49 : Box := ⟨25046112442458382989137285523700317054600302934966440679049,2468616871224407457486370864523104573702348517144195745685⟩
def polyval7Tail53 : Box := ⟨25441309745516193658658330934250607562617810589704422825782,2073419568166596789112991490549941601500503972383942803327⟩
def polyval7Tail57 : Box := ⟨25842742783109772435061358352227856456344433954863644465684,1671986530573018086122711935356013277301469129996400368469⟩
def polyval7Tail61 : Box := ⟨26250509947573546673123138520750699518977632606169517656705,1264219366109259808907272074180022790328874885401054877036⟩
def polyval7Tail65 : Box := ⟨26664711183770511051240273887764188978100141710467842292477,850018129928276642526386856916249487834514783164055813895⟩
def polyval7Tail69 : Box := ⟨27085448155722990420077233539657087924333417868907290977182,429281294850714580170104946250212812661757307561304579924⟩
def polyval7Tail73 : Box := ⟨27593750000000000000000000000000000000000000000000000000000,2⟩
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
def pend : Box := ⟨1031305805838576701950101874493145463887434757355113947943887,3939453106973057723473697858872384991117456135963629443⟩
def zend : Box := ⟨1003788767651484264438984375000000000000000000000000000000000,2246133913315496484375000000000000000000000000000000002⟩
def betaquot : Box := ⟨428757102646442113413872792373660640583298848871275168466973,394785107096198669217252412384003825157769045945970235⟩
def crit : Box := ⟨148357899621163128539965108919263779811941214534547469938,9769138610943379339914788658426973751431143266542290929⟩
def subsonic : Box := ⟨440911651938949759939605588466191708801096963536169480328,4882532399469919534314831218869417408803980951587213432⟩
def pendTail4 : Box := ⟨27513098526574147126464473215878135111465139587747746370562,1595136469179084313555079903645904333066156338645381641⟩
def pendTail8 : Box := ⟨27513134301596475698105623310224006522328059969894808792540,1595010545023955389554560701929386854115268691898203438⟩
def pendTail12 : Box := ⟨27513134303152712064850902655469451873469515544973051425127,1595010529318343575211729989140185213452872361469970988⟩
def pendTail16 : Box := ⟨27513134303153483293223529255467761864672866789739378337395,1595010529305316593395200301692557709304368671556397981⟩
def pendTail20 : Box := ⟨27513134303153485162237668613102710314150365285432182430837,1595010529305268488959645395485638440357963621677509685⟩
def pendTail24 : Box := ⟨27513134303153485178298290792634992587459776083429426464309,1595010529305267864231136416594895345958941812273483072⟩
def pendTail28 : Box := ⟨27513134303153485178700868164295461025650329179841622549600,1595010529305267839709107453571554846719366440949302980⟩
def pendTail32 : Box := ⟨27513134303153485178726042388808862368614576699605686748551,1595010529305267837055728782634167805169722494673556525⟩
def pendTail36 : Box := ⟨27513134303153485178729141928964900199191553755594093542070,1595010529305267836304964641384888800217109490934245180⟩
def pendTail40 : Box := ⟨27513134303153485178729075338100791822876796875644783665469,1595010529305267835762938064819669620884876076760749671⟩
def pendTail44 : Box := ⟨27513134303153485178725529058380586793941067154496851266694,1595010529305267834765763306263897352983578610130136599⟩
def pendTail48 : Box := ⟨27513134303153485178695140444366080811022005480666232690814,1595010529305267829990601395930468318768278217776516610⟩
def pendTail52 : Box := ⟨27513134303153485178153375334175445016456171878849735602479,1595010529305267767558772868950027316462055498577024062⟩
def pendTail56 : Box := ⟨27513134303153485152491233171761591903517683147912255480662,1595010529305265435166582719487378969744465865866467876⟩
def pendTail60 : Box := ⟨27513134303153481233891376392487735229365843487627224424664,1595010529305004035486509024729705126901521218915708172⟩
def pendTail64 : Box := ⟨27513134303150954420649881917062003055668942024341652447849,1595010529179119895865612263523447650994587629507961711⟩
def pendTail68 : Box := ⟨27513134291771852041317463830489309887373673190484787916871,1595010109305432438699151483345362781526881757502380298⟩
def pendTail72 : Box := ⟨27511719143128923124932555418159379478908622753702706492070,1560331661262814619042391037778809491092720344027252614⟩
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
end SepticProfile.ExteriorCertificates.C25

end
end

end OAI
