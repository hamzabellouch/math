import OAI.MathematicalPhysics.Transonic.Certificates.BarrierData11

namespace OAI

section
noncomputable section
namespace SepticProfile.ExteriorCertificates.C11
open SepticProfile.ExteriorJet SepticProfile.FixedInterval
def cell0 : Box := ⟨250000000000000000000000000000000000000000000000000000000000,250000000000000000000000000000000000000000000000000000000002⟩
def resval0 : Box := ⟨110056735651494492212136743762074378550088571075130993889,354991529842489966530532963817666632271340123096022928⟩
def polyval0 : Box := ⟨3770442088657208056445687388501133003040223655435996043051,15503353324454648134912648673643009944186767409922133443⟩
theorem cell0_lo : Holds Q cell0 (0/1:ℝ) := by norm_num [Holds,Q,cell0]
theorem cell0_hi : Holds Q cell0 (1/2:ℝ) := by norm_num [Holds,Q,cell0]
def resval0Tail4 : Box := ⟨54470357939127241970930551526801977744900395850343,1710633864686906820507061217301886597196573843136⟩
def resval0Tail8 : Box := ⟨6348812269239562893744023361445275051498434355,356782514227475637172401596113522856389337750⟩
def resval0Tail12 : Box := ⟨5565568433496056440742870699520429700919339,472702924311165233287143758259521687996496⟩
def resval0Tail16 : Box := ⟨21482878683159466398643540553102908426834,25648439140174561723027097349254080069256⟩
def resval0Tail20 : Box := ⟨282134177626016090013362094520856567040,369144040514943248401320809110223370771303⟩
def resval0Tail24 : Box := ⟨10819787850836099652335985944421748778,5905558610853417084616364467203828933753380⟩
def resval0Tail28 : Box := ⟨1102635660338941447623561866372801217,94488898730002824203242005801900276784601700⟩
def resval0Tail32 : Box := ⟨280119476754027054159297430438165275,1511822374222871336020694348202387934590809241⟩
def resval0Tail36 : Box := ⟨-362221818557751243970015645207607515,24189157985418560293902076789041321903606205002⟩
def resval0Tail40 : Box := ⟨-137583360881782774280185852218855067923,387026527636738577448473881258309959900706345741⟩
def resval0Tail44 : Box := ⟨-35288692162007792369468873890189567672092,6192424409102474548209379655949214170693927876702⟩
def resval0Tail48 : Box := ⟨-9034150799801663279607966463805263030161093,99078782076109369906891543492927770394827224262992⟩
def resval0Tail52 : Box := ⟨-2312744796859994727377798901101974561028139821,1585258345019237250525612394007259883250624494094179⟩
def resval0Tail56 : Box := ⟨-592062711893181266002178274349906000230576039252,25363578461498132510807992529296867877691083093793213⟩
def resval0Tail60 : Box := ⟨-151568053147135140679867567162353938978922489853199,405675160329690911017675772896714063846799859209619024⟩
def resval0Tail64 : Box := ⟨-38801412585342103302323031282211905318815672557358720,6454426234572060286604090297494585213961542529406023017⟩
def resval0Tail68 : Box := ⟨-9932950458582064032400031511594766215565364419237690422,93958565981444399842114298814531223194233140729600734729⟩
def resval0Tail72 : Box := ⟨757353810202250808224929131592055897185648702585224195466,2500745925363492218808304668409058746402661071266484236⟩
def resval0Tail76 : Box := ⟨-24946203297905407878485434184143034249190382125787,583462215052866919677319616264613474273099157276⟩
def resval0Tail80 : Box := ⟨-1298918109642203257833106241387196337893177418,62585242783255593567359200494061596170643353⟩
def resval0Tail84 : Box := ⟨-707956761696945103539606297296229983197106,53458849331213048349217219980222787946456⟩
def resval0Tail88 : Box := ⟨-1887946581525715406928479981670132758094,359303854392565686488330271191438731243⟩
def resval0Tail92 : Box := ⟨-18127579776518297783561912684529267665,2463758407874738781233686488434716564777⟩
def resval0Tail96 : Box := ⟨-526110191170993909211330624926383730,39376328504617895521275206079392540851577⟩
def resval0Tail100 : Box := ⟨-41460276245561269828441904270006339,630019516423590256766199653343759480980817⟩
def resval0Tail104 : Box := ⟨-8319594968563206546794394243855902,10080312075009786105646915698135865211621833⟩
def resval0Tail108 : Box := ⟨-5879428258596277570715350143284891,161284993147247033665077664720829397001460383⟩
def resval0Tail112 : Box := ⟨-462304686215516570443709766568559143,2580559889930278619900072327402203860521495790⟩
def resval0Tail116 : Box := ⟨-117112327552631141622903945470424728831,41288958129105697059402606353594959487556377559⟩
def resval0Tail120 : Box := ⟨-29977193580675971109083229240190130234876,660623301962147059319271385380520299693563210092⟩
def resval0Tail124 : Box := ⟨-7674136425932673998522364842707320561056954,10569965636892692107426134933794004216031012150363⟩
def resval0Tail128 : Box := ⟨-1964578506285965527546748050552190885910586096,169117608398000826524425340327493138478320258211318⟩
def resval0Tail132 : Box := ⟨-502932092249084883311571748544726706104744651709,2705410235545327769238110630090990020319672452941960⟩
def resval0Tail136 : Box := ⟨-128750637201150463149334150162545593105145031318684,43165860060287355428482385333442673847442663902985474⟩
def resval0Tail140 : Box := ⟨-32960429590924102004032191512862817981116853246056431,659753484641104090928684334700368730194575163251950597⟩
def resval0Tail144 : Box := ⟨-8623547438294543975371256033231846320049339424249267311,2551744023724060038909730484510647554166113167957337550⟩
def resval0Tail148 : Box := ⟨53954222127290573064236871916479976670970830,1053753534468492091090004789836548363856810⟩
def resval0Tail152 : Box := ⟨926482955032086873743903220262791536271,39834681490455355706406814021631313024⟩
def resval0Tail156 : Box := ⟨283595787995243155685545257279272139,19520517587192911113433384800080525⟩
def resval0Tail160 : Box := ⟨478668235803523045264274374161727,49282795321190777342672707674030⟩
def resval0Tail164 : Box := ⟨3080008601028108095606214127292,26075372263034153715369844963450⟩
def resval0Tail168 : Box := ⟨61831092198447504142854084264,410401237146008101771057459683859⟩
def resval0Tail172 : Box := ⟨3427109081258806318650534532,6566233836101289284700300500961386⟩
def resval0Tail176 : Box := ⟨486376196709781575822777772,105059727389665563425390075093916510⟩
def resval0Tail180 : Box := ⟨175177101403918875074214283,1680955635510627318150226615928155683⟩
def resval0Tail184 : Box := ⟨1682986126265098002608252949,26895290165859775529801997698691830770⟩
def resval0Tail188 : Box := ⟨394926345874196251769324651160,430324642283832729556890872939593708063⟩
def resval0Tail192 : Box := ⟨101029665595159489733898978809582,6885194181827094496572704631864721821067⟩
def resval0Tail196 : Box := ⟨25863250672644096018390603838083955,110163082662446980122478060556062730497416⟩
def resval0Tail200 : Box := ⟨6620988177219822662215281983797285242,1762603115423085479673646331245262792784152⟩
def resval0Tail204 : Box := ⟨1694972881569735630811789513577194967577,28200060809731052451959222663959190471910797⟩
def resval0Tail208 : Box := ⟨433913074089328469049492671127468094661055,450794179466340516479432413340267915278720449⟩
def resval0Tail212 : Box := ⟨111081843630109770982351141640555741724055480,7108567692971553230728410456855255833312556813⟩
def resval0Tail216 : Box := ⟨28442541830829952047531950502773049133728023654,87074684750839330163258475646853225171488040397⟩
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
def polyval0Tail5 : Box := ⟨2001765051518989247854238266371654054065696616077021,51607931254678016292547928340082726617958323429348⟩
def polyval0Tail9 : Box := ⟨187010081815404666677022147204089880125588535556,9506745638123226926876346006204530745624778282⟩
def polyval0Tail13 : Box := ⟨141847794312229785958937553858405553720632339,11175329230555937770291146432908755510987850⟩
def polyval0Tail17 : Box := ⟨479786463272792020502348523861386770159714,423882337866456872711070462011761417685267⟩
def polyval0Tail21 : Box := ⟨5536636498110091928976610995408599241716,5917404950994486403693338357935062009906188⟩
def polyval0Tail25 : Box := ⟨186362342997240600073138704862594337870,94664664913421725485412398161394023175501704⟩
def polyval0Tail29 : Box := ⟨16610237365311422210018710813856984409,1514634003519615813688013120168783251383038663⟩
def polyval0Tail33 : Box := ⟨3719046100364846307249142259036677536,24234143978846086958249453609213729363217778062⟩
def polyval0Tail37 : Box := ⟨7618552294819752352620879079675894482,387746303635805626529213553070635880162923815086⟩
def polyval0Tail41 : Box := ⟨1442979715173644080519621823803792192718,6203940856824081830244426674772848956066870825012⟩
def polyval0Tail45 : Box := ⟨368751566922403743702698863883747841506042,99263053363488558792658013411296341851845699755514⟩
def polyval0Tail49 : Box := ⟨94398393974557870117435870577227226569243343,1588208765317367445884842582069928623144325412262100⟩
def polyval0Tail53 : Box := ⟨24165973840363335947305540361135317918180393402,25411317589478190774042785608076283617617515117650244⟩
def polyval0Tail57 : Box := ⟨6186489041575839426586270005186270685051251754260,406575281598219577265156037114300659806564938310274950⟩
def polyval0Tail61 : Box := ⟨1583741191853931412493502042725506245141583220721071,6503719748213763578735149973770535032444169416916652422⟩
def polyval0Tail65 : Box := ⟨405437760724637244211325315928843549150536801917278609,103679418080751756266274272810093559808621099155193336607⟩
def polyval0Tail69 : Box := ⟨103792258284016002959112262953000704484940283040477886435,1561565538438902974430933234495995365832366075632113985633⟩
def polyval0Tail73 : Box := ⟨26718750000000000000000000000000000000000000000000000000000,2⟩
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
def resval1 : Box := ⟨109840123856416748154481441156664716469750969783782940831,281624496181096004226155785912556972254993484187040979⟩
def polyval1 : Box := ⟨3752596455095865811753181037188167514062024579047669825632,9430614525977996217108555469413138217650375557402871582⟩
theorem cell1_lo : Holds Q cell1 (1/2:ℝ) := by norm_num [Holds,Q,cell1]
theorem cell1_hi : Holds Q cell1 (3/4:ℝ) := by norm_num [Holds,Q,cell1]
def resval1Tail4 : Box := ⟨52903914234349911862084850625461320683067367765993,3063882827698948261300435079865622698579581411271⟩
def resval1Tail8 : Box := ⟨5982723722465708873065532320980387225506953285,6088712349802674804797195486306045803396814190982⟩
def resval1Tail12 : Box := ⟨-316708847759188895859636867547397651327515247,19242510298493353329756010080656533531451715289433⟩
def resval1Tail16 : Box := ⟨-2109421171413868075051456339301687866008701555,60814742064856375014686892231983016313688560826361⟩
def resval1Tail20 : Box := ⟨-13824429777065485898327697539151059920336554623,192197459336325848550132435802617295206261253464410⟩
def resval1Tail24 : Box := ⟨-90599784606279404506870621702513340485262747358,607391976069464735139639134559364606877886335860075⟩
def resval1Tail28 : Box := ⟨-593754748455433625144507741605737798397859167799,1919351176345917547724049738114685318101141211745850⟩
def resval1Tail32 : Box := ⟨-3891231119483287823250804984919129582770127061352,6064082872092364430130213280561040812205952739667614⟩
def resval1Tail36 : Box := ⟨-25501572264647018202725034750446787175524028756224,19152293124306131398604120437718785512897259428161363⟩
def resval1Tail40 : Box := ⟨-167127103993591390283037512303192245598010788219916,60444174653069609657323411019637804711869509596966470⟩
def resval1Tail44 : Box := ⟨-1095284188732401124331245961856232380539153750967677,190466360870627838936744185925188629464165859631613472⟩
def resval1Tail48 : Box := ⟨-7178054459276662227548094344335342197525253006402658,598251342271540881450050686145505297753307458818168328⟩
def resval1Tail52 : Box := ⟨-47042097704315416511694935866488045183256754309686045,1866413773444934941830124464582198365188365284365762889⟩
def resval1Tail56 : Box := ⟨-308295091514990374689324577269694666431302761166029290,5739170377796208749277755242578904683906493855712501537⟩
def resval1Tail60 : Box := ⟨-2020442711749230170474980922088426079519766639308768704,17092534573971710477893267753842682330914826154754069027⟩
def resval1Tail64 : Box := ⟨-13241173350404616745681494882814845895022883714437369509,47165273374831740680855956252654951505431497994778307321⟩
def resval1Tail68 : Box := ⟨-86777256940851382075418564860611436077538144457996312327,104136858342844147846703547469204205434641668486448201982⟩
def resval1Tail72 : Box := ⟨760066331745992147770122829935272847774402841456080504463,1597379751055833968709995934217392352129077417906680674⟩
def resval1Tail76 : Box := ⟨-24394746885244517549820588887229084451194646523229,404002044292314136126973363733595845832232703364⟩
def resval1Tail80 : Box := ⟨-1242004159326852435412413815231071952706030770,60863902370143865649646578295499238502908119721⟩
def resval1Tail84 : Box := ⟨-3336471485972212071679271989170075481746326,192231580295609513165444063469540247660793808259⟩
def resval1Tail88 : Box := ⟨-17532817199099531154650650443417565537103355,607537643964786545089721844661424879492788332083⟩
def resval1Tail92 : Box := ⟨-114891808630854571849233677398350497686259920,1920059488630336028413701691954491888041232068887⟩
def resval1Tail96 : Box := ⟨-752954852060756014718814585799023589025082572,6067946321546220130918680865395423779019047099977⟩
def resval1Tail100 : Box := ⟨-4934564915527301106270887528622016266605239734,19175152037033170449837865409630265451109144904782⟩
def resval1Tail104 : Box := ⟨-32339164630179419581730551707425090963851905098,60586206145232264693208296001538724491738036872230⟩
def resval1Tail108 : Box := ⟨-211937949320303045664996914681544710876706440778,191372600313948636534617474202254712040643436346750⟩
def resval1Tail112 : Box := ⟨-1388956544665520833162875256025357123550638570300,604112794015789391427411242495325938826284743468279⟩
def resval1Tail116 : Box := ⟨-9102665611119943633542772274094383865970572775458,1904581879370070885334734539677461106138954881097256⟩
def resval1Tail120 : Box := ⟨-59655229349035667819208576143702781488866313338545,5988532962196456353011503560386460950560161128420605⟩
def resval1Tail124 : Box := ⟨-390956511061841048598162331508897134686767189217921,18724304933822677713522630081896348185863546635415940⟩
def resval1Tail128 : Box := ⟨-2562172590894949817171808940639070383870015632024825,57851493210221607482695145218584503528814485942047519⟩
def resval1Tail132 : Box := ⟨-16791454291704039651038470363052574982149858272465616,174145563548873435982036398222729515519079283393847844⟩
def resval1Tail136 : Box := ⟨-110044474860702238246600318957118495439933358796385439,493410791412356019751984998697030494449778470404847566⟩
def resval1Tail140 : Box := ⟨-721187597545489157137133682563226519485228870338755431,1186029147322449132736764860773566697124760441858128744⟩
def resval1Tail144 : Box := ⟨-4803612962663440740303286565428471727348839891298843822,1286146713729638989860291147132675455218696359745744923⟩
def resval1Tail148 : Box := ⟨53161454009292240506288811434943870150490748,775878933197242320035252897830266318972718⟩
def resval1Tail152 : Box := ⟨891366808029665402579202407838665260084,2661034502454152606592271588201297392207⟩
def resval1Tail156 : Box := ⟨368935924303637772328050300957220072,8325896211632483764279340225756717518269⟩
def resval1Tail160 : Box := ⟨669256379247134854274029295517766688,26313594477642922618787627917350142822128⟩
def resval1Tail164 : Box := ⟨4383158259820272943296634613970695909,83161683544632078712554607651460015421368⟩
def resval1Tail168 : Box := ⟨28725447943088457223005914481400940553,262817114987017152058145508451458500234143⟩
def resval1Tail172 : Box := ⟨188255095289645183812580370567978187472,830534401094043942961180110613079753542680⟩
def resval1Tail176 : Box := ⟨1233748592471626351818139387515636222468,2624260078376277314046132799071127167219945⟩
def resval1Tail180 : Box := ⟨8085494775619575782386030654549055161193,8289771538607091920963869439515747650101849⟩
def resval1Tail184 : Box := ⟨52989098561499683903374536151193465715661,26172336834104847396825994913567191785431517⟩
def resval1Tail188 : Box := ⟨347269356332643831818063120417116730630685,82537711369131366481597137134338730217265458⟩
def resval1Tail192 : Box := ⟨2275864453661614239151419643621305549631985,259681605493483899837003382598718114389257187⟩
def resval1Tail196 : Box := ⟨14915105283516760595401901107000926486859200,812999861463017215162806792661711798807157732⟩
def resval1Tail200 : Box := ⟨97747633986055770452789117488215033483756549,2518872507830150635564541381318087699942316378⟩
def resval1Tail204 : Box := ⟨640598894091056591116410111559918280067359257,7629212912142911552506333924682394731898050111⟩
def resval1Tail208 : Box := ⟨4198228912334083342962705095575297571012931721,21938460253062063978108991247639871836769213104⟩
def resval1Tail212 : Box := ⟨27513513051408899339630613071267492776813448382,55091331758766757506861311775383117255043603194⟩
def resval1Tail216 : Box := ⟨180315026330647469218690877028813265589504562186,80759027644804697644220614784420042186052981403⟩
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
def polyval1Tail5 : Box := ⟨1948279263077563162182859912803330253480468808978768,117150657567822516709113568704513572357074579864761⟩
def polyval1Tail9 : Box := ⟨180299373591836757127106833538895284672086550782,269116465483951124894461329075629973567896698128095⟩
def polyval1Tail13 : Box := ⟨15219537016735937026244757170629762570958311696,850517404058502805828851897136180901777312834212626⟩
def polyval1Tail17 : Box := ⟨98878343521012007101548793812492909390063768960,2688003812222979539354447639278381130016408962031738⟩
def polyval1Tail21 : Box := ⟨648006262925706392674998919839002765720424633804,8495083952673249486892985407223817261284741040129775⟩
def polyval1Tail25 : Box := ⟨4246773812800956203458274636914256406781627049868,26846461639599711682604406933189025753888783801852350⟩
def polyval1Tail29 : Box := ⟨27831656858537448689510087078169424453073781128169,84833666538617545500931793484802418430696555138465457⟩
def polyval1Tail33 : Box := ⟨182397546388023411326745800615100341365747742026506,268021843664005480408507961341284692107463765489683050⟩
def polyval1Tail37 : Box := ⟨1195360560008532286522945567743023351538248113643390,846462488203704261355702260487544012739557857986996333⟩
def polyval1Tail41 : Box := ⟨7833914966071908994623269804468713962620175180029843,2671183483595785805481901603140602253433791191467345457⟩
def polyval1Tail45 : Box := ⟨51340345121648855985841608265511973955595277913249482,8415677605888666881377182744303982607932914158497270777⟩
def polyval1Tail49 : Box := ⟨336464085789237948120638714242815070458729947781666700,26423493882835957481082202634289843887321444489447688928⟩
def polyval1Tail53 : Box := ⟨2205051032628350399552190924293864513619581186141178323,82369630942285847999062972031360517110552280846287530847⟩
def polyval1Tail57 : Box := ⟨14451022447433202840409424030949637737754341526137571926,252846737868345040302919707965653220137814205263323623263⟩
def polyval1Tail61 : Box := ⟨94706220711508573032776999099110947818640283011191429333,750086700780341824043617937781869388826919730827807262681⟩
def polyval1Tail65 : Box := ⟨620666688065381141882511755160170601468483632034001161733,2049296125546726389792491263843194272502173520154829534664⟩
def polyval1Tail69 : Box := ⟨4067601298295706408865268973993232054456485638837332803143,4370799765637208639939073939096409254204797291223402303525⟩
def polyval1Tail73 : Box := ⟨26718750000000000000000000000000000000000000000000000000000,2⟩
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
def resval2 : Box := ⟨109733464707785233288693752164228411075306990804417815271,265007101660839554014780417951429221779655544104771806⟩
def polyval2 : Box := ⟨3743777928100147965349624793290541665604598489847147028647,8174563058041621604300178423393482774273421656328898917⟩
theorem cell2_lo : Holds Q cell2 (3/4:ℝ) := by norm_num [Holds,Q,cell2]
theorem cell2_hi : Holds Q cell2 (7/8:ℝ) := by norm_num [Holds,Q,cell2]
def resval2Tail4 : Box := ⟨-141004638804875499016917994347073230184450225615090,33880814305120021759226419906640349342893034054738658⟩
def resval2Tail8 : Box := ⟨-443228449159010633789610859097017109582178541482672,57684086749493086294313992227116520996317205932060165⟩
def resval2Tail12 : Box := ⟨-1017044404828319320026826222564799913665506544907496,98145598871740285366124422519503138862858112992913877⟩
def resval2Tail16 : Box := ⟨-2333707588713087098317734115861092735929730040617100,166833383989971601376640037569166888445999282466023374⟩
def resval2Tail20 : Box := ⟨-5354919664406402901743778347865877310247133625904204,283236670134162490024940493084265780456801008120265411⟩
def resval2Tail24 : Box := ⟨-12287385425109525237355118908998878966043015620427279,480037125951374879417456037923948304896673801254870518⟩
def resval2Tail28 : Box := ⟨-28194604223240726431640840283167919140266143794961338,811689276908820977557769387106341067611775910805359728⟩
def resval2Tail32 : Box := ⟨-64695269156342715475550164495816748625047468977399791,1368109552633296910520651476510319643573574657942499350⟩
def resval2Tail36 : Box := ⟨-148449604685762970882678269885610507648039123576019049,2295852165431006670292781727806239208339742767349069094⟩
def resval2Tail40 : Box := ⟨-340632095959040722060368614564251073587524588524726092,3829238812161862422540612008043169216901530369812290797⟩
def resval2Tail44 : Box := ⟨-781613565378372352330081361385634999191708630755328955,6332002111282693569866961081760608852083116201711398991⟩
def resval2Tail48 : Box := ⟨-1793488555044886746472240522128679354145447747343088993,10342025735502271106365472496763507682164075540929104090⟩
def resval2Tail52 : Box := ⟨-4115334405077612630594659786479003050014567142724656509,16587317212615497836513658965282482092232661672604546728⟩
def resval2Tail56 : Box := ⟨-9443036153186728096703970678033851243215451126967886398,25874773520312211909801491093067733576996239856428377628⟩
def resval2Tail60 : Box := ⟨-21667967414837180502099228655733254533960797846951673691,38582656667896925081701523396536207453732966541542296274⟩
def resval2Tail64 : Box := ⟨-49719264464718548328316378408578507585196461994203648164,53065640255197231703803661935654386175914595379000652094⟩
def resval2Tail68 : Box := ⟨-114085625339764614725035886820076749562775243185785512980,61260809292432302224197356299666497060161888460246801040⟩
def resval2Tail72 : Box := ⟨761421000233591498167942723403139505957993887522005985637,1146110444353301233860441518807704998956242506440667745⟩
def resval2Tail76 : Box := ⟨-26216855973796497146690010050579337454902479285565,394883331083635431793861421038705844007381018645015⟩
def resval2Tail80 : Box := ⟨-4789040863133738483686744825726906403797978448799,672253432707591065496316924532717615256312142878713⟩
def resval2Tail84 : Box := ⟨-10986134061721867903953154124893522406585678629592,1144016346204869351809930387793820519418257547913665⟩
def resval2Tail88 : Box := ⟨-25208754593213459275636783361128114134151060141201,1945174484272602821732821835009297800926546717543392⟩
def resval2Tail92 : Box := ⟨-57843945972242981014787479322678478401648500066064,3303542870515690005584204723589009711650663662167087⟩
def resval2Tail96 : Box := ⟨-132728575443294334811189318195183196155411452770873,5601648934067122201973585964072546066908566996422699⟩
def resval2Tail100 : Box := ⟨-304558661120118714885270714656874520824103139950715,9478036207249170907767093693934423101340540066181312⟩
def resval2Tail104 : Box := ⟨-698839550966986386148996846668651932444527174056426,15989835409816274824631954220255603920553083317747067⟩
def resval2Tail108 : Box := ⟨-1603555506185792496168638891342069978040429296868129,26866587200756414041798409114495056390874307754985045⟩
def resval2Tail112 : Box := ⟨-3679514500661464827339152394468004047358746090901493,44889292049790545990092900935255370740054750548445088⟩
def resval2Tail116 : Box := ⟨-8443004877817645004288901055771385644046187157726124,74413234868392865745470302144892938845120545064895000⟩
def resval2Tail120 : Box := ⟨-19373298122357661993351705325158808001834991236783399,121975788924905250171704716063338093050278272995688824⟩
def resval2Tail124 : Box := ⟨-44453921982662783708305256001207064522569085779532494,196681380202088940654050520941943069341814577605737472⟩
def resval2Tail128 : Box := ⟨-102003859495668567591501573086287543255636837159014759,309362320324715932582607638597761540595716101223770339⟩
def resval2Tail132 : Box := ⟨-234057803855204359595950330531652888015670437518158785,467714737812567435694321650569289409491763589444043554⟩
def resval2Tail136 : Box := ⟨-537068458169937482619095360686971936120399107828954666,660124515880698927704115254043220591708498534609491006⟩
def resval2Tail140 : Box := ⟨-1232356056912473345582329623909910271992594443404233940,810002390645716586451554883667225945651044663539850080⟩
def resval2Tail144 : Box := ⟨-2887550865119315665807772044902327604992182380731132259,649968225334515038803746139278489294160311107043992991⟩
def resval2Tail148 : Box := ⟨53002911296466778811162343837796947220343623,40912783899676777545667941440863229112981918⟩
def resval2Tail152 : Box := ⟨518261902243210157196285468841820653458339,68636589079924260096964916874929935684619800⟩
def resval2Tail156 : Box := ⟨1187195227453905576540892878788034476327587,116786421186854724397950762952770491433483291⟩
def resval2Tail160 : Box := ⟨2724134639722160032869364020685610928111720,198533646183511458926843337636569483219123956⟩
def resval2Tail164 : Box := ⟨6250792609544080870158134392995522266978622,337086096290998231941710191102110501336507359⟩
def resval2Tail168 : Box := ⟨14343053270505598302953837341429980470014665,571374521463609499635091791031116894286988498⟩
def resval2Tail172 : Box := ⟨32911534579876462600056815349822424493328411,966296789497980776155877692465388878599684128⟩
def resval2Tail176 : Box := ⟨75518725892888333286528392686423238393112020,1629086561663506185235504216595570574971889661⟩
def resval2Tail180 : Box := ⟨173285081758913546087104528474969357834068528,2734696283435168897261269405565467782429370511⟩
def resval2Tail184 : Box := ⟨397619520260220515779485838856738018255192478,4563268306409900970096056709720150960659441778⟩
def resval2Tail188 : Box := ⟨912376768312517479116512743402809747881113659,7550678849363791394704193350221437243114337681⟩
def resval2Tail192 : Box := ⟨2093537477263721351623363457468297533941858930,12344061777214479876162735684716214319116425455⟩
def resval2Tail196 : Box := ⟨4803825920309346407186432754909374402154787283,19826081012777997301474181695610772913125766779⟩
def resval2Tail200 : Box := ⟨11022847082153752852975116939096111500091870502,30994686777873635921427070762356844981055407321⟩
def resval2Tail204 : Box := ⟨25292997667309595854669661820401645558392999416,46387060096402297102187549565395521216140732216⟩
def resval2Tail208 : Box := ⟨58037249925606426329860590270269646806481542164,64245764068644092658603386516767055555225263295⟩
def resval2Tail212 : Box := ⟨133172130258019677964670219498187671080105351517,75437293068015228202353258983372818312959522019⟩
def resval2Tail216 : Box := ⟨305578368923062721236288446021486078211046675352,50301786378823623949391694017679119051388242797⟩
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
def polyval2Tail5 : Box := ⟨21603178760983520216981342819497340049406716741786476,3018934056645117597290355273464433265155699915374114373⟩
def polyval2Tail9 : Box := ⟨45158726400604454633135759992496192736628067142202574,5138576271819705320107429580564815043169070759103566882⟩
def polyval2Tail13 : Box := ⟨103620703207942361647765252406374832797942363004980436,8739602052399285234588397789070120751541257032954229445⟩
def polyval2Tail17 : Box := ⟨237767809148422989019576052826435559982798117763556729,14848379798698128182743938029072767753087004836987214625⟩
def polyval2Tail21 : Box := ⟨545581427132239432269582946870871414611958874067267671,25190720364511969698731123248100692632182832811505016173⟩
def polyval2Tail25 : Box := ⟨1251889794073671947459469954660656696562715977712264546,42653104849231060005937029583748470206167722006564473267⟩
def polyval2Tail29 : Box := ⟨2872583226932255709289003562411104005751240307976362269,72027399304919548317560333708740971895092762024068258387⟩
def polyval2Tail33 : Box := ⟨6591422371773828276500222095438109191235110503957861349,121184641122797179321952740159750868993358965462896101077⟩
def polyval2Tail37 : Box := ⟨15124661480920472315071520008689519414629489709528389008,202855661748468468590354005482016189485072258724226425826⟩
def polyval2Tail41 : Box := ⟨34705010847435456517561602050083064947612695648199891017,337159797127398821677181176116698895838725059771562209513⟩
def polyval2Tail45 : Box := ⟨79634032103131195629254291160558104375149916798276049211,554750913113412412653717337305841908982890747538294463988⟩
def polyval2Tail49 : Box := ⟨182728053216302161601208898120856485927065054444160949161,899504656324290349675424981849042807836896456228136018299⟩
def polyval2Tail53 : Box := ⟨419287339224242095207598592448694169589882910054335558606,1426953884548463830426621417372717682351818140756800664637⟩
def polyval2Tail57 : Box := ⟨962095692146631109767125626438944651040485456249844756341,2187510327250704813920401491102972666115005188966586842721⟩
def polyval2Tail61 : Box := ⟨2207622396993167724608040966143204691087990156898167462717,3165466422436863694049080944174212125120184507257964429931⟩
def polyval2Tail65 : Box := ⟨5065604895122201132514723115962019169687866074584352299140,4100647418248433087754898253000315379338432500206062919749⟩
def polyval2Tail69 : Box := ⟨11623524542848366713576882221059883532134499641337071188662,4013697292933857153292018829776654983367072934008592526740⟩
def polyval2Tail73 : Box := ⟨26718750000000000000000000000000000000000000000000000000000,2⟩
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
def resval3 : Box := ⟨109550712336100304214475577528041741207393495942915918683,1794736551667164632838367599499361198053102164476915208⟩
def polyval3 : Box := ⟨3761662533472287061872268228934291053224363002891659119051,236992550054293633915544860281209156994402403775459497152⟩
theorem cell3_lo : Holds Q cell3 (7/8:ℝ) := by norm_num [Holds,Q,cell3]
theorem cell3_hi : Holds Q cell3 (15/16:ℝ) := by norm_num [Holds,Q,cell3]
def resval3Tail4 : Box := ⟨-192633545480088706414620850386955385759062321032433774,2006434551826003781521727260241217725338107961990340108⟩
def resval3Tail8 : Box := ⟨-285664709197418171981563570811209359375802584649083920,2561179257099914065689138570415137946866061034177324591⟩
def resval3Tail12 : Box := ⟨-423510831206212893596668863291088981968359959276977912,3261837643803174897245393849402779806061951801352575847⟩
def resval3Tail16 : Box := ⟨-627873919061894665524467913797270817327445321831163570,4142950726044768142463739395156115101587067908878585809⟩
def resval3Tail20 : Box := ⟨-930851419102540781322479006235344227442165259308757327,5245163671104103669889467301078138871450545216320872500⟩
def resval3Tail24 : Box := ⟨-1380029235391401770679322613453786558396428470343519386,6615058664890724931149769691351240142718388197241172345⟩
def resval3Tail28 : Box := ⟨-2045955618106204622035001685502996786358154778548986563,8303991653654574755444917562581210044702891536426530421⟩
def resval3Tail32 : Box := ⟨-3033221531769313212803658653509539705331210872817173945,10365181320618132462617861095267736438982141514846133788⟩
def resval3Tail36 : Box := ⟨-4496887801166070305229249704769594350891508499105080393,12847857469630248505411765278640621623674620716192951579⟩
def resval3Tail40 : Box := ⟨-6666839096477232297178808337838634947170501150125099062,15786597467807361274590754429883622318682646343321101372⟩
def resval3Tail44 : Box := ⟨-9883889815261134305902138875715010833833012631802376366,19182943146258966914737333403185015498101617143066284589⟩
def resval3Tail48 : Box := ⟨-14653312681843933546823483406369036791985333207073580641,22974815021191747506672056308443443521088635293585586942⟩
def resval3Tail52 : Box := ⟨-21724197311503043882209682063613283760791528023111276657,26986854088914662523265612660767800723590739650568970206⟩
def resval3Tail56 : Box := ⟨-32207102863086396034582080262957661578221977001982017949,30851217424869639455175836354070676030522737614224793318⟩
def resval3Tail60 : Box := ⟨-47748483405834237266414756624814455641937512308168886910,33882925550044203405374264731336629049688402394447129328⟩
def resval3Tail64 : Box := ⟨-70789281393120649032250411470774972405036935232230996300,34885701661240418066301830250141482887452208678569801416⟩
def resval3Tail68 : Box := ⟨-104948235531009857370841247793168475898574490061312854137,31852004068869553328772139866111790077097606460031160261⟩
def resval3Tail72 : Box := ⟨762096381385318371370265483458238140323030356685514202941,939658942920396223186603468957578372805725499642301736⟩
def resval3Tail76 : Box := ⟨-2345122981046901229612530849075259296369108858157076,25112145131611927440988766014596760386378617087853592⟩
def resval3Tail80 : Box := ⟨-3441169692752457317689077945162953359884203252341006,32072057765537409163123932764744284960229960209130989⟩
def resval3Tail84 : Box := ⟨-5101687577708642849641561518505801467531413693144449,40871542940600457143197831242890220332240446294282435⟩
def resval3Tail88 : Box := ⟨-7563482057093708940296359645980403878517014576095330,51950624317342859835172302170776236454392638211104500⟩
def resval3Tail92 : Box := ⟨-11213203467217994364302430326989240053693794241582274,65830084934855423743616565803730961416444372489264852⟩
def resval3Tail96 : Box := ⟨-16624080158864101229221692349414334901250197398115971,83111405247916788333457110008004661061959477342043940⟩
def resval3Tail100 : Box := ⟨-24645949031093841628605263302781839177900131736638886,104465453865079834443914321293687285240869924451984578⟩
def resval3Tail104 : Box := ⟨-36538731637394834657432411066914294362542820994407770,130600920712306657355425805398338533105982390204823918⟩
def resval3Tail108 : Box := ⟨-54170318537346438178783043115662040366224780470633609,162198358132086391060572115883849617802458928379252957⟩
def resval3Tail112 : Box := ⟨-80309941777902387819075069744507053441814105267291179,199787590947192918787422454377043769652248370698788837⟩
def resval3Tail116 : Box := ⟨-119063112835924864675440103725152762257912493237268224,243533863058827649178948033726449641024187320291104343⟩
def resval3Tail120 : Box := ⟨-176516437745454424668923990332820273459071307731033418,292879224718515960511267195128882313592616181227188703⟩
def resval3Tail124 : Box := ⟨-261693584622487553750722801099781945115878036363943620,345957064962475670042403921647891193637186417110020198⟩
def resval3Tail128 : Box := ⟨-387972548660446908882902302071330061085269178688919208,398654472992889433261376163126889098165487687931371071⟩
def resval3Tail132 : Box := ⟨-575186811442955360983596340058826566596707658700312935,443131973565905012646424323211213127406138668856020012⟩
def resval3Tail136 : Box := ⟨-852740404454830858354233539350143512080957688820188525,465512235442978326515099316882735399158146297220815348⟩
def resval3Tail140 : Box := ⟨-1264226222083183497923597114164056436947125084414581928,442302354408770860437629944932546737189576586887430897⟩
def resval3Tail144 : Box := ⟨-1927994860346520474769197757236132429906722913453064962,331033154189904505344679423759192345147879014747537066⟩
def resval3Tail148 : Box := ⟨523891115665706366737386413217183643536706373,4605523327751742330859603253337799347038243118⟩
def resval3Tail152 : Box := ⟨698728457558268081243362755434298767847029317,5872853784706533351043401303694496483456854332⟩
def resval3Tail156 : Box := ⟨1035895184906332357211933010024949655029511472,7471268396399296290668032961657435748945892316⟩
def resval3Tail160 : Box := ⟨1535761358131404916950600174250115103844580285,9477087480335314567810209801647032439550434020⟩
def resval3Tail164 : Box := ⟨2276835517797823975198098694916348815462424491,11979718782996784891240749805378760084539276492⟩
def resval3Tail168 : Box := ⟨3375511401989263704482381994104594257632014670,15080143761603335095181080751068973247145214171⟩
def resval3Tail172 : Box := ⟨5004347980296790283449899328427384561101285666,18887203956517126786022719856838867063932335103⟩
def resval3Tail176 : Box := ⟨7419171712215777273504086866029626752315136467,23509356638026926309629905719410163698288378093⟩
def resval3Tail180 : Box := ⟨10999256868639721511048427453913953897522482767,29038906765167800898900877907681963072670446164⟩
def resval3Tail184 : Box := ⟨16306894671694509852678663967345869133079955968,35524040477050374861466275518059932921410722646⟩
def resval3Tail188 : Box := ⟨24175707232721849396927989872507177408241930210,42921421970401997805566923157670006029320550665⟩
def resval3Tail192 : Box := ⟨35841576950686567225214453091623617951586314423,51018224717578607101348135784743920736855495618⟩
def resval3Tail196 : Box := ⟨53136755253772005639396023943213081391992003373,59306582269811727002598171699103589504234596915⟩
def resval3Tail200 : Box := ⟨78777637568348697051516129167575984025246565273,66784566242922088432858870263720936836890929044⟩
def resval3Tail204 : Box := ⟨116791402696903814454266418036932763343159010394,71644441035944454674352231784506728891804896942⟩
def resval3Tail208 : Box := ⟨173148524948809133322536424208402156957481552807,70788886505542983372905294722205811774013711232⟩
def resval3Tail212 : Box := ⟨256700501954868748659187801089386977798267777859,59085813082520638167020525566393816666186061717⟩
def resval3Tail216 : Box := ⟨380571816418201593751013785907099739092379030164,28227236288419759365031846995141594539765379579⟩
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
def polyval3Tail5 : Box := ⟨33037967225110509294721724628563665053002086886040971887,298262311157427280889086205532162001277227721286122662589⟩
def polyval3Tail9 : Box := ⟨48977445303315739092958370322520890191873055154348963196,379900960533509504522273291511652023032756299191637277844⟩
def polyval3Tail13 : Box := ⟨72611272614805970161626562750596486416046964945186775314,482588237381126299486524089322823651815803547984747939189⟩
def polyval3Tail17 : Box := ⟨107649488383275547043269052243936418520625611235066170582,611077525682602299844108192532367176786456226220324031760⟩
def polyval3Tail21 : Box := ⟨159595224431281366073285139400577238729338980514865832288,770824402113337761646970660625562717185872642533580935154⟩
def polyval3Tail25 : Box := ⟨236607122279907540413173646787871123450359250804967261099,967856692934475844350586441771746118002745162820836685411⟩
def polyval3Tail29 : Box := ⟨350780736159710679281830489036798342986764984393494368794,1208443769398606940360179547813030472187396729403281929305⟩
def polyval3Tail33 : Box := ⟨520048271054085696106037380262642301244342950476891836861,1498427525415443262315685469402149311886527837039634224923⟩
def polyval3Tail37 : Box := ⟨770995030078298389011294741623123796917566871183526810784,1841999138759766792598448613570950719442686711134980806258⟩
def polyval3Tail41 : Box := ⟨1143034924816843392591712236816068007200838091938335496503,2239586030224567762804727250900890419633858302777776181744⟩
def polyval3Tail45 : Box := ⟨1694600857827011297110916330093598465243355829010255738201,2684331426806942707434977014974635655901030735850490273192⟩
def polyval3Tail49 : Box := ⟨2512322244054083451837430907503555603563858029112675674853,3156373187171018960864170566750733695935827028101521076985⟩
def polyval3Tail53 : Box := ⟨3724631100483760499772987560206183982776704428467763341787,3613712085309193806305315085907880629409497631261881081315⟩
def polyval3Tail57 : Box := ⟨5521933688054478597690788547659634200369834585977417522558,3977832416125808909688161779986533074278753096803554344496⟩
def polyval3Tail61 : Box := ⟨8186515881078975092962024279946936559261771584312308031278,4111294912077759199657944559967547236639414449143576471381⟩
def polyval3Tail65 : Box := ⟨12136879226960300565573267041538773731116516956836303165409,3783107501744254329316886493320174417372982845666520036528⟩
def polyval3Tail69 : Box := ⟨17993471220752713352679543926091199457055397982486789414997,2615560942520435960470860737235097898066104769523983866925⟩
def polyval3Tail73 : Box := ⟨26718750000000000000000000000000000000000000000000000000000,2⟩
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
def resval4 : Box := ⟨106176121266128620823865862104986033648128624631940872051,9146328643659721926845132477058491199012375414876525260⟩
def polyval4 : Box := ⟨4578481250157521933714167803562306074256770915554146194627,1874278846982331282151942042592455447284901661422193424565⟩
theorem cell4_lo : Holds Q cell4 (15/16:ℝ) := by norm_num [Holds,Q,cell4]
theorem cell4_hi : Holds Q cell4 (31/32:ℝ) := by norm_num [Holds,Q,cell4]
def resval4Tail4 : Box := ⟨-4214572893635566654501476442713514305776183808736384748,9872676402577069957184604364600556088613889706190835181⟩
def resval4Tail8 : Box := ⟨-5106924577518679217207868041639047562681282755326099688,10887952608889485486780545480473618606324153260603827963⟩
def resval4Tail12 : Box := ⟨-6188138144130850888391495356168502473674171945703325423,11972623058422686110661276983121174253137998886177212778⟩
def resval4Tail16 : Box := ⟨-7498261050520785901379781514576820784153212928068719251,13121668911801347569135392793186192000188856126849080810⟩
def resval4Tail20 : Box := ⟨-9085756890388560427224854004031309363829195432488891408,14326340593233264307000179470047453309863674065296301075⟩
def resval4Tail24 : Box := ⟨-11009349729896306470763756784221143741249165027787720260,15573005767148415528724501629187133393247022443105184334⟩
def resval4Tail28 : Box := ⟨-13340196412627589135907671428208379464450386450924697174,16841705241659824385175254868928856014122831986848594621⟩
def resval4Tail32 : Box := ⟨-16164518767554689563678091921838483429699299675471762010,18104347570131274178154032985819579356775317048808038369⟩
def resval4Tail36 : Box := ⟨-19586793095437021024900798947185279188224635725204852607,19322458333502220331395195202008947313894671270408045898⟩
def resval4Tail40 : Box := ⟨-23733614917971072766975821800430168219408975382144199924,20444381279572235879331304384509542775709291704230146615⟩
def resval4Tail44 : Box := ⟨-28758381953080565460648815972345999518845929262464662485,21401805569276990465694611039736985999160389102498263968⟩
def resval4Tail48 : Box := ⟨-34846968547257946416996135322688796814973623626177402343,22105465443353633133749338485612997564092831649108006893⟩
def resval4Tail52 : Box := ⟨-42224601471485392124067595393305283253069222225993014658,22439824593692906494543848627200991451525749056095663465⟩
def resval4Tail56 : Box := ⟨-51164191427666123147867059176508654315376760173215396800,22256516088156896121134870805164150021898318503097717294⟩
def resval4Tail60 : Box := ⟨-61996428461605792343121989643602568065842876939339395380,21366258260308644101079443659721411675736312891875740012⟩
def resval4Tail64 : Box := ⟨-75122014724668874749907675573084196498714495700568820803,19528905599264619517197817059519169279733875969251481181⟩
def resval4Tail68 : Box := ⟨-91026421638298614524938485475831200674121749944562677350,16441216320376628753227417409417917284614634009992925036⟩
def resval4Tail72 : Box := ⟨762392278981140328461298283881274591600057986230332357541,921555919675514162258206105679500238977580299883610695⟩
def resval4Tail76 : Box := ⟨-53393770516289525262165799998593017064599128285275204,127992428861580702804930784381416205510065722815162556⟩
def resval4Tail80 : Box := ⟨-64669040201734418460090686741367728798001170727966936,141251498245939646259104022203153705794596539615697430⟩
def resval4Tail84 : Box := ⟨-78360457549885154790133798596315291344001588832804778,155444007375311344365065976568096734713134725736204280⟩
def resval4Tail88 : Box := ⟨-94950557511297226955338615190218095047383059534633110,170513628590300215267772256977120580968372858628524562⟩
def resval4Tail92 : Box := ⟨-115053033809028242036656100946623140850053317438281616,186357951329010763912240400877850851552138397892650686⟩
def resval4Tail96 : Box := ⟨-139411509901736508921502724078990160338589582631391679,202813870086487227126867657235003948687625288795333236⟩
def resval4Tail100 : Box := ⟨-168927045638294718167252096921262541580905747409592595,219639451546427331273905402757709355421936739269611524⟩
def resval4Tail104 : Box := ⟨-204691468933922349528793616537579063021376104550918178,236491247378935839602422694455906710623786937158188019⟩
def resval4Tail108 : Box := ⟨-248027764269552494876441905321761225190271849258897533,252895991595740864475171256323624844148280599423824276⟩
def resval4Tail112 : Box := ⟨-300539012050431926083623846570412995825819725373326638,268215383605114455183883036558108808739411101872894447⟩
def resval4Tail116 : Box := ⟨-364167689170827493776944658520335408527700616207389408,281602368227878331306126790251722780623494344053983083⟩
def resval4Tail120 : Box := ⟨-441267524409664516765587196684920086236912055034092021,291946970666143569109893942709232538758905980054148649⟩
def resval4Tail124 : Box := ⟨-534690566705642084060466095746650789353423263745406894,297809314064378890238427087996279585751528804487926122⟩
def resval4Tail128 : Box := ⟨-647892687109650214815134956358850605705052680140942180,297336923238469164955290005636401851229429244452593385⟩
def resval4Tail132 : Box := ⟨-785061417104180992172979678053657695306157856969506806,288162780180340575034162706206233978305605420061982944⟩
def resval4Tail136 : Box := ⟨-951270852248382888048349736528529038639071766797739119,267279820557586103668713859417214254745427403484598416⟩
def resval4Tail140 : Box := ⟨-1152669437929440538806062401882122436789794353212874008,230886609236779653849544411285309288111212062650396653⟩
def resval4Tail144 : Box := ⟨-1447835451141023206174664976537633200349241153065405651,171354077692373919229566931010168092925823536456134712⟩
def resval4Tail148 : Box := ⟨16145560032721315425620875864813510212577181798,34317464844839929771806479111528856699381446093⟩
def resval4Tail152 : Box := ⟨19500212916480952616708156126708767634660013687,37735932525299329108290684290190310378652538348⟩
def resval4Tail156 : Box := ⟨23628703353659635072287049809966430996495608417,41357850850359722650851608087891056127026843713⟩
def resval4Tail160 : Box := ⟨28631259015614718719263678430582874517875269121,45155196366300731519200759359697151143382877489⟩
def resval4Tail164 : Box := ⟨34692931751629146033177440815678477660968557436,49085029159435066109339081508952673019232606431⟩
def resval4Tail168 : Box := ⟨42037952744823553376672423741196495008001873642,53084474509434947054135500013739385699202427927⟩
def resval4Tail172 : Box := ⟨50938026328461928467195301744624032764767891370,57065034003204986844660071051971084580186111964⟩
def resval4Tail176 : Box := ⟨61722380773135609576375352535188036758294058662,60905493406593890226444673805561959448644505862⟩
def resval4Tail180 : Box := ⟨74789946978673460077312251494379058414381450308,64443103266945253503566027503312813641605628147⟩
def resval4Tail184 : Box := ⟨90624115580249118358630514891390892329265647490,67462635987230005788751665155828273946969859934⟩
def resval4Tail188 : Box := ⟨109810618358162916395843160229943077888161910612,69682835078868824173112633673677319817330023202⟩
def resval4Tail192 : Box := ⟨133059195413876601036434516780942411800903041347,70739665068114598296568175851905132989175720713⟩
def resval4Tail196 : Box := ⟨161229849616561184910941732134518874972698049384,70165639959490040603101227623938358067756216274⟩
def resval4Tail200 : Box := ⟨195364659515053233714057882812767584841766865486,67364349221832543733034478310516433481169237113⟩
def resval4Tail204 : Box := ⟨236726327526836672166793054649918130321462775034,61579106854502535572057002945339368053196305168⟩
def resval4Tail208 : Box := ⟨286844889364587790154352387941013477090143271368,51854413804325938472637505759983114602170718607⟩
def resval4Tail212 : Box := ⟨347574312593959006766452763950391929596013795949,36988637842146827609213770763128345902198544387⟩
def resval4Tail216 : Box := ⟨421162734354666919528348348316833892984704011783,15475844343967946591350840692170319043655863036⟩
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
def polyval4Tail5 : Box := ⟨1019407422146771576157949540850081199624685772776090157948,2060869930857916181735602050204888192804571097164712247904⟩
def polyval4Tail9 : Box := ⟨1235229161486064528881632307632437223354434752900663140432,2262149780610125158330518372703649435144550418579428208728⟩
def polyval4Tail13 : Box := ⟨1496745950562757660907678860954973339021780282311623848096,2474216941895653341790440564278440495358893237427634227749⟩
def polyval4Tail17 : Box := ⟨1813629819215360375238646034360541911878187561055337253635,2695045550291492068807372094932164097036530754987293911978⟩
def polyval4Tail21 : Box := ⟨2197602819577160017201089717451000235964777722580324651723,2921597268191300987891989583042030309281964899852199747841⟩
def polyval4Tail25 : Box := ⟨2662868740602686554217631713677533974707038406260068406155,3149527892751510872930753903167666104179346864615147634147⟩
def polyval4Tail29 : Box := ⟨3226638529269492730573770410361924191869669542209168174221,3372821160565401030607649573846642458843532219389096818699⟩
def polyval4Tail33 : Box := ⟨3909766951641045260529764484411537456808418475034308511725,3583332873623689986977097933598392652242987734146271556012⟩
def polyval4Tail37 : Box := ⟨4737524044754187976133725882513228821844771770956979504729,3770224715021491219994761222271545133772585359618433836402⟩
def polyval4Tail41 : Box := ⟨5740529896597446018641871840849032895515656592798572719246,3919262532086409127867277463147957997316855713650715638788⟩
def polyval4Tail45 : Box := ⟨6955887333219630133202601370627296420012487190506792270771,4011948271709334226143415868923386693347830721097017993123⟩
def polyval4Tail49 : Box := ⟨8428554412916464242600971176044044935013528109066955138427,4024447941414399627398886652658317679299307902541572432838⟩
def polyval4Tail53 : Box := ⟨10213007498298782324811604058805633728423737733745581112145,3926269677525957896393492012176627758083874686285190627698⟩
def polyval4Tail57 : Box := ⟨12375256425996680455628757816821070447659387261691904899146,3678635909876139796321624320917541663451972881867483751995⟩
def polyval4Tail61 : Box := ⟨14995286318421136666140830239991880190949540072918652571471,3232481333836023302195779404735626824611171130438374563175⟩
def polyval4Tail65 : Box := ⟨18170016364199054405412789588961015653148154782615063770695,2525993465289812547534880251253390868804910335343420061551⟩
def polyval4Tail69 : Box := ⟨22016885079713451710528745125057774495462423864130300949282,1481594387799443292821264003684313162179329066484304808225⟩
def polyval4Tail73 : Box := ⟨26718750000000000000000000000000000000000000000000000000000,2⟩
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
def resval5 : Box := ⟨93430654832617626461366032033861927745192370991635244079,14876974767931186140463694481108519685501183567774242272⟩
def polyval5 : Box := ⟨8573086146439012864806535583876507649880666789217511183024,3751500186547812237316262665115272444992906144914054139963⟩
theorem cell5_lo : Holds Q cell5 (31/32:ℝ) := by norm_num [Holds,Q,cell5]
theorem cell5_hi : Holds Q cell5 (63/64:ℝ) := by norm_num [Holds,Q,cell5]
def resval5Tail4 : Box := ⟨-17823644815564447733993057785481608123561691507646113769,15058243426423543666348729609036721610659184099707220932⟩
def resval5Tail8 : Box := ⟨-19597361374171484107544331031176061374570742487710720311,15422556202231997590136770896047863364800561868960190943⟩
def resval5Tail12 : Box := ⟨-21547526710963143269134403815920731165708323863937261092,15749380300751727678432137709230096772152063826814286970⟩
def resval5Tail16 : Box := ⟨-23691756168523232798580019883266214649361475822836366411,16030189760723555185889793553769306699342013283819640995⟩
def resval5Tail20 : Box := ⟨-26049361389725088094687754334014776227901037843518163296,16255299098883647897592574983748031286474803177666450152⟩
def resval5Tail24 : Box := ⟨-28641575744141917369979817210257471346110605769665970873,16413726990629933243636720730974320124974147845992642119⟩
def resval5Tail28 : Box := ⟨-31491745568511078071999456197356038820099489838537285263,16493045730512518099913717907901555373556406806426020894⟩
def resval5Tail32 : Box := ⟨-34625540431541249980308214999315659276818325604636503816,16479214308766903012724834400679848366492992006592473147⟩
def resval5Tail36 : Box := ⟨-38071184322507621258435885150974007036773821906420297684,16356393382101295714434697871877623240352215645656372527⟩
def resval5Tail40 : Box := ⟨-41859709845800486403993036171108341113892443806037312639,16106740239806149426475767203959256739590460661659517693⟩
def resval5Tail44 : Box := ⟨-46025237710787146763410951244573735091953125349017842747,15710181670968513036245640459496084788717573368803930836⟩
def resval5Tail48 : Box := ⟨-50605284034164915647827428023172778666229441627198593502,15144162423443984901157749244866694551295931644715428215⟩
def resval5Tail52 : Box := ⟨-55641098222471490287930117656964984991264259994099970082,14383366708263713462027899718026981140618918870034357222⟩
def resval5Tail56 : Box := ⟨-61178034477833919783334406832163824317642966703407936031,13399409942130644292977013423345906067532567430704999593⟩
def resval5Tail60 : Box := ⟨-67265960272856978575721609765999214411009371591888739442,12160497633164511898040631718009888372331039713530083173⟩
def resval5Tail64 : Box := ⟨-73959705469884739420767701721643236991445916693622727987,10631047998180617426769048321287287250834070078722275249⟩
def resval5Tail68 : Box := ⟨-81319492150483679312466525328450653573451466407767633325,8771271410875986152246390617681111362354900859618913156⟩
def resval5Tail72 : Box := ⟨762395588056893550453671391643626987447940586961228242642,940381045818330487077495297926272855085330053702091303⟩
def resval5Tail76 : Box := ⟨-230811739100148092071692875495487279227249957934520714,198136809935311191178381210233674248563571640901339155⟩
def resval5Tail80 : Box := ⟨-253753908687704273115316641690573495935992321424342434,203059158549554336946387612063384784958335776274141093⟩
def resval5Tail84 : Box := ⟨-279005371884959807452739034951364916387171084117580064,207509606496476336082074670975310943381994005762282899⟩
def resval5Tail88 : Box := ⟨-306769650598796536492820451171823254343440772670088150,211378453718226782633211555189569803384289951253317116⟩
def resval5Tail92 : Box := ⟨-337296797882155818956406134699858868730660052712076847,214541213150640193073212378918989162399983331764600432⟩
def resval5Tail96 : Box := ⟨-370861751283041598310470125982210123343603743170112059,216856678801791438908473941639754137553571247414612583⟩
def resval5Tail100 : Box := ⟨-407766807833075123850549268004679682179730080823621166,218164980401158566092113537502285074062001566806397074⟩
def resval5Tail104 : Box := ⟨-448344346633567816689262529888430542723702649867428272,218285426173715665455424662983087970253870300584067592⟩
def resval5Tail108 : Box := ⟨-492959822371241335926875913186436721085273461870182683,217014111444675643306489115274403535456336674035120604⟩
def resval5Tail112 : Box := ⟨-542015056723571381434748976662352409281787342696470277,214121268504386930571058497911924144477306622726517605⟩
def resval5Tail116 : Box := ⟨-595951857297234942874268050049918920431784744351954394,209348330635415042075513926461102763595451414947066931⟩
def resval5Tail120 : Box := ⟨-655255996693013255950262081616357844152335744277407152,202404680419477675150053298221848245949590912823044213⟩
def resval5Tail124 : Box := ⟨-720461587533920278980973389883310062808774006981977059,192964049374754646442244467622429228414715436926384320⟩
def resval5Tail128 : Box := ⟨-792155892859501850774145929035167626426108354491452686,180660532595649866502496376660550008171124581267046511⟩
def resval5Tail132 : Box := ⟨-870984615210312385278145717387450514040953855108573765,165084178345967649281241009338349863804455732349246322⟩
def resval5Tail136 : Box := ⟨-957657712047834092525385523873831088696072199198055736,145776108457296523325902291455990687617513654403921266⟩
def resval5Tail140 : Box := ⟨-1052955874602531103498941026101118598728451874473738686,122223115008550204271968202956708179067132772411320090⟩
def resval5Tail144 : Box := ⟨-1207660318233363226143386621844252841024341537287428915,91461654195053552033548034168798878090274305281380364⟩
def resval5Tail148 : Box := ⟨88208418310005179876953128752107482697353932370,66370414231300358070049874169376475601229113625⟩
def resval5Tail152 : Box := ⟨96928515459591829007961991691096906111437818133,67644635416779479162698966923168157569432541026⟩
def resval5Tail156 : Box := ⟨106574028864429191611800300173393359402801517634,68699640980344219631214676468497620264860233307⟩
def resval5Tail160 : Box := ⟨117179383955097146056784726953753995317201347914,69490551817238602100211042358468930170093310334⟩
def resval5Tail164 : Box := ⟨128840095194257312576988211564958088563374769429,69967089890413220621586238319978635482400951906⟩
def resval5Tail168 : Box := ⟨141661182789852649960892179389505198171800202994,70072413612594850590623092409297643672554548892⟩
def resval5Tail172 : Box := ⟨155758117681944364043306811829890517683186635273,69742363230862101013393705366302115808761197727⟩
def resval5Tail176 : Box := ⟨171257861511800415551479518473811114009422904824,68904624536253104698515479371683372521037602459⟩
def resval5Tail180 : Box := ⟨188300010080276455135177773924139836289952906201,67477802327510264376767118307270053535515120550⟩
def resval5Tail184 : Box := ⟨207038050593601973617731245817688977737841659808,65370394191662071356562465527001224850513853820⟩
def resval5Tail188 : Box := ⟨227640744019741149063546582136837190829539263555,62479654195327656068888312182680943716263294027⟩
def resval5Tail192 : Box := ⟨250293645005285328285609555568471942759364936905,58690335013469482227501899838986704162646440746⟩
def resval5Tail196 : Box := ⟨275200773041749563434855834779962596114223558757,53873295846907845614948732394089453711404995742⟩
def resval5Tail200 : Box := ⟨302586449932347601589301801220981868621619851253,47883962185341593826760425626541536443237496198⟩
def resval5Tail204 : Box := ⟨332697320108076667876584049404569179801501495175,40560622046892768206217264130865861835500383960⟩
def resval5Tail208 : Box := ⟨365804571988757687017473380619340564948879806247,31722541755103987480027227959209663588755984601⟩
def resval5Tail212 : Box := ⟨402206380430206180063207821596841028153741126496,21167882582498748474394233471053152891740166413⟩
def resval5Tail216 : Box := ⟨442232210637518939533694884340883802019908513603,8671289830067501515726974826270209547498400850⟩
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
def polyval5Tail5 : Box := ⟨5318328051976833474159633945417533360460543470087250381458,3825369380572519741423266571019354040039175791389766865595⟩
def polyval5Tail9 : Box := ⟨5847561443314728251926868305957310835206706944573858887644,3890655694081098294273737793703538513401509056972776646558⟩
def polyval5Tail13 : Box := ⟨6429461800871951999010796360372883515533660090839103913040,3941932654182875453058290056835022436562733054843949570834⟩
def polyval5Tail17 : Box := ⟨7069268010400196439191842325558929094641837871343150280932,3976472850232608488432149234543508345170155501245765607691⟩
def polyval5Tail21 : Box := ⟨7772742377299924447433668687226162435403515875217410394530,3991190784145879808843690928328441918550160695975413813965⟩
def polyval5Tail25 : Box := ⟨8546220623548535876244686024952704899834814751404332353352,3982601587027566624456607050639252415539293028576806496247⟩
def polyval5Tail29 : Box := ⟨9396668949130672398487751657048124740923370904921123427075,3946775273986032841246784409227144129855650849764516434364⟩
def polyval5Tail33 : Box := ⟨10331746771930860948980028954887130941348797563117019044033,3879286056448588286955522712074148829391305529187394978597⟩
def polyval5Tail37 : Box := ⟨11359875710975134348540653675894794988582817076417795774812,3775156194760742848914177695197203594216938240766195697741⟩
def polyval5Tail41 : Box := ⟨12490315434307315275824366723402233464292821924280896192382,3628793820735114569026393489311282237102330222840030234047⟩
def polyval5Tail45 : Box := ⟨13733247054610932613948908945895647374558664066418357289258,3433924101303560837278265158953322262621484322602727149156⟩
def polyval5Tail49 : Box := ⟨15099864823665224084756621211051293204201957729467253372908,3183513049976888922580675335889890390159909549092210333103⟩
def polyval5Tail53 : Box := ⟨16602476951465713740526030035865660543041941404357401302407,2869683221832146682580408916497103108918680178509580346748⟩
def polyval5Tail57 : Box := ⟨18254616458019589100571280095197632949913165124033688557654,2483620449569761064046846731144022741522290549938887782974⟩
def polyval5Tail61 : Box := ⟨20071163056183685494470358704596322014266222767683632847169,2015470692087428272694968532556665402348827415738343486020⟩
def polyval5Tail65 : Box := ⟨22068477163269254023078473018958646490302294063670981860608,1454225972207193159578033356929177593450012862013232056422⟩
def polyval5Tail69 : Box := ⟨24264547309289291440335317502303968724830843967230931092043,787598271759703178349966745597095970206147669224112373436⟩
def polyval5Tail73 : Box := ⟨26718750000000000000000000000000000000000000000000000000000,2⟩
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
def resval6 : Box := ⟨75616155453971066981089790795108874477719705686353825505,13560011102369602600554044646039935005243839042037499694⟩
def polyval6 : Box := ⟨15153275010840142515935344478094346407396300523715479508941,3754496375883453193037347225106174173842927463803812691730⟩
theorem cell6_lo : Holds Q cell6 (63/64:ℝ) := by norm_num [Holds,Q,cell6]
theorem cell6_hi : Holds Q cell6 (127/128:ℝ) := by norm_num [Holds,Q,cell6]
def resval6Tail4 : Box := ⟨-35660894017809137167394123627394379670236101935857265548,13216259116135985047806809026306632815740712095169568173⟩
def resval6Tail8 : Box := ⟨-37382696961753837190973600907454385458869405088894163202,13052224547421099317784307151246774391780543726048498610⟩
def resval6Tail12 : Box := ⟨-39187576574537625007264863102420146480966449173992232234,12854706914794133384492841893908306316547591262464903838⟩
def resval6Tail16 : Box := ⟨-41079597844968423710484751786534673129866016285257576081,12621274277710803519902625448190511388805629962875440422⟩
def resval6Tail20 : Box := ⟨-43062968078526527516419878389187754136967164765421196903,12349351930975766327719608368149640200088776649276340532⟩
def resval6Tail24 : Box := ⟨-45142097708225977974370782908290319276515596974609328595,12036214067063187544291870608188599409103832668385135751⟩
def resval6Tail28 : Box := ⟨-47321610107854604094012899351229974666228534902711309085,11678975626717251566981663705481161159886131723723185879⟩
def resval6Tail32 : Box := ⟨-49606351873004481062953253493022343947156711624922785070,11274583728997372356953092836752518083129895466169448551⟩
def resval6Tail36 : Box := ⟨-52001403598477405756614236208225253691740963718415185668,10819808659475669031606882697472179263011814452825133995⟩
def resval6Tail40 : Box := ⟨-54512091176035887333568755756372379848062666602274932835,10311234394358711943821173542735098329426871408201632907⟩
def resval6Tail44 : Box := ⟨-57143997637622550096025198148155745790116501653772248260,9745248637203977492653202560247323300137086013489208499⟩
def resval6Tail48 : Box := ⟨-59902975570383791139795276284474332482371022044245293833,9118032343745642158203773697565886053735894426820674774⟩
def resval6Tail52 : Box := ⟨-62795160131105059815934529614672080336855060512172634106,8425548709131796099079345984694947878698249081119383740⟩
def resval6Tail56 : Box := ⟨-65826982688998033550452524699320425211515420364210261523,7663531590603094413059159170415901630907387436304313078⟩
def resval6Tail60 : Box := ⟨-69005185127174871099337334602781781878542550290478346589,6827473337308167658965945547573852431810218378534647707⟩
def resval6Tail64 : Box := ⟨-72336834831024101593571865374783725287581737741283398602,5912611997298482693965726651605686116845756934920553653⟩
def resval6Tail68 : Box := ⟨-75829277131345161861687289950038746258571143203760070029,4913914517526403095568805160815434362603278449596794773⟩
def resval6Tail72 : Box := ⟨762245756740434142740498194575400614026019550375907034072,895641018511616779495436746269068341695865602548532846⟩
def resval6Tail76 : Box := ⟨-465783520764840629039408736432787117594290918987958673,174789008724318854425203019076112068064910730383528993⟩
def resval6Tail80 : Box := ⟨-488247043939497057476549871020888461875640569890724631,172715706532953471398253837339939576674472242802464705⟩
def resval6Tail84 : Box := ⟨-511820171552811392409974430156892681040893723998264213,170207473973464178938547690618125424077990058062839450⟩
def resval6Tail88 : Box := ⟨-536531438128417518043638175282172279493104594651980661,167232442332534990546452959624369039274848505493143140⟩
def resval6Tail92 : Box := ⟨-562435793077751251430040122022563328393334666921924882,163757056568015001942113690544074011277053737266407169⟩
def resval6Tail96 : Box := ⟨-589590840079134653285505177947834848472082872473813444,159745790455571224774524522316046317437938662646184501⟩
def resval6Tail100 : Box := ⟨-618056963983380480780203855304667962090536743400649683,155161040207938978668024484284351614676764944696504902⟩
def resval6Tail104 : Box := ⟨-647897465091354770330879602769694134325914254086315512,149963012620760584492459371683529858428590886666672291⟩
def resval6Tail108 : Box := ⟨-679178699915257158571443696321054751188983577819716504,144109607449988631732822977477978694100586369458399919⟩
def resval6Tail112 : Box := ⟨-711970228736019298253379779775754569596559664949934166,137556293730603076920701842924255794757403805492744856⟩
def resval6Tail116 : Box := ⟨-746344970284944202744459244792177769161681865084373179,130255979732019714111595829297205689644681900337284102⟩
def resval6Tail120 : Box := ⟨-782379363893553052653614593129278160729751312852116033,122158876230474398545686052998023610299743779412317319⟩
def resval6Tail124 : Box := ⟨-820153539472213111222244926153132745432791750516539387,113212352762833182233823700072637742239873177372548674⟩
def resval6Tail128 : Box := ⟨-859751495695529354665304738885243864641809527648899450,103360786509667112776876956074676655330412885336728839⟩
def resval6Tail132 : Box := ⟨-901261286790742242479216087321285601460445124271584200,92545403438002832201519499118494927057870709902834235⟩
def resval6Tail136 : Box := ⟨-944775218354418153769334311321432257470023545660275313,80704111315056265739162593228451064375766148441787883⟩
def resval6Tail140 : Box := ⟨-990390136419388835241698990145381282998006867350205684,67771318684915158408472448515413601895064870206985671⟩
def resval6Tail144 : Box := ⟨-1087548827162167709370276602845045007192196397767355848,51502199213517280162221755474092513585125255261664852⟩
def resval6Tail148 : Box := ⟨203258461930949960958414418584605226533519761123,65548537002598321187280423353053546374805055697⟩
def resval6Tail152 : Box := ⟨213017059491627483287783604047952052016238300305,64302221905470524669690482974267054269945124980⟩
def resval6Tail156 : Box := ⟨223301767233995645084919119281044677452950613625,62855684400780559963226371078219074385708936184⟩
def resval6Tail160 : Box := ⟨234083033396663522426241123144636228728355535455,61194262041875734911595898616381798410251225102⟩
def resval6Tail164 : Box := ⟨245384831490501824331276990316006377655054609028,59302957359589816303511435627234490676602531037⟩
def resval6Tail168 : Box := ⟨257232293395597843211701571736223651184952483999,57165901482481788265166792370502816852682750787⟩
def resval6Tail172 : Box := ⟨269651764388379198845453875532552217877074715552,54766307355309614127708649379382607096709134374⟩
def resval6Tail176 : Box := ⟨282670861725522094789542826295087613578414981442,52086420563286697669433945818920226661106054278⟩
def resval6Tail180 : Box := ⟨296318536056620331649704784839566944655898287039,49107467627680479684159288806622959357622349334⟩
def resval6Tail184 : Box := ⟨310625135801929029913409219470817484987146882196,45809601645739432077165058214564748719088899066⟩
def resval6Tail188 : Box := ⟨325622474638339869130036310278567064595355922431,42171845141651907564937236281839276275015310269⟩
def resval6Tail192 : Box := ⟨341343902243656833798848205699164159088142493135,38172029988642782373052065060572162718354629204⟩
def resval6Tail196 : Box := ⟨357824378456486962082700806452876440184080658544,33786734255392601092559422245565033125569332930⟩
def resval6Tail200 : Box := ⟨375100551016655918556760216304444390463468960524,28991215822703217893464853519791419196882293560⟩
def resval6Tail204 : Box := ⟨393210837059020277286357900679883961907790914455,23759342608717162719029955870336182567401275251⟩
def resval6Tail208 : Box := ⟨412195508541907885025706298043556954504184448898,18063519233006509728490511914849745116881929301⟩
def resval6Tail212 : Box := ⟨432096781834648301832009844900520433029458782797,11874609938771843195600648801412759960853480942⟩
def resval6Tail216 : Box := ⟨452960511703524211907623751270510839713037181010,5161756773090885734668189712655431432640470943⟩
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
def polyval6Tail5 : Box := ⟨11968987341216602361082276258916411018324357996068703019878,3683469535469256646797930333098049038628158095297162246904⟩
def polyval6Tail9 : Box := ⟨12546861825569270384556919537619920348643476826179481618940,3604437197541924338730896849415753810356992506316522520313⟩
def polyval6Tail13 : Box := ⟨13152638745684061302079153210930821094070322828525792032316,3513402505632382745619747366876823215238399991441869995423⟩
def polyval6Tail17 : Box := ⟨13787663272442479492643687397293273485349603450317169469338,3409525052539799782639927241961568280449534359518156777914⟩
def polyval6Tail21 : Box := ⟨14453347513755808216928951072527978757930567621161217496606,3291915552933673266895718728616254827587944877774054541565⟩
def polyval6Tail25 : Box := ⟨15151171755907321518687401354326704638854530987255257517388,3159633205655386095595380877152010379785067641027051298069⟩
def polyval6Tail29 : Box := ⟨15882687755104797812156923937446217740468150824369454127030,3011682933023841712640683244965799127390732490886263143469⟩
def polyval6Tail33 : Box := ⟨16649522188130551763100507001846704850827063498180431004237,2847012478139375886478576506010219356962492199659706280713⟩
def polyval6Tail37 : Box := ⟨17453380269592945871648806221539226664684980802748604162755,2664509353049620298689071840090574966994032933089754541610⟩
def polyval6Tail41 : Box := ⟨18296049543822965977676795507324152255758031343554383271901,2462997630290165858641770520054458214521054585767186771799⟩
def polyval6Tail45 : Box := ⟨19179403859847924861018682511938451293851934929117185439819,2241234569942254595612103270213905070251199383560190179066⟩
def polyval6Tail49 : Box := ⟨20105407538281468251814256546817825288366261163735012885906,1997907073960921960515260873648276108655757635287333079132⟩
def polyval6Tail53 : Box := ⟨21076119739395823073157693390592812762478272160078272508316,1731627959119131918018234401032186113489634413539739685050⟩
def polyval6Tail57 : Box := ⟨22093699042089598003196744773102033312349418460053989587607,1440932039485564923695471674942771012984991968779182203305⟩
def polyval6Tail61 : Box := ⟨23160408243933423427028740428544511524672020066207376195921,1124272008904857382342590529188235309958741113323991266896⟩
def polyval6Tail65 : Box := ⟨24278619392974420108367766354370182390274363820174746258860,780014113477656921891600231846942134895470238642940079926⟩
def polyval6Tail69 : Box := ⟨25450819122742784740418229010457853759703563682414928666122,406433599771449421271308571733389196247018504091301776775⟩
def polyval6Tail73 : Box := ⟨26718750000000000000000000000000000000000000000000000000000,2⟩
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
def resval7 : Box := ⟨54459200672930586314944239548264295518322006636838208257,22106782078593955042402843806124222385866977541733049901⟩
def polyval7 : Box := ⟨23863155002588442987692469714843097943412348415935210180531,6556846275785113599963446834945729787486803307669278830634⟩
theorem cell7_lo : Holds Q cell7 (127/128:ℝ) := by norm_num [Holds,Q,cell7]
theorem cell7_hi : Holds Q cell7 (1/1:ℝ) := by norm_num [Holds,Q,cell7]
def resval7Tail4 : Box := ⟨-56041556401774252748689069490947433017898236415845136308,21025295005882257831706880129163491663736333965625802476⟩
def resval7Tail8 : Box := ⟨-56925876510093743073155407048313529525774854435905814049,20141025756231291943491489369586424961672448707263693584⟩
def resval7Tail12 : Box := ⟨-57824097863561445263483323874713380577319285860503576267,19242804408393479118616434205416877342222388278155382730⟩
def resval7Tail16 : Box := ⟨-58736492055676225095129275692979000893551647555685340585,18330410216283362651652130833474892462831759547572495479⟩
def resval7Tail20 : Box := ⟨-59663282722483668626681862673228509587992858056867186390,17403619549475935908100520347462448553580969715567935550⟩
def resval7Tail24 : Box := ⟨-60604697022913394961565138338863384306663368057122279070,16462205249046209773390363458400108666456177293227815378⟩
def resval7Tail28 : Box := ⟨-61560965700182825381063352009519217036414509477024435423,15505936571776779360443829174131625276824830667096694803⟩
def resval7Tail32 : Box := ⟨-62532323138357716493001051074687149805985167087017340578,14534579133601888248985273209412432599538522225647726614⟩
def resval7Tail36 : Box := ⟨-63519007419800351945084060196509326018973001787298345880,13547894852159252796936206657247575715033166190478478743⟩
def resval7Tail40 : Box := ⟨-64521260383524180157423593459359769978652905945446025259,12545641888435424584506657088888992239125542813058668171⟩
def resval7Tail44 : Box := ⟨-65539327684469217337305028188068908405117974907639089177,11527574587490387404123920938208108286521084300871445075⟩
def resval7Tail48 : Box := ⟨-66573458853712744514626165993904986640253658346152672925,10493443418246860221737372968066349252603754166346657509⟩
def resval7Tail52 : Box := ⟨-67623907359630056318289813423475657745119155517247944410,9442994912329548290402456865095894383200262280608993318⟩
def resval7Tail56 : Box := ⟨-68690930670020244208517053681655339780522433941296230000,8375971601939350818021277034626810085409036400604915862⟩
def resval7Tail60 : Box := ⟨-69774790315209885163274004474939896123848435890229703329,7292111956747079346284972249755012575895822630927062561⟩
def resval7Tail64 : Box := ⟨-70875751948587243482676857036045988250583357230241659561,6191150319540559901217500740272317279557132446486538641⟩
def resval7Tail68 : Box := ⟨-71994022606061856904853010855904300588404705911311391968,5072813514272679512280448867003864043197124898046366216⟩
def resval7Tail72 : Box := ⟨762023328087419538560972690819189706838952652022255443135,1006248542497777503657523527723925879908276025700452781⟩
def resval7Tail76 : Box := ⟨-734552400544463704889915125760477944535575236110266332,277710857969261726904303928331466867785938691746109353⟩
def resval7Tail80 : Box := ⟨-746118493534856198065947353356204503640937780540449653,266120704078737897153658923972914278850514567197482765⟩
def resval7Tail84 : Box := ⟨-757891337996096773073020982910905598524008619600452665,254347858409376397435995176801674570085463797618355365⟩
def resval7Tail88 : Box := ⟨-769849944884063137632555333667650082258910156449341720,242389251520774784614301892697804400264711464134726647⟩
def resval7Tail92 : Box := ⟨-781997244097716404232368266072475144936511673375723439,230241952307119890389954539122807881061383987442569263⟩
def resval7Tail96 : Box := ⟨-794336212972669027610373887566859212648620462317930678,217902983432167252130640702766715089947102772351144611⟩
def resval7Tail100 : Box := ⟨-806869875823906349881606961030532406311746649130578912,205369320580929929457028138614998061859097017810840807⟩
def resval7Tail104 : Box := ⟨-819601304686440820334291467898620080005962973762805128,192637891718395458976417216808959821520494330757288284⟩
def resval7Tail108 : Box := ⟨-832533620068274656250301017751357263264388836120994142,179705576336561623056239041295431299390135845845540990⟩
def resval7Tail112 : Box := ⟨-845669991715244868140193995793708960250181529822122513,166569204689591411165762265763940335409134294142714694⟩
def resval7Tail116 : Box := ⟨-859013639387936625283446410660490197668319767770178037,153225557016899654025740867128421912756464098789880159⟩
def resval7Tail120 : Box := ⟨-872567833650855373009169979657847321853823152001728732,139671362753980906337026139160205421242826389751949603⟩
def resval7Tail124 : Box := ⟨-886335896674051130434756218731303873003112253805143165,125903299730785149718285638764920954393861616276877726⟩
def resval7Tail128 : Box := ⟨-900321203047391498326090231338032732726275402696739977,111917993357444829252094555833055389578815457485480302⟩
def resval7Tail132 : Box := ⟨-914527180607693326908764820638655223070980306425920014,97712015797152540742640750326714474643818274526188209⟩
def resval7Tail136 : Box := ⟨-928957311288772100090367964225225914835531220686548460,83281885125170924008269476650723102605165103857248140⟩
def resval7Tail140 : Box := ⟨-943615215172007625299705640177691525944230837558906565,68624059021643728063875027811225585653808499989075444⟩
def resval7Tail144 : Box := ⟨-1007465590507065620034250620768902119635110841417338542,51578166084661649041851172359085708924839026697594663⟩
def resval7Tail148 : Box := ⟨352703339878226395031266900457212416506681355012,112746654151719193924892143010011624893124762456⟩
def resval7Tail152 : Box := ⟨358215336096012294127488816576495173292189258112,107181757667055332987250711041225893497234893091⟩
def resval7Tail156 : Box := ⟨363867539135749335704614611184737410172705174765,101529553754678746231983280706962313760659772466⟩
def resval7Tail160 : Box := ⟨369608927962486038453959481837159930393402683511,95788164927683933861930070508349784829377456531⟩
def resval7Tail164 : Box := ⟨375440908947656268597530754132641524964802604775,89956183942513283988119417239245887001022443732⟩
def resval7Tail168 : Box := ⟨381364911525484002955782219435357065562396326398,84032181364685547044163543964437022869021469905⟩
def resval7Tail172 : Box := ⟨387382387685187715917716528594877895553603374767,78014705204981834033272161680450385380099657810⟩
def resval7Tail176 : Box := ⟨393494812326616609553070234958628057519377445083,71902280563552940395453219884143817890431523408⟩
def resval7Tail180 : Box := ⟨399703683621752201209656302008519739771988832779,65693409268417348738580163429251506226080287724⟩
def resval7Tail184 : Box := ⟨406010523381914367578761294410353910636700598975,59386569508255182369419132459952759086059760443⟩
def resval7Tail188 : Box := ⟨412416877430761457434567285016298019938323317708,52980215459408092513645491069402087800741677491⟩
def resval7Tail192 : Box := ⟨418924315983175894182300388696471967610478755517,46472776906993655766345331977700295934076715810⟩
def resval7Tail196 : Box := ⟨425534434030128134082183077235460540416185047678,39862658860041415873136496727556475055209230123⟩
def resval7Tail200 : Box := ⟨432248851729613311600867549316249418043573130923,33148241160556238599161868153341067967839644444⟩
def resval7Tail204 : Box := ⟨439069214803756420843195548307128287121309369203,26327878086413156400538878829783918511987432016⟩
def resval7Tail208 : Box := ⟨445997194942196339191544006285812781971852171991,19399897947985103346546166089865267604781754700⟩
def resval7Tail212 : Box := ⟨453034490246098514584681601105175842890175187930,12362602675734635472493411921858404889269618359⟩
def resval7Tail216 : Box := ⟨460184413754076812605045662814609885536180804037,5214167455103774199659247794239368764460927075⟩
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
def polyval7Tail5 : Box := ⟨20445565441576232991898429322693862720869499406755245783306,6236047644538209621295639136420845859908332312463490751978⟩
def polyval7Tail9 : Box := ⟨20768169759583421059540270653003302539060850956093045577343,5913441415859654263239432681612464690927228986623801783992⟩
def polyval7Tail13 : Box := ⟨21095866311013077945243137607629971434944461498586120962547,5585744864257673364920574344022690533937521336121264270921⟩
def polyval7Tail17 : Box := ⟨21428733517088714562606070745770903505766447505391136595351,5252877658181910687004829260845991021702572783865994766457⟩
def polyval7Tail21 : Box := ⟨21766852964302484903049089001228210554618366094509205593837,4914758210968139937199451940543092057419871791976634479526⟩
def polyval7Tail25 : Box := ⟨22110307526654673667045293684937462468936745474269674569118,4571303648615951168713607063181834168203667385426936709380⟩
def polyval7Tail29 : Box := ⟨22459181385796985883484243933478528825654381693939984622584,4222429789473638952134507696305015709198536255992596624220⟩
def polyval7Tail33 : Box := ⟨22813560051665578188118415963974017690030235494427995991148,3868051123605046647489458025053163988220567770389791614784⟩
def polyval7Tail37 : Box := ⟨23173530383439777448597707666035370856214058423932407308499,3508080791830847387008425547430604555163895414176068770598⟩
def polyval7Tail41 : Box := ⟨23539180610831502952180493358714935868977639154357436145085,3142430564439121883425464590827662311139473487830166829850⟩
def polyval7Tail45 : Box := ⟨23910600355710609880452634739518490107417967554250452213415,2771010819560014955155293079518900033281786852943772886716⟩
def polyval7Tail49 : Box := ⟨24287880654071454498248401204531413931033448240375333989474,2393730521199170337382129283234063370768482449936818927711⟩
def polyval7Tail53 : Box := ⟨24671113978346065122308191849329472782989147883239071082424,2010497196924559713836350321487788673809481704408405005068⟩
def polyval7Tail57 : Box := ⟨25060394260069387921766888199855104436781738312823697385237,1621216915201236945975011382822269031268732092335769536774⟩
def polyval7Tail61 : Box := ⟨25455816912902170052586607531652306132525459903748312235491,1225794262368461441124041289482019676861626455996464486733⟩
def polyval7Tail65 : Box := ⟨25857478856024171970714197878188868901341009121303997444950,824132319252980415776353608786852585777161697852996739017⟩
def polyval7Tail69 : Box := ⟨26265478597719525244963637436422421455889941456206216917507,416132633673297907552467082236762168425714094818069825434⟩
def polyval7Tail73 : Box := ⟨26718750000000000000000000000000000000000000000000000000000,2⟩
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
def pend : Box := ⟨1030415069694476087816766576149551408640869031099752684426919,4931583897468770889340400237419090030120623851804584313⟩
def zend : Box := ⟨1003730425217282061083496093750000000000000000000000000000000,3247696897630575410156250000000000000000000000000000002⟩
def betaquot : Box := ⟨428746048975735827704486009487757541198812742222327240102595,394762800815303791015552699549668602160258965576595515⟩
def crit : Box := ⟨108568070859535518083374527662290762093837049386732048508,12663437682421948251194016814171577044435273420504625524⟩
def subsonic : Box := ⟨568557011026200276850956148077903983467110735497393957633,6876700947853985220266276889068067886664224166327802746⟩
def pendTail4 : Box := ⟨26680031601855142280665468574472019353026095628994077036223,1546078347553894158655891095868476843685257706554885805⟩
def pendTail8 : Box := ⟨26680065256467611522817471028342029413622719014565843538245,1545917442385039097661126681216190620424421726444784151⟩
def pendTail12 : Box := ⟨26680065257845494718676069561323962622227608932029346877774,1545917424499850373811281686040988144355983758413039574⟩
def pendTail16 : Box := ⟨26680065257846137630063748339099714862809160620522907112712,1545917424485775398625518860053233802104204345079870985⟩
def pendTail20 : Box := ⟨26680065257846139098026823569239826470290689164178102214592,1545917424485726010119043231116447252012790976875051491⟩
def pendTail24 : Box := ⟨26680065257846139109925841779664566284393305823218543332085,1545917424485725402453386379389613247725297456072124294⟩
def pendTail28 : Box := ⟨26680065257846139110207839777031995972210680990349309440060,1545917424485725379904105699038087429864274591216346842⟩
def pendTail32 : Box := ⟨26680065257846139110224606466104273216484465737438452936474,1545917424485725377600427407923067185502323746356188072⟩
def pendTail36 : Box := ⟨26680065257846139110226612510521648761508537231769355246262,1545917424485725376985357162432463807036205995727934007⟩
def pendTail40 : Box := ⟨26680065257846139110226649448172605393277466246411159948830,1545917424485725376566289153025120118179967687286839069⟩
def pendTail44 : Box := ⟨26680065257846139110224851242589542520974311676479412227130,1545917424485725375838134764546763609864672962822066537⟩
def pendTail48 : Box := ⟨26680065257846139110209807104195306223198882206688752319490,1545917424485725372539780175102529787319393368881291026⟩
def pendTail52 : Box := ⟨26680065257846139109952651679583191136655142151648080022375,1545917424485725331650730288622208599967379818237127056⟩
def pendTail56 : Box := ⟨26680065257846139098280886809776454776948817445485047524258,1545917424485723820735164745805866670917171587022587582⟩
def pendTail60 : Box := ⟨26680065257846137385317256213061585372752962381299248996861,1545917424485538044484111566490447975970971462181531192⟩
def pendTail64 : Box := ⟨26680065257845065902233819825548775879015114450643565788167,1545917424396825739286861158590450429518857493529914668⟩
def pendTail68 : Box := ⟨26680065253072279386243158354543183501139913949158256091733,1545917121787315419347483118448653271022113856537071477⟩
def pendTail72 : Box := ⟨26679434711893888755052962044051007269623588174081682569381,1516893738107789653536737263009382851660295238195265925⟩
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
end SepticProfile.ExteriorCertificates.C11

end
end

end OAI
