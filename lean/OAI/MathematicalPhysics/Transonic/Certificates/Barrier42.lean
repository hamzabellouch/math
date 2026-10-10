import OAI.MathematicalPhysics.Transonic.Certificates.BarrierData42

namespace OAI

section
noncomputable section
namespace SepticProfile.ExteriorCertificates.C42
open SepticProfile.ExteriorJet SepticProfile.FixedInterval
def cell0 : Box := ⟨250000000000000000000000000000000000000000000000000000000000,250000000000000000000000000000000000000000000000000000000002⟩
def resval0 : Box := ⟨125030132533416626850871240429597303671287634131765275119,305710379856429486062877653064071063117945577708131359⟩
def polyval0 : Box := ⟨3880187486027864440585368136775105210520977842948129215683,14812469762145893877313176469462191758595185544459011774⟩
theorem cell0_lo : Holds Q cell0 (0/1:ℝ) := by norm_num [Holds,Q,cell0]
theorem cell0_hi : Holds Q cell0 (1/2:ℝ) := by norm_num [Holds,Q,cell0]
def resval0Tail4 : Box := ⟨69351535877578565834089496154182254263922530104086,1977626957509955625001374885413569189467193655757⟩
def resval0Tail8 : Box := ⟨9052846988198093322358895648000729647175645684,473365093230125684417521395790096634140912238⟩
def resval0Tail12 : Box := ⟨8879778167964163483911133741655341527939552,707263878030709430130443967638812244089630⟩
def resval0Tail16 : Box := ⟨38310350525986492140783887622783445248207,30623875068559423123884407891929305475016⟩
def resval0Tail20 : Box := ⟨561658246071183928175995987758865616615,420502079130698731407481321475906811191195⟩
def resval0Tail24 : Box := ⟨24010762188878710799147252534998204154,6726620466882279029882587749933007222460857⟩
def resval0Tail28 : Box := ⟨2723102378842003279691451126940651030,107625844486774647566351145088643845182965012⟩
def resval0Tail32 : Box := ⟨771778227158296880594141715360631723,1722013498786813694944070474463087438419644447⟩
def resval0Tail36 : Box := ⟨-61046402527523484237908450095548887,27552215975505673841855166124006014619928596415⟩
def resval0Tail40 : Box := ⟨-151862003834412564614811030155619329519,440835455462992781094509560092418165754769000894⟩
def resval0Tail44 : Box := ⟨-39102468864114141723792897744540745871826,7053367250742433485216147714374271645050535867545⟩
def resval0Tail48 : Box := ⟨-10011136310383288109428396943919744188547128,112853866626389791677282979708961614087422243412055⟩
def resval0Tail52 : Box := ⟨-2562859680166055308087237086276807264141447709,1805659463340242249051215214292473364473043726926325⟩
def resval0Tail56 : Box := ⟨-656092264292763273874169124576004902687632801784,28889936326872357046793830443244493103574767412748057⟩
def resval0Tail60 : Box := ⟨-167959612453792580681458691197739011596747036156164,462081519072543946061989675597467805735448123963244406⟩
def resval0Tail64 : Box := ⟨-42997612685019573937169644665658463928907269996724697,7352994011285862989210404993554912571622663917653034606⟩
def resval0Tail68 : Box := ⟨-11006277728199203272684131287031548086154305998876202437,107328948581778934593875001226599548786017068960747407165⟩
def resval0Tail72 : Box := ⟨896670245458349156510255283083970918417655692763795035404,2665734457565442755749202065669992538637271940940619808⟩
def resval0Tail76 : Box := ⟨-33118318803299550983067162195792242011935547358181,698949756089980964457479627593877115415740811630⟩
def resval0Tail80 : Box := ⟨-1932044212683242494157178462764808226247880365,86814465576351365990750421107880124220095221⟩
def resval0Tail84 : Box := ⟨-1178833861925681644342442474385190624860748,83639006297414406205600956388078698972819⟩
def resval0Tail88 : Box := ⟨-3515695197013993394534690523420731195164,549079304513711781007833775643186170122⟩
def resval0Tail92 : Box := ⟨-37708294272187963849669833617069904547,3002076043402396238713685964806859729522⟩
def resval0Tail96 : Box := ⟨-1220884031333220675167041052110637580,47946547519697777389836790841497521548968⟩
def resval0Tail100 : Box := ⟨-107167326048029661105607033779132427,767140896225842164742069580945837482139295⟩
def resval0Tail104 : Box := ⟨-23898139712112703171574341526263712,12274253871886767488595911212245292321659384⟩
def resval0Tail108 : Box := ⟨-15146971602497304816531129877776583,196388061803458981143082808049423459582760676⟩
def resval0Tail112 : Box := ⟨-554212568388883999146458843824952610,3142208988333344820628517505585534550542629717⟩
def resval0Tail116 : Box := ⟨-137516752092945881468912193721227454373,50275343684478558192832764863156509981114820344⟩
def resval0Tail120 : Box := ⟨-35190465964570256332253881222974658479273,804405465960979082061322291473302464142406736793⟩
def resval0Tail124 : Box := ⟨-9008652692058517028786865075074545692732447,12870479009770476855199051322060449891643248190177⟩
def resval0Tail128 : Box := ⟨-2306213184957059863682624718175855633266475935,205925502081858160840956749476861380439055062666314⟩
def resval0Tail132 : Box := ⟨-590390558858066489880741591277482099256017805344,3294254542244771865355885951904428486775134965835390⟩
def resval0Tail136 : Box := ⟨-151140111001460860427426600580677879038279163811078,52566378908785413685257705589263350815231580838629420⟩
def resval0Tail140 : Box := ⟨-38693500701152530447008790011856857325279789825107574,804787717670128009441793487356366641177647081339809353⟩
def resval0Tail144 : Box := ⟨-10632085979726767151975556911491282882355161655359318620,3237845519434334537119258419950802614907433757657356850⟩
def resval0Tail148 : Box := ⟨85152309911102878693326834886975372477841167,1456985194207048237394031641516418465442435⟩
def resval0Tail152 : Box := ⟨1639301276387936068552435806146517355235,65456077496369287514897947823144714635⟩
def resval0Tail156 : Box := ⟨562123004613902847813791405256654996,36247726596149495859275545821549966⟩
def resval0Tail160 : Box := ⟨1061905633817591271441017932423451,102129834464532999501114926445390⟩
def resval0Tail164 : Box := ⟨7639665881814735229051937574326,39809472531349598244133139503905⟩
def resval0Tail168 : Box := ⟨171272609972364958686133318194,620948282140587471083429471714545⟩
def resval0Tail172 : Box := ⟨10587110179902270518352117753,9934681109665309044285454141141327⟩
def resval0Tail176 : Box := ⟨1672985618577216951565114580,158954856259826623104333089672134421⟩
def resval0Tail180 : Box := ⟨655585340122466776185169031,2543277691098481514623874360003671852⟩
def resval0Tail184 : Box := ⟨2877932208782281824227699929,40692443051893320949027795397676244981⟩
def resval0Tail188 : Box := ⟨584601288797956034122038921101,651079088284103406347177318740835648396⟩
def resval0Tail192 : Box := ⟨149323447264427276692044907803103,10417265272561802919037029347527293765335⟩
def resval0Tail196 : Box := ⟨38225035006353190082436110642314997,166676208525092496740154036761142325304147⟩
def resval0Tail200 : Box := ⟨9785586634001164991857884298283966514,2666810162416522214488807510835954155182008⟩
def resval0Tail204 : Box := ⟨2505109650513833859519583908752687428915,42666614058660216110275091965587827123998059⟩
def resval0Tail208 : Box := ⟨641308200408105388899622860139935740224038,682064598640564209058080400683326353276507282⟩
def resval0Tail212 : Box := ⟨164175670138671278244984675281843922939010738,10759119306118211515527635518361806837849211540⟩
def resval0Tail216 : Box := ⟨42073641309792676593078944643178532080665698021,132722686460367258892171589329858717252724510604⟩
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
def polyval0Tail5 : Box := ⟨2309069496756516993358661967183872170955894539798995,56194312987135818408447960760992086997469078144790⟩
def polyval0Tail9 : Box := ⟨241589260484796162015000305757705530658544342428,11634545440796538783357078592902868740205620965⟩
def polyval0Tail13 : Box := ⟨205039426552758714511405533806820160145562579,15326890701787285103684997306191613705469522⟩
def polyval0Tail17 : Box := ⟨775170247185861989420533592280653399884615,477336795792277513519640491304586476995568⟩
def polyval0Tail21 : Box := ⟨9985979135369595801235943343523940401131,6306847760717902325153077984755776852841213⟩
def polyval0Tail25 : Box := ⟨374692618405889755827381684899451761587,100885733062911385977310132228287728446659958⟩
def polyval0Tail29 : Box := ⟨37165002726641645052650891959531895015,1614170501478881013534439992791378170791757674⟩
def polyval0Tail33 : Box := ⟨9210690163716660054237685515259783571,25826727856063070571243559258903970340497449252⟩
def polyval0Tail37 : Box := ⟨11445252230175683619653102612603208641,413227645637156784100797236301001080754216526807⟩
def polyval0Tail41 : Box := ⟨1533744739401393914129451929276922674504,6611642328771335460543951953153179542263215587048⟩
def polyval0Tail45 : Box := ⟨390660271728401183028855052806617051878713,105786276894129242954934052946205336104920709253849⟩
def polyval0Tail49 : Box := ⟨100002330714213239408203865302804398704980678,1692580336554078681737331076434093230478472614659306⟩
def polyval0Tail53 : Box := ⟨25600542037304035176156232044488612117609326500,27081261384360725489054556634441248532446308755279071⟩
def polyval0Tail57 : Box := ⟨6553737745151844002689360123414167859208959728652,433294038020856932766175070757148123019257608686893856⟩
def polyval0Tail61 : Box := ⟨1677756856015368573935186618961858545627176689691552,6931131711330158182818417918602114825582484631556949179⟩
def polyval0Tail65 : Box := ⟨429505829952176783892356303415100146664674194576651322,110495445716652436955963310916229862595167560570147981930⟩
def polyval0Tail69 : Box := ⟨109954382113389105356917152611384186430497226608347805087,1664845344430478111544230298165786755600464461738797377135⟩
def polyval0Tail73 : Box := ⟨28656250000000000000000000000000000000000000000000000000000,2⟩
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
def resval1 : Box := ⟨124777058336815497787087952690457209533926863702284718408,219137287595841874064108783258978388378271535946272308⟩
def polyval1 : Box := ⟨3861294131812962772099344191982561495945883890686264462108,8368485799026473586201817883868525733020846382452214939⟩
theorem cell1_lo : Holds Q cell1 (1/2:ℝ) := by norm_num [Holds,Q,cell1]
theorem cell1_hi : Holds Q cell1 (3/4:ℝ) := by norm_num [Holds,Q,cell1]
def resval1Tail4 : Box := ⟨67303019630014176604445961170270271078872135351506,3357282877656131646115625986872604046059355195955⟩
def resval1Tail8 : Box := ⟨8535835020473562832166903210862453684703696072,6756679010027070858857423157322889010043433839363⟩
def resval1Tail12 : Box := ⟨-341225036541704086817761557924858023339974666,21353430235488136045178619449261999274570341939900⟩
def resval1Tail16 : Box := ⟨-2290134132594183746376978789085948651287332712,67486197653342775078043302933315936663851072933566⟩
def resval1Tail20 : Box := ⟨-15008849261433920243443237793042977625492818488,213281940310317516864264011734916412869515592774384⟩
def resval1Tail24 : Box := ⟨-98361997731733776204784252024868278052378565841,674025329174711986105255273186092004115553274660840⟩
def resval1Tail28 : Box := ⟨-644625188466536631801856384761876526797705428558,2129919139504745582724615519442583054984066861280619⟩
def resval1Tail32 : Box := ⟨-4224615635148397969304027216505230635796501745011,6729409011049577074207250814199376741033948785690935⟩
def resval1Tail36 : Box := ⟨-27686441026512169294968995167106799462148010113933,21253921070470893056646692925811173742871407363577669⟩
def resval1Tail40 : Box := ⟨-181445859911352183176772643037617948615880056391137,67078943312228595611079851233012052704774352528755178⟩
def resval1Tail44 : Box := ⟨-1189123587515039399817380280000539312753320459356855,211386921203445782328414797373201089905007626413788955⟩
def resval1Tail48 : Box := ⟨-7793040343138553420259855942404770331881349717383712,664052237020885752785307169869475158879170043894135398⟩
def resval1Tail52 : Box := ⟨-51072469192792295479312702315871404404664901561468059,2072290382723135759227520084630100595226641771854076207⟩
def resval1Tail56 : Box := ⟨-334708534101830487732232331344146246231408298955468035,6376166652200309259876632183179757453394638254754558634⟩
def resval1Tail60 : Box := ⟨-2193545849072503881399584182782873077679328167272467395,19016133752063977606377911504391901707031539948179553653⟩
def resval1Tail64 : Box := ⟨-14375622048388403517843301629298133930476344915927254784,52657439382028025071883836248088390751522967091389931939⟩
def resval1Tail68 : Box := ⟨-94211566898009412726406038520730267006657648360584749301,117645567947810358148847265312016709850191332721519604318⟩
def resval1Tail72 : Box := ⟨899975258411100125964376702858806912825795748727489424029,1563216876260308654543642298358453337012827953227226859⟩
def resval1Tail76 : Box := ⟨-32366057529923414994725196592669492426347623696807,448299219566637510249091873385174726099045132262⟩
def resval1Tail80 : Box := ⟨-1845012117275190976645032741852020549305693219,72274363023657897394252636497704863620253734165⟩
def resval1Tail84 : Box := ⟨-4198126696495989601414381074571993478529579,228255875782817472600129638131891794549854655047⟩
def resval1Tail88 : Box := ⟨-20310775404325137115142609097885566449114384,721390795207589609571968519256255791513892752205⟩
def resval1Tail92 : Box := ⟨-133087777234032237512814595495103154956221367,2279882249534820193402716431844798551324987643799⟩
def resval1Tail96 : Box := ⟨-872203839225969066247725628501018048737297144,7205102195463114758569573708640248925169978083815⟩
def resval1Tail100 : Box := ⟨-5716075073965046845334971049565307525541288672,22768721532594414044669399108914353559910033565634⟩
def resval1Tail104 : Box := ⟨-37460869604171980149564196092995952186067526636,71941008606483279734568032810458294368194881764576⟩
def resval1Tail108 : Box := ⟨-245503555037785724602672119491250325535342819460,227242004912596576989652212600604496672274437866568⟩
def resval1Tail112 : Box := ⟨-1608932098295579141990903077819567665954002111416,717363934169783372470589399659688900063471318374295⟩
def resval1Tail116 : Box := ⟨-10544297399389863054910303152161497871008877155327,2261765008336760888047304484487667510155377020971410⟩
def resval1Tail120 : Box := ⟨-69103107436641454284322151034937787839852018553476,7112516426741810419489438542391254578774074622354166⟩
def resval1Tail124 : Box := ⟨-452874124896777785023192074190022631314946322889286,22244590081889444585533209726213026406009155867007677⟩
def resval1Tail128 : Box := ⟨-2967955864923871245745762543677910744666980195514981,68767239652820536282679668587780806473283282310877216⟩
def resval1Tail132 : Box := ⟨-19450795556446235320570458945940201844050410076886655,207267847067603765603483455518436820662016070700504663⟩
def resval1Tail136 : Box := ⟨-127472733843312910176142111849982416524977665932568023,589070136742271227380752090637248841038067083584513124⟩
def resval1Tail140 : Box := ⟨-835406085243015824462250196831093704138668251688213018,1429223874884290479380845905695790128741523308317204983⟩
def resval1Tail144 : Box := ⟨-5781175869660705689146912886882884795794721785401157981,1629590599868790317061441084081507725509640500611265241⟩
def resval1Tail148 : Box := ⟨83866077507110401062069880847615685584675658,1002492114441171205458775588277041431362538⟩
def resval1Tail152 : Box := ⟨1575500010751062157684478618407457860363,4060073391124686114342883333503666778714⟩
def resval1Tail156 : Box := ⟨683404403439086483986521187916274138,12701587728864732095233448503284502401555⟩
def resval1Tail160 : Box := ⟨1018453073523196999674574370922835898,40142768988687418619714116826833099160573⟩
def resval1Tail164 : Box := ⟨6668158494967575816792670327578033511,126867521194267604710002803841379672790620⟩
def resval1Tail168 : Box := ⟨43700398929286189469453425267825072684,400941391855146387662133313600571977831192⟩
def resval1Tail172 : Box := ⟨286394933456965172513900279854720723715,1267024513918469799046364734587761445668463⟩
def resval1Tail176 : Box := ⟨1876917835846479345414024713709653713097,4003451386683796265103114542572124373077046⟩
def resval1Tail180 : Box := ⟨12300568728995060313564768828128842472565,12646514813456538586840788870849426677821435⟩
def resval1Tail184 : Box := ⟨80613007222339148942298490260490564174912,39927494867339346176128095116388021296341021⟩
def resval1Tail188 : Box := ⟨528305404132319843572060126898771546035789,125917072569791030612202022445203919749451251⟩
def resval1Tail192 : Box := ⟨3462302296521570035272807135824721412948493,396167534263038649536192578595611081624593293⟩
def resval1Tail196 : Box := ⟨22690544330483795774246817044276168833578301,1240337087265163354907968038779023869128399760⟩
def resval1Tail200 : Box := ⟨148704751324260668647510104009110665277140921,3843086281866922243972661622963132876312236587⟩
def resval1Tail204 : Box := ⟨974551458278954260475811844948431612299754936,11641479461436622627189770140973878137499943582⟩
def resval1Tail208 : Box := ⟨6386820437114281467437272800641130552721788769,33486067408026201041381200896270307787141649273⟩
def resval1Tail212 : Box := ⟨41856666823153324255738822349970656748951277020,84161349416945834180730081365267814892133468034⟩
def resval1Tail216 : Box := ⟨274331633199990214944465116646866171366406880829,123963764162459048384201314748166401184811746119⟩
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
def polyval1Tail5 : Box := ⟨2245693749357087058841766150074985459184723248582675,123703080589182963401393067825353449206761459455126⟩
def polyval1Tail9 : Box := ⟨232099721276707308149104774845684651592054803996,287397489647026772105547123390462375443184617109033⟩
def polyval1Tail13 : Box := ⟨16289382239739956522246040814813084947042546083,908291369392254674777849438399630939584232828702571⟩
def polyval1Tail17 : Box := ⟨105506981509001917362783966410857542709163676205,2870594645843313813739014793423874616908692654451339⟩
def polyval1Tail21 : Box := ⟨691445962593202318798973378253038110769009935799,9072138664480786215523543417824867582888740311696267⟩
def polyval1Tail25 : Box := ⟨4531460203098417149872970294654819718569140410743,28670092098701817437823831701994327670370996928583601⟩
def polyval1Tail29 : Box := ⟨29697377584955198609874281234049617043589304366555,90596273376483924099332356374413684834609580974868651⟩
def polyval1Tail33 : Box := ⟨194624733740567838465585132047776040366056750606148,286228196414921478477323796911464586822855227249580394⟩
def polyval1Tail37 : Box := ⟨1275492655042141398623094624744261404965951337867552,903962065543198380244844557518548268620881220348357081⟩
def polyval1Tail41 : Box := ⟨8359068664084155947674667473390814967137877441682970,2852638646135293286387903614783901630917337743111562308⟩
def polyval1Tail45 : Box := ⟨54781992396941905578452171109591751454630165125688487,8987383624746769513880729317919748026034900197957452232⟩
def polyval1Tail49 : Box := ⟨359019265372598504553631719532488876685114332111535980,28218689351772958638695345678948145213572525422944783687⟩
def polyval1Tail53 : Box := ⟨2352868657545863963774137787131162924635447523868574667,87966803021333923828596934461565484943352719608237240554⟩
def polyval1Tail57 : Box := ⟨15419760034092771433755472510424842372662216734141933311,270035004778169442542412192501554451295377628198290872750⟩
def polyval1Tail61 : Box := ⟨101054939359477607505917904938110772595720637687612109098,801123082763267107011443366200723002003972465741115096996⟩
def polyval1Tail65 : Box := ⟨662273650635718053759944624172853644399302798059132332423,2189054419324123791568718362377903480695551242131348658198⟩
def polyval1Tail69 : Box := ⟨4340277022293990806779680702630697311729100366454406447465,4671328094115458534781503861766393935784379105183761040681⟩
def polyval1Tail73 : Box := ⟨28656250000000000000000000000000000000000000000000000000000,2⟩
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
def resval2 : Box := ⟨124652512606504749012293177742401674233924899369213724942,197135337583791497652441272886200330285517685079152230⟩
def polyval2 : Box := ⟨3851960772853767427915421096107007253894343436870923634370,7049028022977765540541246054125211512328480529536811789⟩
theorem cell2_lo : Holds Q cell2 (3/4:ℝ) := by norm_num [Holds,Q,cell2]
theorem cell2_hi : Holds Q cell2 (7/8:ℝ) := by norm_num [Holds,Q,cell2]
def resval2Tail4 : Box := ⟨-132565303623769318956103105412542413349907732259423,35900902294098464344461762131750387189084814323950387⟩
def resval2Tail8 : Box := ⟨-456378719871655201797380214122549889667744536612957,61126935588095264132104250143021084014212452145154626⟩
def resval2Tail12 : Box := ⟨-1047224694720445303890708228902475146776355275825409,104011204699410766289072577690027562037966941910032609⟩
def resval2Tail16 : Box := ⟨-2402959214048789518750791952999072883950605790841502,176822083197368839458024798146269184494124592994601444⟩
def resval2Tail20 : Box := ⟨-5513824272751342467905290422516082369343793133719243,300236185605339087211018844397935769171072972145352960⟩
def resval2Tail24 : Box := ⟨-12652007546621684055384205914984468960716112549579395,508944010970937730659470046990423367739851993240034093⟩
def resval2Tail28 : Box := ⟨-29031265241952308271821123069636107667867122322274878,860788514786337333569920513542859358681498862367866851⟩
def resval2Tail32 : Box := ⟨-66615069461734063735504028618178288366760734555178575,1451378191261245686062141321531345308075684349891054430⟩
def resval2Tail36 : Box := ⟨-152854773720955275625841099007574458636961122226559184,2436774712293757367550277266535176014657313483865741000⟩
def resval2Tail40 : Box := ⟨-350740185938045759983973777725087452206665787008818162,4067053389537282430879490754538059772327857816927141770⟩
def resval2Tail44 : Box := ⟨-804807563657987006766763288412447063266568871046322607,6731753238152485407255631214055625250341101337657617134⟩
def resval2Tail48 : Box := ⟨-1846709446163994117623362487330593793779631561272537574,11010330555591813862355604126516729773117872700806616108⟩
def resval2Tail52 : Box := ⟨-4237454930282675786834875939423278909253876329804855333,17696087696619360074639193488058628242043075645425981841⟩
def resval2Tail56 : Box := ⟨-9723253608452228984818342087863585572173451678273002620,27694401785046573667598928681724498769340068773721606652⟩
def resval2Tail60 : Box := ⟨-22310953695007798269392907135648288158403357328907643956,41521914481475833082929039028691187039676773689995402790⟩
def resval2Tail64 : Box := ⟨-51194659175510973597553077676054499428594128898998313296,57701395800880664084168417105098630915156719213182330038⟩
def resval2Tail68 : Box := ⟨-117470737779570679809877217656527767294568134430120547389,68300741543425663830158344754983007378914097832596140066⟩
def resval2Tail72 : Box := ⟨901625771527349584388704342677327305356727720362087528139,1012444388529592821927852372626765505665734528483802299⟩
def resval2Tail76 : Box := ⟨-34300666376267420823192565322928881463869376702408,447739350152430842043879670234683273625791653914337⟩
def resval2Tail80 : Box := ⟨-5267799250798324086678619415562505407295624363605,762410099061734353760243782353402738180068941348905⟩
def resval2Tail84 : Box := ⟨-12083340755025255297458227518678870020580500696407,1297538175458441652658138699182530559350077233619689⟩
def resval2Tail88 : Box := ⟨-27726401389514755766610699869920033181302429602613,2206430085922271200927748927962849312079702131803952⟩
def resval2Tail92 : Box := ⟨-63620932084437206799229507243114601600573945503050,3747751401116938253782055716937826709538052219572061⟩
def resval2Tail96 : Box := ⟨-145984433496153348038799882763992155952688706755118,6356048501444581722792112773218216254902684458742371⟩
def resval2Tail100 : Box := ⟨-334975520241022509678383635140539233460941296063907,10757205613252208195061738706150118537987432835159264⟩
def resval2Tail104 : Box := ⟨-768634000718309803488279269839055538955262211333228,18154137312396339365678680229523679596218991657346839⟩
def resval2Tail108 : Box := ⟨-1763705678060122208385965213443127837409352725321101,30517706774466992719045446585949817324529348518881999⟩
def resval2Tail112 : Box := ⟨-4046994689168732494591911607736287503815848826419721,51023669786279440236217318046708398318872158059067394⟩
def resval2Tail116 : Box := ⟨-9286224009991318686615751469858189268924960389563237,84661898310473369162772479585561063360115134850466191⟩
def resval2Tail120 : Box := ⟨-21308146658688108495113095806152004789209008520140193,138963202372808502009665796052527403649347029170394044⟩
def resval2Tail124 : Box := ⟨-48893620651370190644393580901558643546527597569714247,224522225093323739653115588878619560787396793820805515⟩
def resval2Tail128 : Box := ⟨-112191181086383731176867899195542784965622850194350132,354244180917059418771028536420254553346379885920759883⟩
def resval2Tail132 : Box := ⟨-257433606795251619637050523299889827865917471629351138,538284528467659278749843389241422832153034271921310882⟩
def resval2Tail136 : Box := ⟨-590706517870003298581420871882984838338324212998618384,766753491369953669656481268829760087286293401677110038⟩
def resval2Tail140 : Box := ⟨-1355434329013954082194512372781357814847748848616556169,960333074486468095951816625132112262881690168531063514⟩
def resval2Tail144 : Box := ⟨-3347755344834022070647278257925273855094743606676359233,821043316987033808504586371599384469971968586492089361⟩
def resval2Tail148 : Box := ⟨83588184797742383591851343641965779796061663,62366077237246055090660141114742962482907833⟩
def resval2Tail152 : Box := ⟨792323507466994234967798364422514435430313,104960885697921237629636160834684547139825662⟩
def resval2Tail156 : Box := ⟨1814517510180086833427538805239699476226095,178593139503212368195080343676706254647830516⟩
def resval2Tail160 : Box := ⟨4163586217881610794064208120160199979141891,303603911080525353057297936210279471564812427⟩
def resval2Tail164 : Box := ⟨9553754641433134540251882125750617119201303,515484008344996786556372514782660989173395921⟩
def resval2Tail168 : Box := ⟨21922021784270194731898609091841624275403226,873769222360831971769626925325469311649576562⟩
def resval2Tail172 : Box := ⟨50302216997091228096457673167293891217904637,1477707502294178204086619256244768825756333055⟩
def resval2Tail176 : Box := ⟨115423342779362424916987388098738099542245027,2491293779343519525036753942847979977428041802⟩
def resval2Tail180 : Box := ⟨264850117026304954681044220182370020044205376,4182094211259960960607416374599491766098123478⟩
def resval2Tail184 : Box := ⟨607724423844960662840899023404888436942973842,6978566275305620423310172205098621169271651886⟩
def resval2Tail188 : Box := ⟨1394482960719279506940312515174441458927353644,11547394050409741787862370234718431412336093034⟩
def resval2Tail192 : Box := ⟨3199777154640898492205330837889085127201475149,18878493664844512265240157969697025799878567085⟩
def resval2Tail196 : Box := ⟨7342200749502675849656486118418024312533408675,30322354551043864159066560117209921289972451377⟩
def resval2Tail200 : Box := ⟨16847395690606331039941179450399937012646385730,47406672827110716861489167924023979931860124178⟩
def resval2Tail204 : Box := ⟨38657992506550308250502950946175060212257421482,70956611678609849340766869694174269487289440479⟩
def resval2Tail208 : Box := ⟨88704534046864336354508475630432810187189242364,98293141397807897052138323477797484334865037064⟩
def resval2Tail212 : Box := ⟨203541204879147905801930999126838814857768428620,115468574097924716206802089361535440089901267498⟩
def resval2Tail216 : Box := ⟨467060612271677005270224758245413871123996369845,77170028718483245950034535056685208912172467196⟩
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
def polyval2Tail5 : Box := ⟨23239544077656186036689655278855718283026450662190063,3225942013315492529839723301312478195849569251188494162⟩
def polyval2Tail9 : Box := ⟨48241851256049036852413503588982185015535668019430948,5490939422471320364769024623619106729381301275160167306⟩
def polyval2Tail13 : Box := ⟨110695118508501066958406054172453348410826899658741048,9338903206202987387970522703215413921752342327145266557⟩
def polyval2Tail17 : Box := ⟨254000744880816387812049050916884076333486952322914541,15866596813329680786111317043643939034897947998143651324⟩
def polyval2Tail21 : Box := ⟨582829481336979705700507970749739583270190273131747837,26918198256450378801621923211347043987972679592979309352⟩
def polyval2Tail25 : Box := ⟨1337359087178311889970835928085336725911784227443973666,45578180110646338931390296337680393292795247949509670382⟩
def polyval2Tail29 : Box := ⟨3068700855618424747777487986718321229694015030981457877,76967137775905843712935465645567019676437752309407023679⟩
def polyval2Tail33 : Box := ⟨7041433397773505220418467771754292997966596789217575370,129496173863668978540190763785660766794043770412683840930⟩
def polyval2Tail37 : Box := ⟨16157255668796065886874112698083711854230314869555075935,216769874419862165459526618681376464133119415258001648540⟩
def polyval2Tail41 : Box := ⟨37074398918462903044707215825594232694863264764214332692,360289001682596703614591687806837518432611448938939730389⟩
def polyval2Tail45 : Box := ⟨85070824114015083998421629669695625682597623014658546027,592813594404077439486947619083653576797250823025517081453⟩
def polyval2Tail49 : Box := ⟨195203302725257958324197074564710775292450897396762925070,961237587841217250506330658627196465319121609037823666212⟩
def polyval2Tail53 : Box := ⟨447913015909894808689509510967884932171709184147970229277,1524924088530039577328371479093348297413532487602574916248⟩
def polyval2Tail57 : Box := ⟨1027780099109655517082483330633233108361117342924883667097,2337792903716655028999365074936840424184965978701324252629⟩
def polyval2Tail61 : Box := ⟨2358341674845121327170609709016571569764507790725913667746,3383177283745737895966325348922998874719291512577312072724⟩
def polyval2Tail65 : Box := ⟨5411444977549482548441520768329959675748418033131993332810,4383332887704576792046776022438014788940164370955879846655⟩
def polyval2Tail69 : Box := ⟨12417088605087695614728308185268282725463970705153076472939,4292370316818620647956302250838524471784893119085518918107⟩
def polyval2Tail73 : Box := ⟨28656250000000000000000000000000000000000000000000000000000,2⟩
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
def resval3 : Box := ⟨124466576433557349529003065440480421324400034862907349652,1710887142231336414193909125913696867052169700299613201⟩
def polyval3 : Box := ⟨3871120048397279674528012651613042477392800421175831157671,251631066645318341881653736844226992071021469316476586460⟩
theorem cell3_lo : Holds Q cell3 (7/8:ℝ) := by norm_num [Holds,Q,cell3]
theorem cell3_hi : Holds Q cell3 (15/16:ℝ) := by norm_num [Holds,Q,cell3]
def resval3Tail4 : Box := ⟨-184210677825838289295509510271126483577966670450891620,1992851458364395019555308282209846318230315380063589298⟩
def resval3Tail8 : Box := ⟨-273198270852458284270379081055125946556701996698264552,2545176417269487969058620887163636604741253961224938071⟩
def resval3Tail12 : Box := ⟨-405028777427744536383931526607641683514505832645307399,3243465130587951928811686425610939539519200360599000776⟩
def resval3Tail16 : Box := ⟨-600473440299161809826454868569583774377068180192634731,4122641557354438043467259119778796298880249714400771857⟩
def resval3Tail20 : Box := ⟨-890228972834230533734977492289360373531204447944174020,5224024152819662560838249189197867983833682472497555213⟩
def resval3Tail24 : Box := ⟨-1319804625627758383668624768593239657022133813082170376,6595330047811324384225347952818032987403299570998680782⟩
def resval3Tail28 : Box := ⟨-1956669916373057374422614453999375330526135395592434924,8289774843301090364892333643790346156537473744594985244⟩
def resval3Tail32 : Box := ⟨-2900851449750233656987738615486200472264272050598157064,10363563439533814665665215029830155950554714564485797463⟩
def resval3Tail36 : Box := ⟨-4300643181102420406349928557292700998438128407478818151,12870649543522160154355565577417783712686366867904894533⟩
def resval3Tail40 : Box := ⟨-6375897591293490960433947766709527666214347527301070941,15852998013664464824579656248783810523010090754090390665⟩
def resval3Tail44 : Box := ⟨-9452555904496464031144726978258641092282122145385021009,19323600191632416763763593311967878206825360381556075116⟩
def resval3Tail48 : Box := ⟨-14013840694311432451299385251955452870172096899060303369,23237994681805156798614146934836948342929934073620669670⟩
def resval3Tail52 : Box := ⟨-20776151232506322423383700003257679572463521896182398765,27447775349403342071607964895251798135182026021381277615⟩
def resval3Tail56 : Box := ⟨-30801581768457683599338743082809842715746678711012570231,31626136798891047121637647724312896806667599012422146701⟩
def resval3Tail60 : Box := ⟨-45664734956025989132551611840371907078006941646961486854,35150335938375807620261208786936500870325670802945402109⟩
def resval3Tail64 : Box := ⟨-67700030266233437478230053854894586763785208406609166248,36918171908436197108664966336788387951950941611141539011⟩
def resval3Tail68 : Box := ⟨-100367988092901735758470071871461468844344352207442627465,35063919632819473860067060251644690715544195333431914080⟩
def resval3Tail72 : Box := ⟨902448943096375464891095587383357598946333302145519551532,757420433432844184212319436540050356603242691324705920⟩
def resval3Tail76 : Box := ⟨-2403912556912551587585603345600038075013652686594227,26694359524191876314202580259225463828606232669240107⟩
def resval3Tail80 : Box := ⟨-3516722316291406137895435782570095300384423146910165,34110776369239461797149507692801812990510776800359052⟩
def resval3Tail84 : Box := ⟨-5213696888692222943658396097804025518864591811038578,43496537898871659099154558119216275970504254929471882⟩
def resval3Tail88 : Box := ⟨-7729540914659916085743780785750215021546083145716601,55327722235335740157625752156413866731930110592376676⟩
def resval3Tail92 : Box := ⟨-11459393217303047498512532451967290427980197818477336,70170647233026179880620782741701065200024903488657982⟩
def resval3Tail96 : Box := ⟨-16989067573180572881556056039463581586608591573115777,88684143902429782183314991008833370388238560950689736⟩
def resval3Tail100 : Box := ⟨-25187059343620698774608105487436577781052542041623065,111610957194959057644490167987441919909843290884620352⟩
def resval3Tail104 : Box := ⟨-37340952094424164889165801542334751842922179013593860,139749315794412633372268950505250662188074120990203181⟩
def resval3Tail108 : Box := ⟨-55359646566729366562033341169516834885346907599972473,173890482744140923019732759053497200935839189713477976⟩
def resval3Tail112 : Box := ⟨-82073174252319533920307259179836407102021130767557961,214699891910983089247982778992540982108842094593574024⟩
def resval3Tail116 : Box := ⟨-121677184548715726297964215500134864474673466082858306,262506907581224040865090611955672826837165766881976824⟩
def resval3Tail120 : Box := ⟨-180391917024993095473092686873414835299924042471799537,316949093579011498887148260689232249537392085418042000⟩
def resval3Tail124 : Box := ⟨-267439157543323181822924500737327521794857401879015572,376387814722238206902194671203747869590662017508996156⟩
def resval3Tail128 : Box := ⟨-396490619796301407428037262612336271514750547296738493,436968036092999227493897798934653115886885959024483645⟩
def resval3Tail132 : Box := ⟨-587815236297271829311585075509871527362478528875584020,491128891551896174051434658390468508907698581355593337⟩
def resval3Tail136 : Box := ⟨-871462614236365474671824931308279973251174226309287953,525271852246064625087115641929634557799757430603205126⟩
def resval3Tail140 : Box := ⟨-1291983207017986549116071000826617049402256936109331228,516143538266345214701669425085315105286030716750257914⟩
def resval3Tail144 : Box := ⟨-2129052045658212194712796480534743190522423561917216310,415663551587236003856118090828563070106370662598108988⟩
def resval3Tail148 : Box := ⟨804447600859294670363901021213181635572677673,7049362061229698399678107077697198015487894715⟩
def resval3Tail152 : Box := ⟨1069673247380364458303951954321570152115978935,8989439784201568558619475448004064530407169540⟩
def resval3Tail156 : Box := ⟨1585836590930778016671367924828493005595477424,11436068208912507963152162246792797437406134581⟩
def resval3Tail160 : Box := ⟨2351074309422267705258073148704353829511822727,14506279822509252707247057139831059844233432396⟩
def resval3Tail164 : Box := ⟨3485573760748283000348754878532761016139450072,18336916321033509150716161186095911469813789402⟩
def resval3Tail168 : Box := ⟨5167520393945808044292936563304646009479355634,23082528198639892928612691986995488357626384778⟩
def resval3Tail172 : Box := ⟨7661082178938949978005243244403578620740223858,28909686898862462172685877974269168599736805994⟩
def resval3Tail176 : Box := ⟨11357900052260824770653766925849959496624545357,35984360140979537623672918713982610083697399088⟩
def resval3Tail180 : Box := ⟨16838599375919113610808821480779200677684463640,44447768308509536064458186926947040210193309993⟩
def resval3Tail184 : Box := ⟨24963983450995800075753106539355332827609381938,54373565044149207037413504138763359020432376271⟩
def resval3Tail188 : Box := ⟨37010232016852385488084053708385467254759006268,65695260885425603374654221636731011687216388947⟩
def resval3Tail192 : Box := ⟨54869339127310088872185803248826215587411672239,78086852138738114154601235064826385616898373845⟩
def resval3Tail196 : Box := ⟨81346271347255622281471629389400253905378920129,90770606693470008052444123742948566553954227606⟩
def resval3Tail200 : Box := ⟨120599518188979928361922484774750763133874812562,102212367623898985103315257568444839229517948225⟩
def resval3Tail204 : Box := ⟨178794228014788993852128912174365024335231233322,109644285538452344276416555474470252401702816009⟩
def resval3Tail208 : Box := ⟨265070511486818094274538643326773441984775162908,108324183312787925196496852206422567988321480586⟩
def resval3Tail212 : Box := ⟨392978995421830324185268463289355985194196367221,90394727685868411391511278865341576042383462750⟩
def resval3Tail216 : Box := ⟨582623040664223515041301391867265944660806437476,43135896747221253314089739135724344056677259320⟩
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
def polyval3Tail5 : Box := ⟨35307910363538199178979888700014430324261844829199017405,318795048315276365013743852552845491543989174942099657329⟩
def polyval3Tail9 : Box := ⟨52342307857876907057145218858124276052741925332348649093,406054669154873414078789420999888616211278431237790864893⟩
def polyval3Tail13 : Box := ⟨77599833124669977554188886941587774954349285356795165642,515812596917978563701452998873945783486302101347844556294⟩
def polyval3Tail17 : Box := ⟨115045254458051074280232939485389744049916818912475127583,653149847078009636448946982777109053699168561691978481231⟩
def polyval3Tail21 : Box := ⟨170559781386188348398480473066023390140135650579487237974,823898177611682890110280029451442859165118992580390239067⟩
def polyval3Tail25 : Box := ⟨252862572763588765053486240124114970987794235116540293252,1034501314661290029175103077997327903997249276940931339966⟩
def polyval3Tail29 : Box := ⟨374880175062178755855717422280806045509063609757611251723,1291661646691438165431885847783698526648889190752695295358⟩
def polyval3Tail33 : Box := ⟨555776776763406836994115807972699539805611723878051886024,1601625392726865529463495357048953879521474461615158898564⟩
def polyval3Tail37 : Box := ⟨823964152114175394933242517362024952061620427473992290267,1968875523534505885222428898213357980651851145452115360367⟩
def polyval3Tail41 : Box := ⟨1221564038574871343804180932563516395732525582352364010707,2393873808009068930294435488605028494754980265022083826276⟩
def polyval3Tail45 : Box := ⟨1811023812759969933034874791002255084888074265275051281285,2869298848251884087778546351399570245328463000668527396146⟩
def polyval3Tail49 : Box := ⟨2684924528565871602057923172684374090217565825795931716372,3373932279573839313745987387304752049342000080942520712826⟩
def polyval3Tail53 : Box := ⟨3980521776303177072166532221595564488346737517906254358001,3862900244007817390872895725788057422229008559918475712281⟩
def polyval3Tail57 : Box := ⟨5901303162546258585178773578227313947908948241104650163059,4252306823095249380196503364971553792535644932573407600700⟩
def polyval3Tail61 : Box := ⟨8748948246835601855692530035972244890997311827868713580879,4395288474527431599246560839562465810408535894091765602017⟩
def polyval3Tail65 : Box := ⟨12970710590132703327346382257390658054097765904406386981182,4045006896740888928997052831777806749120114971798879230988⟩
def polyval3Tail69 : Box := ⟨19229664083908340417164579484828283501843592124804865704111,2797833709253586601163932252660487932200721567285554839376⟩
def polyval3Tail73 : Box := ⟨28656250000000000000000000000000000000000000000000000000000,2⟩
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
def resval4 : Box := ⟨121494067070139271692016018003271526645187366563282139140,8401651035359535347006771584709004561332107614032638903⟩
def polyval4 : Box := ⟨4744233880125210851353595052786107812348167694615632054489,2001892557080784273680413068058276100282113510916542657341⟩
theorem cell4_lo : Holds Q cell4 (15/16:ℝ) := by norm_num [Holds,Q,cell4]
theorem cell4_hi : Holds Q cell4 (31/32:ℝ) := by norm_num [Holds,Q,cell4]
def resval4Tail4 : Box := ⟨-3715135873700197540588924040303039574295298991786507015,9142712302303583219442806446227171632553524239305191781⟩
def resval4Tail8 : Box := ⟨-4501766117717060243642443410940019979935414970851580076,10097251375497120733035580532496704765642292312763920798⟩
def resval4Tail12 : Box := ⟨-5454858442783595180035466512993213427865558280728245005,11121028164503931401106001015305723301954680608049996838⟩
def resval4Tail16 : Box := ⟨-6609734890364069153820136968460135828823454857549878188,12210710854920578802286499715861645729801437931742669039⟩
def resval4Tail20 : Box := ⟨-8009116236303366186930270120201189325423139062815568539,13359826882269602911975072631049376564756552549269196944⟩
def resval4Tail24 : Box := ⟨-9704767884129871437857626782802610686966401983631795867,14557767455619598336848167989219157666699200980102669598⟩
def resval4Tail28 : Box := ⟨-11759414760136984488154924979043766059318092239692810115,15788537323695586763028586082802818886546220458268250648⟩
def resval4Tail32 : Box := ⟨-14249061610949192495558026335913298052916817869971205220,17029189131867508189802658568620367812647028273475731159⟩
def resval4Tail36 : Box := ⟨-17265804543342839739934948528171875966492702782748068513,18247868725483494190755110513705199561245132414686654369⟩
def resval4Tail40 : Box := ⟨-20921237809783037691144355315150466234544850252679670607,19401381233566103181107793853448479236448287802099240789⟩
def resval4Tail44 : Box := ⟨-25350581862242743973521953228004794529766930899770663574,20432167621525214456972773874105166171366506999247513579⟩
def resval4Tail48 : Box := ⟨-30717685377762806884408040080033473803816524592069928688,21264556848122116968082348209445065772015872311766999481⟩
def resval4Tail52 : Box := ⟨-37221086288855129920457608610197854733092903785125460052,21800128847833163483289649097833311802297764331641217880⟩
def resval4Tail56 : Box := ⟨-45101356026171348380905038961291026336971233235736821341,21911987128091546961579237129888484902330738796738306448⟩
def resval4Tail60 : Box := ⟨-54649998648966440020039981480193719686140003375260108869,21437695416801829248170123416912712314153855363868694987⟩
def resval4Tail64 : Box := ⟨-66220234037171395752984945653912949578115133113602298176,20170578813026636826511103601006493703640672327957982443⟩
def resval4Tail68 : Box := ⟨-80239718956239477794732890505304385907727463576091247947,17849021416347013353281725628053497453255896931377385232⟩
def resval4Tail72 : Box := ⟨902821313959296724194434684125130324375738160672194892352,712131564132059897884915845490119912595245489707984376⟩
def resval4Tail76 : Box := ⟨-50310921412995281837858026613883363293358868773647209,126855912170629698123875592942280681072030480347086350⟩
def resval4Tail80 : Box := ⟨-60924047800421920843466802679072516240165215415914663,140196960236950814341465781711462724748560769375957269⟩
def resval4Tail84 : Box := ⟨-73822592631188626865332720391666483953651578297437601,154532431506558477772672189374163073109919223308410236⟩
def resval4Tail88 : Box := ⟨-89451957612114203473985068378106754292914386159338672,169824872897598150269298580168418211594335950765720074⟩
def resval4Tail92 : Box := ⟨-108390296731071438025122450553011353429872631548117752,185995496151330796100331858048612152123100500447767487⟩
def resval4Tail96 : Box := ⟨-131338170109080331847321542507705002915232145573614214,202910728570492491158475994833465735060657311064963797⟩
def resval4Tail100 : Box := ⟨-159144457094717776561499225209773034506327489451237555,220365454625569852523222731424317305291881722765258495⟩
def resval4Tail104 : Box := ⟨-192837757697839560293427130270526950255569685501361734,238062010896499194193401458493333865985971585453924083⟩
def resval4Tail108 : Box := ⟨-233664442185369385379290674769707670272648069477827681,255583940638169390472284398912306185322464598711166193⟩
def resval4Tail112 : Box := ⟨-283134756354883334157811585103975730137642014720930250,272363291082668162154933039779267867408255425193941994⟩
def resval4Tail116 : Box := ⟨-343078687995424066492422752351478360325306886417086967,287639964411914800529986116616302961259635676226493722⟩
def resval4Tail120 : Box := ⟨-415713661127253778078634517407172562424385865173381164,300411301560847261299706993445394589079542745275775967⟩
def resval4Tail124 : Box := ⟨-503726562141132502144097234932839944304526497440794576,309369673759987493208443640545731327999139882306128074⟩
def resval4Tail128 : Box := ⟨-610373132118100041333191196832816597424155488907189510,312825364349498466078223537866828273208966172228879242⟩
def resval4Tail132 : Box := ⟨-739598402014202916989021822919534225740887756079995753,308611423893448997693442627670946561442699255404682291⟩
def resval4Tail136 : Box := ⟨-896182625863837703235187424315317490199372633932634774,293966451919212999244329795986622889334162161646575678⟩
def resval4Tail140 : Box := ⟨-1085918639627323465332128648424501011957268448156199314,265390348673424511591337079202529133830559731574917791⟩
def resval4Tail144 : Box := ⟨-1519201908781525302727365106876799185272179205349292030,212697029215809044518327744419145691670312083780910739⟩
def resval4Tail148 : Box := ⟨24736508224277259370243749792620233539128235762,52543166380869530342932158793028972529386159818⟩
def resval4Tail152 : Box := ⟨29873292416139149597162161253831026832510002941,57776346950889489251063934265826487478824602310⟩
def resval4Tail156 : Box := ⟨36197920656069955107578779447864540579249489836,63320451568830566789813179431134903445743082710⟩
def resval4Tail160 : Box := ⟨43861570675940898946732376378087833467814157857,69132694396064894582333333020574332627046068145⟩
def resval4Tail164 : Box := ⟨53147731895051467643469597360004584545664037272,75147211579046662345629368098637039092275188346⟩
def resval4Tail168 : Box := ⟨64399914596258017175601766082355024250374531882,81267589064509755420532051439591602677430025914⟩
def resval4Tail172 : Box := ⟨78034355411345077829136988526524261398356437345,87358146024565126463426565123770647447534153485⟩
def resval4Tail176 : Box := ⟨94555414593949563710926245139726119522760860067,93233068381165218052083470450693642712134974514⟩
def resval4Tail180 : Box := ⟨114574233129807291840935913638316982897151404373,98642896014103845427146249754131580813303106832⟩
def resval4Tail184 : Box := ⟨138831339840832562903791909973487541172714544983,103257756573007257383812386002893205266709564933⟩
def resval4Tail188 : Box := ⟨168224044756765120130660179204603420063915312081,106646603946662851077458392353785157288573255427⟩
def resval4Tail192 : Box := ⟨203839632079980976362499625531537474153199608993,108251555164105176892112408805123263816724218898⟩
def resval4Tail196 : Box := ⟨246995580605495189275659342474505172897323991850,107356219467978919351198576848704275233418480184⟩
def resval4Tail200 : Box := ⟨299288299415239825633750048073059024656941162821,103046669809978862892404018259763523624826248042⟩
def resval4Tail204 : Box := ⟨362652181659615707610107454446527211596302722432,94163410720311868122800853313513770896881308983⟩
def resval4Tail208 : Box := ⟨439431160922328837640854220125440857713551798469,79242336047919542537346396206053471496799139856⟩
def resval4Tail212 : Box := ⟨532465417436173923354635983957223522862791889492,56442231665571361415080488171735382428114388054⟩
def resval4Tail216 : Box := ⟨645209732459054562243973933624261819047382251914,23455302739831900750924990222056155679197657748⟩
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
def polyval4Tail5 : Box := ⟨1089630675384882773305719200407034104298618816484026498521,2203013613208101492443245595484316540274254345227982346105⟩
def polyval4Tail9 : Box := ⟨1320319394287995111665918467362756413961039032892413254820,2418183000337978396340154365673539367533094403339129191275⟩
def polyval4Tail13 : Box := ⟨1599851078982269354922822102728823075322116286776579950249,2644886059333647629629533629268948767943954216848407116174⟩
def polyval4Tail17 : Box := ⟨1938563870545356824412782949811029480415147542698494414449,2880957818237638892149475453141024612763129043039517773054⟩
def polyval4Tail21 : Box := ⟨2348987308603029492067712134345887277811998277171516701222,3123151142322632002767397382657639791930460691144573701356⟩
def polyval4Tail25 : Box := ⟨2846303627038016969346279711285486488704567122352059596726,3366823143569068759338756003864330333953969813944081709908⟩
def polyval4Tail29 : Box := ⟨3448909369420048294789576472773559560943163725642329944019,3605543768750167135886139006856675947870744764772462689191⟩
def polyval4Tail33 : Box := ⟨4179095907224699819371976626975551032504498967583866575466,3830608532425261378491114181512576596807758078189613872242⟩
def polyval4Tail37 : Box := ⟨5063874034103435782969647094006479858872820631361326278484,4030433342242524636995178106906296876155843324253998133973⟩
def polyval4Tail41 : Box := ⟨6135973139294659564053723169960939482450229164704189580314,4189804456947701782710330485834217033120832043023384197832⟩
def polyval4Tail45 : Box := ⟨7435051921233574121841149832527304053280112561973249177404,4288950639355118816978384673034509787075170157623612521864⟩
def polyval4Tail49 : Box := ⟨9009165427636404281659923757496842100157956549444746405627,4302397286120889041501676656280665022927869509860544300041⟩
def polyval4Tail53 : Box := ⟨10916542690269830783903176499261848579267099816653892031259,4197553452796507291431682156307710920959287852826329792933⟩
def polyval4Tail57 : Box := ⟨13227740712021613678485070625167280494820381865314446735014,3932971905571195418296718913104422122935205249198804295864⟩
def polyval4Tail61 : Box := ⟨16028254485775251395427077406180976620711362148153614327659,3456209206663824368675263303687608985275666657103454240150⟩
def polyval4Tail65 : Box := ⟨19421679593988062816451067912195748401926395619356558999506,2701196876383105727694763862063715880942799738670132622148⟩
def polyval4Tail69 : Box := ⟨23533544668924173349696484509335364139504048654469941879603,1585015250683920891014692037326436892504832685223404292043⟩
def polyval4Tail73 : Box := ⟨28656250000000000000000000000000000000000000000000000000000,2⟩
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
def resval5 : Box := ⟨111238927862460904511070577132500583590758326027623166295,12906633384270885956548136960517997375270108215255830580⟩
def polyval5 : Box := ⟨9014437001843005522290596498292747306213035963766011268503,4008827816156996276408700183276677348153139810843168124320⟩
theorem cell5_lo : Holds Q cell5 (31/32:ℝ) := by norm_num [Holds,Q,cell5]
theorem cell5_hi : Holds Q cell5 (63/64:ℝ) := by norm_num [Holds,Q,cell5]
def resval5Tail4 : Box := ⟨-14629892177151186206559585307114338369553411665369810003,13139682334151810042299915424100448123525536904634048862⟩
def resval5Tail8 : Box := ⟨-16085808579469181355680659800228498091368182890512400621,13489408428336279309796379014444973303676929095789189399⟩
def resval5Tail12 : Box := ⟨-17686533584312724112739546830158651562181289533312841884,13811659302871106923807350791455339152966283917319547818⟩
def resval5Tail16 : Box := ⟨-19446549331011011019365193719589458177645128745530472632,14099651010504004739103292026709497404334866641519981654⟩
def resval5Tail20 : Box := ⟨-21381707109566235009580886312296947117305144301458573926,14345661802784382492949261114970599442925324930164962193⟩
def resval5Tail24 : Box := ⟨-23509435588668843505901186097985128971482996917987822138,14540921125487395717945970964293060235757075229605927128⟩
def resval5Tail28 : Box := ⟨-25848897792192304922039057353547942162057449379056134207,14675487018412474932256761617508981539415775661656357559⟩
def resval5Tail32 : Box := ⟨-28421163687708813770058495146414131959350958936155243863,14738110129742742306865026183144774772952074850772983168⟩
def resval5Tail36 : Box := ⟨-31249399949560860752451817960120041742302685113825946947,14716082935753800144678134557824871171607857929962173120⟩
def resval5Tail40 : Box := ⟨-34359078605564914302150921288692725624439675223289601475,14595072611544510004415336919776870260290974043937651867⟩
def resval5Tail44 : Box := ⟨-37778206446488215174954353835681487667947699521655005457,14358935838451594375761438251499336677276680639066101729⟩
def resval5Tail48 : Box := ⟨-41537577264436034088442758798744538296942040231239683568,13989513657528968651370796792182349609736146164734144984⟩
def resval5Tail52 : Box := ⟨-45671049191891432539477683621423953330865397065719553069,13466404284280189223951369546697299585072989316084101815⟩
def resval5Tail56 : Box := ⟨-50215849639214277273039288481393896681466377315160601475,12766711585921839526776172838050281143028120396074172733⟩
def resval5Tail60 : Box := ⟨-55212910576955014068327615357990702574762431965284371303,11864766686838847490826596402410427962802434464535364789⟩
def resval5Tail64 : Box := ⟨-60707237163491486406136314751766811950071112580913839118,10731819907887028268871669319360087717756290641853230467⟩
def resval5Tail68 : Box := ⟨-66747975740016349165398770801176647184704868809166636866,9335694590412527043516555114559344755398583539416819471⟩
def resval5Tail72 : Box := ⟨902884791398460911240885459540376016501038743212768130697,706919271685478039096331810295873370449940657517718220⟩
def resval5Tail76 : Box := ⟨-202473166470369749835862958372250127504610553594904944,185070725052523129343228173092149237747941340262471321⟩
def resval5Tail80 : Box := ⟨-222586749747351421795364724229900298517170551372043258,190121274922441184654766297059442803436201297803116607⟩
def resval5Tail84 : Box := ⟨-244736717590866586354687592286242830426903760375029304,194805514808381116591672217101608317499968968035891112⟩
def resval5Tail88 : Box := ⟨-269090866733754182839293518061938359045494527483803578,199030331183690523018797669856104983668620103742690458⟩
def resval5Tail92 : Box := ⟨-295868536902081537290581577082893016657540521942652032,202689826293235827454849338588292368430630411681527849⟩
def resval5Tail96 : Box := ⟨-325310896616911163163763128904732814054079840826995600,205663651465464531672613276558707603710024484187784025⟩
def resval5Tail100 : Box := ⟨-357683113472530043556289166851656837466347644352899030,207815314643962012144135951058234768227717647672991934⟩
def resval5Tail104 : Box := ⟨-393276742322169223983024893403260751233666888387669047,208990302976226447765724365138200068105578795772990366⟩
def resval5Tail108 : Box := ⟨-432412351117090793663390645155598476051607318015849035,209014000960653107195453032025965125269576043707963374⟩
def resval5Tail112 : Box := ⟨-475442408047199750515579042633753745585279735405050151,207689382661883971419800252268297800297718855086110795⟩
def resval5Tail116 : Box := ⟨-522754455985717799147784898073395053527587855777089838,204794454291727232630018382122322139893431323244712644⟩
def resval5Tail120 : Box := ⟨-574774602828013924150187407930902894412551363041496955,200079421014825223932556182795263232292363070722913751⟩
def resval5Tail124 : Box := ⟨-631971359159733487213788842731070254643282911051484194,193263549152453821853951104031003613064179484601767041⟩
def resval5Tail128 : Box := ⟨-694859857817529972724788501894291459324531093192969351,184031691999280085108814561699255131210114209538701283⟩
def resval5Tail132 : Box := ⟨-764006493345211209818924708794803316393155180299497781,172030444209084743477890314468672430692353198962372261⟩
def resval5Tail136 : Box := ⟨-840034023187851461866760325757749077048266417968734853,156863886113620397737018923751155884399802802142005907⟩
def resval5Tail140 : Box := ⟨-923627694119004240290524334983731908158588588184973798,138088857700599047926917884402110842575373664154316111⟩
def resval5Tail144 : Box := ⟨-1214152104758352916385926455199829830250599175449352058,111144610588120159015450992001933833771895123809655738⟩
def resval5Tail148 : Box := ⟨135176516678102754545223625048716397523704220646,101592210184311790636842824089537168028215264041⟩
def resval5Tail152 : Box := ⟨148537213308663816913717904830679363398292502433,103537532579686027199058655022312437325144530050⟩
def resval5Tail156 : Box := ⟨163318391519004508071392448236823967034961626486,105146212318877715346925498840686227701678122273⟩
def resval5Tail160 : Box := ⟨179570470504269777127121590780845953291002374908,106349658856430362060966478117246239839295668890⟩
def resval5Tail164 : Box := ⟨197439820324650870157968861673869822941249289515,107070790031865134184557065068963863814243527575⟩
def resval5Tail168 : Box := ⟨217087378232957840329686817458549043213617635409,107222463214824954704517257223346113926292453030⟩
def resval5Tail172 : Box := ⟨238690096610543665414078664431812749720958518344,106706318761474628236255501754024954632151967293⟩
def resval5Tail176 : Box := ⟨262442536658269565876367619798524263672010788849,105411498295671554678754279650274782422545859752⟩
def resval5Tail180 : Box := ⟨288558620678796521827270622859253573025654923237,103213224683724227815936093458814137491081133293⟩
def resval5Tail184 : Box := ⟨317273558731340897762892370953447396983715482027,99971229239987725550739292478448354093645377467⟩
def resval5Tail188 : Box := ⟨348845967010980967966801558508002586144908760007,95528010215851633238726658504783437442277809986⟩
def resval5Tail192 : Box := ⟨383560197031336481358799798637769549021201904566,89706904989271044191942694302452283992174880333⟩
def resval5Tail196 : Box := ⟨421728896588008057546284254575657275184862945282,82309956570694544970067328826318633917383689943⟩
def resval5Tail200 : Box := ⟨463695825567657113584646180476576921743510204688,73115553057341441790037929999653866227875288270⟩
def resval5Tail204 : Box := ⟨509838951962831042288669153585138133044395675020,61875816482884455381868782146077450780063492478⟩
def resval5Tail208 : Box := ⟨560573855976359004379639968669939302593339485416,48313715103465169662346650548562939329169709950⟩
def resval5Tail212 : Box := ⟨616357473148500590202086539460325734604217811691,32119870499817282972544454258706725405440330625⟩
def resval5Tail216 : Box := ⟨677705196866657285632729388456830375858171223018,12948597235767656234234903097627286406782594362⟩
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
def polyval5Tail5 : Box := ⟨5685142044812543510054190258632195164165210910790422853614,4089467538819768918575660569045719792123352812528193814516⟩
def polyval5Tail9 : Box := ⟨6250877376188545169982052648654367508087582398768061786423,4159273415109532446050572088053377335218860983248508905750⟩
def polyval5Tail13 : Box := ⟨6872912358680007485464773211014132785565571453011955136726,4214104768732625841993296487691860375027293423810245817202⟩
def polyval5Tail17 : Box := ⟨7556847055053846904252442020220362601037516216337284193820,4251046149423599550083519174090803485971921438640074498031⟩
def polyval5Tail21 : Box := ⟨8308841206356526395397443781880163871259195902278677836203,4266799322205073886793653862843903298134924952463420503712⟩
def polyval5Tail25 : Box := ⟨9135667519733367846772153633507386452921996560815085571035,4257639140902187405786139247070877290906672862260214165007⟩
def polyval5Tail29 : Box := ⟨10044772665442367882422695963918547588227642998513112063035,4219364648153559114891196317674335117070157513964205481383⟩
def polyval5Tail33 : Box := ⟨11044344344020408173495376519350095562941854685760698654582,4147244892051375661542499266772888791612205097639083901348⟩
def polyval5Tail37 : Box := ⟨12143385027412537923000497838648811125713340616989576214243,4035958906521616354768347336787900063755596588916989939311⟩
def polyval5Tail41 : Box := ⟨13351793038201065953190440828560451677062646826712302941143,3879529245774818713536885116939584635202901659968167289903⟩
def polyval5Tail45 : Box := ⟨14680451697160718576980671680004071010891148749356016333863,3671248400609900917658974855933437218317720712886060382797⟩
def polyval5Tail49 : Box := ⟨16141327342032123480166141871449745543845147813392433156651,3403597355459275230007577502961980024696296918645169585165⟩
def polyval5Tail53 : Box := ⟨17747577100302995593793683735378807422810688072945511855673,3068155469183328554242080869179267283925165087328954216055⟩
def polyval5Tail57 : Box := ⟨19513667386634208865192054605149001780487324820800375089435,2655500779052678290647184346171868785141711447326447858779⟩
def polyval5Tail61 : Box := ⟨21455504192157657171289363406342014599120732250935739888136,2155099735323227513636064432522827030489216277504618074342⟩
def polyval5Tail65 : Box := ⟨23590576339108215251173459479533284308307780286808443416321,1555185272458712980250044990977679360100695773871331850259⟩
def polyval5Tail69 : Box := ⟨25938113274772854612475301814588396799713513281420221357986,842622002463940748759418278417964765429975471842479672183⟩
def polyval5Tail73 : Box := ⟨28656250000000000000000000000000000000000000000000000000000,2⟩
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
def resval6 : Box := ⟨98001412934176379273893807402215254191021069643613497394,11279643977724348494347258620813595676849292900823820933⟩
def polyval6 : Box := ⟨16048949059604983988587067848256662592538967793014093363497,4012153982728635775831173334651256384521548598021167865063⟩
theorem cell6_lo : Holds Q cell6 (63/64:ℝ) := by norm_num [Holds,Q,cell6]
theorem cell6_hi : Holds Q cell6 (127/128:ℝ) := by norm_num [Holds,Q,cell6]
def resval6Tail4 : Box := ⟨-27816832128893181826772049302969432549192586638739933077,11063634858755416949844264856953122554409013867258064914⟩
def resval6Tail8 : Box := ⟨-29159929379788278461441790192482051920177260399489686726,10959725898319523832196045651645507626795134916023388482⟩
def resval6Tail12 : Box := ⟨-30567804318462900285010075798052153961576949649368088136,10830465197712524747336933931651889686968986448711768998⟩
def resval6Tail16 : Box := ⟨-32043653069942902884192967740987302252380642020506965589,10673980137759660124264608432031918553937828430213455011⟩
def resval6Tail20 : Box := ⟨-33590757496652197759995166523694490618042819658516112699,10488287550254566471088777612713266813503902030911678926⟩
def resval6Tail24 : Box := ⟨-35212557904556831286705408796118809228389880104071388445,10271287204560595255468446290288864924488129499857723253⟩
def resval6Tail28 : Box := ⟨-36912660701543990311761183018927248390935359529961795334,10020755476340320422129744491240899680918148146300405187⟩
def resval6Tail32 : Box := ⟨-38694846417021700762320914599065673995683077607851878730,9734338689075303432471975889620315728006529559863343900⟩
def resval6Tail36 : Box := ⟨-40563078108706158739560813678129489290047755912198512217,9409546111769548470156125555098628507411941015945143830⟩
def resval6Tail40 : Box := ⟨-42521510175298392751921307084814822350799357713409970563,9043742595524747140061818991038080928129852076915121186⟩
def resval6Tail44 : Box := ⟨-44574497594647091135133647309260453284361985222314847009,8634140830817045378860194975393886719328049048645697908⟩
def resval6Tail48 : Box := ⟨-46726605607940556457927873318418963937390399789088385943,8177793206404373644785210171430999127595337789164220498⟩
def resval6Tail52 : Box := ⟨-48982619871462585789468542998312728737800930852848370952,7671583249848456379564387052536716356647346512013713112⟩
def resval6Tail56 : Box := ⟨-51347557098486762932538230505457310135135660214986175380,7112216628644297586588987940584688690907679304635767425⟩
def resval6Tail60 : Box := ⟨-53826676214961627025210476593274902014419509165092359625,6496211689909472687263759579862571401311290022593418874⟩
def resval6Tail64 : Box := ⟨-56425490034839619598291132648224392293460825820291223747,5819889514935813208700511858911523140799631973927609641⟩
def resval6Tail68 : Box := ⟨-59149443942415668125363400834704412611679638942789383904,5079356880696138953722576256150612739802002433237673093⟩
def resval6Tail72 : Box := ⟨902801651151383032168049926216463805824321751955479716360,650577258418772536179556671531440462673954861318049099⟩
def resval6Tail76 : Box := ⟨-388213930491536019482353696343928634725330235702536475,156748425746700373748319928085554263602263589073825942⟩
def resval6Tail80 : Box := ⟨-406924141115191286684311981416118987706207645967535105,155373338191545643837685064778228709912864909409806938⟩
def resval6Tail84 : Box := ⟨-426570904838839779862756410425247170058002892555048822,153647004728230652373703607586052519579126048507532150⟩
def resval6Tail88 : Box := ⟨-447166238763671995057666304642591278845854235546402002,151543227381826108574417872040392155984837747836890585⟩
def resval6Tail92 : Box := ⟨-468755939100149350784497622556203694018651585759244657,149034409909125626394304076839659463848724261133853689⟩
def resval6Tail96 : Box := ⟨-491388015001269123022113652081908208165870295617574638,146091324996758622667951563854521442728464650579583703⟩
def resval6Tail100 : Box := ⟨-515112793558225811491229904319726182331029360486550106,142683025971839452369015520900696150751904755708361049⟩
def resval6Tail104 : Box := ⟨-539983031712065786965379258408509278917184895623811626,138776753965959288307871686323427756924391206944677358⟩
def resval6Tail108 : Box := ⟨-566054033569630007488459884292418396141645905802103864,134337840283896463032419186532129605258474018210171664⟩
def resval6Tail112 : Box := ⟨-593383773383648294452854504840608148311785462546452201,129329603735528476604599138520414197538563127305381697⟩
def resval6Tail116 : Box := ⟨-622033024470454038272685153736081627750165191858097779,123713242677467655365258649648639512033340947269506471⟩
def resval6Tail120 : Box := ⟨-652065494351994451503416722726947100006306227358940830,117447721498376186458829586801135490574368246884077460⟩
def resval6Tail124 : Box := ⟨-683547966422652520499778093677380213485750473679963929,110489651268732753975210001767111695048374338319884428⟩
def resval6Tail128 : Box := ⟨-716550448455906321366258782893145550383703691842086926,102793164261992181428886527576105324523863569155636360⟩
def resval6Tail132 : Box := ⟨-751146328281117677431831024848352479265346016316500524,94309782039566866122560189983167846485740720182220056⟩
def resval6Tail136 : Box := ⟨-787412537034111058994834912395025273387726051579646492,84988276774562423461728360042596371776009009198130630⟩
def resval6Tail140 : Box := ⟨-825430232207597235905964013571370053205552517197173533,74774509845976944417396750713982663911294798253261546⟩
def resval6Tail144 : Box := ⟨-1061595915761424791567344066699628123219097381367742043,60351078594102846106425821843878587518339472221279104⟩
def resval6Tail148 : Box := ⟨311532342561514565438121299868331799491614527312,100240263236910028131149319467531240328417716313⟩
def resval6Tail152 : Box := ⟨326486820645994356049776198960979842833685128366,98323125808598459133883960312629648623445145971⟩
def resval6Tail156 : Box := ⟨342249978279152015054837146502343780999806519221,96098668225472709886552127916440385470983913089⟩
def resval6Tail160 : Box := ⟨358774200884618786365052540462812059539486347266,93544625899576498160831156386446212677219379571⟩
def resval6Tail164 : Box := ⟨376096231964099286164716312113378411021934308321,90638005029851430123426093879127533360596720652⟩
def resval6Tail168 : Box := ⟨394254590627834752839060976296109190425043871816,87354475992466020843647913173904704993345302622⟩
def resval6Tail172 : Box := ⟨413289655733533014099595486331738466636125194628,83668301635862948223555423681451320508285952965⟩
def resval6Tail176 : Box := ⟨433243755676596566654401523930410715094477367305,79552261902263978040946192496178382475269155799⟩
def resval6Tail180 : Box := ⟨454161262516043911127470229316278438323702845582,74977574573302266391772947220471237124095664646⟩
def resval6Tail184 : Box := ⟨476088690644939541259881091513264421475494226072,69913811945103641310214554793367212442849915765⟩
def resval6Tail188 : Box := ⟨499074800224745789125122634941837681722889105709,64328813228507790574645212638597899224950819794⟩
def resval6Tail192 : Box := ⟨523170705613604147348403008833725226637025673448,58188592460008137253724860612041670429988955172⟩
def resval6Tail196 : Box := ⟨548429989029658727413479956644153885690437668034,51457241698380891111919473927411822164191174739⟩
def resval6Tail200 : Box := ⟨574908819702175711247342610625919410424714535077,44096829270845137594561479813776293046149249065⟩
def resval6Tail204 : Box := ⟨602666078775416096900214849804109614401779292276,36067292820921472774443370776179224066702541728⟩
def resval6Tail208 : Box := ⟨631763490243105877992222345867501822967744232134,27326326897905424934715719518890022125372334457⟩
def resval6Tail212 : Box := ⟨662265758476426549667786540099420128656193061142,17829264804571241811782009116882018548256211538⟩
def resval6Tail216 : Box := ⟨694253552336823916237478865326326454194560770632,7528576546776894520386728252351928487625964121⟩
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
def polyval6Tail5 : Box := ⟨12795001781503297656691890668799648769220547242280968166787,3937894569027774145039107184727644815630680614832910290314⟩
def polyval6Tail9 : Box := ⟨13412756890717527841915806135627859743572349711064415721727,3853414939759454599057613009180161511060977171236929565081⟩
def polyval6Tail13 : Box := ⟨14060340220475579989109898812201053801916065007849251380139,3756104857203543173618371306893999703180762445582334865228⟩
def polyval6Tail17 : Box := ⟨14739189618471788161595683836884951268149594575913357822329,3645065926218453676369061123765638202781649705319016952467⟩
def polyval6Tail21 : Box := ⟨15450814646213530417585351904364558259045921386953422432505,3519347496620898647891035842168844674821854475692855101958⟩
def polyval6Tail25 : Box := ⟨16196797748803145621738658203003668262691673786114021399943,3377943847375639766224832166313069689230645179817088369955⟩
def polyval6Tail29 : Box := ⟨16978797773612820301407739609611082067850588251883268324716,3219791235385524250580649292383485151706141089618595677954⟩
def polyval6Tail33 : Box := ⟨17798553659073870965929306440146807194946864674977821511522,3043764792479619705639160994843356399673268927734957852017⟩
def polyval6Tail37 : Box := ⟨18657888301565198708760838082540414688044069452143312840296,2848675262971097761837022048232425728393460628166199172772⟩
def polyval6Tail41 : Box := ⟨19558712608999566708022654541972749721200851938892548562261,2633265573781012545332739065412989723039267845807935775550⟩
def polyval6Tail45 : Box := ⟨20503029750121685631705255473497976987487208885906607230041,2396207228727923420286349445730960051012032549499842323811⟩
def polyval6Tail49 : Box := ⟨21492939608967298133592085654623113259595738095884309333764,2136096518167671989881868948182109310905230486860004718016⟩
def polyval6Tail53 : Box := ⟨22530643454388671453168689163110930137872809956942757632116,1851450534731595218831501280810451581097173421909306841640⟩
def polyval6Tail57 : Box := ⟨23618448835030151813992490968046972315379829779331544572298,1540702985454045132148225067763106926962833061797062226358⟩
def polyval6Tail61 : Box := ⟨24758774710638801929270856565251870445561718017585321517657,1202199790100246266107527303407183696112277324147089858670⟩
def polyval6Tail65 : Box := ⟨25954156831154257311344638272494044754443991185292291113155,834194455000893223314915060684022299600762518146872189485⟩
def polyval6Tail69 : Box := ⟨27207253656210478079686113062327743687539501548819539694921,434843203302486919423264521979476310741948422588391623306⟩
def polyval6Tail73 : Box := ⟨28656250000000000000000000000000000000000000000000000000000,2⟩
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
def resval7 : Box := ⟨83305076592266467137152366079210099847063115238475719605,17916873510861348034093807389741607423399429769699179773⟩
def polyval7 : Box := ⟨25360469585037722356627723737706333546515509217315514326188,7008233214246406981291085278080689211330606232433893916786⟩
theorem cell7_lo : Holds Q cell7 (127/128:ℝ) := by norm_num [Holds,Q,cell7]
theorem cell7_hi : Holds Q cell7 (1/1:ℝ) := by norm_num [Holds,Q,cell7]
def resval7Tail4 : Box := ⟨-41877399822436949542417346993933769921449141126819967012,17130644287325229687096097132740798932038127510260752731⟩
def resval7Tail8 : Box := ⟨-42538240878403147955826210771320828929042229666663475799,16469868139035078304190021798005167733713041993537484189⟩
def resval7Tail12 : Box := ⟨-43209442779236030637620569905115873491967753001649981976,15798666246258951416648254157774657017175302749738494883⟩
def resval7Tail16 : Box := ⟨-43891235424398459456098381392585264650676507860591537283,15116873601104006127981297655706418638931708080614236974⟩
def resval7Tail20 : Box := ⟨-44583785931286463807057229000600464422233421796627636848,14424323094216031982080844380524861660717713659586688394⟩
def resval7Tail24 : Box := ⟨-45287264045929223288602097234725592710749242905622253649,13720844979573272904271663543945825665525440963999237533⟩
def resval7Tail28 : Box := ⟨-46001842192734886907013244996429561901213925760342786990,13006266832767609300673993921510216531893282508430481517⟩
def resval7Tail32 : Box := ⟨-46727695516759787168468151157618806348177176082454086923,12280413508742709040434971077876857693746281610839952473⟩
def resval7Tail36 : Box := ⟨-47465001926637001508699919947816326275499319284105591230,11543107098865494700302467033755620184051929509737821260⟩
def resval7Tail40 : Box := ⟨-48213942138182244753430509147916812110443402071614962312,10794166887320251455294280089679755209883686805355222247⟩
def resval7Tail44 : Box := ⟨-48974699718687809357957266713743307467882711954366404452,10033409306814686849038832553313261052758347710593138842⟩
def resval7Tail48 : Box := ⟨-49747461131915410324834721524422597288751112198794261375,9260647893587085862844510386591300830823965600401792395⟩
def resval7Tail52 : Box := ⟨-50532415783798962274200718292471915985498314761695046128,8475693241703533381811168459936671297612860224109053434⟩
def resval7Tail56 : Box := ⟨-51329756068868452727120995861977749133867846098905893577,7678352956634000042242491093809219898952228728481051894⟩
def resval7Tail60 : Box := ⟨-52139677417394384462659284709788521533735101436483216999,6868431608095422277382996428419530578158399615941703371⟩
def resval7Tail64 : Box := ⟨-52962378324441754236111070692636183308663379870736319728,6045730681595791012019729304947868416398000515330347905⟩
def resval7Tail68 : Box := ⟨-53797729282276811655600422174828631117828352562618267312,5210041992724004802779463658126903448964842960616142455⟩
def resval7Tail72 : Box := ⟨902663460390078808043430217205070215486970027325402531362,742770255587184867653408182558165533823099027656051478⟩
def resval7Tail76 : Box := ⟨-586326481038268199184044298851147487543146874534603238,242411599828741162400828264761552649721915117907947915⟩
def resval7Tail80 : Box := ⟨-595545842146562593717054785097366048845865938898264550,233160429004185234816560030662076888537808550290165815⟩
def resval7Tail84 : Box := ⟨-604942832050554422601702920008313700500439852316866468,223763437316393327541029886195205207604534934172005891⟩
def resval7Tail88 : Box := ⟨-614488096859758534598635938395690340051602602292529718,214218172506143584907127292553282084352830135894183824⟩
def resval7Tail92 : Box := ⟨-624183974381587354025642267038932951030892701661720405,204522294984311786461742954852424759990143064008691528⟩
def resval7Tail96 : Box := ⟨-634032841101092342459884409195991654325254521037402544,194673428264806767871021780167926606610736285089823183⟩
def resval7Tail100 : Box := ⟨-644037111002415150616825556430750891181584234323211770,184669158363483958818697184110726540473797756758717293⟩
def resval7Tail104 : Box := ⟨-654199236159444746408157358318679383668258780246502756,174507033206454362960453020576363273782863033290847176⟩
def resval7Tail108 : Box := ⟨-664521707336824629998800230933939639020275155161902235,164184562029074479359791247926225571121361569286825084⟩
def resval7Tail112 : Box := ⟨-675007054600446027803730221049656844770344000777016716,153699214765453081554910471692846437404108410274343027⟩
def resval7Tail116 : Box := ⟨-685657847937573955071870384567582229240842210067170418,143048421428325154302982350958292900862488501809271868⟩
def resval7Tail120 : Box := ⟨-696476697886758117008891463052683285823481108893694450,132229571479140992541708529934389125948235795880271559⟩
def resval7Tail124 : Box := ⟨-707466256177683044238705568265435246633892971231116683,121240013188216069338555295256307842038940768980274255⟩
def resval7Tail128 : Box := ⟨-718629216381114542418494481001650522661465528545391162,110077052984784826891438939055213649326977138878651524⟩
def resval7Tail132 : Box := ⟨-729968314569158170650340982607170755582449577297521744,98737954796796187589333553024178486813597606151416424⟩
def resval7Tail136 : Box := ⟨-741486330043080388742442332733994282406979815387068308,87219939378033565406682937806317261810433455220335291⟩
def resval7Tail140 : Box := ⟨-753186594268105485888604425127827128654567751930602246,75520168137694332243653469066487958408869474041388482⟩
def resval7Tail144 : Box := ⟨-959880128010850957234481030560991096931899741355542018,60407328616428451569963864167782797437802713001198908⟩
def resval7Tail148 : Box := ⟨540638384332065322433778993556411591671280581145,172432207900570244868643840376502599623046061375⟩
def resval7Tail152 : Box := ⟨549085053722498417417192964973149422372701858291,163902354695938558359298900590076504551598947955⟩
def resval7Tail156 : Box := ⟨557748948939063970693485520582931217223625964104,155238457945371855812794693484842763487110150825⟩
def resval7Tail160 : Box := ⟨566549551463618813954290788110475277544362982022,146437855420310678882351200099551257574587919532⟩
def resval7Tail164 : Box := ⟨575489016831803317558194259732213536356846411471,137498390052125258397976658741973632984277233601⟩
def resval7Tail168 : Box := ⟨584569536130509944790639019729283411772030187187,128417870753418624897453354882746694091184977611⟩
def resval7Tail172 : Box := ⟨593793335019830003607033482972406332947297707637,119194071864098565950179444755012125413510657325⟩
def resval7Tail176 : Box := ⟨603162674278074842581846042080557743866770348908,109824732605853726968195880503406627364655552275⟩
def resval7Tail180 : Box := ⟨612679850355897921430851039123254088776149901332,100307556528030648118317166182698052223447483754⟩
def resval7Tail184 : Box := ⟨622347195939161135525078576612666242040232999820,90640210944767434023950999643833969763810148369⟩
def resval7Tail188 : Box := ⟨632167080520682494490515149226217147512290306173,80820326363246075058780595526276949749437521974⟩
def resval7Tail192 : Box := ⟨642141910981005286423751603666740057265630392451,70845495902923283128139489219663630615186348223⟩
def resval7Tail196 : Box := ⟨652274132178331075771861404372752656872934681226,60713274705597493821080715398371860897461542237⟩
def resval7Tail200 : Box := ⟨662566227547761130592884020138349612598429374488,50421179336167440617604733191941114608939728209⟩
def resval7Tail204 : Box := ⟨673020719709993351971314420138701212708998909923,39966687173935413126769590317638878729929309025⟩
def resval7Tail208 : Box := ⟨683640171089717875100226263798717981719188450521,29347235794301443832927142284940101966508385004⟩
def resval7Tail212 : Box := ⟨694427184813704918909215926359456572672239897304,18560222330336459797118552599819571579939664268⟩
def resval7Tail216 : Box := ⟨705397149433701737094198855666644534528938882804,7602628384756398978495975991986358912831226214⟩
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
def polyval7Tail5 : Box := ⟨21857124166613474739269410142627492180489703395116835886982,6666949569885105075286758021746916572644185238661713456920⟩
def polyval7Tail9 : Box := ⟨22202000877922683578599618386841314919134361842174716186956,6322070662701024008801601489333682334170144215105753965077⟩
def polyval7Tail13 : Box := ⟨22552321546810211221602194223781034815986448192404405286408,5971749993592462089838338771606479891954208445303680369867⟩
def polyval7Tail17 : Box := ⟨22908169851550658431116315551282297049957871500532020222767,5615901688851834724823633070882147549603836080084466502311⟩
def polyval7Tail21 : Box := ⟨23269633011317357783837138163562545465933228267605290176857,5254438529085134722062477284425408819725692704286652199956⟩
def polyval7Tail25 : Box := ⟨23636799621718272560071297882287832007354004688587422064899,4887271918684219937943296525553376843286680419519842820481⟩
def polyval7Tail29 : Box := ⟨24009759676292876316910693700240169112181308459657943889769,4514311864109616180834097411312509175440861199411089242961⟩
def polyval7Tail33 : Box := ⟨24388604588569640499684679255463793958978103453718469322826,4135466951832851998037650878144234190801315614905528867250⟩
def polyval7Tail37 : Box := ⟨24773427214471739447708581416168154979229393268488912040351,3750644325930753050010202217752215531587692773432895622516⟩
def polyval7Tail41 : Box := ⟨25164321875076290881916714973053617896193082539421425545904,3359749665326201615802417498630243110501807693535232063567⟩
def polyval7Tail45 : Box := ⟨25561384379732709633989196548907457211917336583636466840788,2962687160669782863738184208708514623002039447125735728735⟩
def polyval7Tail49 : Box := ⟨25964712049545840982377484887452387968659012063514109501769,2559359490856651515441364030438617665462134786079291822887⟩
def polyval7Tail53 : Box := ⟨26374403741229629377118614078282430125752001018581613996704,2149667799172863122887068389109304249889941018750419160751⟩
def polyval7Tail57 : Box := ⟨26790559871337169294679106371229497258886159727217987401731,1733511669065323349852511289065664083792794590332144082976⟩
def polyval7Tail61 : Box := ⟨27213282440873109883146968581575440971628140111621600734604,1310789099529414777956713278291658128446826064971015599092⟩
def polyval7Tail65 : Box := ⟨27642675060327824078335451253604860052972099667239915804030,881396480107008173189367908092055196641868038748000790001⟩
def polyval7Tail69 : Box := ⟨28078843253772629450554934912094576199984116135017849385214,445228557691711836475636670195055955066238772173235021286⟩
def polyval7Tail73 : Box := ⟨28656250000000000000000000000000000000000000000000000000000,2⟩
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
def pend : Box := ⟨1032365084926775545332167342892884721310475162075673368888174,3617872508584005751466122902301447370953374076039354869⟩
def zend : Box := ⟨1003839379490122297806132812500000000000000000000000000000000,1870821951792236679687500000000000000000000000000000002⟩
def betaquot : Box := ⟨428770525800584789698339493986441185166393773794585535769231,394812195886353682161433598157943712247100835142367582⟩
def crit : Box := ⟨213895857929445522731090790476853283827137137409457758225,8782725535117802148305361767588281284127898640398126473⟩
def subsonic : Box := ⟨326197678849219644186728944795197857915161644044750308472,4135381469834614215673900389716445512392819747154924682⟩
def pendTail4 : Box := ⟨28522370516477243379711729891128631405480961984290097673409,1663445494483625779526688838782252402107998268346202524⟩
def pendTail8 : Box := ⟨28522408207919029138880675314196559236797485266151854718240,1663330771657956435896821701665594494786452954024178680⟩
def pendTail12 : Box := ⟨28522408209645505832303954509583058687117752334454923598090,1663330756097411328483570559307801232726763849692215159⟩
def pendTail16 : Box := ⟨28522408209646406360139431835649019519281113566927900942489,1663330756083874163597032074779448459219915008703829594⟩
def pendTail20 : Box := ⟨28522408209646408655363889173443838891162754292932585018143,1663330756083821792929117891587953829111504733022069552⟩
def pendTail24 : Box := ⟨28522408209646408676081956236693934416825072008480704906386,1663330756083821079374453535065528191731951868131642146⟩
def pendTail28 : Box := ⟨28522408209646408676626263290775929108278104556035512687952,1663330756083821049962798741057397984565758072493406279⟩
def pendTail32 : Box := ⟨28522408209646408676661752345388839770716245475223424189567,1663330756083821046619806305159033402368852115508971555⟩
def pendTail36 : Box := ⟨28522408209646408676666217167121624077422134503725456110190,1663330756083821045626414929371517738685340641090421852⟩
def pendTail40 : Box := ⟨28522408209646408676665939144883617067212266527267218768147,1663330756083821044873802646135235027790913313859320990⟩
def pendTail44 : Box := ⟨28522408209646408676659702361683977087638480680599472972250,1663330756083821043422952477707316715558830125475580770⟩
def pendTail48 : Box := ⟨28522408209646408676605160894782439781826698113336826850613,1663330756083821036158955241427536522687445514363715983⟩
def pendTail52 : Box := ⟨28522408209646408675601078797903058705648271723450212047102,1663330756083820937485272472430370886064608261316721591⟩
def pendTail56 : Box := ⟨28522408209646408626495683034405252900458865746741519684693,1663330756083817491245354421515886446481541586264269287⟩
def pendTail60 : Box := ⟨28522408209646400928714048967068117788641853177236300296646,1663330756083426392776643275316528130597550513824091029⟩
def pendTail64 : Box := ⟨28522408209641360304534370715371754611845008252821685266477,1663330755895104318931791122886510404883689347107723439⟩
def pendTail68 : Box := ⟨28522408187118384380300761769812368633507259225339094763396,1663330150289702024068103092761496928929376239559192051⟩
def pendTail72 : Box := ⟨28519848238754927857343753847548347219898306342329402434266,1621173758620773713124949674381957916504732792727438531⟩
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
end SepticProfile.ExteriorCertificates.C42

end
end

end OAI
