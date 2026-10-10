import OAI.MathematicalPhysics.Transonic.Certificates.BarrierData06

namespace OAI

section
noncomputable section
namespace SepticProfile.ExteriorCertificates.C06
open SepticProfile.ExteriorJet SepticProfile.FixedInterval
def cell0 : Box := ⟨250000000000000000000000000000000000000000000000000000000000,250000000000000000000000000000000000000000000000000000000002⟩
def resval0 : Box := ⟨106929560713929582295542533531803633383756898618948184363,417375420435337875640071908182343607409633091989322724⟩
def polyval0 : Box := ⟨3738502356881023197709597673445680348994641231178886950415,16491232551007523856839266042626039531454989824005640721⟩
theorem cell0_lo : Holds Q cell0 (0/1:ℝ) := by norm_num [Holds,Q,cell0]
theorem cell0_hi : Holds Q cell0 (1/2:ℝ) := by norm_num [Holds,Q,cell0]
def resval0Tail4 : Box := ⟨51159699421531728618452752795239015480552317701313,1749697917943604571474875961094345905430524349746⟩
def resval0Tail8 : Box := ⟨5764879845394600645052731965138394368204736482,347044551647300499289099082007536617602551706⟩
def resval0Tail12 : Box := ⟨4886562323667806847101820256734196503669203,442290650909860701943794298520035071545445⟩
def resval0Tail16 : Box := ⟨18241532598310782220838983204011524063233,24896201516500552113627715711224307525882⟩
def resval0Tail20 : Box := ⟨231734073282012376120334968597943963013,361190786755193559353526894718389361632308⟩
def resval0Tail24 : Box := ⟨8598501711821698950599588862877415638,5778404954387564317022116191354181467527536⟩
def resval0Tail28 : Box := ⟨848061488459053337153989646745731010,92454446605590005795856486693359204167180574⟩
def resval0Tail32 : Box := ⟨208078814400224491434865309846416241,1479271141288917536556196908977343675560980072⟩
def resval0Tail36 : Box := ⟨-402668887184238618733071777294261158,23668338258867087512540756354567717676614722059⟩
def resval0Tail40 : Box := ⟨-135437592078022203924517660598642151864,378693412014139218268315361278546586135511306148⟩
def resval0Tail44 : Box := ⟨-34719112346178681938520612381673983012913,6059094559675408187185885299180735455972204592742⟩
def resval0Tail48 : Box := ⟨-8888259373679407015603316426754790072641234,96945504622053370336211338320822826490742939518705⟩
def resval0Tail52 : Box := ⟨-2275395845774286924681551554249786425074051946,1551125940769065043657312370265484719273866120832703⟩
def resval0Tail56 : Box := ⟨-582501364914816064579449636553359175207504588244,24817468957264011758668113524581609221736571073723339⟩
def resval0Tail60 : Box := ⟨-149120348833978697645027411524982143041974059210592,396939702986322798793417035690447300078551045246117475⟩
def resval0Tail64 : Box := ⟨-38174803974434119054734915271870991985631375688978623,6315246365077664418307547135610296993194875728653992521⟩
def resval0Tail68 : Box := ⟨-9772626482528806227551132736665584630056844052273175633,91882036439497679041292325784230770052319519301986775075⟩
def resval0Tail72 : Box := ⟨733441380282548713152485783882127715605258439794037532950,2652653945668911107994234357083871297877535000494870822⟩
def resval0Tail76 : Box := ⟨-23351705548669530315777130996789559426007122155924,597363843428163371893074653063083500718818028002⟩
def resval0Tail80 : Box := ⟨-1175434478616680272675242418850919923509316944,60568201150429104333082488619988118569425150⟩
def resval0Tail84 : Box := ⟨-619419482783658881629285811326708300047080,49787432693961117290207420512003966450831⟩
def resval0Tail88 : Box := ⟨-1597358536289715001875583772829446026997,333216440631883852547666761258493952508⟩
def resval0Tail92 : Box := ⟨-14834442483597089286356627364477295509,2383581063610770228677696058313969958798⟩
def resval0Tail96 : Box := ⟨-416508177079634335022035227011954035,38099411541592870367011673690785063097041⟩
def resval0Tail100 : Box := ⟨-31761934717706641242089415478449075,609589134440144313065521819488248988418328⟩
def resval0Tail104 : Box := ⟨-6170941844849437450830222228305657,9753426000152871113414149723128161600803954⟩
def resval0Tail108 : Box := ⟨-4679665510983150328458448531147074,156054815961347246095368176523136981325084049⟩
def resval0Tail112 : Box := ⟨-449084138478244901525191817212503325,2496877054964603940569220758963543725837172631⟩
def resval0Tail116 : Box := ⟨-114104302468057433584389591775997097767,39950032772468161206600908003657121901197513578⟩
def resval0Tail120 : Box := ⟨-29208297479812588676739645941707579719042,639200496976751130307844889079106359552410013476⟩
def resval0Tail124 : Box := ⟨-7477307679462849233446989249960972538612020,10227200941652738778505615070505562031644322686246⟩
def resval0Tail128 : Box := ⟨-1914190497797113963937478901782886744742742849,163633420512889331743460273092570595927556486143116⟩
def resval0Tail132 : Box := ⟨-490032763688036261119761969824478422398355148131,2617675322497849833299142487640835749269257481931331⟩
def resval0Tail136 : Box := ⟨-125448400047518710979028906747246944797424844819758,41765197292568591870092075462161046688703876842356877⟩
def resval0Tail140 : Box := ⟨-32114942697855159563019831176072965885810431218256248,638135467140974977578579986126336622162339094345627903⟩
def resval0Tail144 : Box := ⟨-8334641314822441155246049839344470697210902964463444252,2443854632295431389377004670539775678437346451558081255⟩
def resval0Tail148 : Box := ⟨49199374914184988883139109559100015409533344,1056243259123142904362461497440914834584318⟩
def resval0Tail152 : Box := ⟨816638992933429586141473376183274282341,37462416240448809542601046407062736796⟩
def resval0Tail156 : Box := ⟨241659848660484262666384881396104920,17681857151264039911280087533295560⟩
def resval0Tail160 : Box := ⟨394381852455631726614302605238967,43133555543809280388779410165098⟩
def resval0Tail164 : Box := ⟨2454072595156281977243188873063,24181006535837624803150250060693⟩
def resval0Tail168 : Box := ⟨47652084296698202314565456869,381165067096488804131819291616212⟩
def resval0Tail172 : Box := ⟨2555299986832943008696186048,6098490061825574506469668526353099⟩
def resval0Tail176 : Box := ⟨350951563434507069037650103,97575830036933838491591923358545492⟩
def resval0Tail180 : Box := ⟨123766477893027429876373537,1561213278534269801616738638940007950⟩
def resval0Tail184 : Box := ⟨1532648833967609505102936539,24979412454598452728125601025397066718⟩
def resval0Tail188 : Box := ⟨368056537698022575764329210198,399670598928678266677738760729789015545⟩
def resval0Tail192 : Box := ⟨94175602565254368262529332169464,6394729494569757826989611008611361744147⟩
def resval0Tail196 : Box := ⟨24108735557414660237453719457673748,102315649311182108948635389938776763492539⟩
def resval0Tail200 : Box := ⟨6171833829055547618513128533178210435,1637044602884881568810778155220751750389195⟩
def resval0Tail204 : Box := ⟨1579989404069844671563627861253298816580,26191232406111964356637707818030810276691589⟩
def resval0Tail208 : Box := ⟨404477296419620103068176935592852638861896,418680521041567064646981720236699435835405154⟩
def resval0Tail212 : Box := ⟨103546240895030247468604511951581035243284923,6601813761844646165181955269826144131647284311⟩
def resval0Tail216 : Box := ⟨26510836096068075709352827530279964677201900030,80776395257146000047482594890263853815424947103⟩
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
def polyval0Tail5 : Box := ⟨1918620471604469960948929977883388281675793586751654,52435584160802688103706056905118753032568077440773⟩
def polyval0Tail9 : Box := ⟨173289629398872055889012965740907380974469326872,9316862940252592420928640478914101178093650290⟩
def polyval0Tail13 : Box := ⟨127094089057114495082441124078778293395976829,10582384719613155978555972014638259435470899⟩
def polyval0Tail17 : Box := ⟨415742481577862830573065013180290467915697,415298755321290867756207129996213563722612⟩
def polyval0Tail21 : Box := ⟨4640731228944265174916003821075326152409,5854287643617885755576272579646304389453702⟩
def polyval0Tail25 : Box := ⟨151135704884555640610664153247079829046,93656414786115035309928611629422327406284918⟩
def polyval0Tail29 : Box := ⟨13036959071204342892678208728565487501,1498502095959912786277189262755512834472103768⟩
def polyval0Tail33 : Box := ⟨2831037568181272221816979591534484614,23976033471739074811238422730829077332259568811⟩
def polyval0Tail37 : Box := ⟨7038202481191811027735725706215024301,383616535527091941206060118087661812447745452897⟩
def polyval0Tail41 : Box := ⟨1428322402984526768149169937203904255632,6137864567096605784098649005701015400082532739514⟩
def polyval0Tail45 : Box := ⟨365185932936754552556410363764759008962189,98205832731188117124905128811587266099416897924733⟩
def polyval0Tail49 : Box := ⟨93486209625016616980882965422702580965901856,1571293236055712867555926604401979396411085233706364⟩
def polyval0Tail53 : Box := ⟨23932459561402909777512398475340510822837973507,25140669340211007349743900875995019044655048964284559⟩
def polyval0Tail57 : Box := ⟨6126709475709650303119163706211935327310854141979,402244965653268260742341992016765891215454511145648281⟩
def polyval0Tail61 : Box := ⟨1568437623722336563079368178125434916166644223452092,6434449040185493239908564793073243223664261034000339275⟩
def polyval0Tail65 : Box := ⟨401520041072547356895715060506976285897226478748160989,102574759610150030729199689541207416319421210834304739802⟩
def polyval0Tail69 : Box := ⟨102789245261146254337408132257993642443888511713822056309,1544831288730920325703119607377208740305432613272772134924⟩
def polyval0Tail73 : Box := ⟨26406250000000000000000000000000000000000000000000000000000,2⟩
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
def resval1 : Box := ⟨106720847503454386329207692389825125620765222020417115672,347236077685727255378122560448786115333476936146732360⟩
def polyval1 : Box := ⟨3720956150653904510409764666261174152660962102047992618978,10529568496702175995297112679072990028895474888119178682⟩
theorem cell1_lo : Holds Q cell1 (1/2:ℝ) := by norm_num [Holds,Q,cell1]
theorem cell1_hi : Holds Q cell1 (3/4:ℝ) := by norm_num [Holds,Q,cell1]
def resval1Tail4 : Box := ⟨49700160147106752820222240545768997429099609979207,3118913513322833323012715777455519293521207265301⟩
def resval1Tail8 : Box := ⟨5430597460342474730538240832411853212350009272,6002401641319367757367351985901026660515315175863⟩
def resval1Tail12 : Box := ⟨-314341628154554424497490921999198107438296000,18969714466123524093435693341149421542902585847631⟩
def resval1Tail16 : Box := ⟨-2089796368800889573843463522194116528096263022,59952582680671159176835875552532512070793621399670⟩
def resval1Tail20 : Box := ⟨-13695797565723118933691414479497595002157971908,189472676523628316378166446718171360382888252905072⟩
def resval1Tail24 : Box := ⟨-89756780258180160691908268331097924666359137342,598780753272484680022436141631800834011511804961735⟩
def resval1Tail28 : Box := ⟨-588230035147542521339130866727280799078112199469,1892138320255022263581140307367174507967079018285849⟩
def resval1Tail32 : Box := ⟨-3855024358347374076146606012843247309315038569088,5978095554336511958924719777423179239483068414657624⟩
def resval1Tail36 : Box := ⟨-25264287634866355355739224062504485355572435291149,18880653590709380738198627218767922237861801236019946⟩
def resval1Tail40 : Box := ⟨-165572035443860650481438665185104092799289416309523,59586464715866352461362478418578622391390668892105265⟩
def resval1Tail44 : Box := ⟨-1085092891484885586111513551053866841010361619676616,187760850421298009942964250497759522518515247798358695⟩
def resval1Tail48 : Box := ⟨-7111264773635345096609948743250010353680466735100256,589735173350715530936755651861709703405627578124238583⟩
def resval1Tail52 : Box := ⟨-46604384820496523522850836664456324531236159375237069,1839725098634241946456871319135421051436820431710424871⟩
def resval1Tail56 : Box := ⟨-305426496359599102828857747936929091713575677196231892,5656306192089936995196669573873530174185194748200260357⟩
def resval1Tail60 : Box := ⟨-2001643086540199849484025325905247464253941745457674679,16840376274483375157773355148714014501218358582201900617⟩
def resval1Tail64 : Box := ⟨-13117968128795860724555957543800534629069785890620229778,46432117749919917336810080836154090055757155039578505792⟩
def resval1Tail68 : Box := ⟨-85969859410176336317475662775669837818523178336110921302,102237767348292229425193681708634467216591500896663426552⟩
def resval1Tail72 : Box := ⟨736046010126571932709563679265716794687750559573987000546,1786394820044475522660088562351695273581843287112523441⟩
def resval1Tail76 : Box := ⟨-22839651677006788397309015291704354164131582964904,432741026249086785083365982734452919356490739579⟩
def resval1Tail80 : Box := ⟨-1124362470492179720819941492742697634931962741,59325286307957694584545018019299829635321843812⟩
def resval1Tail84 : Box := ⟨-3200447545601794644983311163533266409200497,187367447286764325811317751104949563640117614399⟩
def resval1Tail88 : Box := ⟨-17181247446565572216549764129269481546713982,592164752324716934622926109389049368728962321261⟩
def resval1Tail92 : Box := ⟨-112589487594154733072990447569601468864784508,1871474751475433406718832824995171093492645348880⟩
def resval1Tail96 : Box := ⟨-737866379901617306556824492576834403805781078,5914402371683324360796173899773522207531359086974⟩
def resval1Tail100 : Box := ⟨-4835681104994029039177552880603727479566316294,18689928528081335792254721104650033809478765943723⟩
def resval1Tail104 : Box := ⟨-31691119689519741551248823359796191291539659722,59052995763664722446954644530344013643229706795628⟩
def resval1Tail108 : Box := ⟨-207690921997206210769999563734094327008285872866,186529097252554457620189729825264046042352392613569⟩
def resval1Tail112 : Box := ⟨-1361123226400878168247726043666437110756695654250,588819343103046349519936507376921529821524795311927⟩
def resval1Tail116 : Box := ⟨-8920257176540785401872406496055052282431960855524,1856341463568378843502299090511371229814252137382688⟩
def resval1Tail120 : Box := ⟨-58459797432177693272895427058258029098605557064584,5836688357020901635266616052615803754038872010669582⟩
def resval1Tail124 : Box := ⟨-383122128451520291323335560148934785676061578605856,18248457223894014812196073556430741661721827463263732⟩
def resval1Tail128 : Box := ⟨-2510829181019925442306467779817813584121282220444492,56374162352319080609933181400676948600002465970645085⟩
def resval1Tail132 : Box := ⟨-16454970120741139547505478523986041697640886279971122,169650682132781297516376693374690881808199711473516122⟩
def resval1Tail136 : Box := ⟨-107839292191847092958105725254644002817921533311486171,480346472961518745430196772326936764158780292144023226⟩
def resval1Tail140 : Box := ⟨-706735658044832514178247636800594355213690925816788337,1152221877731886335472915858386041716116889666684079349⟩
def resval1Tail144 : Box := ⟨-4678659664641196328858996699785831219443920511614992827,1233344623144097292772551861788225153767957316627301054⟩
def resval1Tail148 : Box := ⟨48482374307729378542699857001204694009755613,806215874357920826909817817292572352711513⟩
def resval1Tail152 : Box := ⟨785929602231214779334716472164186002714,2469384603318782013957749366825141981210⟩
def resval1Tail156 : Box := ⟨322196972479357840329447377002220376,7722146840927270580393549838608272675370⟩
def resval1Tail160 : Box := ⟨620804304086159332928226403722216558,24405469832695449689475027428008533309022⟩
def resval1Tail164 : Box := ⟨4066128353331028561072243521139370648,77131231515839913819842728800594736318755⟩
def resval1Tail168 : Box := ⟨26647764398986442094079860463467712507,243758984289205887910896561311179577714969⟩
def resval1Tail172 : Box := ⟨174638788494992083107267233661226008948,770308346467209066768876017386416713496616⟩
def resval1Tail176 : Box := ⟨1144512764266892595574804077538860269053,2433962206068568638161736103330660219205289⟩
def resval1Tail180 : Box := ⟨7500678851897716403911835277269428550755,7688639074496322319265814411794115536561880⟩
def resval1Tail184 : Box := ⟨49156448923796334719426071513670070026076,24274445734497738321083200918534233884757585⟩
def resval1Tail188 : Box := ⟨322151703666991318441744089159439715447747,76552442851344278539641671043998947675782493⟩
def resval1Tail192 : Box := ⟨2111253405151994037394170989882075079141817,240850428151426834085276559108179595223869034⟩
def resval1Tail196 : Box := ⟨13836310316004111406979385096402077790609463,754042584480096878990869587403092604531170995⟩
def resval1Tail200 : Box := ⟨90677643286964739796052331789541034619513202,2336198863722934829771092833218290748008440691⟩
def resval1Tail204 : Box := ⟨594265003045476253930419552492986908206776212,7075863216640149763278375017485825174050878371⟩
def resval1Tail208 : Box := ⟨3894575123969559997237182589588869875354673857,20346817767884261430643916177500373135808152151⟩
def resval1Tail212 : Box := ⟨25523487560819972844934774633359608071276449456,51091285057096084538642749285158399899240302120⟩
def resval1Tail216 : Box := ⟨167272051777188984946763080913623288297427704972,74869479818980769907176586949284630362989495722⟩
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
def polyval1Tail5 : Box := ⟨1867764988789320293391159370759754736454585500618198,118105061011696590559069085459146284407829048979367⟩
def polyval1Tail9 : Box := ⟨167279096733805025580850956597829678300765726850,266158482843189917714687203790004098796774515720856⟩
def polyval1Tail13 : Box := ⟨15042100483379743364642447319876333587361931510,841168351497612135372659208543229464395808946169966⟩
def polyval1Tail17 : Box := ⟨97804966714743533717308219096910251527911985315,2658456742754281771667741380663641577318308017706656⟩
def polyval1Tail21 : Box := ⟨640972159121820786741935083430491928312995214265,8401704263881651145073401669833712055582967381465838⟩
def polyval1Tail25 : Box := ⟨4200675115247617859965641354032614372921809091665,26551359577049914472557955064838114600960927698512192⟩
def polyval1Tail29 : Box := ⟨27529544434446293551198346414157528156569467555275,83901154709321701798305307482331245141440184133035703⟩
def polyval1Tail33 : Box := ⟨180417622405518310374797350753092025073947598282025,265075670883292890886245101466716548141182034911090366⟩
def polyval1Tail37 : Box := ⟨1182384930196791110851792596773537970097412498952732,837157845408800643498696055608007774623049533279534537⟩
def polyval1Tail41 : Box := ⟨7748877878537684138336568845713622634621313416151450,2641820245168170254376454077731181583215393799488448790⟩
def polyval1Tail45 : Box := ⟨50783046064784561786860205951561274152241983679194494,8323163811959378797358979509021656965723981589860737599⟩
def polyval1Tail49 : Box := ⟨332811770690172107072715876468634171473248314842071008,26132995583065208391784807474501157729645656907681773414⟩
def polyval1Tail53 : Box := ⟨2181115220395112295943687628516077848792440431975123618,81463905551967572041445182778139366446849971855183610544⟩
def polyval1Tail57 : Box := ⟨14294156708381436845052777963319189388940734854051902654,250065415115382130032357734631558469396409787954382885687⟩
def polyval1Tail61 : Box := ⟨93678185404054983390049169355140058501859501300436142230,741828609495745686766534522226055111544427919370734130305⟩
def polyval1Tail65 : Box := ⟨613929355870346329434198356577798274105141886305917072866,2026684711965896057366723520974072949695823830617364946971⟩
def polyval1Tail69 : Box := ⟨4023447481406499112612706867881146337232826816245411223733,4322197022075015106134064320004531032386322326868845967602⟩
def polyval1Tail73 : Box := ⟨26406250000000000000000000000000000000000000000000000000000,2⟩
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
def resval2 : Box := ⟨106618060738371201458463114219011080134402972130121397892,332188065765941927561821858208784791872451871581107000⟩
def polyval2 : Box := ⟨3712284871155631719471906185290816109240707279523713884517,9309212712985104028754923960790509979588543061191600412⟩
theorem cell2_lo : Holds Q cell2 (3/4:ℝ) := by norm_num [Holds,Q,cell2]
theorem cell2_hi : Holds Q cell2 (7/8:ℝ) := by norm_num [Holds,Q,cell2]
def resval2Tail4 : Box := ⟨-144980964814182807398367619099381023083427979606318,33814617414769531058882838288793296649366462805666177⟩
def resval2Tail8 : Box := ⟨-445117640283282783985733467406485818238445441120537,57570490464566867607946959056924915237586131176699137⟩
def resval2Tail12 : Box := ⟨-1021378103667780367162855396440012313446419511625388,97950696864214292736623685625706306509829001182938233⟩
def resval2Tail16 : Box := ⟨-2343651681972045557357462330384446262917937400412931,166498338774309504588833895786965495048222643460035921⟩
def resval2Tail20 : Box := ⟨-5377737356211232072276067632056248715402196193760909,282659244280185791768938431605786955408042185402420118⟩
def resval2Tail24 : Box := ⟨-12339742844321688811647846170508117534961036011382790,479038631492489187241292372807542011372611219860299152⟩
def resval2Tail28 : Box := ⟨-28314743427942531061754708836462205934351609337426541,809955069684751084702501038158051453755374637247525853⟩
def resval2Tail32 : Box := ⟨-64970940278479106255579468564717420692260072506187611,1365080352728431785872795835855407141502956830555386782⟩
def resval2Tail36 : Box := ⟨-149082158961185067577728676346232225275719167999029132,2290522212615785783907759933397207046466614891558029132⟩
def resval2Tail40 : Box := ⟨-342083553435811932042019663146182135796769026473146507,3819773800158220807489057944332774011479813207502095324⟩
def resval2Tail44 : Box := ⟨-784944076116710576465848911800636702694568652343229106,6315000830306095796008761543619010133632851954395165272⟩
def resval2Tail48 : Box := ⟨-1801130736752380668164108160670300572032981131267668078,10311061823309183218896203723734816174151915806575102845⟩
def resval2Tail52 : Box := ⟨-4132870136332902113088580503632246121264552355327368523,16529995638765875670436253628047278852674417533128414230⟩
def resval2Tail56 : Box := ⟨-9483273598778505605910829164479644733449950674908270138,25766663183730689448011315752349037676588123366274541171⟩
def resval2Tail60 : Box := ⟨-21760296158030151653513877446961662475779257135581474461,38374539769147355204922197183585559864774503226465755639⟩
def resval2Tail64 : Box := ⟨-49931121772356921708996818026355994038016798058828226212,52656253467694086057893191857072127270831858091117978868⟩
def resval2Tail68 : Box := ⟨-114571784185009683215737664681105246438943757276558641100,60437703885145486408743893862881766262574101343498325917⟩
def resval2Tail72 : Box := ⟨737346808328681791934466276736980013547449884777966286961,1353670104739328045201622450028411929492226693817169791⟩
def resval2Tail76 : Box := ⟨-24666375332038741750499344899882992466781835652438,389702968203757312911382056522175004077749862962185⟩
def resval2Tail80 : Box := ⟨-4756342972490396586389895703228078674479606958324,663338825687543682387796093755534432467739597779780⟩
def resval2Tail84 : Box := ⟨-10911369204426772118992060508501509556981361644266,1128827593663814026100708612633886330200569303696104⟩
def resval2Tail88 : Box := ⟨-25037199519071450611158571992845495523762971550783,1919307152654299147918209891503420192849625294596072⟩
def resval2Tail92 : Box := ⟨-57450296123760459274987073666137966186204491857849,3259515329239114395655044839973354126256082057357326⟩
def resval2Tail96 : Box := ⟨-131825307474036514069786887263423245490117910560943,5526771611095843830329658819811331512253694593069025⟩
def resval2Tail100 : Box := ⟨-302486024670650034265105309277237954208624217438619,9350830501136192311713615182871650854387424597785368⟩
def resval2Tail104 : Box := ⟨-694083684493390258222458538280325079956199541714104,15774048131293709345307795479917217317849384820759231⟩
def resval2Tail108 : Box := ⟨-1592642706731515833603261152157374987521477653783547,26501263131445893562036084341979722224865789989503030⟩
def resval2Tail112 : Box := ⟨-3654474018009055061111543279066649996136048524001869,44272489044537662506075639644232222723428397606419391⟩
def resval2Tail116 : Box := ⟨-8385547048221050821382915076735928034350953292608211,73375736043903628543451627419697797052197681158701773⟩
def resval2Tail120 : Box := ⟨-19241455528595454899996279228959053722042622042357466,120239683807240732822563413111719553937245416923767826⟩
def resval2Tail124 : Box := ⟨-44151396292918026356163314625519294553796154924985591,193797269562802517611803811890234951075593291367563534⟩
def resval2Tail128 : Box := ⟨-101309684795794155163478409002566354082090061936651992,304620234131749126564912069729789635307659522137296147⟩
def resval2Tail132 : Box := ⟨-232464952304799561113013913417410300407549455123144032,460033568281302757731259690073388459317329920725379272⟩
def resval2Tail136 : Box := ⟨-533413504934877056287688218673506703874863483708378536,647958398577984891879920152993788135944031650769821903⟩
def resval2Tail140 : Box := ⟨-1223969367329961859055368944237007020144139622909567547,791398993182383635653740987986690772072125342516569955⟩
def resval2Tail144 : Box := ⟨-2844885036881560445500199119069894910994701854986802027,624883926278623643168799543944128657842893121584033104⟩
def resval2Tail148 : Box := ⟨48343974532485666495927779333038145900083099,38021528815666538474079980342046303060667607⟩
def resval2Tail152 : Box := ⟨480363918067775285733689425868419385689153,63633992329950797692817015845421811685498037⟩
def resval2Tail156 : Box := ⟨1100471778194966243091762175473140563007837,108274456484058087769133262753118095348362815⟩
def resval2Tail160 : Box := ⟨2525139314986020045617953233588367899523913,184063659201924235431363708049260149427382198⟩
def resval2Tail164 : Box := ⟨5794178429471155120374760293484378626287429,312518074266821331370533919789494792118741848⟩
def resval2Tail168 : Box := ⟨13295307501617085844596052779059628923385858,529731342662483359773759943375057969672147859⟩
def resval2Tail172 : Box := ⟨30507379728510025351377142625946903654193157,895872111763433023158738020372061567855212560⟩
def resval2Tail176 : Box := ⟨70002158113778680622030615329966546510784137,1510360356318124159139832020423785768644315356⟩
def resval2Tail180 : Box := ⟨160626778969384811399074203561327987886142836,2535401900378001290480811555934007767830273346⟩
def resval2Tail184 : Box := ⟨368573809969454955924506801161435383802275018,4230732091990933829171979340593877181504881968⟩
def resval2Tail188 : Box := ⟨845728553277483281069583787738658267458794191,7000484264061022534694648895683582379752460799⟩
def resval2Tail192 : Box := ⟨1940606647792204205587656227924450794263573711,11444686021853160151651814660528105355020573278⟩
def resval2Tail196 : Box := ⟨4452911217034063756936454900935298781439001138,18381807139845325004362404590777484414413790290⟩
def resval2Tail200 : Box := ⟨10217639071445131746563849039620822656765367606,28737382332044237979642565598451877252359593611⟩
def resval2Tail204 : Box := ⟨23445369356333067766212494420924002799072418412,43010177361156518877393249367316891292132737178⟩
def resval2Tail208 : Box := ⟨53797686570389527760418174752333855795217369181,59572542232132076920683767145745911172722369421⟩
def resval2Tail212 : Box := ⟨123444038644444721636868113577296834507247445405,69960566611858275077734509056533919206903285485⟩
def resval2Tail216 : Box := ⟨283255420383248162722941725731567233928992437835,46685177060572323833699772169219984485704658330⟩
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
def polyval2Tail5 : Box := ⟨21306528491276132412245747547196947083690617952166307,2985453548759790073053495663428624805411739444689585273⟩
def polyval2Tail9 : Box := ⟨44659914487134736539262638064352743337705659583321235,5081582318695722421414449867095855189655679001301934055⟩
def polyval2Tail13 : Box := ⟨102476159667762597810988038388442344823092489579234260,8642666497678348558361267217438717688635417554165596230⟩
def polyval2Tail17 : Box := ⟨235141542400506350195161191196891811489593715864953102,14683685747900865117082864425843709999889141832633265288⟩
def polyval2Tail21 : Box := ⟨539555201944470546973065739440570575136523800943944356,24911305514870566879999360602011890355507593532894746183⟩
def polyval2Tail25 : Box := ⟨1238062032654058708557881701402996010429902008081333151,42179982738722191593169447142464991384494814870798713461⟩
def polyval2Tail29 : Box := ⟨2840854079759685720091238752072262058223754539139118909,71228413468577307502506555150392762065898139697431415386⟩
def polyval2Tail33 : Box := ⟨6518616749102999291110822808724580503422650837623683672,119840283658222416868400575534972343162208359179466414572⟩
def polyval2Tail37 : Box := ⟨14957601879108370205394608191024784188540107451713910888,200605103688740403048159423707566174403935939997773501266⟩
def polyval2Tail41 : Box := ⟨34321676298072411671451802657718665077266978533384817370,333418782679815374769160015946759106567023552104113220584⟩
def polyval2Tail45 : Box := ⟨78754433593728285820530606753861231707674480104755655213,548594554316904106208250918978968319299958968343240675758⟩
def polyval2Tail49 : Box := ⟨180709728650907774238318829849112181343650191820514602896,889519948351153982437254606988822012075188901160004481362⟩
def polyval2Tail53 : Box := ⟨414656096665589156700990860104117121568731549645655153219,1411108483509523278161681516761348011344522643909389073047⟩
def polyval2Tail57 : Box := ⟨951468854419524936766905472722537301078677213210538032000,2163204915008738529372628318876812924790803442830049547736⟩
def polyval2Tail61 : Box := ⟨2183238081413050638728741677108669143469644952973678733679,3130257861768197779832855962423376344894399450020463828265⟩
def polyval2Tail65 : Box := ⟨5009652704864391073168944256706926831956207074480908049543,4054936792545255893206856733899500973473711049167715592821⟩
def polyval2Tail69 : Box := ⟨11495136756473229745952842811333583740184370847436819331343,3968652776918613198596381888397146879093805826842101462231⟩
def polyval2Tail73 : Box := ⟨26406250000000000000000000000000000000000000000000000000000,2⟩
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
def resval3 : Box := ⟨106434395452985922055011814269667734786418206223727002477,1885368729193302798497987131569510778452209123405585464⟩
def polyval3 : Box := ⟨3729995061432325151347896115947736715810165332051094376828,235590624164397947304821009819854957560407856871782543611⟩
theorem cell3_lo : Holds Q cell3 (7/8:ℝ) := by norm_num [Holds,Q,cell3]
theorem cell3_hi : Holds Q cell3 (15/16:ℝ) := by norm_num [Holds,Q,cell3]
def resval3Tail4 : Box := ⟨-196833985692541164338083838379926008586489362722796725,2035114243766109372109086627405822612833941011778510889⟩
def resval3Tail8 : Box := ⟨-291887413512134641250920543463993608231870168013765324,2597516942152362466490252582328046687236223173358426100⟩
def resval3Tail12 : Box := ⟨-432736270377838478362564036908179715076368335115249038,3307708256815454896884670405245844437747328911959097177⟩
def resval3Tail16 : Box := ⟨-641551048949740031178168324637585300846678091618728594,4200597544322547453121011119738618213780946141720286277⟩
def resval3Tail20 : Box := ⟨-951128381369694170219549242479998029002925715902931667,5317218289419314713421955080668818981765669272662095767⟩
def resval3Tail24 : Box := ⟨-1410090746991801881301623270009365191549146430963652899,6704523918031970901477299377304570567614575539785782743⟩
def resval3Tail28 : Box := ⟨-2090523165640920166126554774579921735677875163782733052,8414156077559039803132132730690598264455565050178212549⟩
def resval3Tail32 : Box := ⟨-3099294932191156703865648988253323721382642081645503800,10499414379065190487671087732995337326885195804266220880⟩
def resval3Tail36 : Box := ⟨-4594844598988625923794204971402982878836731098159767032,13009205048863146314177360462933915243451217486128564301⟩
def resval3Tail40 : Box := ⟨-6812064469749784621210729692962371056186560614738221024,15977051534627770843183085168964747779745781033027292144⟩
def resval3Tail44 : Box := ⟨-10099192984729336937957547107275006590215840993659722024,19402189858982020590863033397226820284654502420691231933⟩
def resval3Tail48 : Box := ⟨-14972509346575900111951396722587178712608714050596759302,23218159809877779430303299843668834015139227373404126379⟩
def resval3Tail52 : Box := ⟨-22197420771369754005730189575472065966764947798861899380,27241862069861818102577999782512067787812823230954708358⟩
def resval3Tail56 : Box := ⟨-32908677997514152297936704312013637849949706514415935820,31092365761161442382470898411285369622655136089508313490⟩
def resval3Tail60 : Box := ⟨-48788600202635565493690101491552745289638139895914775111,34063200365630606503172864246951425591005322184626155945⟩
def resval3Tail64 : Box := ⟨-72331301483353088387969789596485875408126967924061850875,34923525221159375573381752224375807374322009450937689004⟩
def resval3Tail68 : Box := ⟨-107234378434682426739472745949673773866592438606971258276,31611057362578017978172293020646746365366265839528994849⟩
def resval3Tail72 : Box := ⟨737995256343623017828984293640220105771350716863156943869,1156551881809137127576906754018701645204364849854032996⟩
def resval3Tail76 : Box := ⟨-2367874486690768589534440036780672172091699950984923,25183067074477990720737603986758054969942828789488104⟩
def resval3Tail80 : Box := ⟨-3477163680647156199450344124020134576833506385447590,32159243299111378782582678648812150920807188741303973⟩
def resval3Tail84 : Box := ⟨-5155050457449267041167247414123553709790282234945436,40977640808522487244490091311855246494837074773500442⟩
def resval3Tail88 : Box := ⟨-7642594934534116996237783629866248145324677134916834,52077939480668886605520797676936869466068454501989317⟩
def resval3Tail92 : Box := ⟨-11330491878153973746948539387261168005888078630962955,65980025523024327184049099596135282375925263794769201⟩
def resval3Tail96 : Box := ⟨-16797965520955841665842857425414985677908585299817155,83283458052449003806393170246859021423266460954376962⟩
def resval3Tail100 : Box := ⟨-24903741927327034524120775495325003830229445587971978,104655491165150198676574619301305669598354147322596690⟩
def resval3Tail104 : Box := ⟨-36920921239491620065307642551247729170473197415251626,130798464438505179016079421741184351314465884344655661⟩
def resval3Tail108 : Box := ⟨-54736931869541476440645686352303757326781432985167527,162382231780694537867459040586889151839662601671700779⟩
def resval3Tail112 : Box := ⟨-81149971612465658203287825883564681335720045627966683,199919095231620612090571206651938048783487945090202596⟩
def resval3Tail116 : Box := ⟨-120308494973727259770799044468168435541251006004398677,243546169020229042649520336605083593206852905354490849⟩
def resval3Tail120 : Box := ⟨-178362772965159583195997789001392342101446234015010483,292661014876972174561233859715162291068884195277439442⟩
def resval3Tail124 : Box := ⟨-264430859905349041689632989864163160597922482761728611,345327460292615341538656075294639501783228890918837942⟩
def resval3Tail128 : Box := ⟨-392030682792428047790748969320786440779383206756910989,397324799133375315772008698178887820160953226346322135⟩
def resval3Tail132 : Box := ⟨-581203178425205721360916118511548157717481924436141969,440647702828912581754762233768758660715754906594477957⟩
def resval3Tail136 : Box := ⟨-861659940002422547065346008106016356898927420742745704,461165133659668835961956319055394097721253767351843562⟩
def resval3Tail140 : Box := ⟨-1277449797207452799396567510962170047143082261698979909,434997933004910632222696158389105237916606190442874300⟩
def resval3Tail144 : Box := ⟨-1926550604599149170226789371175574396898345396680552582,319851337782286645576588347041913981485768517852409487⟩
def resval3Tail148 : Box := ⟨484720253156010843336290471742489981664164391,4269373457020034032206498199237514767011332033⟩
def resval3Tail152 : Box := ⟨647511755406270382281910117021921406209576368,5444107304836413899553646810429207154123746330⟩
def resval3Tail156 : Box := ⟨959964264455238187044066355602315111777880671,6925868739424172496322349814244228661154095199⟩
def resval3Tail160 : Box := ⟨1423190342080481915203273348600688871711369075,8785322284637571043939288504166467572788594113⟩
def resval3Tail164 : Box := ⟨2109943906505371953868947984165585114203352091,11105366384942946916411844363555775988077751616⟩
def resval3Tail168 : Box := ⟨3128087056923308821368285155200744855179356282,13979637886491148187991335690985300159410251754⟩
def resval3Tail172 : Box := ⟨4637530223207488158526908946823570087384028448,17509074456132953361929034070136569984933979986⟩
def resval3Tail176 : Box := ⟨6875347833930241447825001901361967906522947117,21794279509580971892510583210335769511873103003⟩
def resval3Tail180 : Box := ⟨10193013427917951784631464470933792681124191968,26920916400908732214509203803410161931659933366⟩
def resval3Tail184 : Box := ⟨15111602387442182400602615216035068453642583724,32933800185634075625349385280342222056274983254⟩
def resval3Tail188 : Box := ⟨22403632481311634064692128674442110295446338710,39792979924201958942482235082830271514939168810⟩
def resval3Tail192 : Box := ⟨33214396163227667647313209078350623424192223816,47301498959888161119671617278373647534457330936⟩
def resval3Tail196 : Box := ⟨49241841179464194336581756128942309000545218231,54989066529938649204418353836782357233059763702⟩
def resval3Tail200 : Box := ⟨73003251687233005225346367185609543313243636144,61927647426711187594271790878730218363956811844⟩
def resval3Tail204 : Box := ⟨108230615047190648895898612514378990768991455258,66442597877874979043585575178009027833922455073⟩
def resval3Tail208 : Box := ⟨160456770935072035410881626044855313164654681270,65664388220630526848694678955913139259051245715⟩
def resval3Tail212 : Box := ⟨237884403871395374286427396581740413215982691683,54838090693103082879633449593248600043586637614⟩
def resval3Tail216 : Box := ⟨352675296340014460514160121511771083832401042755,26265999879414317078631369613537551030202812924⟩
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
def polyval3Tail5 : Box := ⟨32670802394827479098655186782418990209361764287325518163,294941829013343968219862154301381620000924262113257202875⟩
def polyval3Tail9 : Box := ⟨48433223485378597990753427857977496743319491670425154648,375671479994052457565487735596986911508749582799247120304⟩
def polyval3Tail13 : Box := ⟨71804439229117286848111445416300631340920303903976381123,477215330383470490210627848991003244798269701716094920389⟩
def polyval3Tail17 : Box := ⟨106453321479006440342583267804704446172196062793956560152,604273782152065467707448210880927160822250541193188008405⟩
def polyval3Tail21 : Box := ⟨157821853016227339843954390409729398439683445021910569802,762241583301123864244027375430060138921428059256646611756⟩
def polyval3Tail25 : Box := ⟨233978019130082096398836413196397893786592411833917875195,957079311487081918513961689442756416113490939755789081197⟩
def polyval3Tail29 : Box := ⟨346882972096443936988270476116566556305077333345482617494,1194986326063091092610207503217396986650154900300678501254⟩
def polyval3Tail33 : Box := ⟨514269659935726815314815546061495877542416728503409303771,1481739156344436892322611489009687012093719427727474308119⟩
def polyval3Tail37 : Box := ⟨762427978323699747475424031038405824598996716729358581235,1821481824811842153633059761761351746592259680660122835036⟩
def polyval3Tail41 : Box := ⟨1130333883984939205787488974578363134382055191469997256923,2214636246549201515812809272415404253307301238100757531091⟩
def polyval3Tail45 : Box := ⟨1675770991633299371323328473470453760835178782695058167880,2654420859718511914224009772756529890725527697722993805849⟩
def polyval3Tail49 : Box := ⟨2484406117685726778462656926946078057227586302963719644276,3121192957281034790135729859527536139050647022492445820575⟩
def polyval3Tail53 : Box := ⟨3683244183370440663249757261043252858629117207373181984133,3573418354447271656272221466343925223911333989844888371740⟩
def polyval3Tail57 : Box := ⟨5460575715764799572175620454024556343392227703264607521089,3933451663562046760163849736391408337186365972603866365301⟩
def polyval3Tail61 : Box := ⟨8095549918255677682842233903181043368188494716534355975899,4065378048787569894273161015283330763846442929561732245237⟩
def polyval3Tail65 : Box := ⟨12002018082046834120058958842110940180477392819490362767055,3740768589525494305301156976043029190754718759042842136045⟩
def polyval3Tail69 : Box := ⟨17793533461367178945329689309315637475352070748069086391830,2586106421249160999363422427804032188065190834127587363363⟩
def polyval3Tail73 : Box := ⟨26406250000000000000000000000000000000000000000000000000000,2⟩
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
def resval4 : Box := ⟨102925768684126401059365193761494442879880454827715537281,9495132592823983505802903620195682528845624769808173921⟩
def polyval4 : Box := ⟨4537725835679292851217424203061892113574879327928049786650,1854626166328485936182256337104624295183523382073687777987⟩
theorem cell4_lo : Holds Q cell4 (15/16:ℝ) := by norm_num [Holds,Q,cell4]
theorem cell4_hi : Holds Q cell4 (31/32:ℝ) := by norm_num [Holds,Q,cell4]
def resval4Tail4 : Box := ⟨-4381576108815372435038124292553930066543348250077916111,10180481518220540838754158250503236741225378529883882063⟩
def resval4Tail8 : Box := ⟨-5309281136012042434657841395196724037543568403634371759,11224695027414609125111666504619853397226435475219877692⟩
def resval4Tail12 : Box := ⟨-6433336661289143821690942324191971302577497312544637005,12339523506373293578519748840788026941440220231194930832⟩
def resval4Tail16 : Box := ⟨-7795371820840518698010254392953511248206662240597069253,13519542104420626542371528447141420195550783275977692688⟩
def resval4Tail20 : Box := ⟨-9445770526944151494659469490065614604957183219779118044,14755419466672285554517023499803387938701412223747124930⟩
def resval4Tail24 : Box := ⟨-11445583725609434095070563804716424958837472610587852191,16032716170923887039441929349636191503277231260300830907⟩
def resval4Tail28 : Box := ⟨-13868787776100722776757892181588568456000898381439650597,17330379099701044316152140253483996310961868621680812064⟩
def resval4Tail32 : Box := ⟨-16805020957398070929030186648089307099653691953904461972,18618859610516154878080239530785042072022429003334149743⟩
def resval4Tail36 : Box := ⟨-20362899334666217383323676069239392771258292310186526590,19857768078831935057117576198138598773815771032558214327⟩
def resval4Tail40 : Box := ⟨-24674034645057054818323490902683956606283813602782481344,20992957825905964640172196699080766708108839521248023725⟩
def resval4Tail44 : Box := ⟨-29897902831009365267699580121868760484084949772367530891,21952907596942483246172071973294726976461265595632421694⟩
def resval4Tail48 : Box := ⟨-36227743316051052375963804204208187988594192316062216215,22644242697585927729526718610643461022123521351283031669⟩
def resval4Tail52 : Box := ⟨-43897707246959196752856064343773785131742282813432086471,22946199503656555320851428890623036154826087282147184000⟩
def resval4Tail56 : Box := ⟨-53191519127440486351245001694702244049965888715951240168,22703794963883540931949261860439095448822065515321601602⟩
def resval4Tail60 : Box := ⟨-64452972251319339147597135606467087746093984054792741123,21719410259335652187783232515428248991070591872907612320⟩
def resval4Tail64 : Box := ⟨-78098646176265470642713795683524989191905036396075373558,19742433952136768102788334398969580166531052328960595874⟩
def resval4Tail68 : Box := ⟨-94633278429793753744380384918932624681716960552780314576,16456529675158536495307565940862597099638623532738663044⟩
def resval4Tail72 : Box := ⟨738276479680621554569853354902855125631206145217965407928,1145270215314640044227266220856226566778630765766308957⟩
def resval4Tail76 : Box := ⟨-54890891944286296927269490223658860703362042545562047,130489980679796980327092090046915725316592123525580248⟩
def resval4Tail80 : Box := ⟨-66484969755841255850390940322842055795263835185089593,143972841688463434872703649593247833434021551646596594⟩
def resval4Tail84 : Box := ⟨-80560847130023953486633891560235583507418528510570438,158395288071161889785801250132346485301298344654424410⟩
def resval4Tail88 : Box := ⟨-97616803012125898428663108065840489800318063614045604,173696646735230569550193049109072079238509664677325345⟩
def resval4Tail92 : Box := ⟨-118283764009991467334511436907658092379570011083469527,189768540033211215434879867858351436771284607832456047⟩
def resval4Tail96 : Box := ⟨-143326234794163302072374757294706065397282744609857856,206439772437296819751687552403017971073470849368022787⟩
def resval4Tail100 : Box := ⟨-173670577295260956201413923339691056882445062898673658,223457631807440041776365304490678502201663722938287517⟩
def resval4Tail104 : Box := ⟨-210439278345554368147549715555448060795168580501216778,240464500765125087578334478307078128003212502421144451⟩
def resval4Tail108 : Box := ⟨-254992472301789994129634560510134473586747387964174797,256968686226018058923230693269160362067502083228349687⟩
def resval4Tail112 : Box := ⟨-308978254638425207840265644460201185624708570812757479,272308130581244791041242256891164756291865735429833365⟩
def resval4Tail116 : Box := ⟨-374393647693329831811775501605143109762710084826342072,285605369836429306040493147953714935422167696756355854⟩
def resval4Tail120 : Box := ⟨-453658473788547503034954861142683312147396125274407139,295711740646516472502531249803303663184560625851192129⟩
def resval4Tail124 : Box := ⟨-549704868413612419299710092227845826252883386366876375,301138395541903095410319590029225171516053786222709533⟩
def resval4Tail128 : Box := ⟨-666085744710397395074101943517687710797548237579220557,299971146627664936583024699945247193180666644503932858⟩
def resval4Tail132 : Box := ⟨-807106221538098459473896713561310511493574152416290150,289765501889636500963203445321359414634864482867893313⟩
def resval4Tail136 : Box := ⟨-977982876863330219370347555273850023385739023413895463,267417459750367363012522550727711439919222273691102065⟩
def resval4Tail140 : Box := ⟨-1185036767112433431555909179261862971153560064746795744,229004650843798969339638760758994591728891585848981146⟩
def resval4Tail144 : Box := ⟨-1467021451136295046442614199868612823884460405363523377,167134404001244258527658147286573484005962420235271311⟩
def resval4Tail148 : Box := ⟨14959597961002055059260143117270739107632183913,31813698660819048094433387678305925093424112327⟩
def resval4Tail152 : Box := ⟨18068757255421676889109752287950696825733208193,34983201061592041357655014511072476694177755459⟩
def resval4Tail156 : Box := ⟨21894186894090569910769355369337297722205959035,38341594893219525375913664076577457163116106772⟩
def resval4Tail160 : Box := ⟨26529519056509339737411858813895638877415938264,41862856561562434200276061526794867086895862737⟩
def resval4Tail164 : Box := ⟨32146221496200031338008511202996222506406892354,45507241344487792601138811436634181388252209241⟩
def resval4Tail168 : Box := ⟨38952065217677356803984330598126887493272814887,49216538908960882567956781286278554540924848327⟩
def resval4Tail172 : Box := ⟨47198809505544663759192294170687039938961202055,52908802818044965980344473082604045137587055480⟩
def resval4Tail176 : Box := ⟨57191514911761302293357055939008072480377153005,56471779912958784842422902956938608940069438850⟩
def resval4Tail180 : Box := ⟨69299827944134293396397571771807160871433170001,59754739341423577067019225419670740671472298820⟩
def resval4Tail184 : Box := ⟨83971654894894212154988844546602862265507302554,62558334077767080418749973510088221825490904242⟩
def resval4Tail188 : Box := ⟨101749730626626255095272705857976679059581420007,64622046211147100921321546380967905253356168062⟩
def resval4Tail192 : Box := ⟨123291695222032669088823748394212859094566401516,65608667920164459681030806671951107581135689295⟩
def resval4Tail196 : Box := ⟨149394421165620062257694956098297365208954202744,65085149068508340345479644307667331235725025411⟩
def resval4Tail200 : Box := ⟨181023490959529259426780197956400035017807296821,62498995088780875391872665262571536705944793258⟩
def resval4Tail204 : Box := ⟨219348915598703603593811871453475460721132008606,57149219614889657554062417877047646526717285332⟩
def resval4Tail208 : Box := ⟨265788415190187926647916496044097806071194936502,48150638312368962182173112436863246070338024887⟩
def resval4Tail212 : Box := ⟨322059862757040172954092495600147101142190011401,34390025205931055024636340826839143430505339804⟩
def resval4Tail216 : Box := ⟨390245719914627040149771674474638953822544814949,14472240520581577025577289236376762675850452446⟩
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
def polyval4Tail5 : Box := ⟨1008051204921433372442994956424901662594812511675852697966,2037885271373497502998209568940491426483988051246207718870⟩
def polyval4Tail9 : Box := ⟨1221468755402066294358732816693239752643994226973254077631,2236919259415814626847308155001309858760462454378840003334⟩
def polyval4Tail13 : Box := ⟨1480072257364153013223439384600708329747070055421844516034,2446619903243828982603721956774160401551802236581212982973⟩
def polyval4Tail17 : Box := ⟨1793426051722254940319228030073865561938081018533800264963,2664983837172047806826381601803265624758318288147784777903⟩
def polyval4Tail21 : Box := ⟨2173121607403366637193689453073859372115077159505688878056,2889006495430496391781078093556405906636920807768558599341⟩
def polyval4Tail25 : Box := ⟨2633204483691057924064544520244223082141967445655272838713,3114391984128429402604606626079692559724995681905112611099⟩
def polyval4Tail29 : Box := ⟨3190693898265432634877933104770486516949314679684449155252,3335190963952412701530140566926223536594616279610139939815⟩
def polyval4Tail33 : Box := ⟨3866212295885904557813701342671608426562401177800644257021,3543349852982328423850777208726444936265724111563101344476⟩
def polyval4Tail37 : Box := ⟨4684748206333853763148491147762525950494963864190189017934,3728150947893994078947318677143246271490909553448539158097⟩
def polyval4Tail41 : Box := ⟨5676580610977378166971193989957117394317061830024497566416,3875518522170238161052828738685730279018040766049038722699⟩
def polyval4Tail45 : Box := ⟨6878399011788409575191936020070110413370546014684896032175,3967160429349794037692866881888296067011631180999752082379⟩
def polyval4Tail49 : Box := ⟨8334660635996086748340086329823561103507002591632615801981,3979508003970879884358910195341778843850362431331108974354⟩
def polyval4Tail53 : Box := ⟨10099234981595103001487604986310450902904503555229204609389,3882408853057278486472655805136472887196080138131342810615⟩
def polyval4Tail57 : Box := ⟨12237396538135680449169124634502694668673948393976957920390,3637517151498291695606832021865354598659189860460529548025⟩
def polyval4Tail61 : Box := ⟨14828239396794648582485514591036942330543263544523954367516,3196313912790770345757780155453184381204673187823586228848⟩
def polyval4Tail65 : Box := ⟨17967603070105703653672996436404604689145275469014369798226,2497674937817714797012028947277220855551721655847184102995⟩
def polyval4Tail69 : Box := ⟨21771617789548628856163057268913825572584235065307505626959,1464886181031078974046141474083974027761654601658176541038⟩
def polyval4Tail73 : Box := ⟨26406250000000000000000000000000000000000000000000000000000,2⟩
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
def resval5 : Box := ⟨89441986381080166372656155437041298636061765477977894531,15620604960211765039563898949279649956291398575287711720⟩
def polyval5 : Box := ⟨8487773429246334607487182523277716406383993312574644912384,3710873135910757366084900702577517228335641643208336964040⟩
theorem cell5_lo : Holds Q cell5 (31/32:ℝ) := by norm_num [Holds,Q,cell5]
theorem cell5_hi : Holds Q cell5 (63/64:ℝ) := by norm_num [Holds,Q,cell5]
def resval5Tail4 : Box := ⟨-18787494316806133844319376955145278161420752144071115370,15746890515888767247835334912344344699906838025490463410⟩
def resval5Tail8 : Box := ⟨-20657121688687260605538690592616341065678703807202767388,16122734098893039895001363580034391461862058627785191377⟩
def resval5Tail12 : Box := ⟨-22712745498850660742354800341298835075826006378944941190,16458530623945524325472137691962527107543879846054108361⟩
def resval5Tail16 : Box := ⟨-24972927774707972511047546518205653317166560817805246145,16745258444877192505643908248465963547253657076623586034⟩
def resval5Tail20 : Box := ⟨-27458024467901660781221871271339689165414523120903722268,16972671534850074690367263766219956503666871910517667149⟩
def resval5Tail24 : Box := ⟨-30190417178215791504527838234361285986963332905932279363,17129155559157357779280108423711199970173522462252591844⟩
def resval5Tail28 : Box := ⟨-33194714734856557611063253636488115642125798158725717836,17201569039515803129302992073149576371091191652077306479⟩
def resval5Tail32 : Box := ⟨-36497974831682105905333275507788406835107915969768900730,17175067238309710907843583564979524890879611605648302647⟩
def resval5Tail36 : Box := ⟨-40129947717710271880219959180985779409841015109169545606,17032906947221598953937096081869261682189708992285462265⟩
def resval5Tail40 : Box := ⟨-44123344137665397178554038502773191826733682559132741781,16756230177929596186038956471017213078831870836383917214⟩
def resval5Tail44 : Box := ⟨-48514129935725107883969822201384251127923381629677946515,16323824546660100343908719149060499335319753411853719124⟩
def resval5Tail48 : Box := ⟨-53341849975765483621575226025341710120205693054588264404,15711857917572463040551641962639516569813976232615543976⟩
def resval5Tail52 : Box := ⟨-58649984295437092976254789224812824670963921157607648082,14893584620110637434151279978288582111340597816885431605⟩
def resval5Tail56 : Box := ⟨-64486339701712869182130469431108671623337878678110663531,13839020280263213471160475885544913720883587139388638137⟩
def resval5Tail60 : Box := ⟨-70903480334744926800865384717221788016866241924429112194,12514582002573266907128878072657846943890230904541636916⟩
def resval5Tail64 : Box := ⟨-77959201075678256513257920837558688517738854483521336223,10882690305704280866088927567639759038955546352033824080⟩
def resval5Tail68 : Box := ⟨-85717010676393775756225885935760246915493927391333851160,8901325970538325740763872859290654756233070681929603452⟩
def resval5Tail72 : Box := ⟨738265403539113839054499465980530632318147024052342522415,1170613412698530142227587596176303503184101574065893223⟩
def resval5Tail76 : Box := ⟨-240591716160091016060671100048401493413724368462472251,204843350442522657696783585058495714556028006814120093⟩
def resval5Tail80 : Box := ⟨-264508778627208301777380346766218887779518985541165086,209864327929981675128782485385534632424447734012463200⟩
def resval5Tail84 : Box := ⟨-290830476562474603095057251127519494771578593913921786,214386292198500978834005428328322353603942263219088663⟩
def resval5Tail88 : Box := ⟨-319771490691477333814248626037057438459367917429415480,218294391418909329979295161438029942977450951048542314⟩
def resval5Tail92 : Box := ⟨-351592472246542805831266959592271498222155201541618071,221458367300160156615623217120807262616686778378944369⟩
def resval5Tail96 : Box := ⟨-386580011473584371220742318563724906097804933847837480,223730501836032625855523219408422227889388979513716646⟩
def resval5Tail100 : Box := ⟨-425049217680985508098605695616000106559515058943976226,224943587409201614924600624592764647139101955817586752⟩
def resval5Tail104 : Box := ⟨-467346557217335735872234248398130425137018914184290848,224908675906390580913411593614565773651633329720216439⟩
def resval5Tail108 : Box := ⟨-513852973861542335952022082996559830570406842896877848,223412583594424903574459844127467929684714065337452265⟩
def resval5Tail112 : Box := ⟨-564987319728042794248517060870987427132732119629313489,220215126135891793442431375693775237510136148733998740⟩
def resval5Tail116 : Box := ⟨-621210127586979690341961534124820351690161514656653624,215046055487906179532704899825982805583036058596831434⟩
def resval5Tail120 : Box := ⟨-683027758574096682381756601663374496600571863941291874,207601667524457387204134684512664590764446759757956026⟩
def resval5Tail124 : Box := ⟨-750996962645997784567121381985229456894417329671205580,197541046024973908991904162988052574984346552754133340⟩
def resval5Tail128 : Box := ⟨-825729892853732926286082855981682073858612771990708691,184481905149370457057857209733625502081785879381400496⟩
def resval5Tail132 : Box := ⟨-907899618594916491259045902924936304900820056021860669,167995988640226245700805102436435125542688855773175108⟩
def resval5Tail136 : Box := ⟨-998246187504427724209602528285003186475252502905999279,147603979719178228397731562756914646963605759439966284⟩
def resval5Tail140 : Box := ⟨-1097583339071839307910758809562588772899944588612290241,122769866158166046433180498679287190537204575228738244⟩
def resval5Tail144 : Box := ⟨-1237166318823635171805911707312651303220580748573742949,90725777042574218523527946392704952272190798610147553⟩
def resval5Tail148 : Box := ⟨81728125116917595806029559580446084556036264311,61544711937547061704730312770075359428113881797⟩
def resval5Tail152 : Box := ⟨89808427582998416479810703951517233688290121243,62728461303714715886227376251454793249155434529⟩
def resval5Tail156 : Box := ⟨98745409565054203015908345884607953951266793504,63709402571122831772529499270011513974562091629⟩
def resval5Tail160 : Box := ⟨108571726006043608522119952562440694120145193237,64445871983587697532200707803219420172262564111⟩
def resval5Tail164 : Box := ⟨119375875191354510135581174645088372876855884368,64891299295600945581439408175306001709498545949⟩
def resval5Tail168 : Box := ⟨131255162848830810751540728672594796226741624800,64993033796697660226137368967125828722728951297⟩
def resval5Tail172 : Box := ⟨144316577757921926108894058910089372886933423244,64691645187117205968589005496845158085736328897⟩
def resval5Tail176 : Box := ⟨158677755325674413453276070662083081186859192778,63920148784230870212703933579759368175560475195⟩
def resval5Tail180 : Box := ⟨174468037049974127340813097181177596880537983048,62603147116556132183197439571304791126962684552⟩
def resval5Tail184 : Box := ⟨191829635411700529811156007995354954300587214639,60655879161569735669063078245333168682141240251⟩
def resval5Tail188 : Box := ⟨210918914687195461448948849705148477729243548421,57983167585902470447097119750641057767710865506⟩
def resval5Tail192 : Box := ⟨231907799216465555682379426763329539061550893043,54478253357747952024326728633910690293528335580⟩
def resval5Tail196 : Box := ⟨254985321810445820514827907642441521084168064768,50021506012268655130299676885106199426301790939⟩
def resval5Tail200 : Box := ⟨280359326242790479608305824105571382942614217906,44478996651330217219886048139866427140495353850⟩
def resval5Tail204 : Box := ⟨308258339159393212706235930445666288659926976670,37700919437921177942888844787862754593142558101⟩
def resval5Tail208 : Box := ⟨338933628264678297443856736977333966404218280121,29519845890885402222903566852945601050454845831⟩
def resval5Tail212 : Box := ⟨372661465340568796339392718518942366079755192447,19748794681449090362680786077959730449738776180⟩
def resval5Tail216 : Box := ⟨409746482811340094341855550565509122048043182243,8179016359381111486928106734478095092350590124⟩
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
def polyval5Tail5 : Box := ⟨5259012153478091055297085755561045945270937281258593281405,3782667467191685418523045494038510984096304819534972404614⟩
def polyval5Tail9 : Box := ⟨5782343009192639741725682888139201799603602919927851719911,3847223214656223723404379482882082786952949688996866545621⟩
def polyval5Tail13 : Box := ⟨6357753374222979604467894226007246155604248516397543016913,3897925702308752987565793602711276505243042171432156829150⟩
def polyval5Tail17 : Box := ⟨6990423761490142905358107038045455823873296252456598766655,3932077925249987677259220828439724170156800993345232450337⟩
def polyval5Tail21 : Box := ⟨7686052208840055430318456303355787623068706337984704500742,3946628787374148401613319639594163579601734711172787817207⟩
def polyval5Tail25 : Box := ⟨8450903775313049639057751071572654709018240116329589529554,3938132275279653529048743287353136023582261481410138579503⟩
def polyval5Tail29 : Box := ⟨9291866966172794972498125860254898452123657520267951077176,3902702223237418705630732928797618245448512503926752003144⟩
def polyval5Tail33 : Box := ⟨10216515773054692529090499021739667806869720908867217543406,3835962190782078696583823392296638221721696509334477583949⟩
def polyval5Tail37 : Box := ⟨11233177887830543982534315722309494056272679383706913649800,3732989941476574824888450548630680252463790331695261945156⟩
def polyval5Tail41 : Box := ⟨12351009704545930955487937633255602262747939371934329148147,3588255958876752727267889904369443803723576197288323751557⟩
def polyval5Tail45 : Box := ⟨13580078784922469371827773388760870091946458564411336659455,3395555377862905609122553621023165160329324064730218232662⟩
def polyval5Tail49 : Box := ⟨14931454530136428504994731362254303192136610353468966752302,3147932645774779406750615735347124054602192928675690774788⟩
def polyval5Tail53 : Box := ⟨16417307875493633753280608512376583464079721164257785548408,2837598157593881156535829652750130442968833740254649628369⟩
def polyval5Tail57 : Box := ⟨18051020905883749610888828040943432717738064427240758085628,2455836032111106394256779496384992695167525358404680110749⟩
def polyval5Tail61 : Box := ⟨19847307379246852287553277325863972580640051355783772442235,1992902110882550589262080423857373263510723216883182229990⟩
def polyval5Tail65 : Box := ⟨21822345243530701198062264175635458409736036098780026844421,1437911168023388221760657273452050344923709944940383298987⟩
def polyval5Tail69 : Box := ⟨23993922377146033841237710590541985237515562365115179789895,778712212173707606345045298042926598763374357590824147736⟩
def polyval5Tail73 : Box := ⟨26406250000000000000000000000000000000000000000000000000000,2⟩
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
def resval6 : Box := ⟨70334511365013876984339479547315766549287411714426514637,14402997502676444093280310738163909160070824950105697291⟩
def polyval6 : Box := ⟨14994503404862032773819422081819346678589599518078879435010,3713817394735156380804905999883598927048926945318420291728⟩
theorem cell6_lo : Holds Q cell6 (63/64:ℝ) := by norm_num [Holds,Q,cell6]
theorem cell6_hi : Holds Q cell6 (127/128:ℝ) := by norm_num [Holds,Q,cell6]
def resval6Tail4 : Box := ⟨-37935485425832559928594627796582925814121830809298774392,13979582157128944897818734569259618979511667130727671674⟩
def resval6Tail8 : Box := ⟨-39767105002155825119852530891815004412551359335916775368,13802546017404455004175890911951275991793476096537577477⟩
def resval6Tail12 : Box := ⟨-41687106577117319550167675903417026081087170596181560030,13589810315296982504020229523835808966639506093259285881⟩
def resval6Tail16 : Box := ⟨-43699808031022310801362981198345827541320281443759332043,13338785327087376537760561138133457670212778944840712372⟩
def resval6Tail20 : Box := ⟨-45809685026119254437554131600267331310414485619924757969,13046729462475761488566820349602218416511248027573675411⟩
def resval6Tail24 : Box := ⟨-48021429309312256492389310688355722117352708593854060912,12710740306171038983274328450033665355115190454054601303⟩
def resval6Tail28 : Box := ⟨-50339959150437991738309737095736195768348234971475531303,12327745945980285364549717761181856762796442717948859477⟩
def resval6Tail32 : Box := ⟨-52770430279057810398611404853187989307142595706219154790,11894495853441548605812125888947842479033436674424999876⟩
def resval6Tail36 : Box := ⟨-55318247349286385778092964232566137814853934103272771500,11407551294337342969276995585339478453425355714358541879⟩
def resval6Tail40 : Box := ⟨-57989075958155460974903972977304185055151677955569757258,10863275245440223007310359257031479497601112065041182012⟩
def resval6Tail44 : Box := ⟨-60788855244238020602284342214025250971212093541467303614,10257821792669905820476035745940392476310717464259133272⟩
def resval6Tail48 : Box := ⟨-63723811094548528406241270240238704089142460777709848702,9587124984611787867175419575470313533535922266818972723⟩
def resval6Tail52 : Box := ⟨-66800469989087498823551362586375960010755987772420327433,8846887114056715374326420749669007129485955370125404061⟩
def resval6Tail56 : Box := ⟨-70025673513816599371666555595369807757234710980978336723,8032566398868569325652569131686721056966980485563553256⟩
def resval6Tail60 : Box := ⟨-73406593574335439808529386043847770962711022890759888694,7139364032066334534007359404400759127089518779657948745⟩
def resval6Tail64 : Box := ⟨-76950748341961256013475275884586675130672979339036983767,6162210569294317250711162860584859582628580285485853481⟩
def resval6Tail68 : Box := ⟨-80665981998903744688298289647503077068505669448954753239,5095748628718213506207394619813162535629780777235605341⟩
def resval6Tail72 : Box := ⟨738097995246711774542742312362475153905591814887089963694,1128488661189640370903029051237213436649710110582932305⟩
def resval6Tail76 : Box := ⟨-490008387383678604001547223759923784607084014571163622,182749466689097458553800295858176065952386557612266912⟩
def resval6Tail80 : Box := ⟨-513643107358319274786755821678603876559443838131226832,180532235966084292320623040778035733731248664679005539⟩
def resval6Tail84 : Box := ⟨-538442386241827756548805687510332755607923205164742713,177856338259193872080271306108004728558031097325239697⟩
def resval6Tail88 : Box := ⟨-564439003963474221838410801952893147589450870087030128,174688175456299271882535940148986792816843422476411204⟩
def resval6Tail92 : Box := ⟨-591690768290504771851688475887921728073826199900024927,170992409371188203573523623604955988348896348557176218⟩
def resval6Tail96 : Box := ⟨-620258279144125275788641298419151181340721727461191694,166731626902586500431827939319171032231208941397657112⟩
def resval6Tail100 : Box := ⟨-650205062280004960540459074720628736757389170241151348,161866228079753912455540598763521801861094962490069059⟩
def resval6Tail104 : Box := ⟨-681597710550365216027638960743163788228277738068881875,156354308350651765201169673561309957104130371962681855⟩
def resval6Tail108 : Box := ⟨-714506031986927546926061931632473456496059904779459831,150151534800370263367754553141139263471599639104924923⟩
def resval6Tail112 : Box := ⟨-749003205033477914868061071467023248769593602413445058,143211015994426106855872115584104438640449575481488969⟩
def resval6Tail116 : Box := ⟨-785165941273237845795742969023842633280535043571376258,135483165126421583652688025200357797047235975096605862⟩
def resval6Tail120 : Box := ⟨-823074656012900183054491999122508076306036095983939180,126915556133676756019905417218695619997660789650966091⟩
def resval6Tail124 : Box := ⟨-862813647102658292275572149202787723368315373125134725,117452772427787155590448289447772305532296955893504070⟩
def resval6Tail128 : Box := ⟨-904471282389871985493560532422985058719049254270787544,107036247869582549972966352071886884797674898512278415⟩
def resval6Tail132 : Box := ⟨-948140196223218351779308968791681720088296440479810685,95604099599627021305858910621825860131940784061030530⟩
def resval6Tail136 : Box := ⟨-993917495450117942298671190710630005810485491304131150,83090952315470935945501681604932124797352211265691139⟩
def resval6Tail140 : Box := ⟨-1041905023325834488044602051496259621860684463166871787,69427749005461936950768450669268019225217162528670021⟩
def resval6Tail144 : Box := ⟨-1122216051161504876932610798483468015988443653143912127,52508903227469592338849520482679347551607945652264182⟩
def resval6Tail148 : Box := ⟨188322029617189970293992275212404457908221818024,60820512638456504557343723197637605596354000171⟩
def resval6Tail152 : Box := ⟨197364310332845357127771607699238706763664979766,59668502831945805990672690871680188740551055970⟩
def resval6Tail156 : Box := ⟨206893285448484834564429950127699753886002433226,58331167902345381692142972177981496226519368538⟩
def resval6Tail160 : Box := ⟨216882331237611475076352645842004966240881014763,56794830835934109502418408623712269020555826912⟩
def resval6Tail164 : Box := ⟨227353659647026183347965593211275292553388377239,55045599148383792463851701198541855620624261267⟩
def resval6Tail168 : Box := ⟨238330555836131373686876064484023483939883382630,53068773081076215460810009115634905275331174982⟩
def resval6Tail172 : Box := ⟨249837429198832364502949989720532085784257694100,50848802258015541232394435428105191277737800638⟩
def resval6Tail176 : Box := ⟨261899867642648163374199241549452236467869448230,48369240126673565218308568175381924202984265810⟩
def resval6Tail180 : Box := ⟨274544694488703915046573785480128474758668684492,45612696056085439370217278036671648384009848690⟩
def resval6Tail184 : Box := ⟨287800028118920772019081144304918229053122791384,42560784974517577059975302539844696167855734047⟩
def resval6Tail188 : Box := ⟨301695344503040699952287914491319971621274654591,39194074423209231303938881358727664923573460175⟩
def resval6Tail192 : Box := ⟨316261542744527959066876817370761347850998265009,35492028896576616548024321511937498571165048181⟩
def resval6Tail196 : Box := ⟨331531013791102099724699736412638858850564410842,31432951332855902930700346029447210948864765222⟩
def resval6Tail200 : Box := ⟨347537712462694521790580840396186217608184837802,26993921612434333175589396972626670854079261084⟩
def resval6Tail204 : Box := ⟨364317232956997640282894426254830538012949470861,22150731914061750033908645432368901870882223305⟩
def resval6Tail208 : Box := ⟨381906888000516230007874021541120663402883747948,16877818771730862202665642689966278321033734404⟩
def resval6Tail212 : Box := ⟨400345791840127373316543281681310726147847260404,11148191665135374179297670210824990327980644094⟩
def resval6Tail216 : Box := ⟨419675805750841988367626702368458857839751062909,4933280434619772171667708337888145386560573114⟩
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
def polyval6Tail5 : Box := ⟨11835420113397926619635633964111628809613843523936439495220,3642334255684782974066947078924055326004229762902508357517⟩
def polyval6Tail9 : Box := ⟨12406845900267599718297143137487065713627154311399839138344,3564182920336508673453007246364233080790945516104683174058⟩
def polyval6Tail13 : Box := ⟨13005862690475973677180480395897354768253988138356099063697,3474163143325092994584410449974454392617865011558498489692⟩
def polyval6Tail17 : Box := ⟨13633800700467677500855952846701707768594933024009760531755,3371443891859476976254770543244989140115139294450276300985⟩
def polyval6Tail21 : Box := ⟨14292056279833895991422764849400425572531426682236492590325,3255145803536615249450314342163014582055248102214372206008⟩
def polyval6Tail25 : Box := ⟨14982093195695072755104254189715947234441749862543212479493,3124338574981737769184473590832226653616824070525273772149⟩
def polyval6Tail29 : Box := ⟨15705445887531960879403845632513967014018583653495559689585,2978038231960306738292520206316509017196800500021484010967⟩
def polyval6Tail33 : Box := ⟨16463722879328351231822022756577808480563689313227789122489,2815204259073340258059311761778276044633675470893581232219⟩
def polyval6Tail37 : Box := ⟨17258610356456090502214518722171105283712424828801440027525,2634736581978951741293447195697812421729879827503655444621⟩
def polyval6Tail41 : Box := ⟨18091875915256222378685008840931853020470843156801098232193,2435472394736503902442756141723083669014761472787013707512⟩
def polyval6Tail45 : Box := ⟨18965372493654218977224120295548256718771643610839177892647,2216182824503293388975247846835458249933337566914977053964⟩
def polyval6Tail49 : Box := ⟨19881042491549836624108838555558467772492319337848664917705,1975569425429213933576726141034551984851370523713199654829⟩
def polyval6Tail53 : Box := ⟨20840922090144133133122895350824774835438685292884145254105,1712260493191518124754749541641410809761591213649316274731⟩
def polyval6Tail57 : Box := ⟨21847145779808561572334061137460662912088780244542547584023,1424807191188690496650676065903399648648060044638424098676⟩
def polyval6Tail61 : Box := ⟨22901951106564796318086216496071247665145543037881740644816,1111679478968592234020591264543192074088878567727206656479⟩
def polyval6Tail65 : Box := ⟨24007683647734374887586127666235954897009753536593409017244,771261832999927148871538266070003147642054298875449309876⟩
def polyval6Tail69 : Box := ⟨25166802263937493368568071351354045575172933118998369647601,401848746092710819261388302589825716408955585623410138186⟩
def polyval6Tail73 : Box := ⟨26406250000000000000000000000000000000000000000000000000000,2⟩
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
def resval7 : Box := ⟨47398227417809240924654039645489210936675706340364177194,23576408944778412586318367068947727891032000305416544925⟩
def polyval7 : Box := ⟨23607104605370535808336712919711966127613391731280080064366,6484846628247508010868689303666889001034847433448012131963⟩
theorem cell7_lo : Holds Q cell7 (127/128:ℝ) := by norm_num [Holds,Q,cell7]
theorem cell7_hi : Holds Q cell7 (1/1:ℝ) := by norm_num [Holds,Q,cell7]
def resval7Tail4 : Box := ⟨-60053189041711976424878197119153413351638799973399596728,22363861692928029479148613456534931745578779393546669303⟩
def resval7Tail8 : Box := ⟨-61000804697730215031844530669212207887407202689618376942,21416293666556523843796681585699535377794472697588335441⟩
def resval7Tail12 : Box := ⟨-61963323479402271451208744314520300701664181711520321422,20453774889973131649582625368495967058039113817019810567⟩
def resval7Tail16 : Box := ⟨-62941029635753874573646902088843312384250258042009933490,19476068733625593420826009619949002452695370697922385089⟩
def resval7Tail20 : Box := ⟨-63934162810448292145931547828658195312829238935880762577,18482935558931189945835879812932572436217279901953400326⟩
def resval7Tail24 : Box := ⟨-64942966423144527442654946757258899612087898824395722710,17474131946234954810724863689673808584786112563507859072⟩
def resval7Tail28 : Box := ⟨-65967687734364573734967463754633530254733430625612805088,16449410635014908523475119542870560164420877590223924705⟩
def resval7Tail32 : Box := ⟨-67008577906101812385981069899208749613494074967083986528,15408520463277669872810431635578479429204746500066416276⟩
def resval7Tail36 : Box := ⟨-68065892063381517987567923330294004266393528896180519171,14351206305997964271242098376415528466667615451478350944⟩
def resval7Tail40 : Box := ⟨-69139889356792699327589999192345377241224153084753611420,13277209012586782931149339130873079940150854013479906352⟩
def resval7Tail44 : Box := ⟨-70230833026006616876564712745028031035867015829406334981,12186265343372865381812052505909758472892505612305426842⟩
def resval7Tail48 : Box := ⟨-71338990464297545501486125406022268471792186206611430690,11078107905081936753391435667718351250874479505084921959⟩
def resval7Tail52 : Box := ⟨-72464633284081596568104262754150302874887775401047070734,9952465085297885601814790892567568836622441906979079040⟩
def resval7Tail56 : Box := ⟨-73608037383489658236054038950714032138838062711493702554,8809060985889817764494190032103696575503522054728238357⟩
def resval7Tail60 : Box := ⟨-74769483013989341330545224695907956027089837245233081350,7647615355388475570175756815277742873527406613257504548⟩
def resval7Tail64 : Box := ⟨-75949254846957711359519933983776295186038345529096338164,6467843520073597100306430644213384143708972754390079808⟩
def resval7Tail68 : Box := ⟨-77147605343277932022825818382063148372749488073059679428,5269453346201012553672825207921910364218960316859760217⟩
def resval7Tail72 : Box := ⟨737853211106603352655472506393629213516877959496525573304,1245848084618166755204773493872991769293657009215760359⟩
def resval7Tail76 : Box := ⟨-778457338804154088812746910899996322674793452051207722,291986844499605269473764393536734684084660940620929340⟩
def resval7Tail80 : Box := ⟨-790717740753548813799385313341960644540284419152360749,279703855204449414226222982411871011661889089737664207⟩
def resval7Tail84 : Box := ⟨-803194307403922110739500015618944092176000793575213712,267227287455411679492180593552565899439386399538827967⟩
def resval7Tail88 : Box := ⟨-815867740250351015279461945881785017586511501820581542,254553854608422621803755917966570793277016381877461575⟩
def resval7Tail92 : Box := ⟨-828741144509775777870446141660149848247034521313593173,241680450348996465865415970460732557122277615994212285⟩
def resval7Tail96 : Box := ⟨-841817675488216091395437306892969196674322667609214068,228603919370556139946717825969295169117163904884900481⟩
def resval7Tail100 : Box := ⟨-855100538279144449877527197345843144116539797361505588,215321056579627781137272711820818324861226812234550794⟩
def resval7Tail104 : Box := ⟨-868592988548525675675453220829409788012199767151602237,201828606310246555316942561187160810056386783564195509⟩
def resval7Tail108 : Box := ⟨-882298333332788258272251138677127986792332844690482068,188123261525983972716742963616273918094007275002726349⟩
def resval7Tail112 : Box := ⟨-896219931849388008728233452728806432704440898269424619,174201663009384222260092089486612291294945574563538548⟩
def resval7Tail116 : Box := ⟨-910361196320161436768275116305772545489479639031835911,160060398538610794221776014040774501969678426325862831⟩
def resval7Tail120 : Box := ⟨-924725592807670646649280436617784919079575145485556384,145696002051101584362819082003871634357253951313061069⟩
def resval7Tail124 : Box := ⟨-939316642064744742482198901880436586439354707827734043,131104952794027489012417707517514402916357231525648674⟩
def resval7Tail128 : Box := ⟨-954137920397425998353569968884859705161604548710006319,116283674461346261103164440249724410705016379591370828⟩
def resval7Tail132 : Box := ⟨-969193060541538541286141860882796289355234906480238333,101228534317239195120783250368085649436546893113132476⟩
def resval7Tail136 : Box := ⟨-984485752558877650064439489533945657433215916950316719,85935842305025605676139267615873275090169603360816013⟩
def resval7Tail140 : Box := ⟨-1000019792365040880529276318824477733613050034855951434,70401845619479458338170861994590672608199396892283257⟩
def resval7Tail144 : Box := ⟨-1045574086662756057625702435680489310328551542772865683,52607136467538047481707504514829592004132820382254695⟩
def resval7Tail148 : Box := ⟨326779961495845674847330924574430028606569039742,104613506735513748557733293257520912675308212089⟩
def resval7Tail152 : Box := ⟨331887598204367152809419376157389443584061591167,99457518329805752643961840540212307470296502944⟩
def resval7Tail156 : Box := ⟨337124381547563122660327117836533109824842275889,94220734214239680828882854082421127743391947069⟩
def resval7Tail160 : Box := ⟨342443795755386822088115852831753694321843378968,88901320006194548852948703517772617493808388850⟩
def resval7Tail164 : Box := ⟨347847143873475707489810824460569547602580053106,83497971888105314072765423930911307244144513052⟩
def resval7Tail168 : Box := ⟨353335750277003723518788360419575833611307166492,78009365484577295951975723335834014707213472894⟩
def resval7Tail172 : Box := ⟨358910960238397394722254201905539735762285418616,72434155523183624709898727462641073766370971963⟩
def resval7Tail176 : Box := ⟨364574140256852246968364788809854509702467479188,66770975504728772461880284362947863982473609089⟩
def resval7Tail180 : Box := ⟨370326678393265167585121684839325257073567038824,61018437368315851844901527732942370358933648907⟩
def resval7Tail184 : Box := ⟨376169984610451922166740775303433576387344610722,55175131151129097263235167016616182997083095895⟩
def resval7Tail188 : Box := ⟨382105491118732893343258205714244751069502754714,49239624642848126086728141414382159852505979265⟩
def resval7Tail192 : Box := ⟨388134652726971743750482452436076192560007252690,43210463034609275679745553957609541489776798014⟩
def resval7Tail196 : Box := ⟨394258947199153043711946133284772810093205905653,37086168562427975722106732313386780369859833554⟩
def resval7Tail200 : Box := ⟨400479875616586261929053370879557126924588667184,30865240144994757643988930498835408954331006490⟩
def resval7Tail204 : Box := ⟨406798962745824913428673340099128625339746980910,24546153015756121223867823008196749910808865327⟩
def resval7Tail208 : Box := ⟨413217757412398396453356324702417068093610009391,18127358349189057245629375953235891966716875016⟩
def resval7Tail212 : Box := ⟨419737832899311964795683686358355152622829006445,11607282879082355180890995133720503174417973368⟩
def resval7Tail216 : Box := ⟨426361639424192160041281369113891295675193097664,4984251632124840480863939325910392074179442374⟩
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
def polyval7Tail5 : Box := ⟨20217319639949008639062990104339214300571618107382438783900,6166380999174593018257441968114250788050757326290885006325⟩
def polyval7Tail9 : Box := ⟨20536322595113268905164790293122660687983718590161971380998,5847376208458318286886478825296652031416438533148131228418⟩
def polyval7Tail13 : Box := ⟨20860360879256268167761515624754177876287061065059523018536,5523337924154898857170211696462282172535099203074484636612⟩
def polyval7Tail17 : Box := ⟨21189512095008086752036077168045129723952213673793356033150,5194186708402966468479140146463625891836722156452787100786⟩
def polyval7Tail21 : Box := ⟨21523856918073813560400750421149387307865988267053095344394,4859841885337239301265744067231997104850930625239948835451⟩
def polyval7Tail25 : Box := ⟨21863477297283053210821834355077870691629320167871554137497,4520221506127999647014596732474096785873123263422268639577⟩
def polyval7Tail29 : Box := ⟨22208456474518745727154382597030060862780329969537758097686,4175242328892307130565186505197387281099893128408394728313⟩
def polyval7Tail33 : Box := ⟨22558879005119870404331992672957353921731108803861151138338,3824819798291182453378618507016456924060538496060533056040⟩
def polyval7Tail37 : Box := ⟨22914830778606190106424921012192592802758819096919602597361,3468868024804862751284222783707357147480559378871575059496⟩
def polyval7Tail41 : Box := ⟨23276399039730007246260246325381553095224264235151195090842,3107299763681045611448640593627580156135994546035152422575⟩
def polyval7Tail45 : Box := ⟨23643672409860090966707821255961744316388299029492911230958,2740026393550961891002179849719361274229142706636966064225⟩
def polyval7Tail49 : Box := ⟨24016740908703016779587181329086887776458889687404083058136,2366957894708036078136714157756375695263169411424652457928⟩
def polyval7Tail53 : Box := ⟨24395695976367242622127436228726125627716589193239116240312,1988002827043810235912750050880073321321981838552232038326⟩
def polyval7Tail57 : Box := ⟨24780630495775329317172018341283616868983705321422564387223,1603068307635723560036113494822530461838389240491395822887⟩
def polyval7Tail61 : Box := ⟨25171638815429803186417132434770413762048084506592312186051,1212059987981253607325026858470262276227654273515543874361⟩
def polyval7Tail65 : Box := ⟨25568816772542517528962449482778135179566545810844464926892,814882030872340462565164477149599737446531117181830145256⟩
def polyval7Tail69 : Box := ⟨25972261752385666243284244801167392244876924612576069611641,411437083618134187573699812237475591839533215023004787393⟩
def polyval7Tail73 : Box := ⟨26406250000000000000000000000000000000000000000000000000000,2⟩
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
def pend : Box := ⟨1030085822808556933637320196414454656242258756903569146755186,6128425061110181885205808924198886389482261158945441212⟩
def zend : Box := ⟨1003698721872311894694296875000000000000000000000000000000000,4410893714659726484375000000000000000000000000000000002⟩
def betaquot : Box := ⟨428742101387558179879746722635647506495262331863172397728024,394754834753601585531137528036205294699249726012204551⟩
def crit : Box := ⟨104048892101233878258894085541996012168130135874140438319,16112219163853537715951883943607229327093217202516890460⟩
def subsonic : Box := ⟨635781967277681358811192593474821651226850658153020050340,9192792073166620541937118394354926135782931297941693984⟩
def pendTail4 : Box := ⟨26382132977774817486583751130755370092501108236616041129653,1533486274486710297624632561387336820810812443065186568⟩
def pendTail8 : Box := ⟨26382165519151562540314387739922675374994728732920926038521,1533282991519447816930644899091292061878132274110392699⟩
def pendTail12 : Box := ⟨26382165520440035378742368631901958742773385262915962709367,1533282970450883621083244625192194116624702874883891861⟩
def pendTail16 : Box := ⟨26382165520440616868719604466379174901223367144937310402876,1533282970434749898257077324464958596735079295259292270⟩
def pendTail20 : Box := ⟨26382165520440618153304662606148557377171284971577824225737,1533282970434694762270005682056063776213306878452536839⟩
def pendTail24 : Box := ⟨26382165520440618163384426471430555911512700380976218176640,1533282970434694103088296415084350971966066023474838747⟩
def pendTail28 : Box := ⟨26382165520440618163615935598374441190180202497586542604478,1533282970434694079358887818312682477675977089121015281⟩
def pendTail32 : Box := ⟨26382165520440618163629314009443636413150487897293333594604,1533282970434694077009696587261403546416506955269503638⟩
def pendTail36 : Box := ⟨26382165520440618163630887191945341990554199146819286345801,1533282970434694076402295631964842451212621612708526351⟩
def pendTail40 : Box := ⟨26382165520440618163630945584027520017496262003451903364820,1533282970434694076001652357363063439407136341857075351⟩
def pendTail44 : Box := ⟨26382165520440618163629719017127330924362191319890690240988,1533282970434694075327688649080821385321146052557021737⟩
def pendTail48 : Box := ⟨26382165520440618163619589571085270758959282623642650268096,1533282970434694072370942425851442060013659297030178921⟩
def pendTail52 : Box := ⟨26382165520440618163450721710691106067558909738176873356676,1533282970434694036845375424980643477238629371151928010⟩
def pendTail56 : Box := ⟨26382165520440618155987384674784014262816545826328221293335,1533282970434692763122195173022720316804508583737069056⟩
def pendTail60 : Box := ⟨26382165520440617087777970546688338171689192381593808752795,1533282970434535272986778120867130576010226382337814092⟩
def pendTail64 : Box := ⟨26382165520439963775047204904155746569573099979590080301898,1533282970355337966512621820292323081203427135680401745⟩
def pendTail68 : Box := ⟨26382165517574708517511586152965988298174639979259666188110,1533282700354871171617481913815566140711602993143378541⟩
def pendTail72 : Box := ⟨26381782867043775357511373405116875867537099697917937592972,1506075461322639718186702565692471439621843731252919690⟩
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
end SepticProfile.ExteriorCertificates.C06

end
end

end OAI
