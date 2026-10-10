import OAI.MathematicalPhysics.Transonic.Certificates.BarrierData02

namespace OAI

section
noncomputable section
namespace SepticProfile.ExteriorCertificates.C02
open SepticProfile.ExteriorJet SepticProfile.FixedInterval
def cell0 : Box := ⟨250000000000000000000000000000000000000000000000000000000000,250000000000000000000000000000000000000000000000000000000002⟩
def resval0 : Box := ⟨103671993122326247668340020693257567253075594789271208944,580363965092365620026836618076774484493060209819892130⟩
def polyval0 : Box := ⟨3698769950925649180152983302273289746008300722781409060525,19186099445168229554117327666913225596122915183883849969⟩
theorem cell0_lo : Holds Q cell0 (0/1:ℝ) := by norm_num [Holds,Q,cell0]
theorem cell0_hi : Holds Q cell0 (1/2:ℝ) := by norm_num [Holds,Q,cell0]
def resval0Tail4 : Box := ⟨47532635161940178599488920168682209345836866331868,1967191512003141601979243298326386619520190453633⟩
def resval0Tail8 : Box := ⟨5133150893012586391647257700918401564900679057,362561669144795899319227826388307236116556689⟩
def resval0Tail12 : Box := ⟨4170441478838760223354111850620736589409594,438544541147551777448741501308751783508692⟩
def resval0Tail16 : Box := ⟨14924193568169377654041218002561669436172,24375944974254512719179804685585493203286⟩
def resval0Tail20 : Box := ⟨181780058585839645822736547144881953292,354973029729390688671563418471995438048729⟩
def resval0Tail24 : Box := ⟨6468350398041272256342852505326057935,5678986938271521503664307400086103518486879⟩
def resval0Tail28 : Box := ⟨611946689047347103871388468399118392,90863763086000875624440674372267270063505649⟩
def resval0Tail32 : Box := ⟨143451865256612517083083009842926910,1453820205794144330637166874754691854103121154⟩
def resval0Tail36 : Box := ⟨-438947056267657478520391722607896226,23261123291254285761243580423712391622170558770⟩
def resval0Tail40 : Box := ⟨-133875706230796036843620390733111779084,372177972533949805288778750617998242705934890462⟩
def resval0Tail44 : Box := ⟨-34302244343509409866643740325334298282885,5954847528383583585809764729874152794961015643522⟩
def resval0Tail48 : Box := ⟨-8781476836765448825533217900990414843569346,95277552221495612327674362454096815788109786726306⟩
def resval0Tail52 : Box := ⟨-2248058926026414403240394746234104695889704294,1524438727988563050976403999662419596941736081924047⟩
def resval0Tail56 : Box := ⟨-575503101431532364822415020951986859718244745052,24390480113652221907440963822843176905727126693373651⟩
def resval0Tail60 : Box := ⟨-147328793721048549491545251562741068203882859051695,390109561072621245769465497265095879768306258915429980⟩
def resval0Tail64 : Box := ⟨-37716168481259799333763171074598440768600894548820341,6206394066947068401796189843139079902662415139999026581⟩
def resval0Tail68 : Box := ⟨-9655277685228265040270752875421957019217880858871097398,90250445563556323234536190475569251752210786893900138067⟩
def resval0Tail72 : Box := ⟨711930276001243635230652528916584452282794937360251926965,3148060789513703815594192721349994100659724868819052803⟩
def resval0Tail76 : Box := ⟨-21719912201640434173988118724861034763714798821211,677715434678996484264654911945413010726422429325⟩
def resval0Tail80 : Box := ⟨-1047722801223461861794857464731993922100952050,63127653317543617326710314431720288619829940⟩
def resval0Tail84 : Box := ⟨-529162733846723763635344175428639806594349,49307197048625921820485077292252651616587⟩
def resval0Tail88 : Box := ⟨-1308050774166858699786081331904103263405,318844632394999292154128550140018132537⟩
def resval0Tail92 : Box := ⟨-11646137331611916411902929959032115264,2321294038355778141690344875101718726718⟩
def resval0Tail96 : Box := ⟨-313547927243061487214876322969443796,37106668464720580481261802670836796055681⟩
def resval0Tail100 : Box := ⟨-22932515912558215191411080396327808,593705454342131318195051392687919281708479⟩
def resval0Tail104 : Box := ⟨-4276320810658658682070809732501196,9499287146484008735317811361502862754643240⟩
def resval0Tail108 : Box := ⟨-3659979765949583505546582523684562,151988594311734289365796073428674021293177279⟩
def resval0Tail112 : Box := ⟨-439060480193792729418953927623993059,2431817508576427235495062067375224545159787884⟩
def resval0Tail116 : Box := ⟨-111849671989975419589098636842210816517,38909080032364605892310125805645467806111912349⟩
def resval0Tail120 : Box := ⟨-28632041060848650417199581676300336340268,622545253675303415752146856346169146029031730340⟩
def resval0Tail124 : Box := ⟨-7329792777627771788761106433651412046348732,9960717187124331294190949928085616240396159652994⟩
def resval0Tail128 : Box := ⟨-1876426797512714844965065759794961513049173403,159369715843880632022297538553669632108322322961952⟩
def resval0Tail132 : Box := ⟨-480365257793172381801140148519545531662324241543,2549465111076048291063033672972938814535724568426055⟩
def resval0Tail136 : Box := ⟨-122973512319495862535480610747249393692570400110128,40676154112664290341599939430793124464391900076862826⟩
def resval0Tail140 : Box := ⟨-31481293965151304342086855013634171628966812013092850,621304783002222615472912521001602895365756390276434877⟩
def resval0Tail144 : Box := ⟨-8117037800100416915331162515576182764960735211870832026,2353528381925165331002149636254613031495575737429440497⟩
def resval0Tail148 : Box := ⟨44964116582765154708759820853784667979004291,1180959343332193418082157465990425470914575⟩
def resval0Tail152 : Box := ⟨715172707429259435110926108527515743433,38093137877968545226179434598626991442⟩
def resval0Tail156 : Box := ⟨202815490067867219349709735418795340,17128424141927741674262810543115061⟩
def resval0Tail160 : Box := ⟨317237347618465992501396591313307,39893377558204039260811860771762⟩
def resval0Tail164 : Box := ⟨1892296436698424445362822118329,22679128967774269307334554724913⟩
def resval0Tail168 : Box := ⟨35228220529894382474806236834,357812530337998268707599472975708⟩
def resval0Tail172 : Box := ⟨1811513153318611201644939468,5724873513479838489686637206117160⟩
def resval0Tail176 : Box := ⟨238641274181882979315976494,91597967437986339241429114831639365⟩
def resval0Tail180 : Box := ⟨82361282583937958537750294,1465567477436914933940274861669778664⟩
def resval0Tail184 : Box := ⟨1412115319651262849294676231,23449079637305366244964850368521349686⟩
def resval0Tail188 : Box := ⟨346282061633366269032475454188,375185273872253242606232685132279862768⟩
def resval0Tail192 : Box := ⟨88620012786624684269260556474237,6002964298874858752457905829245193780329⟩
def resval0Tail196 : Box := ⟨22686596752764051828071917737861196,96047407513314619432205783016704044087400⟩
def resval0Tail200 : Box := ⟨5807767387749817437853522040547257538,1536753075431167746577128509990475999977973⟩
def resval0Tail204 : Box := ⟨1486788420400882567731922723752728628521,24586655342762229126300869193423545171331810⟩
def resval0Tail208 : Box := ⟨380617839853467887868845159438193082323161,393029656263005575529535657509679561130530099⟩
def resval0Tail212 : Box := ⟨97438192273246393596955919935841804422504575,6197126205672452010148438980622674621398616825⟩
def resval0Tail216 : Box := ⟨24945558738103302526074108920586648696670541477,75768094270062969222283129019882540865834361593⟩
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
def polyval0Tail5 : Box := ⟨1818991917625131341157539554943134627842551035793700,57104545255301132398882607968324868320821713436264⟩
def polyval0Tail9 : Box := ⟨157451074380995647601284328018803121895071612070,9682540252190784475424106568310081054943774446⟩
def polyval0Tail13 : Box := ⟨110683256309039137959188070072015353027845543,10530461101214092973981131916667593700465245⟩
def polyval0Tail17 : Box := ⟨347080450846663992447411505122585844762911,409735185829732146609594054962962561732247⟩
def polyval0Tail21 : Box := ⟨3714641989756630616929796493742266737146,5803765327929265028183386913544493270709293⟩
def polyval0Tail25 : Box := ⟨116013864373410554538300757282069810396,92849173381077348824583402320717927453717262⟩
def polyval0Tail29 : Box := ⟨9599196366783657884869174824177510375,1485586305410696605190318252733136830531245808⟩
def polyval0Tail33 : Box := ⟨2006263973894129578256885101321870932,23769380833964473169026669958523833737483329261⟩
def polyval0Tail37 : Box := ⟨6522699915986976092680651055293983002,380310093326145614646741743697817485100641906685⟩
def polyval0Tail41 : Box := ⟨1416529499800870497608300959935960256109,6084961491890591715740982576398214733762235455612⟩
def polyval0Tail45 : Box := ⟨362328910328103598283830216677172856046337,97359383530566758035999007712474313044643128879236⟩
def polyval0Tail49 : Box := ⟨92755331045238170969116671389816923034377598,1557750049530951050077377993971316481909245178767781⟩
def polyval0Tail53 : Box := ⟨23745358652405510586361038595765987948459142325,24923978531221623706514319742960756876606193348416420⟩
def polyval0Tail57 : Box := ⟨6078811714336684382419521602602335901359210079884,398777957613573802514578791510891834883459805918472142⟩
def polyval0Tail61 : Box := ⟨1556175797493266092697699483258804608188220791339099,6378988407009353907981518542184683560886974876330869758⟩
def polyval0Tail65 : Box := ⟨398381009039680039147073839609292086776789144205304589,101690332318664463566495007012560046579923008953753868554⟩
def polyval0Tail69 : Box := ⟨101985596881425084864961992007560821551404947588066992950,1531433843868219289957645591014111893229104581027277082074⟩
def polyval0Tail73 : Box := ⟨26156250000000000000000000000000000000000000000000000000000,2⟩
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
def resval1 : Box := ⟨103471743250008147644042120554049054854306764301519944850,514357564405798815814290418379029495295620530279283707⟩
def polyval1 : Box := ⟨3681592758696594487771148545422551279556284608161741159900,13370620568158929237126732953089145079927478893858392804⟩
theorem cell1_lo : Holds Q cell1 (1/2:ℝ) := by norm_num [Holds,Q,cell1]
theorem cell1_hi : Holds Q cell1 (3/4:ℝ) := by norm_num [Holds,Q,cell1]
def resval1Tail4 : Box := ⟨46190133054847870203510954675754194373551857113098,3372934292490994244625457171919819901342286230686⟩
def resval1Tail8 : Box := ⟨4832750842190147956032868777751395863499823899,5955380027580506278352856821817553326932848616184⟩
def resval1Tail12 : Box := ⟨-314095597019407694405391274737608428901013086,18820996913926524728462624638775151122708516539047⟩
def resval1Tail16 : Box := ⟨-2083845987092848330293998860208596324867241318,59482564760468828993120579466230116051537862658266⟩
def resval1Tail20 : Box := ⟨-13656781576012671412339177547081512839243846275,187987207988260363565460784238905713469174236210265⟩
def resval1Tail24 : Box := ⟨-89501084782398402171493004646155476628651404551,594086071521553727690324181309851814772942301981224⟩
def resval1Tail28 : Box := ⟨-586554309265752160138414265064109303897767745846,1877301675162625272261181563788023108091452232546632⟩
def resval1Tail32 : Box := ⟨-3844042321207246507249292126550789344459579289135,5931210115022054378984835570303752115560467531229149⟩
def resval1Tail36 : Box := ⟨-25192315756264510147172298970117889141931358416811,18732509712390340315402857633796520192535003935907707⟩
def resval1Tail40 : Box := ⟨-165100360540255432895169110446908454520773428065294,59118501111132964777783284554926321498821273267762552⟩
def resval1Tail44 : Box := ⟨-1082001722836618290028783593979984143653737089675708,186283454780229361425593298090116104982439380043745347⟩
def resval1Tail48 : Box := ⟨-7091006490782061061367569105804055610356331245650464,585076362210265971001129078413378372649783840165677262⟩
def resval1Tail52 : Box := ⟨-46471620137989273877774777794303994515549629482764676,1825069693287545181960240029103050358922720621444234754⟩
def resval1Tail56 : Box := ⟨-304556409736322734661944345298739706155870747060744214,5610438358620917303869269354654635941608872320402495237⟩
def resval1Tail60 : Box := ⟨-1995940886846872935365246921622128128536382007899336036,16698363566231580681165087285507425368616372309419375553⟩
def resval1Tail64 : Box := ⟨-13080598194422750266777876375049856510829871619869590412,46002635630900769261025397801400806282438686393834272105⟩
def resval1Tail68 : Box := ⟨-85724980143306544799625828758804003411830790730718408024,101007187956795662358014036320721081077369565815144914515⟩
def resval1Tail72 : Box := ⟨714431658641694100539234607339907267440840708991154412455,2318915273645832657016616184498814026793457131696684250⟩
def resval1Tail76 : Box := ⟨-21248457689082496560754891954003582821585182615519,529725867724318889742204600058330246973205667940⟩
def resval1Tail80 : Box := ⟨-1002684778692101702205803174367931840232912868,58328997331879302232741318543919318320227804595⟩
def resval1Tail84 : Box := ⟨-3086031126285283742151070564384228441685204,184202058958510383268442944642165112361768271074⟩
def resval1Tail88 : Box := ⟨-16981964184640388172935674943688728885324631,582160642882875647475021262515991266127927737054⟩
def resval1Tail92 : Box := ⟨-111285184743434041640509939019831451138001003,1839857500561327100099548545391695304763211121062⟩
def resval1Tail96 : Box := ⟨-729318519138511753163643249084300125245088714,5814480670965143735234049835108253299085018246465⟩
def resval1Tail100 : Box := ⟨-4779661845269685789879416705074341563442243844,18374155613560939415829718075405863785513870235317⟩
def resval1Tail104 : Box := ⟨-31323991869036976777607320508327327961219309157,58055187495834472690847195719317899174002352224522⟩
def resval1Tail108 : Box := ⟨-205284913112899598263405767598057412219767895425,183376776085061144061130210313485997116541517487585⟩
def resval1Tail112 : Box := ⟨-1345355206576690446016190722888212944814469708252,578864615355553615557328097659315434425271240709319⟩
def resval1Tail116 : Box := ⟨-8816919881820992091789272337256673108310572654250,1824933110536763674686868761175877159842423402185722⟩
def resval1Tail120 : Box := ⟨-57782566137502053909085934850338144742619810733682,5737773085555802570298218448312567572199306622307870⟩
def resval1Tail124 : Box := ⟨-378683825438733771755286602951535282143780534968444,17938134036703068668235326687645081659158830967981830⟩
def resval1Tail128 : Box := ⟨-2481742318395308506604708340021956409839889674775043,55408447468126945166692981301074077340143333107593904⟩
def resval1Tail132 : Box := ⟨-16264346457840203556575423429167461336063225443746503,166697241015615853902430597909304382350190301627367157⟩
def resval1Tail136 : Box := ⟨-106590020950465526251744153897297019231662897195290412,471658946869777722031000830657417221226486684465555640⟩
def resval1Tail140 : Box := ⟨-698548397105502175067414398352090981588918938571784077,1129003921361639916274706787827573420782425504222632511⟩
def resval1Tail144 : Box := ⟨-4601973130256477863733324747262403088756895796928685337,1191557291908196663713407911253393423032814050522098376⟩
def resval1Tail148 : Box := ⟨44315553244515359154350781389340920740564769,957455096703772914245325811711935891513976⟩
def resval1Tail152 : Box := ⟨688544909684559386083048168943823099443,2319476102958231710067023665682066305044⟩
def resval1Tail156 : Box := ⟨279804018060667627099859375566132719,7240944590876708874134346989167758827388⟩
def resval1Tail160 : Box := ⟨581851982651965506551526974582114087,22884646139331954469587441839614328350187⟩
def resval1Tail164 : Box := ⟨3811313354618790068967556901294637400,72324809534917028094150399427615702387099⟩
def resval1Tail168 : Box := ⟨24977812102303188916931794127436812677,228569181900295255591281196028122344645694⟩
def resval1Tail172 : Box := ⟨163694589193592501075573309643594438924,722306736106676219731412524127863361003350⟩
def resval1Tail176 : Box := ⟨1072788859729260616164638636304523894388,2282290547660545448531631131290620206902968⟩
def resval1Tail180 : Box := ⟨7030629071120460117974918000083199570734,7209525101165796474483722599922032260831779⟩
def resval1Tail184 : Box := ⟨46075930680494692948797980906866410831342,22761803908092970972537721841327948282714192⟩
def resval1Tail188 : Box := ⟨301963219307689802555412101703996657258823,71782200221754127476197696125545434681745644⟩
def resval1Tail192 : Box := ⟨1978946154054875714332839377930723439157564,225842607437449139252839934931781023336207918⟩
def resval1Tail196 : Box := ⟨12969221515214035215535548637001588094241696,707059392304848037566592853570000647997816224⟩
def resval1Tail200 : Box := ⟨84995090122106804605893597496458385679843351,2190650899235126472303987295077432840798760931⟩
def resval1Tail204 : Box := ⟨557023822624251547905255591390064176403342795,6635141279541826696841999881334757452317845291⟩
def resval1Tail208 : Box := ⟨3650511323955611261278018563950064350981398199,19080282085362826700743124044798463303506876093⟩
def resval1Tail212 : Box := ⟨23923991026262932952053889389329083129368393069,47916541239574451239530940356571300142997845871⟩
def resval1Tail216 : Box := ⟨156788877885314611433524902729298598854356437324,70263113475241598843503217570951748289848761893⟩
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
def polyval1Tail5 : Box := ⟨1771260730579440376736969443912100374068216646933370,123374130611279018020039703977572735405871638114178⟩
def polyval1Tail9 : Box := ⟨152250634157900944737353042882429048608045813796,263791443271387306302080947474858545356994692215604⟩
def polyval1Tail13 : Box := ⟨14895782763550295344885963777664780749333635702,833684979041565525875002339923217025854030511005251⟩
def polyval1Tail17 : Box := ⟨96945645488376285619206748366835977333516581367,2634806030653214134508397513367639971797087506168945⟩
def polyval1Tail21 : Box := ⟨635340917613253975750912456638644216092328205479,8326959249816172383754364889765313192866624445920799⟩
def polyval1Tail25 : Box := ⟨4163770216212204440661330928220498421031402355814,26315147528882228432314569087749350526372056250454336⟩
def polyval1Tail29 : Box := ⟨27287684488321956892423058973943076507721268474014,83154733211427405404656969342014756642287833227191341⟩
def polyval1Tail33 : Box := ⟨178832569062615888877621050493702338779776824940820,262717431003214224010401583524067429718804019146857507⟩
def polyval1Tail37 : Box := ⟨1171997124608749770895350188047679625152810497499661,829710021079130393247766218912509267467190813211895408⟩
def polyval1Tail41 : Box := ⟨7680800355835898327586000249773128337055206807330179,2618316689275734724130615584364441548699339972905198649⟩
def polyval1Tail45 : Box := ⟨50336893212006139927705010843923266251335481819297918,8249111962907525701794768355705387588279393739434383618⟩
def polyval1Tail49 : Box := ⟨329887863354203439774756591870444598565576418077644284,25900469015245798430150234430642168415338328067538066105⟩
def polyval1Tail53 : Box := ⟨2161953101278107876038366605539882606441668264366858939,80738927897753996919303531171001322459658251392798430741⟩
def polyval1Tail57 : Box := ⟨14168575844536223842967297216438310401890819123252055612,247839146819071425846774329991829165164840741245374856098⟩
def polyval1Tail61 : Box := ⟨92855178654756042360833181773619463565560936178992272751,735218611491956768517332519920546930287935335028600602696⟩
def polyval1Tail65 : Box := ⟨608535698835127742017577196143633076831400881242167119007,2008586403359168591346145956959066845157967568553516042885⟩
def polyval1Tail69 : Box := ⟨3988099583877420134682798875715808672750991725345208063531,4283298684761711167357299495395681913542537607904700627510⟩
def polyval1Tail73 : Box := ⟨26156250000000000000000000000000000000000000000000000000000,2⟩
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
def resval2 : Box := ⟨103373103886368409678761615539757127207529936824073376113,501516320103187987359813393778187202082580237596615099⟩
def polyval2 : Box := ⟨3673103013742970662938610426566149507520693058355421454949,12207440976327446739864679262832556698939047798100455493⟩
theorem cell2_lo : Holds Q cell2 (3/4:ℝ) := by norm_num [Holds,Q,cell2]
theorem cell2_hi : Holds Q cell2 (7/8:ℝ) := by norm_num [Holds,Q,cell2]
def resval2Tail4 : Box := ⟨-151007189534278300189295642374733819618510083088233,34058779110030910706518437425201447428731536368277349⟩
def resval2Tail8 : Box := ⟨-451018798307528040063942346647168466259065054795964,57984997191581060686216388539556266944652245114767405⟩
def resval2Tail12 : Box := ⟨-1034917550223781808802209686141316573732743322370419,98654353646498007100667812193623000283190504632646577⟩
def resval2Tail16 : Box := ⟨-2374719261108779057180338570027798837073440018361999,167690776297443271614772711655154824780259081983960281⟩
def resval2Tail20 : Box := ⟨-5449024946495854911606318540530813798975871066711041,284675202378734023296741793291304073672670462603655019⟩
def resval2Tail24 : Box := ⟨-12503319172772736760760196530121417436547711982251046,482435804160897446527564914778464082752179457974170506⟩
def resval2Tail28 : Box := ⟨-28690085266861608566373416563741848035238152473390389,815654208433560335214649865775804288453929242474946276⟩
def resval2Tail32 : Box := ⟨-65832198734254487121762296441585666077336067366835203,1374581889977502398716355745056343590690803084301289952⟩
def resval2Tail36 : Box := ⟨-151058400484860546665077594361038308083569543319080904,2306224443065058738849736534856999913649941789604892636⟩
def resval2Tail40 : Box := ⟨-346618232350961828642280821702478208151034131741689000,3845397813954939626325580423841427907933024094066111871⟩
def resval2Tail44 : Box := ⟨-795349339146130541638089182497520823880743094453670112,6356044965588968316727462516321455315312977477159795685⟩
def resval2Tail48 : Box := ⟨-1825006627578894686202453402029229985498846890154897247,10374956334601432226702504323537618438717081621037523890⟩
def resval2Tail52 : Box := ⟨-4187655696404553093371966918156282029870883060535162319,16624942509797287345685939029474212553205689472593656442⟩
def resval2Tail56 : Box := ⟨-9608984409494369812063020654743969666395738330041133958,25896389290048624182052732593421150244167827112088657288⟩
def resval2Tail60 : Box := ⟨-22048751873554747624947843170662532068264938639710043801,38521848156984839691009179970871456500871998266334782180⟩
def resval2Tail64 : Box := ⟨-50593011545399827781726408518483700689764129225369630417,52737758017934997016801409868025844446360769563410061640⟩
def resval2Tail68 : Box := ⟨-116090577083514077027511337657940856031190743723275779513,60187129997816156497104209290574846481963654934799303924⟩
def resval2Tail72 : Box := ⟨715680907983113892066362055954769304204027127428554186353,1904744750554012338706853714982470857688315317050845283⟩
def resval2Tail76 : Box := ⟨-23103330620028773028405979300857454987744085369111,389041736088586741346572465169519045535965550016103⟩
def resval2Tail80 : Box := ⟨-4776339829985626598289150397232146045769607157253,662001899368284861005700403674423099273694555457951⟩
def resval2Tail84 : Box := ⟨-10957526652298966607821784179587395187813487973449,1126535000622188448987910981229553421513916179581859⟩
def resval2Tail88 : Box := ⟨-25143112471102052017894874412655896064564023120083,1915368919883392374539565506975584022946166553640039⟩
def resval2Tail92 : Box := ⟨-57693323722257768867004441820466409516229296544525,3252734533220302436976745043633148842959409111236608⟩
def resval2Tail96 : Box := ⟨-132382958000814014951720526416673289802543858254013,5515060816275189203153395637574823653729374970790134⟩
def resval2Tail100 : Box := ⟨-303765608190936282202652575934551533346514003725781,9330524145842594770313748478791340857208561706146679⟩
def resval2Tail104 : Box := ⟨-697019813676033721351777224796362704618717033171811,15738653169464883859733742646316254742489439124576986⟩
def resval2Tail108 : Box := ⟨-1599379941496185210417169000852363613151937007021441,26439152561188195630318745418149047617873739372994107⟩
def resval2Tail112 : Box := ⟨-3669933260246279678622331124812840830110471184606238,44162565336586383344559177522519422400506123531461321⟩
def resval2Tail116 : Box := ⟨-8421019787244850846592163066853200597628261462450734,73179111096814535967471388147493352454440067605656380⟩
def resval2Tail120 : Box := ⟨-19322851187874323221411519328372788113762914952282300,119883369595593918513626880672116805739742146414049319⟩
def resval2Tail124 : Box := ⟨-44338166571497204476263125668256263276062519601613247,193141500371062528413280089329470590273626508510194976⟩
def resval2Tail128 : Box := ⟨-101738247415344049143125443528963055484521500243844793,303391580071838249606473494875071987524656157798613897⟩
def resval2Tail132 : Box := ⟨-233448331032250290766017405570414637970602453846693322,457685268879247172622809163782385725228753286162335170⟩
def resval2Tail136 : Box := ⟨-535669963328678734134692154380387867982994780959156478,643373445769086236280733492306463399904854898499427250⟩
def resval2Tail140 : Box := ⟨-1229147002017439423398716785880260053944494151911676728,782249023146785494563234427786735850642392488044171165⟩
def resval2Tail144 : Box := ⟨-2838939069397125646413336187279718935049926341855448838,607526297621529195506388531561583920961747486608317059⟩
def resval2Tail148 : Box := ⟨44196992184661865312969819723884875740883284,35847930289218217106756675804035401200995348⟩
def resval2Tail152 : Box := ⟨449929900885857613841503085479077226644876,59649500052877582819118665163359706107481997⟩
def resval2Tail156 : Box := ⟨1030857004275601125713763944652521583975101,101494939266151865718640977312219998638525938⟩
def resval2Tail160 : Box := ⟨2365401507951643169554201187511394869512544,172539080265293044017203822470610119680360332⟩
def resval2Tail164 : Box := ⟨5427644452461658745159366547259667890688660,292951679721634535794775700712328997344146897⟩
def resval2Tail168 : Box := ⟨12454259544008339726396643598349200941528330,496567694565567240391931211388681660704821740⟩
def resval2Tail172 : Box := ⟨28577513163969353188493792166823326456119997,839791468107509800481021857830201225149933680⟩
def resval2Tail176 : Box := ⟨65573891065225147653715599935233887659720098,1415825253994324459611396647263321550430959072⟩
def resval2Tail180 : Box := ⟨150465688346017130577708755146054960498637304,2376735851913839258661829723608617118742714169⟩
def resval2Tail184 : Box := ⟨345258196542298192187918036471864382266015102,3966036059561146943214474390836917978904460319⟩
def resval2Tail188 : Box := ⟨792228604341446529274698190443750250146374281,6562649060381465288506507853625975188741599565⟩
def resval2Tail192 : Box := ⟨1817845797210218120750948071866830566037126057,10729250793670684338926495374556897305461513236⟩
def resval2Tail196 : Box := ⟨4171224472741460552541026317889751055560173131,17233568378673856597960135138860152474855723900⟩
def resval2Tail200 : Box := ⟨9571281364293419756773150174316576503829194016,26944350255613760252509569481684002821400892718⟩
def resval2Tail204 : Box := ⟨21962238559235806275329846138677693972981955803,40331816882305146194322327124635931060448468850⟩
def resval2Tail208 : Box := ⟨50394498309520061643021835876504946643997002178,55876410098876118716148491719213265854017947895⟩
def resval2Tail212 : Box := ⟨115635091261602296592762732857051176717830170341,65658386814359470072006983053255205030344676156⟩
def resval2Tail216 : Box := ⟨265336471554183473671682726363759271935386773407,43942573432664244690521674894864915073804386786⟩
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
def polyval2Tail5 : Box := ⟨21037502663757356763904086294548707778731396414349532,2958661428074827329330886458196855027185785938494410364⟩
def polyval2Tail9 : Box := ⟨44260640508890626160415057471325519033787964665050863,5035965350676223623890273502896883028760445033781054024⟩
def polyval2Tail13 : Box := ⟨101560020134677907261120495047910572891655609541750924,8565080982747753442804060806928741748412584663829979054⟩
def polyval2Tail17 : Box := ⟨233039370926100652337109163224543569955351579753565810,14551867562595379712530652888125605986608798954837654772⟩
def polyval2Tail21 : Box := ⟨534731564475796851612954208123297385968873431137223388,24687666936025115168178620412163425697809054145103001211⟩
def polyval2Tail25 : Box := ⟨1226993726042002070646076856166455810947898542737667984,41801304590514317002182076018081914077998423238286122510⟩
def polyval2Tail29 : Box := ⟨2815456770767432575637344633759393426507985379163764271,70588920532279082422764052234806498063740059370120796415⟩
def polyval2Tail33 : Box := ⟨6460340146669040328897794180775031577669757154416525520,118764286855945922353704855821222742955322389195069607683⟩
def polyval2Tail37 : Box := ⟨14823880531217472319554220054400423010837228196278124517,198803804684405554395069271602403937466618254796097352743⟩
def polyval2Tail41 : Box := ⟨34014839623748057347828972769099949553864448253558727811,330424560061046577146416874503975873587256750276209380671⟩
def polyval2Tail45 : Box := ⟨78050366919293886291018216656500873899703057909159688824,543667159573383674261835577689890695432814602279052427732⟩
def polyval2Tail49 : Box := ⟨179094179000134593755677100326854207490858452753425283957,881528473442184143451852403334587203002600885980321088087⟩
def polyval2Tail53 : Box := ⟨410949060430405824142309217198680840969536078967965152018,1398426359979314104202988597602677309069619332910886501268⟩
def polyval2Tail57 : Box := ⟨942962698237704439863679825942049995657984206496183382829,2143751888183875256117070527635484392332751534888630403375⟩
def polyval2Tail61 : Box := ⟨2163719876464629413509121933056515091572358555052052401314,3102078934856818052317314778697850242683332704257918525561⟩
def polyval2Tail65 : Box := ⟨4964866280034403348352647247831452975583046907710909267701,4018354016166101780411374536195285003762382570830827586109⟩
def polyval2Tail69 : Box := ⟨11392369915614427440504440837511937107597800810077822263091,3932607333313246343207652820868664562674354105277054667827⟩
def polyval2Tail73 : Box := ⟨26156250000000000000000000000000000000000000000000000000000,2⟩
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
def resval3 : Box := ⟨103187073451480748088611957654275345465058481130873278903,2098415545964347732700977208438776091337508050592469136⟩
def polyval3 : Box := ⟨3690705199011187923178437545369658579625891613303841679626,236473013860991609239311769279491100194037921144131521192⟩
theorem cell3_lo : Holds Q cell3 (7/8:ℝ) := by norm_num [Holds,Q,cell3]
theorem cell3_hi : Holds Q cell3 (15/16:ℝ) := by norm_num [Holds,Q,cell3]
def resval3Tail4 : Box := ⟨-203390932098448611110467591390630314057916304295084146,2089667052903109757155802578299743519649528858064676338⟩
def resval3Tail8 : Box := ⟨-301603301151354625308564646171292074830460156840980910,2666905134780094390331800118320483740365307597757643236⟩
def resval3Tail12 : Box := ⟨-447140511400217774588285059251512081318658999472494526,3395707274338071589162240644881086246636324031297988391⟩
def resval3Tail16 : Box := ⟨-662905986285291974589602959548390101666030320808061869,4311807544309679913826461484067946645241075819339986705⟩
def resval3Tail20 : Box := ⟨-982788039654818212897889648694740509729735922142468516,5457169015971311685288030473463919107372182722379131729⟩
def resval3Tail24 : Box := ⟨-1457027619106254534728634895559853195813542781832962240,6879743256894023138357514519728185786848945866922802981⟩
def resval3Tail28 : Box := ⟨-2160109196672835775234850681453955003181097661349387709,8632159763910950848545381565982508810547017102023070484⟩
def resval3Tail32 : Box := ⟨-3202459363407776324054831637764770819163497058943089547,10768545843521982494561307222320312813765586800525901739⟩
def resval3Tail36 : Box := ⟨-4747790523772973495455598522901552091572625187416446776,13338210409389469446526920331467958892867715190334905639⟩
def resval3Tail40 : Box := ⟨-7038813705239882671776960052572534770141971887476730948,16374206683021526921174432138505870411628044236480099338⟩
def resval3Tail44 : Box := ⟨-10435358958865875390896778819922076280353959290206452665,19873691987605230566051055655479463519660778402133145653⟩
def resval3Tail48 : Box := ⟨-15470890573409640797260913416535474388768155880487508634,23765335852821083150841081983293134965758228434298302070⟩
def resval3Tail52 : Box := ⟨-22936293430621757800145658205420171115060373012131975535,27856503311490967569491706137655365376127834493682761701⟩
def resval3Tail56 : Box := ⟨-34004090057993411535311054591639642009109105877005352252,31749129246522131649466045302781466245263137161056293265⟩
def resval3Tail60 : Box := ⟨-50412598015003811382995664117205973784814735726270732837,34707460855923200748808040108707776036897571048993016330⟩
def resval3Tail64 : Box := ⟨-74738951527531338813975712498196713478122873561585500039,35452222360772103950029638414894714428974906877175979667⟩
def resval3Tail68 : Box := ⟨-110803848381962637198314448220183683100670772041969425176,31842821015605877287535507216693662451102252031422097693⟩
def resval3Tail72 : Box := ⟨716303561739303134651509457767341820406732902803761620970,1717247158568937240999674034538067278533968598478989308⟩
def resval3Tail76 : Box := ⟨-2422674914170098966559517324748892472176215460773033,25621523014708369470862956525787523279459758453389392⟩
def resval3Tail80 : Box := ⟨-3560723902293043319898706076945405358813844536013352,32716093611453557798770891606241962575922836527640379⟩
def resval3Tail84 : Box := ⟨-5278932431043969784723613336503845501945825848613801,41682794922057518565327281350556989688091242183762015⟩
def resval3Tail88 : Box := ⟨-7826255550933691943833900729997306953591778763804049,52967497807696069401497307917386044836181078289605063⟩
def resval3Tail92 : Box := ⟨-11602777030027213618314788584378857891081020948883216,67097063367228732231729923977194370455037663014309226⟩
def resval3Tail96 : Box := ⟨-17201640546031641863231408677565594154607514353101014,84678314817416555516369617362624828222186851116401655⟩
def resval3Tail100 : Box := ⟨-25502208368662065929176631419696210062777153361901387,106385292958724423866118431206109895814431764004644031⟩
def resval3Tail104 : Box := ⟨-37808174745791551629295944052497525190073522637770359,132925243268857356894284687593187761972470664573036732⟩
def resval3Tail108 : Box := ⟨-56052325231758130133555261912485477647383997119477626,164968618630128899373590645769383022830531190092721458⟩
def resval3Tail112 : Box := ⟨-83100101631764479835480015859912436415159448836534871,203019969023694845906996969167725199634812052238640407⟩
def resval3Tail116 : Box := ⟨-123199650730938723377279535400150783333295165813522258,247193731006862409893835038654518055647008030624537179⟩
def resval3Tail120 : Box := ⟨-182649041844535344249782617373481739856343932567525245,296839366364225842327692964872061101561151705234983961⟩
def resval3Tail124 : Box := ⟨-270785446945663029806393108918399077663298129352468890,349930648271509772859883871661996373110432503032700821⟩
def resval3Tail128 : Box := ⟨-401451644843415235213555187102728057020631662351135219,402089096216389949739484854965321070037103377865249780⟩
def resval3Tail132 : Box := ⟨-595170179805949194222018990309597010350211630616206694,445044062289764953774008664718053022295561921452482491⟩
def resval3Tail136 : Box := ⟨-882366649835752431247670342023958372603743688231655280,464230497228142032574688819046044575519224480173516465⟩
def resval3Tail140 : Box := ⟨-1308148402578262999181193520539553163403965275557745982,435073161406793509964330509078535407265136588927700778⟩
def resval3Tail144 : Box := ⟨-1956045508519257655856838241955163783438858673819706447,314748670050881749840990452025265326311878894801278896⟩
def resval3Tail148 : Box := ⟨452883845324816411945852722916807893370799229,4002025341160536671400324066959982949253236153⟩
def resval3Tail152 : Box := ⟨606417137721410622433179283718297110153297141,5102990036845957863236876868446726661195026310⟩
def resval3Tail156 : Box := ⟨899039779406028822818900660336772382254030770,6492005427396122912031831929043619160841235229⟩
def resval3Tail160 : Box := ⟨1332867043704808661226256101859208922014077422,8235123843416446135417619662488935262597821545⟩
def resval3Tail164 : Box := ⟨1976035540640177690253863250565043098222607724,10410094845105194881430431560088590271938142460⟩
def resval3Tail168 : Box := ⟨2929561861639593495516756291484131505830242831,13104757959796626273025772437409525618993151589⟩
def resval3Tail172 : Box := ⟨4343207662344384142446046190375396642430480010,16413833005658462212912756096731927914546170323⟩
def resval3Tail176 : Box := ⟨6439001355543871453107638674017011643855976234,20431782194445946594211823879139335740674158382⟩
def resval3Tail180 : Box := ⟨9546110082683926971981462328405391830341726872,25239147610790299507762804380341462850162705061⟩
def resval3Tail184 : Box := ⟨14152538985297754935512762379563804517997625009,30878308386544751860996981410580935226048258049⟩
def resval3Tail188 : Box := ⟨20981777707937267760999930644854018143291350541,37312377617713508049662694727580815266282934966⟩
def resval3Tail192 : Box := ⟨31106432297598872979614682376416580059167694004,44357582782338889855562145813642513978588280270⟩
def resval3Tail196 : Box := ⟨46116689622493797847640202794474635966665830973,51574366027457831293066251936756443737952952629⟩
def resval3Tail200 : Box := ⟨68370073475176141647138407505276759858375816025,58094736857174079994792317140442193196811687828⟩
def resval3Tail204 : Box := ⟨101361719266184592734904002603475147878840570585,62351817720302409437997186792391850143122469155⟩
def resval3Tail208 : Box := ⟨150273322966772194540466091458334407839630462501,61660116242048802094791716330853108419119706579⟩
def resval3Tail212 : Box := ⟨222786982698782080342808634971081606728715793272,51568965397606811547767741259181708030830991225⟩
def resval3Tail216 : Box := ⟨330292185595359212365063041747799513186688626192,24872441080908059100482364108598912972919393248⟩
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
def polyval3Tail5 : Box := ⟨32376893107114325750378669314535897840940085121371011433,292284269828463710136651432838879511045129234836668947203⟩
def polyval3Tail9 : Box := ⟨47997629502354677656278013592400875472698010499315182467,372286397380429650323547202972834370035908050858738553723⟩
def polyval3Tail13 : Box := ⟨71158651513617414187278327692233684146207779828725383940,472915106038348064262734410807607006384731927625403155433⟩
def polyval3Tail17 : Box := ⟨105495912048309280851485713513644880580823943304806635636,598828389678484497363164634122444117575662486329551980250⟩
def polyval3Tail21 : Box := ⟨156402450330162473879600739622313891871406901734981358449,755372313876595780336997519983021536688277102189553150832⟩
def polyval3Tail25 : Box := ⟨231873690594545086176473982686063846813856070377031378636,948453636754671876499201433968176585240865214708243007018⟩
def polyval3Tail29 : Box := ⟨343763210080386307836286141838847989185225462846139776923,1184215688194345205437674118959152094578641807776615752866⟩
def polyval3Tail33 : Box := ⟨509644471961287173159259037257810321257179292186133458879,1468382690060101556784877037208143634479934892982845256115⟩
def polyval3Tail37 : Box := ⟨755570928430537026841728256636735766501504394202024075167,1805060935080252737218082941685175384351709438771991270401⟩
def polyval3Tail41 : Box := ⟨1120167998079941060847708147084403320386798108055604570036,2194667948725848923890899801669330946501959721337566776769⟩
def polyval3Tail45 : Box := ⟨1660699607022770692016488292766251175234035867223458432394,2630482390209115775930776495763035924395096985521030561089⟩
def polyval3Tail49 : Box := ⟨2462062109873598755176102108553217361765557758681519210164,3093037215965194559662005149884608172066374924781184821570⟩
def polyval3Tail53 : Box := ⟨3650118183469962700080547066394876956080958802267344854886,3541170496395146607355981289773194654627658717725224065020⟩
def polyval3Tail57 : Box := ⟨5411464926033923741568884995851382460856264860250278238226,3897933492210813128749690222810271278758614063454776426507⟩
def polyval3Tail61 : Box := ⟨8022740956254938990234389827295966245825430848140602520573,4028631581781350895113683939674070814743966570858973939049⟩
def polyval3Tail65 : Box := ⟨11894075510225369914207563576043726907391312479704858143671,3706887465633230509183790212114685674325385472861379312985⟩
def polyval3Tail69 : Box := ⟨17633503708373826414095095378628008454045344594664171847874,2562539954006253814602023300869357348976462492964198160284⟩
def polyval3Tail73 : Box := ⟨26156250000000000000000000000000000000000000000000000000000,2⟩
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
def resval4 : Box := ⟨99492387613687367241872810500600260746804162574964352481,10102517235982551331545988796547469114831575597384737350⟩
def polyval4 : Box := ⟨4491177915816516546043267442750693710475619650389089768770,1840919798812059873147537787317232648234545472740543017547⟩
theorem cell4_lo : Holds Q cell4 (15/16:ℝ) := by norm_num [Holds,Q,cell4]
theorem cell4_hi : Holds Q cell4 (31/32:ℝ) := by norm_num [Holds,Q,cell4]
def resval4Tail4 : Box := ⟨-4613625013918944982260347428123189398302745428102863844,10661622106550465333490567195387093134193263558293642498⟩
def resval4Tail8 : Box := ⟨-5590454184660162236431756961155626598280421030870464060,11753281016810869157445894232984403471383804183563112116⟩
def resval4Tail12 : Box := ⟨-6774038317545937174828995720324233256007903607062960010,12918231254374961318209109605646125430623905939025784035⟩
def resval4Tail16 : Box := ⟨-8208205196477836624626067525516782279205800421379836038,14150616377314333209733056163301872512627568149444575652⟩
def resval4Tail20 : Box := ⟨-9946007003376054387786729958076099342512827843785387267,15440447327993465230563582065050184724801071631382744290⟩
def resval4Tail24 : Box := ⟨-12051727867823471038429523262292711656420852524486446206,16772334321309342976852082889943470777524839651367237157⟩
def resval4Tail28 : Box := ⟨-14603261846766391695391412677500877213867454835379752730,18123898482053558898793919115025995196802064327480956801⟩
def resval4Tail32 : Box := ⟨-17694994353016090176121514497987906996538068325510285857,19463786951310187747705466395736886160868047176795901432⟩
def resval4Tail36 : Box := ⟨-21441293625958235137987328407639892550215703312459536295,20749199351424229581561682959654982436843888033795918238⟩
def resval4Tail40 : Box := ⟨-25980741399682729123403982286320190356771416987375291957,21922812893345578111314124198236456706795288959681023748⟩
def resval4Tail44 : Box := ⟨-31481259267863864533098315091204359804026837322216992238,22908968292057837611965031711143755667322261237531687623⟩
def resval4Tail48 : Box := ⟨-38146320378007656872827598911485234584023801091952292651,23608948049967948171648352773893078819399297737367227189⟩
def resval4Tail52 : Box := ⟨-46222476235790668723949096368833206596361740637282835906,23895141389724016902982457921168850217275781645617446135⟩
def resval4Tail56 : Box := ⟨-56008477048286697665370917401981481451306177186037060700,23603844728144681282504575950069325324414877752148886271⟩
def resval4Tail60 : Box := ⟨-67866322982485302487081774115053432002648718857730438520,22526391334831155213390915723622961134702357828705573535⟩
def resval4Tail64 : Box := ⟨-82234655142092408945012774161977030617056173371679745753,20398236591566803116860764670651122830938839147974353793⟩
def resval4Tail68 : Box := ⟨-99644962540621869229501483737062849188871969382798387177,16885540869651082684105446573404720944597815176238844723⟩
def resval4Tail72 : Box := ⟨716569979269300730671752449426850410207685045249251918713,1714655549056586623247794733047730079957091632767560296⟩
def resval4Tail76 : Box := ⟨-57276639921673323714751000539430148255299064707160579,135402078968991702466428296495824916330704534936791939⟩
def resval4Tail80 : Box := ⟨-69377704154588754930198119511638439179571489692719660,149367800422673753848289418553674564708703406573475595⟩
def resval4Tail84 : Box := ⟨-84066017512831436221913684156860090275280014306030508,164300056637836683527073536039497686093113589310643531⟩
def resval4Tail88 : Box := ⟨-101864071244549713353201899790594637938818645844374455,180133527692667447829975273479936159939812128847691663⟩
def resval4Tail92 : Box := ⟨-123430243486775622054091715951020483481733189058489945,196752962204475779078561101683172581700473272536467809⟩
def resval4Tail96 : Box := ⟨-149562302203977902070117266729381422637189609849016873,213977265484152220022696610984781957245286922631441635⟩
def resval4Tail100 : Box := ⟨-181226914965541877768460010163665922150104821926619264,231539947648463359389768186079665753074158119369767328⟩
def resval4Tail104 : Box := ⟨-219595407558885635052836665242394424123302144997456748,249064672431004313891814559131940611429213829647383872⟩
def resval4Tail108 : Box := ⟨-266087093245073160853612569230251628208936240482423107,266034766502002263637521631277945658934735932549808232⟩
def resval4Tail112 : Box := ⟨-322421775476457757635726813314650652025303596532046292,281755293811787296142420536799143801975059430440109875⟩
def resval4Tail116 : Box := ⟨-390683366237705222438629864840402001271913256833237030,295305988206850825026017030661858503802803690325227826⟩
def resval4Tail120 : Box := ⟨-473396973356626575549030748007862710986608944305324685,305482958259497802818971813617961010241795317146393245⟩
def resval4Tail124 : Box := ⟨-573622308370460782713156810817559619585265061721299258,310726616206575620771518908186444556907629169426748700⟩
def resval4Tail128 : Box := ⟨-695066870257272839794963964650811137342428206711579242,309032720263452229075281427252348923715745350810123339⟩
def resval4Tail132 : Box := ⟨-842223091883713712820760774740460878069530733394021968,297842734697232735670835675693990508702350649663480150⟩
def resval4Tail136 : Box := ⟨-1020534522443499388921727637022808372919884089810603912,273908878600077475144170378606560956470929949562858051⟩
def resval4Tail140 : Box := ⟨-1236597217666714526261307111638592804611463918220137637,233128216016902081108011543123773505082662663043436333⟩
def resval4Tail144 : Box := ⟨-1514254447090779035635010160687226724195588831619901192,168169248841003559829595477364267773947702269431829328⟩
def resval4Tail148 : Box := ⟨14007792194274599916749203636827872374787941977,29827265203650669105402018809302655642063023244⟩
def resval4Tail152 : Box := ⟨16920419123764592389201176756597630517442578537,32799891145839162219188422551145590661597589950⟩
def resval4Tail156 : Box := ⟨20502728238919661145061549727387527678616545275,35950263456236047925998867414586620679453336898⟩
def resval4Tail160 : Box := ⟨24843467453555645612910118322949270590351766471,39253886282353846071228170411605208161282948902⟩
def resval4Tail164 : Box := ⟨30103207140488502927327443651973097536179708217,42673640154791980979958773284534907586005017590⟩
def resval4Tail168 : Box := ⟨36476513668524572349759235414813966967817931914,46155127008293850760791119454628461191057549506⟩
def resval4Tail172 : Box := ⟨44199146064423905429315292196162980914569677710,49621736464869478045143969240503024154077047668⟩
def resval4Tail176 : Box := ⟨53556777124509069324917554438562560017784535066,52968494871510879185783667759577965298406963212⟩
def resval4Tail180 : Box := ⟨64895560918383184526024022925348845910748277021,56054415972774259137270324178233492381748519683⟩
def resval4Tail184 : Box := ⟨78634937593814132168686496095532843431073443722,58693009435676596950233784959895967384599377429⟩
def resval4Tail188 : Box := ⟨95283149153449036374669150826598279808202146769,60640527064412030971483126609602104274686679599⟩
def resval4Tail192 : Box := ⟨115456040157302949546547620740734853471750206362,61581433504714358726499030774185955093831826350⟩
def resval4Tail196 : Box := ⟨139899838819739845489959563588382221619548472183,61110474949653011890939752204814321272382658202⟩
def resval4Tail200 : Box := ⟨169518761210962949299785716163367492102407246474,58710581458077478454769814239930184474462932826⟩
def resval4Tail204 : Box := ⟨205408459687551453258746047630705165023643727289,53725670687969776933674095185568085495505115338⟩
def resval4Tail208 : Box := ⟨248896552864170286788769886925737817326463711315,45327216701053718544651128803766947904846573699⟩
def resval4Tail212 : Box := ⟨301591736405761743488682418860423192031408967571,32473199207564674076472669303715002781337145505⟩
def resval4Tail216 : Box := ⟨365443701127998096808852712442057576266316203483,13857678082516109017994243514620612266654955963⟩
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
def polyval4Tail5 : Box := ⟨998961892314760258693471443693805037466733499992321951048,2019489894710234896389768080066621409807206646616402130532⟩
def polyval4Tail9 : Box := ⟨1210455210984789327351871191405782096432113979067978085946,2216726480591707740004598851304802210633728436957330855001⟩
def polyval4Tail13 : Box := ⟨1466726978202446912809479138624616053414212007533835228490,2424533176435637026653305628791244145129319623031088436777⟩
def polyval4Tail17 : Box := ⟨1777255374110400005169459840134363025966997990465680880343,2640924621698766482072504548654080037663967309705614922908⟩
def polyval4Tail21 : Box := ⟨2153527351542675079627480221439865409322968947006753505018,2862923283890187014265335355125642765224209061107949745317⟩
def polyval4Tail25 : Box := ⟨2609461826026992002851556293177706597940436452450061401083,3086271938012644128421874810462268301539347557858606151844⟩
def polyval4Tail29 : Box := ⟨3161924559079456904114060781012144606412885147572026497898,3305074813280917679555161551363761628198170107686903397028⟩
def polyval4Tail33 : Box := ⟨3831352050292994816487807909469539310477734347289544163910,3511350859410360212187991389468912146876715359828390185318⟩
def polyval4Tail37 : Box := ⟨4642507516864337624784386804711136107054860560182898309750,3694478914678751490186861128691219097358182564099757311709⟩
def polyval4Tail41 : Box := ⟨5625396925477956523401783361917667684071324072660716759278,3840510059248677967659756457235323489934172692268812080003⟩
def polyval4Tail45 : Box := ⟨6816378962063740283579464016443266545128578865389179174152,3931316956509541199028419409116929272228725592190985631208⟩
def polyval4Tail49 : Box := ⟨8259509999024196255443765339265673338370334412436342075786,3943543310552843361319333124354702105428881482582214556599⟩
def polyval4Tail53 : Box := ⟨10008173812467493293271353666857465544867819062745908957729,3847308442016220551166915750068035778213028683176142238323⟩
def polyval4Tail57 : Box := ⟨12127056335350855765487111513194947977601270225054062391656,3604612095012411271153642631994765412523622100915096043685⟩
def polyval4Tail61 : Box := ⟨14694538495881165933535560506532863003959239435494705257318,3167372555450200524709748290562981133329890119104208913488⟩
def polyval4Tail65 : Box := ⟨17805595656179056689665243740805848007301466747287771555222,2475016525419992008767223681419613126210648224221097998737⟩
def polyval4Tail69 : Box := ⟨21575310925270102116553849343019609159739199462294423707632,1451521397437616124494378054428710614060619864435206012762⟩
def polyval4Tail73 : Box := ⟨26156250000000000000000000000000000000000000000000000000000,2⟩
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
def resval5 : Box := ⟨85031781973355640329422050107405820523764689242723480458,16808205597091999276810252906951614832209234900011535965⟩
def polyval5 : Box := ⟨8405571086718859129022116783204624074614883957809678040080,3680379563312389146063267821731938582985575646396843038012⟩
theorem cell5_lo : Holds Q cell5 (31/32:ℝ) := by norm_num [Holds,Q,cell5]
theorem cell5_hi : Holds Q cell5 (63/64:ℝ) := by norm_num [Holds,Q,cell5]
def resval5Tail4 : Box := ⟨-20072645250979002515747618286437095299225318003723641891,16789273615667046803639446505436695584514288572370969538⟩
def resval5Tail8 : Box := ⟨-22070156337759830290303104243164067117663851600644209220,17188565406899086315695991200323533209269069922144332303⟩
def resval5Tail12 : Box := ⟨-24266393525330536777384565136003822549988402768386000903,17544924021210243676344157101077231562977075001279200805⟩
def resval5Tail16 : Box := ⟨-26681181845293152856867807776623479035583369058915940254,17848700868373311453124090623372779899273540663304128814⟩
def resval5Tail20 : Box := ⟨-29336269681705747447361797850142207742315879235795879078,18088938870632356628130392375946891159881664094732329659⟩
def resval5Tail24 : Box := ⟨-32255569630608003938258137431290321387259010484969844593,18253218382491481241017531105594664577063684452232582003⟩
def resval5Tail28 : Box := ⟨-35465373869391917447671462487693764248759741310505384296,18327487446901628407064958009860333433201492869193213506⟩
def resval5Tail32 : Box := ⟨-38994590952819522776571127006175462146168325393599185831,18295873586609041682804287512903104518829012693432736577⟩
def resval5Tail36 : Box := ⟨-42875006172993876304873779269910913355507229976260534676,18140475190689658651184105192651502597610801646332470666⟩
def resval5Tail40 : Box := ⟨-47141567828174545187239947222365384250077034876898001070,17841130356788473612871444157529751418681194531100416445⟩
def resval5Tail44 : Box := ⟨-51832701978668907253318945481910536326872988299764528249,17375160829595045054912313072335751108598732675344527834⟩
def resval5Tail48 : Box := ⟨-56990658524594546242209356568506240021680601187981547668,16717088433746232539126913068217025466439735752194015723⟩
def resval5Tail52 : Box := ⟨-62661891722403120028231242083195896885919499460796461695,15838321132400890873353476923417563951891708307968495154⟩
def resval5Tail56 : Box := ⟨-68897478567222911869071440064419552899600278375812896476,14706805548698118471360052670074844730170713596181393380⟩
def resval5Tail60 : Box := ⟨-75753578809108551726202992032188707878515942375416096333,13286642463461162455281330128613399718382491822552291480⟩
def resval5Tail64 : Box := ⟨-83291940745152071100865796074583648828135489628564078242,11537661445633641548022048156239654893464656751541070429⟩
def resval5Tail68 : Box := ⟨-91580438696796600212531139591843879736963276327543983260,9414947660791602089023719844010255965274893565112570504⟩
def resval5Tail72 : Box := ⟨716541566847315825313523714681803200730400582672478535963,1748959785636111562717850200687826812386376904389120425⟩
def resval5Tail76 : Box := ⟨-254741713944386835139794758049378081679916348288751286,216372714409212313725433330671811120128379599004446731⟩
def resval5Tail80 : Box := ⟨-280068575699197744701868499841105764307098426733642255,221655094719711843094551836398183055936352207448810505⟩
def resval5Tail84 : Box := ⟨-307938654497036288973632608128183808495975539310733379,226407007520864486865484042635003050988812316619668983⟩
def resval5Tail88 : Box := ⟨-338582131260675319542437714344106792543252282881305511,230506600078729654694024682454999819429751490537727064⟩
def resval5Tail92 : Box := ⟨-372274990278291210162176398487828355206112423061570590,233815799183267593751250900002031922113315925201433690⟩
def resval5Tail96 : Box := ⟨-409320680541178533637653569879170279143333266991658466,236178034932508957833550451263661419169931266678321788⟩
def resval5Tail100 : Box := ⟨-450052847744211297869517956218168272609622423281279398,237416090776273667242106497572167778928909332355452640⟩
def resval5Tail104 : Box := ⟨-494838339208462053786386048110703693878346567710479396,237329719536106455215032645275333100853964097139822440⟩
def resval5Tail108 : Box := ⟨-544080507829068556150232417422661878740593671605789298,235693000774064194719018498252710420622966172460534650⟩
def resval5Tail112 : Box := ⟨-598222844804331880142566613525291207777463599492273159,232251412378975844544435265914628718464760898179245252⟩
def resval5Tail116 : Box := ⟨-657752973863600369753586205766113195624883865492683629,226718586448388296475358179816043424345603726472895778⟩
def resval5Tail120 : Box := ⟨-723207042967272026361547175649437208865226712328195048,218772716470414719833339120517263135938588927851767588⟩
def resval5Tail124 : Box := ⟨-795174553032012839146217118078552738352180142053833034,208052579423536887972443779371055948025153175223846733⟩
def resval5Tail128 : Box := ⟨-874303667170281691653190402680641488932426142379106883,194153132682607449809299224422661228815479647887706578⟩
def resval5Tail132 : Box := ⟨-961307048260925995484602765514035336512807911860315835,176620641511220998587198063665285283375964210950564543⟩
def resval5Tail136 : Box := ⟨-1056968277428933675174708268193452714958502253112067593,154947288395532494578734770512843930809838481729315370⟩
def resval5Tail140 : Box := ⟨-1162148935119503955951113101480418998175126506003215709,128565206400624498926856031471264180773874157574621908⟩
def resval5Tail144 : Box := ⟨-1293272779324587332646507318130302388257116078569401189,94831886208339565980989381125154279537180142346540098⟩
def resval5Tail148 : Box := ⟨76529567417499722889839670846538494364190071863,57741073267389171763491872623466726914798232518⟩
def resval5Tail152 : Box := ⟨84097066821245006730099247824931500050666213729,58856486156688703811035748951542803984447456998⟩
def resval5Tail156 : Box := ⟨92465702100266152168745940144031552915634101039,59782667257527683026650550740532957488834142846⟩
def resval5Tail160 : Box := ⟨101667114629515261013108119826656559414181357047,60480419307775354752243157645891823755041072558⟩
def resval5Tail164 : Box := ⟨111784174697587210435360528119102339469424304573,60906165914139707134334806645931533745239760319⟩
def resval5Tail168 : Box := ⟨122907999881340864608221090387121974936915068447,61010639005438236854704096988882658212286257871⟩
def resval5Tail172 : Box := ⟨135138775016225508865977795935049259918175923238,60738224300251725415400222433351005240613892847⟩
def resval5Tail176 : Box := ⟨148586654493744750063413969635385115747757032519,60026235931388081700498439006323019228770527207⟩
def resval5Tail180 : Box := ⟨163372754348207395351945178804187902731029567623,58804112784694498278836993554523833355950341944⟩
def resval5Tail184 : Box := ⟨179630243067646095171039517437931121783844679856,56992528365102057779501896213390763845525696421⟩
def resval5Tail188 : Box := ⟨197505540953106097782224222659793929419652625111,54502405162284223799354878792319367886197159489⟩
def resval5Tail192 : Box := ⟨217159638828129116055974065481992808740728704293,51233823562482042664279856176003295103635256675⟩
def resval5Tail196 : Box := ⟨238769547975164497494207963389881582436765833253,47074814333303084053586155426555936069673150686⟩
def resval5Tail200 : Box := ⟨262529894357512841554127994091575808478407142565,41900022585176170729599609916241236871094331122⟩
def resval5Tail204 : Box := ⟨288654671484890271530289910107273370319335004290,35569229876228650121556498794083655034492136169⟩
def resval5Tail208 : Box := ⟨317379167709501995728010041608227983659179511772,27925719765191270551344367409630166516491417126⟩
def resval5Tail212 : Box := ⟨348962085319688565626765258436711581727377617413,18794470615114572337586199302450365762121283694⟩
def resval5Tail216 : Box := ⟨383688270923626003830462946303563026704159152317,7980093472704547134997900625071430339241472313⟩
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
def polyval5Tail5 : Box := ⟨5211537416503102265475363289502666479681324535616907217402,3748492923461144272955001744425510649171449668812808184279⟩
def polyval5Tail9 : Box := ⟨5730144086955550003497591500222918552857141769197927729227,3812464125013747529533764201794922037982849824464780671630⟩
def polyval5Tail13 : Box := ⟨6300360052281645771722475069590760913084969492257531072590,3862707016386085479413904001328250776327639696182842223736⟩
def polyval5Tail17 : Box := ⟨6927319136658970519786145830196684492235560541357326035430,3896548924305800704973695040853552583649093070334735163081⟩
def polyval5Tail21 : Box := ⟨7616667940071739353428307968872188323898655300639273902053,3910966287824027674128955142310848799459758569541187637245⟩
def polyval5Tail25 : Box := ⟨8374614965017550951522617943471457990747138671513184812050,3902544193213114943811770158964685883974776288119801035124⟩
def polyval5Tail29 : Box := ⟨9207986532183696743027387410176988129143365923039669861933,3867431547250008421877608263664327116390814710140484565867⟩
def polyval5Tail33 : Box := ⟨10124288260540781817768917015536255945201471148163524196301,3801291407241321447249181449411649841801111764407973498691⟩
def polyval5Tail37 : Box := ⟨11131772665420642606485914140198660226103104861237057504178,3699245960956239010341050293427647794678012315856065025184⟩
def polyval5Tail41 : Box := ⟨12239513483389032980009284966679221064225685027830633253243,3555815597584902033981328106454705737907054551665460990306⟩
def polyval5Tail45 : Box := ⟨13457487393307375588917733180036797863854942524800044382682,3364851453502516094283131597428399384908995957042670918069⟩
def polyval5Tail49 : Box := ⟨14796663869590391662088844085575051885264456234977582445488,3119460753464313018876424199446311055099441134786619936944⟩
def polyval5Tail53 : Box := ⟨16269103976907658522983589870320559820020100310432304805236,2811924198297457534321617182025195081141508423798546473724⟩
def polyval5Tail57 : Box := ⟨17888068996106734750459711346240004309930674403836978022116,2433604573548016286358075794586300244191682154819514238061⟩
def polyval5Tail61 : Box := ⟨19668139859678716644113097671099404132494333162001360921130,1974845669174483319080960901316056434757552790687543199905⟩
def polyval5Tail65 : Box := ⟨21625348472443669538283404240693531215249770699235694067126,1424860507472737485448007934234045884014120530463894771345⟩
def polyval5Tail69 : Box := ⟨23777322118837394290264642269068058676980403660541577210118,771607770988122266002530178331633527898355987437218276586⟩
def polyval5Tail73 : Box := ⟨26156250000000000000000000000000000000000000000000000000000,2⟩
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
def resval6 : Box := ⟨64250979560229806998191653728764522360267883682088657608,15771127219324312993119071733475030449856112779105967461⟩
def polyval6 : Box := ⟨14853511177436773301588527043135482844736500746464785437430,3683283276289084540013208476472633525325685771699238571986⟩
theorem cell6_lo : Holds Q cell6 (63/64:ℝ) := by norm_num [Holds,Q,cell6]
theorem cell6_hi : Holds Q cell6 (127/128:ℝ) := by norm_num [Holds,Q,cell6]
def resval6Tail4 : Box := ⟨-40915140872439227244841362087867204748748912638273836505,15168089197043316813861055099759844107635409858135854486⟩
def resval6Tail8 : Box := ⟨-42890618072449616887067128681107097928616982191233947661,14980031015558357049192940068305559295446518773581836792⟩
def resval6Tail12 : Box := ⟨-44961426450502518205316787301998443545023636134223930784,14753561405648748836112957926535283958431603509851197643⟩
def resval6Tail16 : Box := ⟨-47132215834004629831434889712983198346802452401058695273,14485889899725792348233057689403496153913358029231016560⟩
def resval6Tail20 : Box := ⟨-49407813425772442686373036626645789344848955418748013641,14174062591001408399911276274495315398138061324946035428⟩
def resval6Tail24 : Box := ⟨-51793279486654809744977688360513636504131982784113586477,13814952212026049868757933444494815836689139506582120663⟩
def resval6Tail28 : Box := ⟨-54293918592710905112953963176822121952467972054128838818,13405248784675320382403616930721684911271945334614811749⟩
def resval6Tail32 : Box := ⟨-56915291431033331331244639301418200528524706403970712917,12941449787668135323312159346210321003370983045187404640⟩
def resval6Tail36 : Box := ⟨-59663227165083403589145362630593116631078252198018814489,12419849817140973384605113047831757021883455031951558084⟩
def resval6Tail40 : Box := ⟨-62543836397039031836633738167754178451213764384258435377,11836529714775297358982187793157965416443865367845103955⟩
def resval6Tail44 : Box := ⟨-65563524755979667764061434097933561874961049451803544488,11187345136711400374803569550048883417654952884043972387⟩
def resval6Tail48 : Box := ⟨-68729007142124450098206690114445662338929077636622759052,10467914535155836226727523125253571311710065193344374694⟩
def resval6Tail52 : Box := ⟨-72047322658798551189785129850676528628533779534306245188,9673606523198392139723155475684578392719412636908079767⟩
def resval6Tail56 : Box := ⟨-75525850265332030760782658538873880233047308126145100121,8799526591895082033107433988031170524301543023005966002⟩
def resval6Tail60 : Box := ⟨-79172325185697887662645065659936863157273483458610890669,7840503147142378375227355202167030265973334929386250762⟩
def resval6Tail64 : Box := ⟨-82994856108285055465992483877042389226874295782658455055,6791072832053080270407976752275778962088618308033611620⟩
def resval6Tail68 : Box := ⟨-87001924776934379152131415504204009667566781471032527219,5645462333860600163579383701982602371015630065641374759⟩
def resval6Tail72 : Box := ⟨716351605820228674283398416729886768875099874703547960045,1710432206016804533361305010757766223138282868103407840⟩
def resval6Tail76 : Box := ⟨-523767694472424860140642282271560341402705762386107104,196387277185040291196099977476852174666458018001914989⟩
def resval6Tail80 : Box := ⟨-549033981700772078490222972351523562350808941383397394,194050511815721981965292332605501139081783275310971925⟩
def resval6Tail84 : Box := ⟨-575541972825921225678003065878424266980510615462064273,191224637590414173089824515310672152576402045014847382⟩
def resval6Tail88 : Box := ⟨-603329801259738765312083448791647937662157444451858699,187873676626059423483422896165614364170506088921202727⟩
def resval6Tail92 : Box := ⟨-632459258012285852303879949761176731219189360969733244,183959890806773763045242070991613813133546924027361380⟩
def resval6Tail96 : Box := ⟨-662995118441441535210301992424892649958802375958699964,179443325256409333119514279527398260345643001905137650⟩
def resval6Tail100 : Box := ⟨-695005285334351708645507382886982458889116242793150663,174281688699308757916232451740463024125065058451128347⟩
def resval6Tail104 : Box := ⟨-728560939902828326067880404847096020183663701207379148,168430227674541859642982244270745306242900558326206251⟩
def resval6Tail108 : Box := ⟨-763736700069462000123536570178404235726883831555531663,161841594263357952455571411097235491023797083607054243⟩
def resval6Tail112 : Box := ⟨-800610786395971279750330257405184103433851197970115236,154465707003455463529176462000677886349925807254905233⟩
def resval6Tail116 : Box := ⟨-839265196022763489088787521879017010479660713872820466,146249604647514811861933129437999151667108873192567771⟩
def resval6Tail120 : Box := ⟨-879785885006497628529783658095852471443519494743409283,137137292406468035310768794923731717144381525163269922⟩
def resval6Tail124 : Box := ⟨-922262959461114536903223607394880145782274571216625549,127069580300172870686013228890737763167546113947194391⟩
def resval6Tail128 : Box := ⟨-966790875927375856542012211463710957160189955063398465,115983913219479257406136042273231975133279306974557579⟩
def resval6Tail132 : Box := ⟨-1013468651416478123581787034762265668503606020742648462,103814192284079134627209522673506443423663095751979591⟩
def resval6Tail136 : Box := ⟨-1062400083597787539853683628219655319551193750290290246,90490587059350645192957118807165462862256252685861570⟩
def resval6Tail140 : Box := ⟨-1113694005236538472047944257000445553194117680941000639,75939334205685309438524841387093553586926226450652511⟩
def resval6Tail144 : Box := ⟨-1182760352542126528510503121176121026935225653432704095,58151272885397214603502969105116900221078353555786957⟩
def resval6Tail148 : Box := ⟨176340901187445816949880101613911275160374456828,57144796916324013147835547277690539780389932895⟩
def resval6Tail152 : Box := ⟨184809020695828755583330898728095600313796211832,56072014594810929860254031343351511893402044866⟩
def resval6Tail156 : Box := ⟨193731812085001565699158819056922513205222789835,54826105994816649228995251633920491975301325056⟩
def resval6Tail160 : Box := ⟨203085406801896796855336968860723580817071671604,53394057182586868719868484277769402248007270373⟩
def resval6Tail164 : Box := ⟨212890603830383306335681310503932719055037673222,51762865888066024921462290436415971604178670706⟩
def resval6Tail168 : Box := ⟨223169207049307141725368815080132388501105966891,49918774132108536177519653505319307700518056944⟩
def resval6Tail172 : Box := ⟨233944073054052404128318868721609307592760069973,47847227642211933737938335196333507124897849179⟩
def resval6Tail176 : Box := ⟨245239161982718189463330187527424180520356773625,45532833198358152721521861753431273628738278789⟩
def resval6Tail180 : Box := ⟨257079590796429882615535238752043070422994317611,42959313785356334095943401777602745851561394282⟩
def resval6Tail184 : Box := ⟨269491689132085438785735995236744904011091607040,40109461441499785971782375043842032559468361356⟩
def resval6Tail188 : Box := ⟨282503057851736498394981799942707740324680371802,36965087687902011254902354823345109451435608914⟩
def resval6Tail192 : Box := ⟨296142630418800965522877796108932310912611560736,33506971417153169750084620629733546404434793446⟩
def resval6Tail196 : Box := ⟨310440737237589724330625438894504014600542155258,29714804113933967051229426101150569061264596003⟩
def resval6Tail200 : Box := ⟨325429173099219708521166450732990161629109944914,25567132273925065995008002560762212418700228599⟩
def resval6Tail204 : Box := ⟨341141267883893238735603726464337269906865038614,21041296880742329897395891213119883462489391032⟩
def resval6Tail208 : Box := ⟨357611960676768407423882995896064540151755635582,16113369793695623659002583033371135005170825300⟩
def resval6Tail212 : Box := ⟨374877877471334440634974925391376671564636351591,10758086890135336773074267713854972055705581639⟩
def resval6Tail216 : Box := ⟨392977808503929037419376977895886973308154791464,4948715527021479168076012745613243149423691752⟩
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
def polyval6Tail5 : Box := ⟨11728517347326363425083022420123918629814617230865920750444,3609415488233668382226106557893051489688416671575866931168⟩
def polyval6Tail9 : Box := ⟨12294781843887184271149069704428216702876272235378287634568,3531969417121622072176228771321311822093215523504185956926⟩
def polyval6Tail13 : Box := ⟨12888388052572809794959848279173644729381870432169696770583,3442762092887612718863505359766180827621595548023504113033⟩
def polyval6Tail17 : Box := ⟨13510654251927665369050713206527081133070506496432288394990,3340969980843317393419895681084503111697144473854180985032⟩
def polyval6Tail21 : Box := ⟨14162964179115777978189677878658918263728419619200550719292,3225721660714875380141464282814311214904792077559142831955⟩
def polyval6Tail25 : Box := ⟨14846768379873022487776245590065753818783920664534482391620,3096095231358101801127016849511835192449289375619651536837⟩
def polyval6Tail29 : Box := ⟨15563587433951914419386078983411277128319458602030418310605,2951115605526164123307122872847249996918159356424305903876⟩
def polyval6Tail33 : Box := ⟨16315015336444386299516004535520009172382530060016167702028,2789751665490064526283221359067025342191988184897770598854⟩
def polyval6Tail37 : Box := ⟨17102723042358816477432219737741412308101397695685897197790,2610913272517364998597677640210041517578198796848534807167⟩
def polyval6Tail41 : Box := ⟨17928462182333314140856640382689176024327212174289256023205,2413448122872424685247936795149870142596946483208799587960⟩
def polyval6Tail45 : Box := ⟨18794068957747915534668321708820837508088568950010165607319,2196138442638247621398238974467092059898002127790201794542⟩
def polyval6Tail49 : Box := ⟨19701468223897277156897693728345700254044266130929703357418,1957697513279043468868261763379711621167323760327148428744⟩
def polyval6Tail53 : Box := ⟨20652677770303643032689385212118580581466683445321895694762,1696766019462919099259284996611632475340850273486811429976⟩
def polyval6Tail57 : Box := ⟨21649812807688245260415773939879800780666152935819064546321,1411908210244833137685052968965442811352700385884723588874⟩
def polyval6Tail61 : Box := ⟨22695090671578847100413006451904446291420056028231838188359,1101607864270102304280177380466965287133866178352137520790⟩
def polyval6Tail65 : Box := ⟨23790835753015128075422943862939496379076171797052160853542,764264049196880870125022297714618627419258563786980273481⟩
def polyval6Tail69 : Box := ⟨24939484685775566411334767360131095152484169453347880642733,398186662023222986748572628551101188055186113612307656772⟩
def polyval6Tail73 : Box := ⟨26156250000000000000000000000000000000000000000000000000000,2⟩
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
def resval7 : Box := ⟨39039665663289340327675720065729114299247660114680823063,25887922814404498350251177779737152919528262065582194940⟩
def polyval7 : Box := ⟨23388256920236302162337958008286060429117154197689483092454,6429248365139193895379841896197716001426139493859443915988⟩
theorem cell7_lo : Holds Q cell7 (127/128:ℝ) := by norm_num [Holds,Q,cell7]
theorem cell7_hi : Holds Q cell7 (1/1:ℝ) := by norm_num [Holds,Q,cell7]
def resval7Tail4 : Box := ⟨-65251558701163125848195354570228536812601859458624820764,24423464104035910383029894234506613304801942559584938127⟩
def resval7Tail8 : Box := ⟨-66281194875354893328682048648361030537463552001327392257,23393871838798433459865801279623596853822445877600702795⟩
def resval7Tail12 : Box := ⟨-67327031814591056144147529002022526312287582241238793275,22348034904036808933912607398662559219134951794304413255⟩
def resval7Tail16 : Box := ⟨-68389370788642794865037526815798547401328518846832482843,21285695929988471206684900389696199102888488758225011737⟩
def resval7Tail20 : Box := ⟨-69468472184341860011283502023961592715269024855457537791,20206594534289417244599629942088054654616098001674991725⟩
def resval7Tail24 : Box := ⟨-70564600492392518153919549172724360623959021837532050309,19110466226238759222737511652873373210797329699569584177⟩
def resval7Tail28 : Box := ⟨-71678024376838201800116013150718655940600768047925795348,17997042341793075580048531406039371745453473224397953253⟩
def resval7Tail32 : Box := ⟨-72809016740915365350748234958241784036773093823757723470,16866049977715912029627375313197008365666331388790521071⟩
def resval7Tail36 : Box := ⟨-73957854793942825772194991120516359244582685262366148421,15717211924688451608179241313081221401325372728460986682⟩
def resval7Tail40 : Box := ⟨-75124820119266524222493409233113368909820592970085481744,14550246599364753157821265790520438750305009502525405754⟩
def resval7Tail44 : Box := ⟨-76310198743276373557573245881008695251872106307095031646,13364867975354903822481439090237043034199831652966299366⟩
def resval7Tail48 : Box := ⟨-77514281205512108051140979219409515804442240747027244064,12160785513119169326595093812632071004719348173849119970⟩
def resval7Tail52 : Box := ⟨-78737362629875318433913480074136851429430640484386379840,10937704088755958890750087666238893617183496638857989208⟩
def resval7Tail56 : Box := ⟨-79979742796965123818921928494726163619258041778857296182,9695323921666149840135003607255497617380063977839968282⟩
def resval7Tail60 : Box := ⟨-81241726217554455164113005847927124266298855795713014667,8433340501075874150705131163594787465457196368971927038⟩
def resval7Tail64 : Box := ⟨-82523622206140269409171348244531499953076014003702422852,7151444511192855300106231340435423418040847989798295225⟩
def resval7Tail68 : Box := ⟨-83825726652490923663006062873837409599906161547554935722,5849319012548273151902453090378620074630535817169620340⟩
def resval7Tail72 : Box := ⟨716077961655007978475307265894658465708919938378072471104,1838715766916570051674985365819863420786187828810553196⟩
def resval7Tail76 : Box := ⟨-838306487403545286419139260777116293874477227373351035,315836195154044394865501573256772924973338649191752659⟩
def resval7Tail80 : Box := ⟨-851512814170037391172458454937082243759279694966522828,302608719827004301602327808099673506065929316300587642⟩
def resval7Tail84 : Box := ⟨-864948653524509824985004523056163019199348808401609945,289172879482085958697372169680566044647609483929126737⟩
def resval7Tail88 : Box := ⟨-878596495117885829569819777441199216307003439817478813,275525037888222752815649110793824554518123260141757020⟩
def resval7Tail92 : Box := ⟨-892459683113400738024444440471181750690922880691552947,261661849892706672197828184559455114624009151804561297⟩
def resval7Tail96 : Box := ⟨-906541615415850518569207536084657092895734782044475277,247579917590256881525968355807598586569349287969343941⟩
def resval7Tail100 : Box := ⟨-920845743545319624075611037381154322194893335576502307,233275789460787775757698339799492089375049746532232001⟩
def resval7Tail104 : Box := ⟨-935375573482697913445681741281414976784198362303742372,218745959523409486369775780900971035161815353102415512⟩
def resval7Tail108 : Box := ⟨-950134666529005091813692532276262368864676384355442665,203986866477102307998924784297105648643802658073865948⟩
def resval7Tail112 : Box := ⟨-965126640178275313270347316833038110479555177622390017,188994892827832086541461909457396295028910312323068790⟩
def resval7Tail116 : Box := ⟨-980355169004214853084472219755289579151950075976950824,173766364001892546727726772514535025195910561779155417⟩
def resval7Tail120 : Box := ⟨-995823985560850163708268195701954093025303338923338127,158297547445257236113736212735830726945996235688279510⟩
def resval7Tail124 : Box := ⟨-1011536881297387065966288258102940087771669889934483227,142584651708720334085659570367553237391435142800999319⟩
def resval7Tail128 : Box := ⟨-1027497707487505326480641990873490750999381709280186371,126623825518602086962308308602248581763642497550254892⟩
def resval7Tail132 : Box := ⟨-1043710376173319676521805658106356770476716949148198929,110411156832790322621556613979654673293146170053248485⟩
def resval7Tail136 : Box := ⟨-1060178861127188657477397843838838828744049572343821764,93942671881269643320714289040970115529875674056508610⟩
def resval7Tail140 : Box := ⟨-1076907222276312511871019720192258757937582438897913486,77214330256610867550161075212315625296772807084775341⟩
def resval7Tail144 : Box := ⟨-1109077362072552179297560102036180368588867848766963835,58306576872195146112970392139564308317677484022436141⟩
def resval7Tail148 : Box := ⟨305986616490250943217871624059183557793007657202,98291948294818731742556886081328448712948000476⟩
def resval7Tail152 : Box := ⟨310770326140579500070284152178291952630262223198,93463810675068397423503525790551109626629221580⟩
def resval7Tail156 : Box := ⟨315673904615994171587593329402662234043978465820,88560231516861577410877605391023746385620027559⟩
def resval7Tail160 : Box := ⟨320654856291907491765133539594561180464722557219,83579279840759528854165045367284343838364706728⟩
def resval7Tail164 : Box := ⟨325714401349452020684655560499840643920268031875,78519734783214712237981324404149272592802783951⟩
def resval7Tail168 : Box := ⟨330853779896766334623296688471762976020269954977,73380356235900396629486470488514460596009824138⟩
def resval7Tail172 : Box := ⟨336074251609575216050250940132982599845677565713,68159884523091515172470948538269003468285060702⟩
def resval7Tail176 : Box := ⟨341377096039760158110998462822328617474442172120,62857040092906573110256875614092632279085870472⟩
def resval7Tail180 : Box := ⟨346763612928980763710057199900100201370828040901,57470523203685967511024495858007935634983787192⟩
def resval7Tail184 : Box := ⟨352235122527244976342370404170630960256569218519,51999013605421754878668708444162211649908422224⟩
def resval7Tail188 : Box := ⟨357792965916505964537258082232899268080714324064,46441170216160766683772037768259354639365108305⟩
def resval7Tail192 : Box := ⟨363438505339364973020575397517234511021856887454,40795630793301758200546810945684068339899026117⟩
def resval7Tail196 : Box := ⟨369173124532960706543522439783745927963650304957,35061011599706024679315910573210211978416460079⟩
def resval7Tail200 : Box := ⟨374998229068127083655498884143827268141862658939,29235907064539647631237623237535820739991715070⟩
def resval7Tail204 : Box := ⟨380915246693902497682953471566185431498336549053,23318889438764240481939290719308413803920319542⟩
def resval7Tail208 : Box := ⟨386925627687478671956317341431069188862432700151,17308508445190913911172082818000518470553757047⟩
def resval7Tail212 : Box := ⟨393030845218712797616043577305700393796888381844,11203290921264666290460950861254189985567739636⟩
def resval7Tail216 : Box := ⟨399232788632579953714989293900218350979827247207,5001678703479751886986703746904528646676379428⟩
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
def polyval7Tail5 : Box := ⟨20034639938316060892272006369569080357080991099293769008818,6110629997879478645921162686895340425821122407042235431132⟩
def polyval7Tail9 : Box := ⟨20350760524254565839358652037225069342702866259039976187830,5794507662618941762203461865807234722820889697225882814627⟩
def polyval7Tail13 : Box := ⟨20671870863801019728769680644020267779435154000214515319890,5473397322925191348770141855302055072066513304732372289158⟩
def polyval7Tail17 : Box := ⟨20998047935524218428002579806541683700709750287254955181594,5147220251201891814134945807796330619408533862633162642011⟩
def polyval7Tail21 : Box := ⟨21329371686172655276861779632129107752404320176493834300392,4815896500553454657656104863796196489197459484606993268540⟩
def polyval7Tail25 : Box := ⟨21665923324102844497603846954204721278486995000655147274332,4479344862623265433723382011973325461436558256176424206866⟩
def polyval7Tail29 : Box := ⟨22007785339040853487116528819619776001151121782785222758361,4137482847685256444115296167875263826698185402005454312920⟩
def polyval7Tail33 : Box := ⟨22355041522300664884326515804344169190665538052276687472111,3790226664425445046898006231285507801574722364775843066243⟩
def polyval7Tail37 : Box := ⟨22707776987321656307266532859503039582713889203957050241295,3437491199404453623956723791989992696068117821059183396136⟩
def polyval7Tail41 : Box := ⟨23066078190530136910288325887940269999950489419920853085698,3079189996195973020934567192785202137127242909315621245692⟩
def polyval7Tail45 : Box := ⟨23430032952530053710355925486712535120847739540183679530189,2715235234196056220867290209494894482329777142503562820988⟩
def polyval7Tail49 : Box := ⟨23799730479628061579994448846102172796037118689072571284240,2345537707098048351235200197855654224515240914827882980899⟩
def polyval7Tail53 : Box := ⟨24175261385698232760485395589869077529597753839930265411503,1970006801027877170899266589496112406086139352795270333288⟩
def polyval7Tail57 : Box := ⟨24556717714391765006970126390981530026757372309135228034261,1588550472334344933829613920647790828549113626201949593677⟩
def polyval7Tail61 : Box := ⟨24944192961697134425105564947467195286522013795430412781959,1201075225028977412253188394805472344732300447598002591198⟩
def polyval7Tail65 : Box := ⟨25337782098858464614773270731248273040353951811870617485850,807486087869439030983791637772071767097374553714201799460⟩
def polyval7Tail69 : Box := ⟨25737581613982837593313371222071627969057702505618382366404,407686588077958673471253550835844095298672707963805728371⟩
def polyval7Tail73 : Box := ⟨26156250000000000000000000000000000000000000000000000000000,2⟩
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
def pend : Box := ⟨1029808393014819473702152138937113599508388733914841059113836,9112270556022355565660967370176922154559776707867894675⟩
def zend : Box := ⟨1003659287160451829865039062500000000000000000000000000000000,7283394443160007148437500000000000000000000000000000002⟩
def betaquot : Box := ⟨428738943374370938746495789496160685082851050125835961770798,394748462081268580906318477195328830029895222463500663⟩
def crit : Box := ⟨113190647342280003556416048661531261490260135460500901820,24684602052070867624951335265016388851035236940601873590⟩
def subsonic : Box := ⟨717581593308363701190093152754966820221893699527932487299,14912362469111818741494130010636658626512485955370601092⟩
def pendTail4 : Box := ⟨26143706569956105630354876953117294220056318030268562770949,1530729646762589654334619903202663891838219425453932754⟩
def pendTail8 : Box := ⟨26143737764319548805967708852769084799231044391962079765530,1530421251167096820478071396789402636207188692012607352⟩
def pendTail12 : Box := ⟨26143737765503756121237435422511353877199669665686039896617,1530421221862041037663312016203607738251081973063643326⟩
def pendTail16 : Box := ⟨26143737765504268571955502694568026821000100926958111608224,1530421221840337732795541935247595298288121823587771225⟩
def pendTail20 : Box := ⟨26143737765504269657777271542907785763052448977126898023020,1530421221840265936692124175644140173211323414201798318⟩
def pendTail24 : Box := ⟨26143737765504269665954125858662077591420994009018604963800,1530421221840265108345717231427017983485137497222657954⟩
def pendTail28 : Box := ⟨26143737765504269666134596936334595105561589859369175028123,1530421221840265079633006066280633882235208195941775161⟩
def pendTail32 : Box := ⟨26143737765504269666144653045295771246199882104618328663431,1530421221840265076900017963942189391057468507137440739⟩
def pendTail36 : Box := ⟨26143737765504269666145808413236767346890995930919045517505,1530421221840265076221284376166292072274580952279559518⟩
def pendTail40 : Box := ⟨26143737765504269666145874919220979531977512013401030837087,1530421221840265075791512196611630716971650617582601701⟩
def pendTail44 : Box := ⟨26143737765504269666145122607911727721786912050065808209624,1530421221840265075097624311721622212877930423145159838⟩
def pendTail48 : Box := ⟨26143737765504269666139005654519455363968338937678984806456,1530421221840265072175434808384045098241160412556457032⟩
def pendTail52 : Box := ⟨26143737765504269666040334407136224427324343533365698204171,1530421221840265038455329452898258556425156019505836223⟩
def pendTail56 : Box := ⟨26143737765504269661832855538642105481345706553361099653781,1530421221840263876392968217147804406920349595438457735⟩
def pendTail60 : Box := ⟨26143737765504269080634779332636328391370840035297089664158,1530421221840125602590889520603973268363641835719057483⟩
def pendTail64 : Box := ⟨26143737765503924948201857646526870672862635665285114743177,1530421221767125387269125746624415794084099473132170102⟩
def pendTail68 : Box := ⟨26143737764031954833864985627231363913585974516612120924093,1530420970486864402322516475546328606448666932992420159⟩
def pendTail72 : Box := ⟨26143542416304038347089515036787930624535171267425090742281,1504431746990305179449130142706898079288226796923299322⟩
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
end SepticProfile.ExteriorCertificates.C02

end
end

end OAI
