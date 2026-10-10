import OAI.MathematicalPhysics.Transonic.Certificates.BarrierData13

namespace OAI

section
noncomputable section
namespace SepticProfile.ExteriorCertificates.C13
open SepticProfile.ExteriorJet SepticProfile.FixedInterval
def cell0 : Box := ⟨250000000000000000000000000000000000000000000000000000000000,250000000000000000000000000000000000000000000000000000000002⟩
def resval0 : Box := ⟨111179098942378064098788682225913982456785078364638853844,342325679437045856877748556886960164538687308294852069⟩
def polyval0 : Box := ⟨3780756308963856872269375793701853305277777020159740109426,15310003477045157832463269469383005908036636138430881510⟩
theorem cell0_lo : Holds Q cell0 (0/1:ℝ) := by norm_num [Holds,Q,cell0]
theorem cell0_hi : Holds Q cell0 (1/2:ℝ) := by norm_num [Holds,Q,cell0]
def resval0Tail4 : Box := ⟨55627305827739883711564712800153151924964833976452,1714224216319457187832955620544416671494946979433⟩
def resval0Tail8 : Box := ⟨6554254518499959826490530593740642916446708851,362876164980054027172859105582236051068879149⟩
def resval0Tail12 : Box := ⟨5807875171365768306956983574622079576075015,486596236748444638078379332127598733838885⟩
def resval0Tail16 : Box := ⟨22659283709011830727452481670814808738850,25956512141043504674996397909569406603035⟩
def resval0Tail20 : Box := ⟨300759809523805501386970919255285828892,372357405175526614375067746776163150096030⟩
def resval0Tail24 : Box := ⟨11656070213203192733171888128117337782,5956932327676787282060874886409225181657845⟩
def resval0Tail28 : Box := ⟨1200291949222543586859828387672540868,95310875623091318306899527415792310038509240⟩
def resval0Tail32 : Box := ⟨308274907234717489157204192254777485,1524974004085216222877983903338405687509617716⟩
def resval0Tail36 : Box := ⟨-346244089630513963840348227820993492,24399584063056215075778149678356090809672195417⟩
def resval0Tail40 : Box := ⟨-138468964845593273048652827692759910545,390393344878021344983152489193067312715997860921⟩
def resval0Tail44 : Box := ⟨-35523618406932780667051753277441764225576,6246293484742525773413459503367397298652204779703⟩
def resval0Tail48 : Box := ⟨-9094324482359756113181681211997215558748580,99940687229935718507949351302211024610591117470147⟩
def resval0Tail52 : Box := ⟨-2328149571928859968972514408906904118832451543,1599048813038446819036778395622079047225857822247820⟩
def resval0Tail56 : Box := ⟨-596006340877408508314212772350877397811748491416,25584222252650781053815269463814316343337346333109913⟩
def resval0Tail60 : Box := ⟨-152577621930563978729725595686883259222643417082453,409204514516707600783422057437891378224685781181397736⟩
def resval0Tail64 : Box := ⟨-39059860561390684472047352811058911949238964880024823,6510653605514285058945593088175362065488772443299975824⟩
def resval0Tail68 : Box := ⟨-9999074370977811431531949567778428322863753686596015223,94796193037884069427545978598457850794622107402925137848⟩
def resval0Tail72 : Box := ⟨766559254529028430859660574753377415245896124694988406726,2480182135702155489838458921005706248846197929281363234⟩
def resval0Tail76 : Box := ⟨-25526307022522712998973413589029678316580270173024,585224352683786114553418831177428396350185452610⟩
def resval0Tail80 : Box := ⟨-1343629225863429365129131579646120500796104334,63806432380593752937935080619830257832342484⟩
def resval0Tail84 : Box := ⟨-740278411170049044859899334581167416515823,55157826397643200013310444398858721587193⟩
def resval0Tail88 : Box := ⟨-1995446075109858464244661179108958337843,370349646702492326596738794385826560769⟩
def resval0Tail92 : Box := ⟨-19365067013840392883837252430170309098,2496380420481040574177125263191694231939⟩
def resval0Tail96 : Box := ⟨-567997951788335621929332601079720535,39895827650473575352703204152319873165698⟩
def resval0Tail100 : Box := ⟨-45232325610699730175177395943761061,638331384105602037663652982767911357441603⟩
def resval0Tail104 : Box := ⟨-9170294688737112169395372073635978,10213301942806969374189310716024685297820968⟩
def resval0Tail108 : Box := ⟨-6363348457016330786373135919101800,163412831027133360880731453784551478776156776⟩
def resval0Tail112 : Box := ⟨-467737951343454944883610918709671019,2614605296004764136732476101754825517079806287⟩
def resval0Tail116 : Box := ⟨-118348856561087444980954196761751452024,41833684625140885667226589105138604305855087693⟩
def resval0Tail120 : Box := ⟨-30293261809873759969704692599058120151857,669338925602410581845255440270212578508958271685⟩
def resval0Tail124 : Box := ⟨-7755046224334421232692559266220088705498887,10709415539284211874411319571375763474010010029529⟩
def resval0Tail128 : Box := ⟨-1985291350042627250440672522515904549539759481,171348787417987175788549445046530785224037538184022⟩
def resval0Tail132 : Box := ⟨-508234579619469129141188785854936827933900623677,2741104128785988202357069568937888384033397974202216⟩
def resval0Tail136 : Box := ⟨-130108078044493032457645313724087032864371072671694,43735689754166111280528065002008542441956713129561945⟩
def resval0Tail140 : Box := ⟨-33307986304167189927096112503154225454580971304163096,668544951280980393711281603453990608376198682468873403⟩
def resval0Tail144 : Box := ⟨-8742569674024953296266554856583957157686918486926528880,2594480933874196320206258551585420511375807113336571419⟩
def resval0Tail148 : Box := ⟨55817767201492489651659590065308572652653576,1066382034930679130736837294899557945191940⟩
def resval0Tail152 : Box := ⟨968983455772350489900923176516916900309,41072123448647099939009073337356352392⟩
def resval0Tail156 : Box := ⟨299839585665482472044854966471917975,20367339344951102351217215001697559⟩
def resval0Tail160 : Box := ⟨511573791120912452229683198146991,51975099316424496443705439366815⟩
def resval0Tail164 : Box := ⟨3327211537045833703600055719755,26849928852710916232539419298938⟩
def resval0Tail168 : Box := ⟨67508163915934409022834357601,422333588454156152619461762602478⟩
def resval0Tail172 : Box := ⟨3781456773988138263302827274,6757136581794736961330725457117974⟩
def resval0Tail176 : Box := ⟨542298320834317646116183574,108114170028021713952615239207084831⟩
def resval0Tail180 : Box := ⟨196749461075511688912350726,1729826717438557300733636982710754293⟩
def resval0Tail184 : Box := ⟨1744943163202821297395995420,27677227476552564297399569045966151148⟩
def resval0Tail188 : Box := ⟨405831332680774061550686365897,442835639244760997385153011504388622721⟩
def resval0Tail192 : Box := ⟨103810671585582510161722254036260,7085370130594986293228390758812489985399⟩
def resval0Tail196 : Box := ⟨26575133136130129935472554491168872,113365897175345801286256962050242588702335⟩
def resval0Tail200 : Box := ⟨6803229408249563151340361394899533813,1813847976778387653351459519271764935117495⟩
def resval0Tail204 : Box := ⟨1741626620759163659780640992084897915695,29019934853543825618753771174555449108301023⟩
def resval0Tail208 : Box := ⟨445856434850696424705855028254674386263230,463900967270574430018287457420164056437915675⟩
def resval0Tail212 : Box := ⟨114139364755733054920319254581684815488228506,7315409883138234522971453938514474345106072800⟩
def resval0Tail216 : Box := ⟨29226507490250191210605425349203713613051410609,89649767887943931428119742093648133240542645793⟩
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
def polyval0Tail5 : Box := ⟨2029206552552168335312529810133847866164815735124606,51668479518208264546284385504821652995784951828827⟩
def polyval0Tail9 : Box := ⟨191637550594239067544235543036447173540789220718,9626974141273794473544705032474372490180522736⟩
def polyval0Tail13 : Box := ⟨146931659049077362553452343559409360074562758,11441449202831037229147521033899496093148544⟩
def polyval0Tail17 : Box := ⟨502327695400780059001292554559069686703193,427368260561096796774628568425171976357138⟩
def polyval0Tail21 : Box := ⟨5858628082823154680500724313949578215265,5942631441312758014825512451908649973178424⟩
def polyval0Tail25 : Box := ⟨199286433052691266039640052920978306230,95067639412813384702667071528741117087639464⟩
def polyval0Tail29 : Box := ⟨17948027317593391936254287083439344139,1521081558143814636347728342959265914566564560⟩
def polyval0Tail33 : Box := ⟨4058170303430821127689945164543525024,24337304847349573092359821756306360736463410654⟩
def polyval0Tail37 : Box := ⟨7845060117537148213899054226022739735,389396877529868233773408509486534026448497953725⟩
def polyval0Tail41 : Box := ⟨1448831687641799978914794183623350850770,6230350039124258217037339990153659249915604091036⟩
def polyval0Tail45 : Box := ⟨370175642624406733450508722767816449276810,99685600278957683739167202588905058441384094886797⟩
def polyval0Tail49 : Box := ⟨94762707856662533488048653495736125981202367,1594969515623337207395556999640218805308965493474917⟩
def polyval0Tail53 : Box := ⟨24259236177444934411908844481998011151230054529,25519489506940407193675458805990363542458301346489466⟩
def polyval0Tail57 : Box := ⟨6210364162659312873908545436883339251172938443491,408306009894697123977095021446215311770674757150095552⟩
def polyval0Tail61 : Box := ⟨1589853222587620730865472053884131341438188826600297,6531405670930396231110335377976374308113698003160350164⟩
def polyval0Tail65 : Box := ⟨407002443280784262562562303312308499085027573524313406,104120925956183394440942816057607152617385133194898681520⟩
def polyval0Tail69 : Box := ⟨104192850065611887423891571763668405304929149324354903858,1568254126381115480968983294944547137171696531362716949146⟩
def polyval0Tail73 : Box := ⟨26843750000000000000000000000000000000000000000000000000000,2⟩
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
def resval1 : Box := ⟨110959692988881157902331895963247803041159849454083385811,267883305397687893595552543822321274090949239520394281⟩
def polyval1 : Box := ⟨3762813452318655427538928065524232354101978996370389874720,9202002903940598050468294842984862327990329447258643625⟩
theorem cell1_lo : Holds Q cell1 (1/2:ℝ) := by norm_num [Holds,Q,cell1]
theorem cell1_hi : Holds Q cell1 (3/4:ℝ) := by norm_num [Holds,Q,cell1]
def resval1Tail4 : Box := ⟨54023491615924279136036168389238655933950031555968,3064815675969143545907058074757162000225474661757⟩
def resval1Tail8 : Box := ⟨6176883898750019051960709625052093001411228566,6126863709156222677439765732188469369928685636719⟩
def resval1Tail12 : Box := ⟨-317937661154599835393690695909399773342468666,19363082569586922271276966095843608497203573939610⟩
def resval1Tail16 : Box := ⟨-2118940913700071720215963373646045325820335591,61195805044687210213391036126508381785431982950600⟩
def resval1Tail20 : Box := ⟨-13886825290929781425533979287318277064168401648,193401774226663735459610404360938431761127855078158⟩
def resval1Tail24 : Box := ⟨-91008699952248335632867190509775397599129260616,611197994131674465870519986343468455241702174108970⟩
def resval1Tail28 : Box := ⟨-596434616071359907273290636820537108159290607238,1931378685444405635312312709716172855835014739493816⟩
def resval1Tail32 : Box := ⟨-3908793899891527367194273663208701804374613668208,6102086647278902423747354413924309379625210577033900⟩
def resval1Tail36 : Box := ⟨-25616671702330588806289841622552191346239943025575,19272344228813364367457470086976218246039292627949591⟩
def resval1Tail40 : Box := ⟨-167881419668394512853150869083906485701410584467532,60823204883196024257893115889761128561954406608722764⟩
def resval1Tail44 : Box := ⟨-1100227671938790932349616968125234274001268211304663,191661724100077149560593967552405602699770969173660177⟩
def resval1Tail48 : Box := ⟨-7210452070818058169568705510067192681270084492581054,602012506616047130673328635991522470909235746025455273⟩
def resval1Tail52 : Box := ⟨-47254418691313090571291709872526971900990353668085890,1878190981602976717857031431031572383615756201690720315⟩
def resval1Tail56 : Box := ⟨-309686558335376507903031116311777500715189666314897545,5775671743829278823468615116324561695137239023005608823⟩
def resval1Tail60 : Box := ⟨-2029561828702725597146440669535778083861682860962331283,17203175521344652476185820390008822839226620062973146670⟩
def resval1Tail64 : Box := ⟨-13300936394317403240915241385292239851749590894989770414,47484011274121178590828344654123925471011325346710266612⟩
def resval1Tail68 : Box := ⟨-87168902272011781182658190968484732311726661959716639157,104941447609696554991230776263318186700937940024652006621⟩
def resval1Tail72 : Box := ⟨769312256289399464350438375388440563894001125081467159189,1563061701426333247985237762415203933761126297687274301⟩
def resval1Tail76 : Box := ⟨-24960562263536178425880417721671868187311631624928,400535882861769370599592857881422360410934227031⟩
def resval1Tail80 : Box := ⟨-1284598242460528996539431886566689872350506235,61521778596710917196936240162682646524822026542⟩
def resval1Tail84 : Box := ⟨-3390269343429370468803169343465782201423183,194309673833065246630675756993574508176644491964⟩
def resval1Tail88 : Box := ⟨-17688337280426290156253539187698238475719146,614105368196165194947364748314171143225752851199⟩
def resval1Tail92 : Box := ⟨-115910386560032320110106245683777272787579139,1940816213167488871279999482016695114888154562100⟩
def resval1Tail96 : Box := ⟨-759630197246217523044142989877498213239161806,6133544365178736617966290048682607412695658282115⟩
def resval1Tail100 : Box := ⟨-4978312457502227054180160033288859125201683774,19382451598852714831856600602363150099009396250101⟩
def resval1Tail104 : Box := ⟨-32625868521246415534897529437543585870903782999,61241226690681299145847750825704986027459730069767⟩
def resval1Tail108 : Box := ⟨-213816891940795589793552463788298106597512743856,193441815887761055431091253193253447118686243327629⟩
def resval1Tail112 : Box := ⟨-1401270383023178864454699999460811822389719536826,610646161612083897226021876890545385784553350226548⟩
def resval1Tail116 : Box := ⟨-9183365582180689717401940006148729550776267674602,1925188765167787348140273607509398214545770962384656⟩
def resval1Tail120 : Box := ⟨-60184104679379374847260189948409528091257840335433,6053387073987186298224338151488440957576215153928831⟩
def resval1Tail124 : Box := ⟨-394422548426781712570701645670104757622998148097510,18927481423655204537710156689950117980070530195780428⟩
def resval1Tail128 : Box := ⟨-2584887613369836459844784225496076016111120754664681,58481870619383171146150540842116675525782876589315066⟩
def resval1Tail132 : Box := ⟨-16940319462998093011940874953638095834500678814564005,176060792976333852881427430382135998834639145353797813⟩
def resval1Tail136 : Box := ⟨-111020077650003619049885034118225687288409182011738939,498958746863357338984626807237082392255994460580901053⟩
def resval1Tail140 : Box := ⟨-727581332661439527722773204670150799820017216170072453,1200253098209608460800951241882396340067204893885560981⟩
def resval1Tail144 : Box := ⟨-4858090608982498112761510365023414201143027955988634325,1307326267902148355861070229339832421776692410078784111⟩
def resval1Tail148 : Box := ⟨54995455548958844886271322258078262010555128,777803386759584121234526189774118684055742⟩
def resval1Tail152 : Box := ⟨932163358557102586694897601772562989498,2739677719261163873171480430905167893969⟩
def resval1Tail156 : Box := ⟨387189726917951573041670448924130433,8572644891572176730647794907252176182202⟩
def resval1Tail160 : Box := ⟨689013089409173994279388120616981611,27093432869145905384030209934186933391512⟩
def resval1Tail164 : Box := ⟨4512438485471824133648859565404296939,85626291034981027193092646403097892697242⟩
def resval1Tail168 : Box := ⟨29572697388513889071433371473925193210,270606053085872574614661804184279882513425⟩
def resval1Tail172 : Box := ⟨193807629223182982036129122705293648182,855148417068305577316116289614922922488349⟩
def resval1Tail176 : Box := ⟨1270137678856549118853045040545522027473,2702033683587397239415660675632023672227116⟩
def resval1Tail180 : Box := ⟨8323974292151523721468545216750333183785,8535451065759217143963226627243372388647539⟩
def resval1Tail184 : Box := ⟨54551997921043362344870736212669396879966,26947996276809207823389686426456937017540703⟩
def resval1Tail188 : Box := ⟨357511973575349216911680047278934675653512,84983875166312851826998720621158924892400568⟩
def resval1Tail192 : Box := ⟨2342990470023408205791316131538810427991497,267377936786907202529737409474785792392125706⟩
def resval1Tail196 : Box := ⟨15355022344345414551472205539067428233048569,837096303307188374020621400642935245816045159⟩
def resval1Tail200 : Box := ⟨100630674435902497632889390975550358047347580,2593536478240550283397395264738189325110772822⟩
def resval1Tail204 : Box := ⟨659493187983180117110708406981923094360377280,7855405467389351186209235760523929490114999327⟩
def resval1Tail208 : Box := ⟨4322054556789343319300170107558736552175568249,22589230082430638100859766976535560115574271977⟩
def resval1Tail212 : Box := ⟨28325016805910602581295756674217081979201869015,56727932226900170228703833177564842512220166072⟩
def resval1Tail216 : Box := ⟨185633844800218171379651056439722089229058329635,83177876375386922948777735473984159454290057616⟩
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
def polyval1Tail5 : Box := ⟨1974848217158258060096424228840385581070769255926784,117240716477892976355143180829673123745630272071543⟩
def polyval1Tail9 : Box := ⟨184691062759745931622637037032754785554925682882,270299070560855789742534039245347066858535188722408⟩
def polyval1Tail13 : Box := ⟨15289708769008763262296664529035456560953615118,854254957244362140332686218514685633651820887772397⟩
def polyval1Tail17 : Box := ⟨99307402768080504088222658626642261271038972853,2699816104443151608560529563219098849972378390675116⟩
def polyval1Tail21 : Box := ⟨650818012480054528518326750081839989517088374704,8532415173547902623933850298460939498131925605458118⟩
def polyval1Tail25 : Box := ⟨4265200892835765310411773961814387775553108720070,26964437192170648086720218602356965234813383845606402⟩
def polyval1Tail29 : Box := ⟨27952420570182318790416853760891537248075369750073,85206465019234863758138153557365786124576008291201589⟩
def polyval1Tail33 : Box := ⟨183188983448652243898964895133968446392513957677001,269199661196675892430273519372919378487914290282635782⟩
def polyval1Tail37 : Box := ⟨1200547321929067783467181759084808610009202132280240,850182287815254669109405351838570028416662526691752600⟩
def polyval1Tail41 : Box := ⟨7867906928994329609588259400457950601883791725179276,2682922288072475254598658394731996973912204833910399988⟩
def polyval1Tail45 : Box := ⟨51563114849857231019761405637943604601131097014238719,8452662686636268859999432164873350926872525419197330516⟩
def polyval1Tail49 : Box := ⟨337924029480024355885798858771115055947504335421526121,26539629120895880341836305884784118407814129212682557174⟩
def polyval1Tail53 : Box := ⟨2214618919600288288776908845450467069642820906398052568,82731721901340843192158713928914650591413925934586956517⟩
def polyval1Tail57 : Box := ⟨14513726551492502098588361115715900416265923894814376161,253958659252963461593548143445643952108768650830386385409⟩
def polyval1Tail61 : Box := ⟨95117158327873284570436798745605334672683331398006773558,753388159770169866614543979456402557079800713254827304071⟩
def polyval1Tail65 : Box := ⟨623359808829762704223807739242127758096694585776054256792,2058336011341680451340447661241165806530993079846714449258⟩
def polyval1Tail69 : Box := ⟨4085250950301734778596475697492792974753523832287980229530,4390232221600659212031662494961181197237571937628655553166⟩
def polyval1Tail73 : Box := ⟨26843750000000000000000000000000000000000000000000000000000,2⟩
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
def resval2 : Box := ⟨110851663647486064391798305612191501754100947879985895345,250774003073141761863940613036046025976457985172578087⟩
def polyval2 : Box := ⟨3753947125657662624911858337773891200987696744608875357926,7936242545991338009544300892936715099645522401254157620⟩
theorem cell2_lo : Holds Q cell2 (3/4:ℝ) := by norm_num [Holds,Q,cell2]
theorem cell2_hi : Holds Q cell2 (7/8:ℝ) := by norm_num [Holds,Q,cell2]
def resval2Tail4 : Box := ⟨-139894435379509796763778691579482571187002957134662,33954921443887085725746553393720116806758309623179958⟩
def resval2Tail8 : Box := ⟨-443209253106798499361260316517027082541464007828728,57810548582970250573265365984215108702981547392962562⟩
def resval2Tail12 : Box := ⟨-1017000791819878708960676916120040068584640687479666,98361348367212480276061997070905064325124428147576884⟩
def resval2Tail16 : Box := ⟨-2333607514905960543305822373147713949892944959142741,167201468776587276270465479125053149749667647481017354⟩
def resval2Tail20 : Box := ⟨-5354690035298246206397460527663421917299352388480916,283864665437434696173657296863814758570091859527116206⟩
def resval2Tail24 : Box := ⟨-12286858518725604240762918926464669116608096424795362,481108593383113238927788481699373475491804693683627366⟩
def resval2Tail28 : Box := ⟨-28193395185154643832756113946916698018210961797339069,813517463202988602266708277262633242930790045203544871⟩
def resval2Tail32 : Box := ⟨-64692494900539014452121134470780560262125507235967125,1371229069430087698892101250081338664108778846556449508⟩
def resval2Tail36 : Box := ⟨-148443238885253487695085378828947233703603900464155839,2301175556407644062610976514646294205443318772471870515⟩
def resval2Tail40 : Box := ⟨-340617489008927298514057339691480284627646802144190317,3838324029324978726468897231162760573051712720110043233⟩
def resval2Tail44 : Box := ⟨-781580048306749043396379107351109573457010896234573308,6347509688925936952904118995187758497822686314732208787⟩
def resval2Tail48 : Box := ⟨-1793411646855190825764627983081846928306097942274612760,10368500707874122721322760846584228300040963615598052932⟩
def resval2Tail52 : Box := ⟨-4115157931735645878884447882567887573632980038725239891,16632527618023316181801375682429872713908995693583723954⟩
def resval2Tail56 : Box := ⟨-9442631217892474439074264399778340750148954111675701957,25952004355540544791826232841942612480393592169888573890⟩
def resval2Tail60 : Box := ⟨-21667038251311460782096200397106486476305088209472790662,38714647424979017189240385354967762213764744410064731296⟩
def resval2Tail64 : Box := ⟨-49717132407623517797585211966124313746127408373447399443,53291357604019919108942237584188763795568588712203072494⟩
def resval2Tail68 : Box := ⟨-114080719178292629204266582132915341101107170444316927257,61647128840015920298927230797549772197749376428555143376⟩
def resval2Tail72 : Box := ⟨770687136949410988303506514192872415954771783684203638589,1104919368826076027493478516971566014334192783788587333⟩
def resval2Tail76 : Box := ⟨-26784954536668314997595215602716995992152329909504,397527161833390951950602496107273383268209942975579⟩
def resval2Tail80 : Box := ⟨-4809977758347726668363365309392539598275020654218,676777415633216146677835496435629839231293562466010⟩
def resval2Tail84 : Box := ⟨-11034080358073175312215414282406797171926872810420,1151721762883575930175673005067718598534518579513120⟩
def resval2Tail88 : Box := ⟨-25318771979663388708582453993386807620677320873074,1958291361775477997634209333616069624785064573469498⟩
def resval2Tail92 : Box := ⟨-58096391595025660154976663334271351609536768351833,3325854923629393393036819686869980163323464149781627⟩
def resval2Tail96 : Box := ⟨-133307836545308229845102651985482514091913542430857,5639563711625934146857628659885496176467535258531543⟩
def resval2Tail100 : Box := ⟨-305887832212922906116294688844391579678639477823850,9542376166666463555736362953856887435956611332168398⟩
def resval2Tail104 : Box := ⟨-701889463670953869938770391094578958834174227827720,16098814134583926100919409258636659546146099017767150⟩
def resval2Tail108 : Box := ⟨-1610553828337230225452008552900076570740504592604472,27050704788260849048632369156533271287943174771155282⟩
def resval2Tail112 : Box := ⟨-3695572833370985608004670345567269890765751900109689,45199269021516866411698284594490369674052512844186547⟩
def resval2Tail116 : Box := ⟨-8479852288358282723201447115985739959054349361691917,74932589293324616850122191844322550749084880579951959⟩
def resval2Tail120 : Box := ⟨-19457848099501012496732738320420861388583010415836795,122840094723728124006276887389064589836228671268815959⟩
def resval2Tail124 : Box := ⟨-44647930151216637676774067660726698344844074828446638,198106078096991003068123873151414562280373669516857140⟩
def resval2Tail128 : Box := ⟨-102449030159663023992653387944699652959556739357293084,311678590741902423918854525453115192268526422279108889⟩
def resval2Tail132 : Box := ⟨-235079291360389880569922302968486077403168255280515490,471404146879027883050919828614691350878709292270073015⟩
def resval2Tail136 : Box := ⟨-539412360876507405747196778159678761767847843837102951,665817194749409972990869363353974523801958897149276502⟩
def resval2Tail140 : Box := ⟨-1237734389751987503818950649019957996420883209823164680,818334128957559851954766195677575854632161704973765615⟩
def resval2Tail144 : Box := ⟨-2909636258682764210837952331393744148910422865437810424,660302195577350560048992741582119605692081796484538978⟩
def resval2Tail148 : Box := ⟨54829356341017344391705947871696743629405904,42109568950604719983679944538387757770598890⟩
def resval2Tail152 : Box := ⟨533726072933050344202468110679421685142548,70681948531966040189706140908920482505499156⟩
def resval2Tail156 : Box := ⟨1222587505980421141602542003932060314950352,120266635383428191864245971447673810307992660⟩
def resval2Tail160 : Box := ⟨2805345640630430734253295098697482031117209,204449904596193998566770089097420155715633683⟩
def resval2Tail164 : Box := ⟨6437139171416340520729863126891659052423600,347131167770754827482971453926508631293898980⟩
def resval2Tail168 : Box := ⟨14770643630746724589818948490776545105767506,588401278582964769924860877494760838095455889⟩
def resval2Tail172 : Box := ⟨33892682363524169510188081916924511763191032,995091987935252195471850587641291601760523079⟩
def resval2Tail176 : Box := ⟨77770065171944952561498056043356112718332172,1677632354463118762117229635122648070589292080⟩
def resval2Tail180 : Box := ⟨178450999303546247970886199639935603234515025,2816188030611164694884581996614552476528844512⟩
def resval2Tail184 : Box := ⟨409473221888491540954866350575344771450624564,4699248755008907884922613080850317846190725295⟩
def resval2Tail188 : Box := ⟨939576242767556515067812751478506375221355971,7775677908574279406753029390746921015393762069⟩
def resval2Tail192 : Box := ⟨2155949324113811973877945691270134917510460384,12711889494668428732781372267911764726365312280⟩
def resval2Tail196 : Box := ⟨4947035989815580049601657889168304494524253893,20416840645641337048691948636118041815452068413⟩
def resval2Tail200 : Box := ⟨11351456553641464405473096949423520711882132727,31918197215134684354856780262182786765521795604⟩
def resval2Tail204 : Box := ⟨26047024148294815586174277898124563643053476086,47769094900812719019311052205420933253588183207⟩
def resval2Tail208 : Box := ⟨59767437224998505964713132650920747518962351987,66159603018726128354140617849762032896860929036⟩
def resval2Tail212 : Box := ⟨137142213767125522687379480000553034854746642315,77683757470986209864613771253981983994682377160⟩
def resval2Tail216 : Box := ⟨314688540561118891889923335810653753015615748037,51797159195900737604029677260466296163983813235⟩
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
def polyval2Tail5 : Box := ⟨21716241542464355219206024441595315325465043373497361,3032320438974524924054660015298180127915274249084818799⟩
def polyval2Tail9 : Box := ⟨45358145722463420950092149025310552634223474367578215,5161362972556599744116980254887328618649633550808684903⟩
def polyval2Tail13 : Box := ⟨104078280499487583100486388362220942076516878973515626,8778357774056622535490334965084481808643256624276900095⟩
def polyval2Tail17 : Box := ⟨238817764860122754187953982551099724326827053999418851,14914225999786344443013962582503379120093113466917801221⟩
def polyval2Tail21 : Box := ⟨547990652912873532757067507744250623153400276924941594,25302433028882264068830813988015856872726553230633212126⟩
def polyval2Tail25 : Box := ⟨1257417997594543737507554712151338971434731093176779892,42842263552023475168119047147025354914316174475225824340⟩
def polyval2Tail29 : Box := ⟨2885268229066069405828958605753561158409485106363095369,72346841569865794311715342821860826839313396360731645025⟩
def polyval2Tail33 : Box := ⟨6620529346313991938718104891745055980901868296580899368,121722128603050820111845931105657872954451843757400635570⟩
def polyval2Tail37 : Box := ⟨15191450272750736162800328576753772162139270765512230613,203755458082350584182505778873525946113998561618360177105⟩
def polyval2Tail41 : Box := ⟨34858264244073815521831444429578770248243811518485020002,338655495282163172454495576684238310387978345885267775327⟩
def polyval2Tail45 : Box := ⟨79985686968230159100737203281116781219657528061210576846,557212296796645602145960604676413729481890882009912562279⟩
def polyval2Tail49 : Box := ⟨183534959600501792922563442042895432136081478920015244425,903496669512755649027745198162964091163449979118334075213⟩
def polyval2Tail53 : Box := ⟨421138864618832867273773294388060655531605785472367872737,1433289104080834972664735742702435681626862905025923510209⟩
def polyval2Tail57 : Box := ⟨966344197740269323410138240272665592926362071505643492150,2197228047071825456843169001071275164157778883685883806849⟩
def polyval2Tail61 : Box := ⟨2217371007426440867578077517083804237992058684176449325230,3179543575976458261649310379332053985468673873982560456590⟩
def polyval2Tail65 : Box := ⟨5087974032526210523193207517517726656231408875272622824162,4118923982317151564333475940042711582912181022424749608377⟩
def polyval2Tail69 : Box := ⟨11674852722692389431708739469217324313375190283305210355902,4031708896811682851154991316663660314427395464688959359859⟩
def polyval2Tail73 : Box := ⟨26843750000000000000000000000000000000000000000000000000000,2⟩
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
def resval3 : Box := ⟨110669006403764367086319857369293290918563965504447057915,1775066850099647864831235302276316378548861538366830256⟩
def polyval3 : Box := ⟨3771906957569534324492028081057756753144379150425003047825,237770692592603419308530109414460266867109088936309373419⟩
theorem cell3_lo : Holds Q cell3 (7/8:ℝ) := by norm_num [Holds,Q,cell3]
theorem cell3_hi : Holds Q cell3 (15/16:ℝ) := by norm_num [Holds,Q,cell3]
def resval3Tail4 : Box := ⟨-191485354617696743002740814729060507454518074303976971,1999964250528701580885374498112586668740874795077900405⟩
def resval3Tail8 : Box := ⟨-283964085153880333832599039984121388314061456027008445,2553018895981311600288856831577665413775924154220073985⟩
def resval3Tail12 : Box := ⟨-420989579594409520884964104685482037133112831694444997,3251593472971594332714277602125127454630231665256468809⟩
def resval3Tail16 : Box := ⟨-624136049771079938117852299331583984866485096044791257,4130163267429693015358356981766141017541466878712794910⟩
def resval3Tail20 : Box := ⟨-925309859199921710869383792742609502847781520903574588,5229312561581728497413936710245841744148905287356603968⟩
def resval3Tail24 : Box := ⟨-1371813622761557791855295362528964765923435501904151956,6595580648218121072638153704300204387038037413236211700⟩
def resval3Tail28 : Box := ⟨-2033775601636157668536011903582253980848876663980348119,8280321207112963014028137047887944067308695677853360693⟩
def resval3Tail32 : Box := ⟨-3015164107704343343329885873513300119788245309698065982,10336828948259752915271780445721687666769601588817591237⟩
def resval3Tail36 : Box := ⟨-4470116855111602779815802074823300787169663542222230996,12814549158037296230723163463172311129844791149771203766⟩
def resval3Tail40 : Box := ⟨-6627149960857854228308468934206783021321027543885102513,15748511705072540745539761325972556409346687138508331112⟩
def resval3Tail44 : Box := ⟨-9825048880652082206416117797055452793107292912243003449,19141101498378325003038981881066774453024059022596097856⟩
def resval3Tail48 : Box := ⟨-14566078340968635872055223697430488151468047114448853738,22931711905750115072774413495542977710459041729455735719⟩
def resval3Tail52 : Box := ⟨-21594868464527575649149369360568882883320669362521252373,26947456110464227890837260642995192132132279339999515269⟩
def resval3Tail56 : Box := ⟨-32015367011216842587777341044944363289655124340239497842,30824529943778954905309523970973627841684305247334839831⟩
def resval3Tail60 : Box := ⟨-47464226352965173447017190761789453545104871157745732491,33884425238984282464368778119077411687409407098294385613⟩
def resval3Tail64 : Box := ⟨-70367857483865279971404521496394774186349824765851867364,34941085340618228213537196182428961526759448155974598699⟩
def resval3Tail68 : Box := ⟨-104323442969336513850309152657972505961882489127646202671,32002931123775495394342710319319257858037045788068901757⟩
def resval3Tail72 : Box := ⟨771372619814470730888681945721893218532064117198792932730,895053746775084108417613528367569144575710789007122706⟩
def resval3Tail76 : Box := ⟨-2342088218570506120748582762622739115359549489994392,25144435973336350061245290713885646650032916626816435⟩
def resval3Tail80 : Box := ⟨-3435846776323323852581810338193034882673651167763064,32114547589123675897315285900931665686095084268566608⟩
def resval3Tail84 : Box := ⟨-5093796052932074669588457402283003742505102666039972,40927548396736843984202898749701394081954915040936394⟩
def resval3Tail88 : Box := ⟨-7551782515448947539218495183734097530846445671778156,52024609184493865787920392898802304475680615827499600⟩
def resval3Tail92 : Box := ⟨-11195858368763783961497872208507136755199268061356707,65928060770936723105163300457737294799372998389102734⟩
def resval3Tail96 : Box := ⟨-16598365267672731519227605548578677317412019317062032,83241499714834159784223012599725966749443952617821008⟩
def resval3Tail100 : Box := ⟨-24607825544465639093588807131283778633944894571472056,104638700707259232002883335507346296313349329372672557⟩
def resval3Tail104 : Box := ⟨-36482211848068309409532608712634002040538711157528565,130832362856781886147695552374518547566989583817394559⟩
def resval3Tail108 : Box := ⟨-54086525399098909206918434779034459221860429312301506,162508594953633187893342015263663092804221274062774074⟩
def resval3Tail112 : Box := ⟨-80185714669113885174078557371115746761411370153964499,200204958070375511674967160888382782321603618522480136⟩
def resval3Tail116 : Box := ⟨-118878940541143847018985992962264741831897525019753997,244097516321180639144770662474399034286596097604150342⟩
def resval3Tail120 : Box := ⟨-176243394007290526069479520087483571910392513497579737,293643521092547449778919871527405963437939009562841791⟩
def resval3Tail124 : Box := ⟨-261288784959003099867382580183751096638620425524148069,346997809964117524996635926370726357959519735971528531⟩
def resval3Tail128 : Box := ⟨-387372414891919452524366951786820335680013412837984287,400077862340310398417226702228460235538577732183946894⟩
def resval3Tail132 : Box := ⟨-574297086048853144040233807797054436520924797963878248,445087434814199057487424391067835626906148347653721880⟩
def resval3Tail136 : Box := ⟨-851421346409393780177787806864567154678814956268608912,468210929340969763389857296124465476298569389275295722⟩
def resval3Tail140 : Box := ⟨-1262270676633256309753030058522660492571316258897703458,446043907966455619785518987464143404315727025940360318⟩
def resval3Tail144 : Box := ⟨-1933854110124254643309964937855160042227806985003330404,335927586407958981647009403435858003474077263578050243⟩
def resval3Tail148 : Box := ⟨539806184301362918475237349883634016441189523,4743020382016890340764408607371943076328025106⟩
def resval3Tail152 : Box := ⟨719635893247527659086443895493480951870422455,6048211881281450271010697070797510854329712068⟩
def resval3Tail156 : Box := ⟨1066891343090014621186669085648343655145634329,7694345430131029469899555430715744004370859735⟩
def resval3Tail160 : Box := ⟨1581714561382090714264031137621600895231811488,9760041747789193430837571704916520779401282494⟩
def resval3Tail164 : Box := ⟨2344963215349096381102123591706601178326701861,12337374394089315005765242631117372069028149884⟩
def resval3Tail168 : Box := ⟨3476513788010551994625786255697712307146990492,15530334164032026632401411442996549358234264067⟩
def resval3Tail172 : Box := ⟨5154088575512352960246621417260843735905501132,19451003520982707372073756635468290731573705801⟩
def resval3Tail176 : Box := ⟨7641168901973106890916394777490559261134113127,24211064493303935553610198045738310328226189420⟩
def resval3Tail180 : Box := ⟨11328377720531659313528601882518577030867860342,29905557445747377795051412529974512835889674653⟩
def resval3Tail184 : Box := ⟨16794831186875096597080192110491749301742446848,36584075974749851075860438744305514857933475056⟩
def resval3Tail188 : Box := ⟨24899095135609102025094965774222534686638341647,44201943081561319124420560639577644489996592789⟩
def resval3Tail192 : Box := ⟨36914032161073816157246038142748879536592151795,52539906418688765975655214657304651493151429629⟩
def resval3Tail196 : Box := ⟨54726718499903345145435260999741719691666319571,61074828537396814519981498230926476250784036849⟩
def resval3Tail200 : Box := ⟨81134829831077959526979897141752126457562475161,68774704719766549688931045070614413945538046604⟩
def resval3Tail204 : Box := ⟨120286046599516218347386575907378304585477424224,73777583155034842967011345708398344468974004179⟩
def resval3Tail208 : Box := ⟨178329492237380070209219891401938091533440455713,72893303606472292388982940398104799338916170744⟩
def resval3Tail212 : Box := ⟨264381519769875284982175712209425250038755828504,60836004190542178270175270984192341319548240608⟩
def resval3Tail216 : Box := ⟨391959657648742648684148043566227931170137529281,29048819523932984198923893928568364699256797869⟩
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
def polyval3Tail5 : Box := ⟨33184758266745861776292402025736298125074915723739990638,299589914295019721240653810451060931741152623947975372228⟩
def polyval3Tail9 : Box := ⟨49195031170473134475662872591450625985905259397877126930,381592001650327266583542639534827767811911918300804669848⟩
def polyval3Tail13 : Box := ⟨72933853475628805821437171484604915314751189825136342670,484736447191957446278216778018304269073120883523816458112⟩
def polyval3Tail17 : Box := ⟨108127729066559141043097317685583940621075592779280675216,613797818084893633159077367978241497653670228539979741175⟩
def polyval3Tail21 : Box := ⟨160304237825837077501561063364782175654685379628926141695,774256012211053402906427420971924970340994996578958413671⟩
def polyval3Tail25 : Box := ⟨237658266633014225593749538077074372748918505001979218662,972165744160420919238686915348940297296181997185934108439⟩
def polyval3Tail29 : Box := ⟨352339105098227613159815756857386921388336384631394715515,1213824378780460103218233715512207638950062205547744998103⟩
def polyval3Tail33 : Box := ⟨522358623330018928381723447411786596351700149145793133304,1505099946141066072699557002034782904786599954910673982621⟩
def polyval3Tail37 : Box := ⟨774420231586735580122829622556666136736159693646798362500,1850202480686983464434617484406199423912131879043405436648⟩
def polyval3Tail41 : Box := ⟨1148112940622316798645255161983680861617675725815245034264,2249561608939568659213212242047307805603606445197504017271⟩
def polyval3Tail45 : Box := ⟨1702129245414462511304742373118944685401945756752252622698,2696290493451467866301226266742012920930353089814821791103⟩
def polyval3Tail49 : Box := ⟨2523483418386349191164798141886753729012483617485033053536,3170439268158196255315400339599709423590414316142643423128⟩
def polyval3Tail53 : Box := ⟨3741178045102136901720475824363211383001217663525512482215,3629822788189385674302706162113847724872103691660817840881⟩
def polyval3Tail57 : Box := ⟨5546465280165900590164098128549901225832102530138163221500,3995577398561866826647107526443227121484807719565194801203⟩
def polyval3Tail61 : Box := ⟨8222885073422368093970797638337582432994380727889791631252,4129654363478439390366493673339816763125234023599851085623⟩
def polyval3Tail65 : Box := ⟨12190798195844788683200154079227593293431327564493012997994,3800036856740740144862488095313324958996768063539416429576⟩
def polyval3Tail69 : Box := ⟨18073408536594338788536525877565521205815872469502914672149,2627339504167397810758825824920301038070312953928033557437⟩
def polyval3Tail73 : Box := ⟨26843750000000000000000000000000000000000000000000000000000,2⟩
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
def resval4 : Box := ⟨107334960245244710541142904116468787720230654276585501307,9052532582948270709947339974979171461087219357260638064⟩
def polyval4 : Box := ⟨4592361953550742122937177360307079425021353362188420820295,1882357210166297359252679237919338728273771864200229329948⟩
theorem cell4_lo : Holds Q cell4 (15/16:ℝ) := by norm_num [Holds,Q,cell4]
theorem cell4_hi : Holds Q cell4 (31/32:ℝ) := by norm_num [Holds,Q,cell4]
def resval4Tail4 : Box := ⟨-4164096169638900803775741095900336761517092210144624392,9786031401879138429077549682731034146770896221657502136⟩
def resval4Tail8 : Box := ⟨-5045762483277382629320388073883937646578452153407668259,10793426437856679323311001896797583471797146757276585927⟩
def resval4Tail12 : Box := ⟨-6114027105084125642730633144681240377470157693679534689,11869963912221159065247557171937068474385507455683847885⟩
def resval4Tail16 : Box := ⟨-7408459578001505095754826303687312674689765394065448001,13010763552784962383564315303478145991709214593979986265⟩
def resval4Tail20 : Box := ⟨-8976943081131757459132721723531076960561708498879903084,14207269636919667156172679310048425433605005948397613997⟩
def resval4Tail24 : Box := ⟨-10877498383222299263377445137014492267447692306235865316,15446114220111561954089464933641170177599787558262504928⟩
def resval4Tail28 : Box := ⟨-13180430131688735331774948351337438663252232011467186198,16707691967487576704032464192407294342646141469544205485⟩
def resval4Tail32 : Box := ⟨-15970927536453030006598944171249264828545747524088920382,17964378231651756533013335766528469293494337070944250388⟩
def resval4Tail36 : Box := ⟨-19352215658075255831480326755324903743973712540889541426,19178307395646581192929517137575319503453896076044530224⟩
def resval4Tail40 : Box := ⟨-23449373871483192053095215631808739001002503009679583237,20298609922690875433867900572160888839649140497017774011⟩
def resval4Tail44 : Box := ⟨-28413962756515097453345831719988451813279842393695460285,21257983907350550418980916651654595100518802405862100170⟩
def resval4Tail48 : Box := ⟨-34429630571520299645798448200620947247151444835469274288,21968449325969400727030719255070424717184069303148424817⟩
def resval4Tail52 : Box := ⟨-41718906702640851770382389948759798205834116836359062064,22316099568564848934258616028654613064772949649152455928⟩
def resval4Tail56 : Box := ⟨-50551433389568260847557098451865353774167475804000436896,22154623901858548453689972151566901712501689722350247572⟩
def resval4Tail60 : Box := ⟨-61253940232764366527557901891741970932190273234109128852,21297324687483531423473659369552738650021683243329129214⟩
def resval4Tail64 : Box := ⟨-74222330451105317834435944663955080387218016260272802071,19507292546913193575087018317535967596045373091938831151⟩
def resval4Tail68 : Box := ⟨-89936248511476301216204456506315346921564041068123452445,16485326188542890337058090882288705273694591316282571723⟩
def resval4Tail72 : Box := ⟨771673897162483990129569330454385035315912209999890868053,874712708140279078081250788997208204718000647756856873⟩
def resval4Tail76 : Box := ⟨-52989359280261238893557264468154685278194210457459671,127443077716037795771296469824339026314050164797560229⟩
def resval4Tail80 : Box := ⟨-64178337702933995059995510177244811456344066764562916,140658670215980661900967354368007404645345803713789235⟩
def resval4Tail84 : Box := ⟨-77765865823745101574547852813343069903355917088919670,154808346459664178965728721401060371244404011916544891⟩
def resval4Tail88 : Box := ⟨-94230081678753767244481198568506743485998284603218894,169837261910173147629802205821288487382937086292349332⟩
def resval4Tail92 : Box := ⟨-114180022291319570143078332954919807264455500798961683,185644972344536914843543283742249610321535967157255309⟩
def resval4Tail96 : Box := ⟨-138353668575732098668878849457216845787983717355223895,202070960182344688787968868989378886237778969957367703⟩
def resval4Tail100 : Box := ⟨-167645243224118330596406120380232538197296690333750648,218876661014798949058665172280362012495369780455757086⟩
def resval4Tail104 : Box := ⟨-203138289464942551449814476427544717172964084997166532,235722973310053280154479782413062514440768072622468796⟩
def resval4Tail108 : Box := ⟨-246145753098267242358154862888244258642194621453388660,252142198638135101622372163964977357414586480152593557⟩
def resval4Tail112 : Box := ⟨-298258550507137757162157784734086702381757511703868643,267503123867294252765915411233285846715175134525963467⟩
def resval4Tail116 : Box := ⟨-361404419255223261175483669780556414140550549626513671,280967669163821264336607120446390165656052274018496097⟩
def resval4Tail120 : Box := ⟨-437919228250522289090614775279169244394106367196695237,291437175108024005387383732517547731552291570992328247⟩
def resval4Tail124 : Box := ⟨-530633385354657371300893879547643743670162648004859991,297485975231719159561639877426989784744394209145470368⟩
def resval4Tail128 : Box := ⟨-642976538796475001490940654272318609226465972620899335,297279380285192237029132440143734867358786025665645792⟩
def resval4Tail132 : Box := ⟨-779104445466405491960595805451096137988399807762535012,288472567516503435032062598317577246245182116540747420⟩
def resval4Tail136 : Box := ⟨-944052699169319402548827946194183021529110587423979123,268086097864947611778776346461778849855337356643659286⟩
def resval4Tail140 : Box := ⟨-1143923108952240589801446642351018524971756512501965674,232352839452250247990869998243876491343659687340550709⟩
def resval4Tail144 : Box := ⟨-1445574120806794124495825535557944964261433608720778497,173524552664506035399422968827048248260505609489356678⟩
def resval4Tail148 : Box := ⟨16629668320325544128353223089435270911544357718,35342195959382238717696566818644075927210404403⟩
def resval4Tail152 : Box := ⟨20084622068475428757428982274310519687222551599,38862633396057412806119647895065040400064793750⟩
def resval4Tail156 : Box := ⟨24336840758540903818241111562960700388504632888,42592526724270580442905880460810318685118441320⟩
def resval4Tail160 : Box := ⟨29489319872960263883447815917430421341347677333,46503027282512698714556819044840292126488287358⟩
def resval4Tail164 : Box := ⟨35732657135217685663257954747346494338642365509,50549897794119865945322906729462671826426718333⟩
def resval4Tail168 : Box := ⟨43297803796207704124320662468403087296432400487,54668367322353811608358617506057067791152424957⟩
def resval4Tail172 : Box := ⟨52464606997480083160671936531199863373328707519,58767271700261234973310736731708944887468016760⟩
def resval4Tail176 : Box := ⟨63572161774198823375378940043290177974774823522,62721748637543627961153827628229274256237486114⟩
def resval4Tail180 : Box := ⟨77031354734802810945894471271458976189236765902,66364153763545632297204261993964579789794294195⟩
def resval4Tail184 : Box := ⟨93340063428318256481906807828012114442295062320,69472789467462367046958772797436780555441669846⟩
def resval4Tail188 : Box := ⟨113101573648765423908978767687788162071903516036,71757947724377215075330177446153298305746904536⟩
def resval4Tail192 : Box := ⟨137046895962855968825707471657760572958866906112,72844657649205279176304549174699321879472774308⟩
def resval4Tail196 : Box := ⟨166061806985820692727316773766018964428513472692,72251394035402143778062580629107832871368688044⟩
def resval4Tail200 : Box := ⟨201219615706364294084573002733505846963716275075,69363839433291173723392997245509432384575366307⟩
def resval4Tail204 : Box := ⟨243820866940669538519868987724729659771213848486,63402593117650091015111027565108785008165316690⟩
def resval4Tail208 : Box := ⟨295441450611132917961532206346843085776624074448,53383477954786222131758179306126144162932376723⟩
def resval4Tail212 : Box := ⟨357990896533928868011485275233505450322513092023,38068801440119973184120889458926546890651686026⟩
def resval4Tail216 : Box := ⟨433785035048184652957613939725753385221034760704,15907430889090099756130252393932457671964953692⟩
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
def polyval4Tail5 : Box := ⟨1023947858575412108369568484105154414367093160925155818177,2070059886852825480291796267310430286133772047912822855427⟩
def polyval4Tail9 : Box := ⟨1240730845995681224254317310494306253223216984006467027026,2272237707536923148290103736450790465386484337926749741881⟩
def polyval4Tail13 : Box := ⟨1503412425304990999392651126726291981929891987435012959164,2485251085111495967233642368914047466404756359882056909093⟩
def polyval4Tail17 : Box := ⟨1821707687992628519492522935501731924548505723695940648687,2707065159726417189342628986869701863642747326287528566483⟩
def polyval4Tail21 : Box := ⟨2207390895960232972795154113733176710421838351943053964317,2934628091772418067702955375938921230960837082748759247362⟩
def polyval4Tail25 : Box := ⟨2674729101537303217488227440945389907201278869672523833025,3163576364262339987620874463125836125473044413915966532494⟩
def polyval4Tail29 : Box := ⟨3241009908894466441938715092203885767514237239443280180144,3387866957041799948626944657474070043547938465878705194025⟩
def polyval4Tail33 : Box := ⟨3927180970781246491345455698341486502428759602430416023030,3599319442935373343765149446395041719927149815058827382262⟩
def polyval4Tail37 : Box := ⟨4758624876443883844579611655414806415801062594740169111488,3787047282406124287578537927556285585226057558493097499929⟩
def polyval4Tail41 : Box := ⟨5766098095093851730597140620700913061559744438421113811931,3936752982075271794677894217853786976260706432731663710353⟩
def polyval4Tail45 : Box := ⟨6986868707980836321624975453517019631323347915194726236460,4029856164646522308704712505047570582888768166709681013693⟩
def polyval4Tail49 : Box := ⟨8466095015639383323049175819247736899545187805117820997184,4042416756199161986890021078159659565171422947567205560034⟩
def polyval4Tail53 : Box := ⟨10258496017244839957890330449403739555343041959579539827996,3943807167704256475726140084950637798949420305222727118325⟩
def polyval4Tail57 : Box := ⟨12430375555840660415988668344899985479245778876344812311514,3695077210757157908249610409805557430488332117153339574990⟩
def polyval4Tail61 : Box := ⟨15062075005877862145790536440167624454020788749422442614637,3246943154172728271137587336442362874582145894069228494925⟩
def polyval4Tail65 : Box := ⟨18250945231996633215504455482246774795875020852175759327620,2537317326408107684887479399704519738511428922814221632260⟩
def polyval4Tail69 : Box := ⟨22114947829718355529739466193019969827775614138187193504436,1488276421188239547112256421147704271561121163690687313290⟩
def polyval4Tail73 : Box := ⟨26843750000000000000000000000000000000000000000000000000000,2⟩
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
def resval5 : Box := ⟨94820919877219415448360233377256724253726826337499490506,14664128267705278660154703551950262430518733960096202819⟩
def polyval5 : Box := ⟨8604783337049372565443918579753095282265598870944249414848,3767964621762491462348545360426284567655114623267785107283⟩
theorem cell5_lo : Holds Q cell5 (31/32:ℝ) := by norm_num [Holds,Q,cell5]
theorem cell5_hi : Holds Q cell5 (63/64:ℝ) := by norm_num [Holds,Q,cell5]
def resval5Tail4 : Box := ⟨-17523201215065448163907404562639461207301582834086337739,14856689220300616613859197565892000999512372582628664980⟩
def resval5Tail8 : Box := ⟨-19267021336902908086121330681569402759752073073719365262,15218259799929977756700057493179400859665932953447000901⟩
def resval5Tail12 : Box := ⟨-21184313999069725509836320889145250566700983129707359715,15543194597642725812763465101543936531530934677065051097⟩
def resval5Tail16 : Box := ⟨-23292399568440594796246136550759160963563666281557356987,15823125752099696685355938422692841666603203651091792071⟩
def resval5Tail20 : Box := ⟨-25610264164305138781478504728992131485396170776031186684,16048546344790516699865604697480611160350534108875039061⟩
def resval5Tail24 : Box := ⟨-28158783239068503710915605622965128517305736889250824511,16208676454011913379702895834414775744136420082340981794⟩
def resval5Tail28 : Box := ⟨-30960909595379756281959172509916096839127848550397093501,16291315217600093221900451157717772936074025129923206363⟩
def resval5Tail32 : Box := ⟨-34041880106641573359187798737341436568708763840382339602,16282676792085119278652897354030299405178680936056298199⟩
def resval5Tail36 : Box := ⟨-37429443008608908792860176838986518025347259287831691947,16167208515776116178094108763584798013574996651658093541⟩
def resval5Tail40 : Box := ⟨-41154107809144604088171645779476922812290722947512951633,15927389409145775168250681441526511050277836222190744172⟩
def resval5Tail44 : Box := ⟨-45249420066901576778725101676979507132229193947296773493,15543506953907834448671608874744391702343246871651620382⟩
def resval5Tail48 : Box := ⟨-49752263513678951499871775059410074488342578156841243811,14993409880697888949617081587276941796610784539737073036⟩
def resval5Tail52 : Box := ⟨-54703192241465637075714847515413566589805829896012593541,14252234462308557203989715353972792575248056738669886933⟩
def resval5Tail56 : Box := ⟨-60146795945957326566341279289633611536454966569421981764,13292101552829567929211985534615948448629793092380140633⟩
def resval5Tail60 : Box := ⟨-66132101516047593062830603181539139645648619490446770864,12081781330419092351953796733642112596300044182954007914⟩
def resval5Tail64 : Box := ⟨-72713014581864520818827483934513782970876778279612779677,10586322389910088223957663144439107312138546240499462249⟩
def resval5Tail68 : Box := ⟨-79948729276800269620935461019455092512097816436777292863,8766638231896821820833353630241559272911626550988303696⟩
def resval5Tail72 : Box := ⟨771682018000009325573542006381005360396047864922904885231,891473952391087578904584169471862631724407156947238466⟩
def resval5Tail76 : Box := ⟨-227928928610287222717735876680755887557623742680321203,196371712182457727956566897480671764888407095022830408⟩
def resval5Tail80 : Box := ⟨-250583616839883666913132692036420329388414430661757092,201278756692826319859617595985170096445889902804606599⟩
def resval5Tail84 : Box := ⟨-275519599090012584542815316473798907334733080275933608,205722792232643075703583647807438623227083887235537201⟩
def resval5Tail88 : Box := ⟨-302937002878935831772438939313685328254378971482274186,209595691613583213260689462417371240999266595415476971⟩
def resval5Tail92 : Box := ⟨-333082757148999702809714093491033296856596607671764088,212774731012303655737908830965510533617955251522456048⟩
def resval5Tail96 : Box := ⟨-366228364497014747538562726929523479655639527636204968,215120690077527081193565435166751942704242637353624819⟩
def resval5Tail100 : Box := ⟨-402672345185854932114456840809932699843392795728846751,216475931763023209231324073388100576408922336499793725⟩
def resval5Tail104 : Box := ⟨-442742925715678713629611173488100868018895216924937326,216662272989450406827383158092357502670671821355733942⟩
def resval5Tail108 : Box := ⟨-486800994939954552183567798923447330682577166380055611,215478624123335934076052457178191819231266140641417306⟩
def resval5Tail112 : Box := ⟨-535243354349405769050907567977952868702795268094759109,212698373013630434664091812340823066540761379308078221⟩
def resval5Tail116 : Box := ⟨-588506291797001506592993613828253704532209592523473061,208066486830633565035988287363890779646462207763619542⟩
def resval5Tail120 : Box := ⟨-647069510850138762723566405384199558492780976984007011,201296302202786155110675658096445174573554028836436465⟩
def resval5Tail124 : Box := ⟨-711460451159056165714180883623908359930998994520242589,192065971118288442276919831998208677540427435304854112⟩
def resval5Tail128 : Box := ⟨-782259038752141255090716107309281570843229456914667897,180014526722579547127010555080433101314546785943166852⟩
def resval5Tail132 : Box := ⟨-860102909040868660523795159818557793328907082094468535,164737529468419486847114504337395161090805997103164103⟩
def resval5Tail136 : Box := ⟨-945693149586360308523309466984134189314310416161586397,145782250027634955369895961144859309181888798518631985⟩
def resval5Tail140 : Box := ⟨-1039800715507476641875559386279489188719241165682092029,122642334564712918376575430759436987516623774849570068⟩
def resval5Tail144 : Box := ⟨-1201336818636259536109904946829008662722200404954007303,92269103581203593626932519417096620121612192443794876⟩
def resval5Tail148 : Box := ⟨90854142509168778657608496642402287827755859609,68348333400838579942070267134741962284958168430⟩
def resval5Tail152 : Box := ⟨99835532669161938641718620259572778224616611757,69659975030878465575956682256926405043056965744⟩
def resval5Tail156 : Box := ⟨109770328045265445613300038879182105150303782790,70745749433351759556152917267561763289047831873⟩
def resval5Tail160 : Box := ⟨120693752070261684791578164754038797214588889922,71559451840223128568451279496932009033255661938⟩
def resval5Tail164 : Box := ⟨132704183801165917039248522338311645059080392642,72049292621345434738785987540933615839877600305⟩
def resval5Tail168 : Box := ⟨145909793143905425636163347236460008517642985357,72156721506348591010428453071934109275742755372⟩
def resval5Tail172 : Box := ⟨160429514168114899100067328128510256379974419864,71815650322197499391207343160919221832548617107⟩
def resval5Tail176 : Box := ⟨176394116266296867224219774010195434699186210793,70951591604718684513667816239019080307113406607⟩
def resval5Tail180 : Box := ⟨193947381906065067969059802335947669099469760602,69480704256588927737544421480608789921991052401⟩
def resval5Tail184 : Box := ⟨213247401582431132409594511285625093498839445239,67308736531378532911844108646955927574156535050⟩
def resval5Tail188 : Box := ⟨234467997632901212639172251795142511388755917346,64329855625366698897333487997123107254253333230⟩
def resval5Tail192 : Box := ⟨257800289738730527202976303441943779866044336528,60425352059675787503497579875693693320674403554⟩
def resval5Tail196 : Box := ⟨283454416211756031726395946598624204750735993263,55462205824602161359942701467814826586358402593⟩
def resval5Tail200 : Box := ⟨311661426569283678293844388175332241980182658931,49291499924620627278974964999776519072755249345⟩
def resval5Tail204 : Box := ⟨342675362442183429773909860026138778091244836813,41746665494047462779535221184518675120348669123⟩
def resval5Tail208 : Box := ⟨376775545557551958864708561859177106470208382808,32641541036162693493892339848416089498111988767⟩
def resval5Tail212 : Box := ⟨414269093444571344914206075838680463884572346541,21768226554611394198697451443219443710565366913⟩
def resval5Tail216 : Box := ⟨455495663031042783656132948408977113290933158214,8894591430916050280041017745392494917082589581⟩
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
def polyval5Tail5 : Box := ⟨5342043970941984916341024738656482221146424706504089096034,3842443164732902370017561331186702303546200649479750604747⟩
def polyval5Tail9 : Box := ⟨5873637343608835152550741884566763410864569259655219913265,3908021610072870019487811974423077019182842292666615844877⟩
def polyval5Tail13 : Box := ⟨6458132556445463344558843077452782434412043191226301709618,3959528294824781781062953733481823740129900403035661247625⟩
def polyval5Tail17 : Box := ⟨7100791839530390902396328338195047609503573140745443564541,3994223650986127484520143123036316230216158323570091808733⟩
def polyval5Tail21 : Box := ⟨7807403193980597027623145161238577062407193274203744888653,4009008425888300847938916251341536456444322493383876181163⟩
def polyval5Tail25 : Box := ⟨8584330594517147717817078417063716982573056749499380199654,4000382215439684604717725239900542035659794314540293423104⟩
def polyval5Tail29 : Box := ⟨9438571305344866907808382905307171667334311605576906692328,3964397514968515861845387875735104945767602352220866438041⟩
def polyval5Tail33 : Box := ⟨10377818899819579742839016471801561837191655071976766174088,3896608805528183792978871847784745268246082095127168372778⟩
def polyval5Tail37 : Box := ⟨11410532551305163595763550986495158492844637799747969792243,3792016156141251332662159769894425086805947717293822219280⟩
def polyval5Tail41 : Box := ⟨12546013219276574658492134038145409547635017241473537520420,3645002769104867514812219852786743435182265447007149987818⟩
def polyval5Tail45 : Box := ⟨13794487416826000623907475267940614337640932127148030923072,3449265836707030133489253348344489556482131687049839760411⟩
def polyval5Tail49 : Box := ⟨15167199314009905357384552792219497500529701203228062824754,3197740012966554506376766934795768905652182292034912062143⟩
def polyval5Tail53 : Box := ⟨16676512006550061601985860869066247106747964906158369861031,2882512732708716100763688835175299822812434564392845764447⟩
def polyval5Tail57 : Box := ⟨18336018861947866248367847612111246854568130986639148284212,2494730531762192070227316206479033409381096844316275480359⟩
def polyval5Tail61 : Box := ⟨20160665945831746182141754268969151607356535378876500560976,2024495435583647022356441117684998881098955992219987227676⟩
def polyval5Tail65 : Box := ⟨22166886631158074074411863288540125292192614203080620850820,1460750388383029708090449220281393593011794004016785157435⟩
def polyval5Tail69 : Box := ⟨24372749674032802569139112518727765103934952408352333884231,791152585681910488179499483176518178774781139072279115922⟩
def polyval5Tail73 : Box := ⟨26843750000000000000000000000000000000000000000000000000000,2⟩
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
def resval6 : Box := ⟨77418007385006716421217902761112422066990138102224833433,13318595128824340388007193426107397823242271214322313163⟩
def polyval6 : Box := ⟨15214343771807483037745011744039130585433079577916625327589,3770981735575404648636638256964310564439302912589972743546⟩
theorem cell6_lo : Holds Q cell6 (63/64:ℝ) := by norm_num [Holds,Q,cell6]
theorem cell6_hi : Holds Q cell6 (127/128:ℝ) := by norm_num [Holds,Q,cell6]
def resval6Tail4 : Box := ⟨-34942902224734427727324858884362807663947841636413302189,12993639595983180795383446582555204008218914308247185711⟩
def resval6Tail8 : Box := ⟨-36630040837262853131947172571284900239720075261734843331,12834293203438074401801621273920635444406992278191354923⟩
def resval6Tail12 : Box := ⟨-38398581346847446920301680897698403849995055986760503423,12642182031841984445970727173108005050490875823379881972⟩
def resval6Tail16 : Box := ⟨-40252509020186160077008950747937875789990502741606961481,12414924525553913370022985219315603917739420846522944797⟩
def resval6Tail20 : Box := ⟨-42195946453969239688439121979293972332753338228402447570,12149999270126757540022950317345841604430569154468537356⟩
def resval6Tail24 : Box := ⟨-44233215282389966728815221879629125273703518157317332367,11844736837326999731761186803290860242067228750606827092⟩
def resval6Tail28 : Box := ⟨-46368845793105992311555508699646565447009034973369233135,11496311801289313662478193813572400098863738601535943211⟩
def resval6Tail32 : Box := ⟨-48607587001273780455153247848471525344313941346757875217,11101734342629540634375325986514692243077817792791599647⟩
def resval6Tail36 : Box := ⟨-50954417209963848885880648981710388907682822658483817635,10657841419654513372036157533341369038183780418581014437⟩
def resval6Tail40 : Box := ⟨-53414555080444985880657217715778758440620343725804565827,10161287484889812535013963533285373874658157280054953418⟩
def resval6Tail44 : Box := ⟨-55993471236954521894602010479964537254525561609785260214,9608534724067202190167602037673710518034298131658820516⟩
def resval6Tail48 : Box := ⟨-58696900431760257658017763667556389335518580024409695984,8995842793581004432812098897194163375279946472404021785⟩
def resval6Tail52 : Box := ⟨-61530854297565574262539181400302420254123317925727130816,8319258031234588900500480267319424799658944342358762834⟩
def resval6Tail56 : Box := ⟨-64501634715615320320376749954004386270384200805066432560,7574602113851756178931062695120231136932313459633325738⟩
def resval6Tail60 : Box := ⟨-67615847829226438853906969147733894149058373270766979053,6757460134020010237034890564725846773999818762603370213⟩
def resval6Tail64 : Box := ⟨-70880418729674204463326623170978208882880738457094765064,5863168066594839034283750591285197789283697629830481432⟩
def resval6Tail68 : Box := ⟨-74302531970385050122289002453119551564238172637936970103,4886796081952526227167051558346929516937763102342864192⟩
def resval6Tail72 : Box := ⟨771537844986865530099096253466817270295635127275389246451,845860476018987313433778548056114405816953621071165236⟩
def resval6Tail76 : Box := ⟨-458426158653614957975991219210687575141902783008465862,172634289713505541919434275554623103605544686829875203⟩
def resval6Tail80 : Box := ⟨-480533880498339539776599324354998750825009017350633358,170613077736422878118365809880269725802935573336083731⟩
def resval6Tail84 : Box := ⟨-503734607666387058485314496872035193229253684337560472,168164416082456460678926435543204765468529136911682002⟩
def resval6Tail88 : Box := ⟨-528055493917541164523215103958823400458905536696377597,165256965383888102263695759762153225173721889542920244⟩
def resval6Tail92 : Box := ⟨-553550620531373701688537852140160659105014078431218449,161857720949933788799348265978506544482544132375167844⟩
def resval6Tail96 : Box := ⟨-580276681182525068657183794700594148126442636689812189,157931738693164346080361398643672172799492346126710677⟩
def resval6Tail100 : Box := ⟨-608293106782131130479680293274963954774350353635151500,153442030450121719361269236404289345492138293077264268⟩
def resval6Tail104 : Box := ⟨-637662197634076303275791843482423634395398209990365793,148349453915426004735248888012971016202570139542666051⟩
def resval6Tail108 : Box := ⟨-668449261972574138802943656463074429674736789414493559,142612596899251549210243543970003989578004447109349837⟩
def resval6Tail112 : Box := ⟨-700722761188503311282133845009330762622603271030516024,136187655622528264471759475614300075235368034410652148⟩
def resval6Tail116 : Box := ⟨-734554462067438158434215475265035940807789161626450334,129028306750080273048162622239292312949812579744717423⟩
def resval6Tail120 : Box := ⟨-770019596377906441007493479447092769937103504621352743,121085572847059992010784179809760037554104629858345854⟩
def resval6Tail124 : Box := ⟨-807197028164751745671091423460868444961921509733979890,112307680928452412543532809438836857445852731875880538⟩
def resval6Tail128 : Box := ⟨-846169429119611903790937527397025582433874519718613167,102639913755076102250090070993447756622861087917799763⟩
def resval6Tail132 : Box := ⟨-887023462418498155589333663873184905234568487746168682,92024453512355848159698292036634397624739643499952029⟩
def resval6Tail136 : Box := ⟨-929849975447040896512249596918119415548888839849627325,80400217489268615407554855453677691215800856415969902⟩
def resval6Tail140 : Box := ⟨-974744301889298681134427722083741809424404865987987495,67702679430777256439255921116360987573343279596963165⟩
def resval6Tail144 : Box := ⟨-1079193771122664137620818795422482858898800207106605265,51627873416952102160089216019220158346328734461574773⟩
def resval6Tail148 : Box := ⟨209356848163078019616165560495251533311953423789,67492207550079687949563187963309621939930825254⟩
def resval6Tail152 : Box := ⟨219407989019405752904921750488692159749052860165,66207794782591248344623362134879194517524794001⟩
def resval6Tail156 : Box := ⟨230001258149031776720774423229968114259025832142,64717105550617679679432497549110004131943584752⟩
def resval6Tail160 : Box := ⟨241105983438792455215454530756092635765265025843,63005060506241291668295902829535893050470381414⟩
def resval6Tail164 : Box := ⟨252746857638436133710433905795671031107385955703,61056211462729984337717372473049249730991865398⟩
def resval6Tail168 : Box := ⟨264949766633729936824436321568945268567507184906,58854212662430295364210601458519044230561011507⟩
def resval6Tail172 : Box := ⟨277741846111057767431635746293341072700692375946,56381772591429096260113938346758254641539319720⟩
def resval6Tail176 : Box := ⟨291151541898953956616687234110176535734056626338,53620603327640157956584681205647221659836774824⟩
def resval6Tail180 : Box := ⟨305208673223272763420119946730920075859498110784,50551367284342438510205309504844560920235873691⟩
def resval6Tail184 : Box := ⟨319944499016390654935229715697342278503083331209,47153621218345059657799757453617947841009253986⟩
def resval6Tail188 : Box := ⟨335391787427893143639248461328645351797738535908,43405757365482433089528390506654535629434673568⟩
def resval6Tail192 : Box := ⟨351584888691317536210340586328584308388715855850,39284941559347511003086803396504573158447552590⟩
def resval6Tail196 : Box := ⟨368559811508985833326704412711968066083621054881,34767048182042229227402091579740403544567416941⟩
def resval6Tail200 : Box := ⟨386354303124785219721682247240150796207421403274,29826591788245632053141271073086235564930685906⟩
def resval6Tail204 : Box := ⟨405007933262954531185026231113167559744763941042,24436655236054854796710767412455018283688720448⟩
def resval6Tail208 : Box := ⟨424562182119547618974030254898279545300246725714,18568814149822820240241888699363893287138458136⟩
def resval6Tail212 : Box := ⟨445060532644092473907077767749273165270964572857,12193057528617772760199936456737738243372716644⟩
def resval6Tail216 : Box := ⟨466550522414409830782426177280582528812124889495,5277592861511141813369268649060726989644252281⟩
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
def polyval6Tail5 : Box := ⟨12022390997433985052290463911300398647022575426191785297425,3699917276982343605513725697285497030760535197066371234081⟩
def polyval6Tail9 : Box := ⟨12602843844709868567176200248128072615879351146001941365131,3620532715649065882693561831713039728809298484245172671221⟩
def polyval6Tail13 : Box := ⟨13211323641094714901717725186450342326911318724952022120485,3529092260043400954238579165291860521347185124724875894805⟩
def polyval6Tail17 : Box := ⟨13849181542102706662802670400793411518608730271691331541640,3424751754303833616262981554330423931541701495111799103778⟩
def polyval6Tail21 : Box := ⟨14517835956233319621956411428999879696506248451292650530710,3306617945680703224413533550929213226017961450585634938457⟩
def polyval6Tail25 : Box := ⟨15218773774562017558272786064111230789429076227288146361444,3173745835754575487694254551865407414636146540056788349886⟩
def polyval6Tail29 : Box := ⟨15953553676975736877941198193999914360032703874153765373456,3025135907424646594192083154054138545212176252167162485605⟩
def polyval6Tail33 : Box := ⟨16723809598219143595469225863712152545921151111989996074691,2859731209261750942403707577579655233872173513546290657401⟩
def polyval6Tail37 : Box := ⟨17531254361285721964798645579480191245175629834029466953384,2676414290057905508047593818275783502576911647749332814403⟩
def polyval6Tail41 : Box := ⟨18377683486233164394602331390766076336126116284183707209965,2474003976051832871082478279376173234692684967134297177689⟩
def polyval6Tail45 : Box := ⟨19264979182892749278305838852632868378242058339671098383829,2251251982937632147746450017878806790238521379258156018427⟩
def polyval6Tail49 : Box := ⟨20195114536351319985571838369333608739105837842540910035161,2006839354373225275243480372633373694866202740146378878200⟩
def polyval6Tail53 : Box := ⟨21170157894513147926108247548069975238668082840059846740099,1739372718295506770088089571055646370846704902302137805296⟩
def polyval6Tail57 : Box := ⟨22192277467498328958586714888592299290313491568761307875621,1447380351919333670663452451433820346719248458888951924109⟩
def polyval6Tail61 : Box := ⟨23263746149105433041414815274104965530786920539663689259090,1129308045846628111741165938959102616802624502722317146708⟩
def polyval6Tail65 : Box := ⟨24386946571068227027341152927101624177615659175097184272984,783514757238297928954143932700577335764460606033029326750⟩
def polyval6Tail69 : Box := ⟨25564376471993556764782236066414248723465065563881484851932,408268037531079279580460888479238089067539907414951968469⟩
def polyval6Tail73 : Box := ⟨26843750000000000000000000000000000000000000000000000000000,2⟩
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
def resval7 : Box := ⟨56832153349312227979949844815211382701392152316299608229,21678161229943883389483661643926764691320515389377059554⟩
def polyval7 : Box := ⟨23963119111204908508592020727751126298278927383021336243530,6585855158789114480006065246172764471851404595314395149504⟩
theorem cell7_lo : Holds Q cell7 (127/128:ℝ) := by norm_num [Holds,Q,cell7]
theorem cell7_hi : Holds Q cell7 (1/1:ℝ) := by norm_num [Holds,Q,cell7]
def resval7Tail4 : Box := ⟨-54765657231076383862459775011297584633288162071569249863,20631275845142192028915673328305274602359748372334577208⟩
def resval7Tail8 : Box := ⟨-55629846298818103734187065261512644357384001026081482302,19767138746413674553179171112087284185266813202991624003⟩
def resval7Tail12 : Box := ⟨-56507617866289594230398266597643552312640331903144450136,18889367184759549414429473092953753240266154740281044555⟩
def resval7Tail16 : Box := ⟨-57399239599379390008336672951207625791854981000185875120,17997745451674627036799340296850520534225833042116664867⟩
def resval7Tail20 : Box := ⟨-58304930042930627260535920405786068890892313369713593347,17092055008123407531030786230561166259088075431643082050⟩
def resval7Tail24 : Box := ⟨-59224911184150755269415977032097340286238442173607397338,16172073866903279736258808047102419716006278215697351277⟩
def resval7Tail28 : Box := ⟨-60159408512931308902653445234093628089780627999862319081,15237576538122726110117211375433106782352748981154916506⟩
def resval7Tail32 : Box := ⟨-61108651077121041005970352560474123441723589391749056608,14288333973932994007327043264357205863156286698354889496⟩
def resval7Tail36 : Box := ⟨-62072871538666193647044898106164667025315723102797695702,13324113512387841366291554745827823483503541021518329880⟩
def resval7Tail40 : Box := ⟨-63052306230636577077227004412682683211285632878178315101,12344678820417457936010798693135556036029993237281630903⟩
def resval7Tail44 : Box := ⟨-64047195215151450916234532185863339440903360021436977381,11349789835902584096443181164921197094577045514254244613⟩
def resval7Tail48 : Box := ⟨-65057782342219405537620463912014229511336085300320101135,10339202708834629469326900374187992598302477073776896821⟩
def resval7Tail52 : Box := ⟨-66084315309506665370859639017308066157351064292889228839,9312669741547369490104601812988148630336300730209389348⟩
def resval7Tail56 : Box := ⟨-67127045723048454243326972166925029183086119460648677851,8269939328005569560437069354799917993800721118192343220⟩
def resval7Tail60 : Box := ⟨-68186229158915541842602397430254396289421454042415476815,7210755892135426342720231641707556049792678509696589739⟩
def resval7Tail64 : Box := ⟨-69262125221649304233536400030107124768686291862847333915,6134859824917663636915991470214493179844690225574351290⟩
def resval7Tail68 : Box := ⟨-70354923275434156920867720634391475652311067766932667343,5041983935497104750778698716833270440010465062300409954⟩
def resval7Tail72 : Box := ⟨771322587134380470555264051488649686756263447811006372065,954545521879904092044869076306852593674383468326622652⟩
def resval7Tail76 : Box := ⟨-720993578362969524159051375933510985326394762021805152,273756856707049516510737012925920214772849009194638607⟩
def resval7Tail80 : Box := ⟨-732345168388466862493224539992154023153491582143305780,262380662486394048070164070777055442243245015658784844⟩
def resval7Tail84 : Box := ⟨-743900686428322754346151019380972824103939292908557092,250825143198261488329815736476645970017519097810193724⟩
def resval7Tail88 : Box := ⟨-755638537788618991050185394871866116546820454534486733,239087291837302201042848813420067106095232048290920737⟩
def resval7Tail92 : Box := ⟨-767561598219919049104665471748120986405813319212336028,227164231406000427356643398612484799461140876029485254⟩
def resval7Tail96 : Box := ⟨-779672790096269202831298152630130047975626334290927337,215053039529650257797701085685733918474476566241199857⟩
def resval7Tail100 : Box := ⟨-791975081903889960651960376236269302394627909566871313,202750747722029499545403775038054898019712595389427423⟩
def resval7Tail104 : Box := ⟨-804471488968118770412171877383316273520368466190793055,190254340657800689755062458580397317191871005660035910⟩
def resval7Tail108 : Box := ⟨-817165074192472899013547979259284743807313053528572721,177560755433446561149201217460716562764652274233785207⟩
def resval7Tail112 : Box := ⟨-830058948809375440139832831009730837220057423719198268,164666880816544020022360262418203994770037616983614750⟩
def resval7Tail116 : Box := ⟨-843156273142726882139429068054736956112020253104189282,151569556483192578026607678523884309364550061500372947⟩
def resval7Tail120 : Box := ⟨-856460257382509131486438319550443666378410583442718365,138265572243410328722872065837330291563836717844660298⟩
def resval7Tail124 : Box := ⟨-869974162371611849955963903016980665508728567133966534,124751667254307611198870582735767599309391741715963213⟩
def resval7Tail128 : Box := ⟨-883701300405074016447994395079228556924198958056940102,111024529220845500603851346658206132423253256790564938⟩
def resval7Tail132 : Box := ⟨-897645036041948812161276794853369191291168185114153066,97080793583982055414629089055998963198983253072186528⟩
def resval7Tail136 : Box := ⟨-911808786941675638740406893303512813500601882516873867,82917042695133122011858273163791022966703525868655510⟩
def resval7Tail140 : Box := ⟨-926196124045064197692274354408178108421751049301380252,68529799103497622306749383037708598952714309692708099⟩
def resval7Tail144 : Box := ⟨-997755987314008646630926907258835625018050267305188482,51699215399305655626749799060886290132139449729885995⟩
def resval7Tail148 : Box := ⟨363287812081545835773070021924228627535268191141,116090349876549252206281123598792107111941312983⟩
def resval7Tail152 : Box := ⟨368964983942954046422898232606259045832834004779,110358480729754948221150959059223166879415153772⟩
def resval7Tail156 : Box := ⟨374786803359260131951916563588770043760737917316,104536660401668965175856406587626969178816605169⟩
def resval7Tail160 : Box := ⟨380700484943288252849883936124696256689928212308,98622978817368381679966409182251889499777795501⟩
def resval7Tail164 : Box := ⟨386707477256687356807741962217435186244606480945,92615986503968830206909960132227076434428233337⟩
def resval7Tail168 : Box := ⟨392809252629421886124869306464919955580737377088,86514211131234298106449664514090004691724699701⟩
def resval7Tail172 : Box := ⟨399007306623308075093219262548215282006193823463,80316157137348109084936937026458176901593291836⟩
def resval7Tail176 : Box := ⟨405303158398315703872866030461518558660091518977,74020305362340480302594181987079842967281620259⟩
def resval7Tail180 : Box := ⟨411698351084917935680808994799216147177643234813,67625112675738248494336650353283492472820357089⟩
def resval7Tail184 : Box := ⟨418194452162316809825526472599758671518939552649,61129011598339374349559209804537119479588220914⟩
def resval7Tail188 : Box := ⟨424793053842636677146368698613284208900774467095,54530409918019507028758555555656939490611980382⟩
def resval7Tail192 : Box := ⟨431495773461179742332954072663957877320877936440,47827690299476441842689352562029180048224863909⟩
def resval7Tail196 : Box := ⟨438304253872839365792850496353813409112368233880,41019209887816818390732741088485553675641021389⟩
def resval7Tail200 : Box := ⟨445220163854768287339807534436281430511527987999,34103299905887897136318335151676545556149316578⟩
def resval7Tail204 : Box := ⟨452245198515400501749813213974932471335520371961,27078265245255715358549238653599885050398454130⟩
def resval7Tail208 : Box := ⟨459381079709942641634187429116563468457531775385,19942384050727985674175607771945874537110304031⟩
def resval7Tail212 : Box := ⟨466629556503993149884562046534956473169350976578,12693907295380251211158407279156892422108316347⟩
def resval7Tail216 : Box := ⟨473994346121723105821121972159717636420388938581,5330947865820629931950084365676450069941769587⟩
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
def polyval7Tail5 : Box := ⟨20536824360732965058124871746324540002767908186268744062634,6263903601306947199301615645142876869328765187539551788976⟩
def polyval7Tail9 : Box := ⟨20860868607726335776039959549040138612325851891361136481875,5939857418511381898933970768883944017363936846558987008899⟩
def polyval7Tail13 : Box := ⟨21190027834641498078638639103248128591385545243629663311463,5610698191419822926373923660611774535788505499515720726365⟩
def polyval7Tail17 : Box := ⟨21524380795453529318823168352380100298430198431895312813699,5276345230607661337278795715214718076738662800436558952227⟩
def polyval7Tail21 : Box := ⟨21864009440812977385096101369616619075832920967711179608328,4936716585248212843564499027982864558800460179739274761796⟩
def polyval7Tail25 : Box := ⟨22208997014628711963367695403698085966462694654799673712129,4591729011432478260561696837130555317852858377434141390659⟩
def polyval7Tail29 : Box := ⟨22559428074297736659041400128146447022166168015443961463429,4241297951763453564739106817440661932343687280753852995414⟩
def polyval7Tail33 : Box := ⟨22915388511430312179604909283060202090366870938252875606402,3885337514630878044163980203487289066632853303916982123254⟩
def polyval7Tail37 : Box := ⟨23276965572902224308065410552931840916487643923726645782926,3523760453158965915701628265862130456910299617644325439488⟩
def polyval7Tail41 : Box := ⟨23644247882239231551889946232362758697187292616492740782971,3156478143821958671876946042080663426908692854561635162546⟩
def polyval7Tail45 : Box := ⟨24017325461338933465788254674841400829058458085811462655056,2783400564722256757980944333120311166263387724527333235668⟩
def polyval7Tail49 : Box := ⟨24396289752535383733838164626692646410923968868117822832047,2404436273525806489957164878647840831527137237942328993267⟩
def polyval7Tail53 : Box := ⟨24781233641011856108358855920688791376412602570179360207778,2019492385049334116032291334357005519344685097482349323311⟩
def polyval7Tail57 : Box := ⟨25172251477567256673735923841759487081480176859512009715943,1628474548493933587485794549156003672541968569104324097087⟩
def polyval7Tail61 : Box := ⟨25569439101741770906341949343899219018831127212652662482797,1231286924319427145763725869812287260261536295989284172080⟩
def polyval7Tail65 : Box := ⟨25972893865315659761081499939292541898199312937952613272026,827832160753231676892607639533451100571318100715401079012⟩
def polyval7Tail69 : Box := ⟨26382714726321373355416719838758001278719191674724152203232,418011365988472264342072769689851450669845482897419783226⟩
def polyval7Tail73 : Box := ⟨26843750000000000000000000000000000000000000000000000000000,2⟩
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
def pend : Box := ⟨1030544300185091483196549776607090155199530926788820932629318,4674084902539792048309366833735570599405189514798763789⟩
def zend : Box := ⟨1003740663686690658125234375000000000000000000000000000000000,2994093409493792031250000000000000000000000000000000002⟩
def betaquot : Box := ⟨428747628033312066139229876322468119935622391386603879619930,394765987308831276722650702003059379637061891879367041⟩
def crit : Box := ⟨112571846161021294145006104200576184906240459852289398468,11918275172927883351564961950280472433626332192329511886⟩
def subsonic : Box := ⟨546531175008638201479381751485314565865308462161052006645,6371747131690357861707609842354929401068081104680356616⟩
def pendTail4 : Box := ⟨26799139906146207920207179579070059010410811704642341393399,1552250364006124891191570516398492531229901127768909145⟩
def pendTail8 : Box := ⟨26799173926100606437392762841327243927366855232650848382937,1552098569313363444611612694339836854583979978149721196⟩
def pendTail12 : Box := ⟨26799173927508468021405552910216598809663293722780197739986,1552098552070450114191793633075293161719840632404729148⟩
def pendTail16 : Box := ⟨26799173927509131969884389335999083664067759097605399383308,1552098552056758003009712648999418826475837681470545735⟩
def pendTail20 : Box := ⟨26799173927509133501984912040542809982480627401411949847649,1552098552056709537744443451967199803736961424156618099⟩
def pendTail24 : Box := ⟨26799173927509133514533355382895977944181229997427341956024,1552098552056708935832778452128787268985345223907987985⟩
def pendTail28 : Box := ⟨26799173927509133514833731046137114638550137508580847690515,1552098552056708913276495691987777385087087077852391070⟩
def pendTail32 : Box := ⟨26799173927509133514851752502502289344835824801748963600420,1552098552056708910948655291512964427347860924584093851⟩
def pendTail36 : Box := ⟨26799173927509133514853920194149417296565894254330464979633,1552098552056708910320705437119314236163262963778522015⟩
def pendTail40 : Box := ⟨26799173927509133514853946060795624561054492044836188204501,1552098552056708909888415870142697066637112179897483106⟩
def pendTail44 : Box := ⟨26799173927509133514851915547113316457226419497738124108527,1552098552056708909129533737852373397010544300401314150⟩
def pendTail48 : Box := ⟨26799173927509133514834856033928588349717840892929683095884,1552098552056708905657151134412549235654721965759258702⟩
def pendTail52 : Box := ⟨26799173927509133514540978378753843061561239646489422238838,1552098552056708862188144324346811315853663143616077128⟩
def pendTail56 : Box := ⟨26799173927509133501093628225968413202302170586387387661144,1552098552056707240934637007102413923002893904241721769⟩
def pendTail60 : Box := ⟨26799173927509131512508134851524903669413040913611697727839,1552098552056512277151981778496173176278977994649380506⟩
def pendTail64 : Box := ⟨26799173927507879672215014977007487902685430404536506160484,1552098551963322444435256257928285397086035569611702655⟩
def pendTail68 : Box := ⟨26799173921911689420306141453630697202778769645223682032403,1552098234691562805379424267138285798729227215751868901⟩
def pendTail72 : Box := ⟨26798439628388019632960873287192465308627236329005179511510,1522306723344030878824340782162002655418129108976786057⟩
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
end SepticProfile.ExteriorCertificates.C13

end
end

end OAI
