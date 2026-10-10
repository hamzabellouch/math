import OAI.Analysis.PlanarPacking.Certificate.TableDensityValues
import OAI.Analysis.PlanarPacking.Certificate.HighHeaders7

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace hm7_0_0_14
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density0 j i k).mul (hk7_0_14 j i k))
noncomputable def s0_0 : CBox := ⟨⟨68525864329348,68525864329364⟩,⟨148051229590634,148051229590650⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨181712868716811,181712868716828⟩,⟨323489710208656,323489710208672⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨218404318694309,218404318694327⟩,⟨278314587829778,278314587829794⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨164432378982593,164432378982609⟩,⟨133873802878452,133873802878470⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨79075855299788,79075855299807⟩,⟨33714426414766,33714426414785⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨23714888583505,23714888583523⟩,⟨1826377192903,1826377192921⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨4229425183685,4229425183704⟩,⟨(-1230638780956),(-1230638780938)⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨412954528030,412954528049⟩,⟨(-324086533134),(-324086533117)⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨18600934397,18600934415⟩,⟨(-32996519904),(-32996519888)⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨187946700,187946721⟩,⟨(-1498302570),(-1498302550)⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨(-7057612),(-7057596)⟩,⟨(-28052488),(-28052467)⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨(-118179),(-118160)⟩,⟨(-177702),(-177684)⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨(-332),(-313)⟩,⟨(-274),(-257)⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),0⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),0⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),0⟩⟩
lemma c0_15 : chunk 0 15 = s0_15 := by decide +kernel
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
lemma s0_eq (i : Fin 16) : chunk 0 i = s0 i := by
  fin_cases i
  · exact c0_0
  · exact c0_1
  · exact c0_2
  · exact c0_3
  · exact c0_4
  · exact c0_5
  · exact c0_6
  · exact c0_7
  · exact c0_8
  · exact c0_9
  · exact c0_10
  · exact c0_11
  · exact c0_12
  · exact c0_13
  · exact c0_14
  · exact c0_15
noncomputable def s1_0 : CBox := ⟨⟨963718899892866325,963718899892867941⟩,⟨(-2150001936585211847),(-2150001936585210231)⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨2086920592816334285,2086920592816339674⟩,⟨(-5749731517967631151),(-5749731517967625762)⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨1550334773843739416,1550334773843750029⟩,⟨(-7477129143974698254),(-7477129143974687642)⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨(-31783153458885188),(-31783153458868297)⟩,⟨(-6946825906474113748),(-6946825906474096858)⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨(-1355496436084065708),(-1355496436084044598)⟩,⟨(-4867796905031102295),(-4867796905031081189)⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨(-1696084540093045212),(-1696084540093025973)⟩,⟨(-2547472089164145164),(-2547472089164125926)⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨(-1280606266561285837),(-1280606266561268635)⟩,⟨(-933818972516065713),(-933818972516048509)⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨(-695189721197710685),(-695189721197699317)⟩,⟨(-179442588837038736),(-179442588837027372)⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨(-288534061762351815),(-288534061762347031)⟩,⟨38961610562629767,38961610562634550⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨(-94379594656907199),(-94379594656905865)⟩,⟨53478217344984990,53478217344986326⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨(-24484759466261397),(-24484759466261111)⟩,⟨29439591373405317,29439591373405607⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨(-4740139966849546),(-4740139966849464)⟩,⟨12392130813764484,12392130813764567⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨(-386131760000806),(-386131760000777)⟩,⟨4664353013966194,4664353013966226⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨244149703018714,244149703018734⟩,⟨1703678166797982,1703678166798003⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨187879522235148,187879522235165⟩,⟨609928427997965,609928427997982⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨61086525444438,61086525444454⟩,⟨153358334659455,153358334659472⟩⟩
lemma c1_15 : chunk 1 15 = s1_15 := by decide +kernel
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
lemma s1_eq (i : Fin 16) : chunk 1 i = s1 i := by
  fin_cases i
  · exact c1_0
  · exact c1_1
  · exact c1_2
  · exact c1_3
  · exact c1_4
  · exact c1_5
  · exact c1_6
  · exact c1_7
  · exact c1_8
  · exact c1_9
  · exact c1_10
  · exact c1_11
  · exact c1_12
  · exact c1_13
  · exact c1_14
  · exact c1_15
noncomputable def s2_0 : CBox := ⟨⟨(-497197897025767290363),(-497197897025767290186)⟩,⟨715611941790952367,715611941790952469⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨(-1348384645968972517652),(-1348384645968972517187)⟩,⟨112943783465822128348,112943783465822128621⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨(-1804294487406402047584),(-1804294487406402046912)⟩,⟨450052311705844445164,450052311705844445616⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨(-1742441439378302976085),(-1742441439378302975335)⟩,⟨899871210077485251048,899871210077485251643⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨(-1253332987938304454173),(-1253332987938304453488)⟩,⟨1213182738679356337337,1213182738679356337978⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨(-607265492418832920782),(-607265492418832920249)⟩,⟨1218377030005597612182,1218377030005597612767⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨(-85075256273230631707),(-85075256273230631351)⟩,⟨950141433997079410299,950141433997079410749⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨183472839746120430226,183472839746120430496⟩,⟨583403124643784789023,583403124643784789371⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨237084783568345523513,237084783568345523990⟩,⟨278037678988227299114,278037678988227299614⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨184842615317363775460,184842615317363776860⟩,⟨93962513804780471796,93962513804780473198⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨113361539645692462449,113361539645692466289⟩,⟨11095044060100706638,11095044060100710475⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨59840452215421156106,59840452215421163501⟩,⟨(-14548331868212984191),(-14548331868212976802)⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨28630633012937363321,28630633012937375128⟩,⟨(-16530229673126864012),(-16530229673126852209)⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨12798295845374177661,12798295845374193210⟩,⟨(-11831851590982680271),(-11831851590982664726)⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨5247904258937771354,5247904258937784468⟩,⟨(-6591286749220902133),(-6591286749220889020)⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨1406638586214598561,1406638586214603627⟩,⟨(-2077359071714090507),(-2077359071714085440)⟩⟩
lemma c2_15 : chunk 2 15 = s2_15 := by decide +kernel
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
lemma s2_eq (i : Fin 16) : chunk 2 i = s2 i := by
  fin_cases i
  · exact c2_0
  · exact c2_1
  · exact c2_2
  · exact c2_3
  · exact c2_4
  · exact c2_5
  · exact c2_6
  · exact c2_7
  · exact c2_8
  · exact c2_9
  · exact c2_10
  · exact c2_11
  · exact c2_12
  · exact c2_13
  · exact c2_14
  · exact c2_15
noncomputable def s3_0 : CBox := ⟨⟨10512346270241733381538,10512346270241767839372⟩,⟨12146647057953433646196,12146647057953468102821⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨31885402530105271543834,31885402530105345670838⟩,⟨31571665728912448705917,31571665728912522828729⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨52386660566613061923773,52386660566613123405395⟩,⟨38207915705606319701613,38207915705606381175022⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨67231141985701979448788,67231141985702007572098⟩,⟨29459373061796858839034,29459373061796886949859⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨70668515613450107407104,70668515613450116514267⟩,⟨9751078303205854116035,9751078303205863211761⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨60816706318684180509178,60816706318684182786114⟩,⟨(-11574325222610530163581),(-11574325222610527892240)⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨41907750696120529438614,41907750696120529814069⟩,⟨(-25738776530060314470172),(-25738776530060314094931)⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨21609471733086729641896,21609471733086729698220⟩,⟨(-29349054995785250874582),(-29349054995785250815102)⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨6155731457115813331761,6155731457115813345781⟩,⟨(-24818643605123033886168),(-24818643605123033867949)⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨(-2375354354729446715380),(-2375354354729446707508)⟩,⟨(-17023930793484415627627),(-17023930793484415617471)⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨(-5321731629543607738840),(-5321731629543607733431)⟩,⟨(-9831390705112525060616),(-9831390705112525054628)⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨(-5162895553388769632699),(-5162895553388769629256)⟩,⟨(-4848837449740160988359),(-4848837449740160985108)⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨(-3874787730362957110960),(-3874787730362957108918)⟩,⟨(-2024405235453118642892),(-2024405235453118641247)⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨(-2490284396186081979526),(-2490284396186081978385)⟩,⟨(-680780361292221279560),(-680780361292221278785)⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨(-1343405781155644627324),(-1343405781155644626758)⟩,⟨(-160139848628700047152),(-160139848628700046813)⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨(-419835986395334320876),(-419835986395334320695)⟩,⟨(-18035992237434695618),(-18035992237434695515)⟩⟩
lemma c3_15 : chunk 3 15 = s3_15 := by decide +kernel
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
lemma s3_eq (i : Fin 16) : chunk 3 i = s3 i := by
  fin_cases i
  · exact c3_0
  · exact c3_1
  · exact c3_2
  · exact c3_3
  · exact c3_4
  · exact c3_5
  · exact c3_6
  · exact c3_7
  · exact c3_8
  · exact c3_9
  · exact c3_10
  · exact c3_11
  · exact c3_12
  · exact c3_13
  · exact c3_14
  · exact c3_15
noncomputable def s4_0 : CBox := ⟨⟨187978342108048036886342,187978342108050393720909⟩,⟨(-127805602111241686742182),(-127805602111239329898104)⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨490737578338145761868487,490737578338154377085261⟩,⟨(-405260432989987312000240),(-405260432989978696764233)⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨594817966622099879098531,594817966622119980958747⟩,⟨(-711182882494895543669379),(-711182882494875441803000)⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨445061786410065712423966,445061786410106750796264⟩,⟨(-974413683776298100158581),(-974413683776257061817737)⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨96554748903783205294115,96554748903854276584165⟩,⟨(-1078895116617232356136573),(-1078895116617161284928225)⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨(-298346113542464172152659),(-298346113542367380616408)⟩,⟨(-953107082567595760035248),(-953107082567498968620823)⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨(-572657797754995064983863),(-572657797754854043327957)⟩,⟨(-637698468848025249471249),(-637698468847884227900299)⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨(-641632439438364392733382),(-641632439438205739576449)⟩,⟨(-264393947375474926658533),(-264393947375316273526701)⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨(-535285243093600491136743),(-535285243093479824985661)⟩,⟨33180274336847829000030,33180274336968495169492⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨(-350094499634463235172886),(-350094499634400375574196)⟩,⟨192908992220838720030664,192908992220901579670167⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨(-175968523206138288164213),(-175968523206112863570436)⟩,⟨230217078967779555305528,230217078967804979937886⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨(-57111116332702287389307),(-57111116332690571103894)⟩,⟨196949913438621889246648,196949913438633605549518⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨3903681327835352756014,3903681327839887898409⟩,⟨140569483297812192781653,140569483297816727928877⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨23847790367369347964610,23847790367370960502836⟩,⟨87596287310605042758114,87596287310606655295682⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨20962648405090077250695,20962648405090629095449⟩,⟨46164941940824542781751,46164941940825094624707⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨7900129763439481656584,7900129763439615857073⟩,⟨14227587025536236162790,14227587025536370362470⟩⟩
lemma c4_15 : chunk 4 15 = s4_15 := by decide +kernel
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
lemma s4_eq (i : Fin 16) : chunk 4 i = s4 i := by
  fin_cases i
  · exact c4_0
  · exact c4_1
  · exact c4_2
  · exact c4_3
  · exact c4_4
  · exact c4_5
  · exact c4_6
  · exact c4_7
  · exact c4_8
  · exact c4_9
  · exact c4_10
  · exact c4_11
  · exact c4_12
  · exact c4_13
  · exact c4_14
  · exact c4_15
noncomputable def s5_0 : CBox := ⟨⟨(-23549640237259380926339),(-23549640237259380655216)⟩,⟨(-781376662657994314394923),(-781376662657994314006788)⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨(-329595482515168456723954),(-329595482515168455843080)⟩,⟨(-2195845823881292257697173),(-2195845823881292256512480)⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨(-1240639668443321531400730),(-1240639668443321529757314)⟩,⟨(-3118591976146857577135683),(-3118591976146857575135920)⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨(-2659680501666694650251741),(-2659680501666694647737503)⟩,⟨(-3182278970948291916098939),(-3182278970948291913323199)⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨(-4020114544190935967447892),(-4020114544190935964138837)⟩,⟨(-2210497297057043087243439),(-2210497297057043083856957)⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨(-4612368037051269517090506),(-4612368037051269513251870)⟩,⟨(-460603414141365583014752),(-460603414141365579270912)⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨(-4078332359162062697549650),(-4078332359162062693401725)⟩,⟨1395493330042757888028363,1395493330042757891984637⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨(-2659735714733985591019523),(-2659735714733985585037805)⟩,⟨2639901575835783094812777,2639901575835783100638761⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨(-995032156761097199604883),(-995032156761097176675578)⟩,⟨2940303789257282613229459,2940303789257282636118586⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨318138366209875282994979,318138366209875402019412⟩,⟨2466244578470551167816669,2466244578470551286839377⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨1019041597573688233784215,1019041597573688706999020⟩,⟨1652699359136036994207944,1652699359136037467410159⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨1177420480714643727144593,1177420480714644966055319⟩,⟨887533813770190719875584,887533813770191958753245⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨1010619156274617779650441,1010619156274620388029055⟩,⟨359000686376187051627048,359000686376189659971021⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨718108249716179961509014,718108249716184222121901⟩,⟨80343472380552519811945,80343472380556780404349⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨414059473035198249931956,414059473035202441153036⟩,⟨(-17580564290514740770661),(-17580564290510549559050)⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨133740162477118392362215,133740162477120145035355⟩,⟨(-16087620561791905228015),(-16087620561790152557470)⟩⟩
lemma c5_15 : chunk 5 15 = s5_15 := by decide +kernel
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
lemma s5_eq (i : Fin 16) : chunk 5 i = s5 i := by
  fin_cases i
  · exact c5_0
  · exact c5_1
  · exact c5_2
  · exact c5_3
  · exact c5_4
  · exact c5_5
  · exact c5_6
  · exact c5_7
  · exact c5_8
  · exact c5_9
  · exact c5_10
  · exact c5_11
  · exact c5_12
  · exact c5_13
  · exact c5_14
  · exact c5_15
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma sums_eq (j : Fin 6) (i : Fin 16) : chunk j i = sums j i := by
  fin_cases j
  · exact s0_eq i
  · exact s1_eq i
  · exact s2_eq i
  · exact s3_eq i
  · exact s4_eq i
  · exact s5_eq i
noncomputable def ans : CBox := ⟨⟨(-2708596403959845941658737),(-2708596403959715599984897)⟩,⟨(-628581088335973677312764),(-628581088335843335590435)⟩⟩
lemma checked : cachedMomentRuleBox density0 hk7_0_14 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule false false 7 14) := by
  rw [← checked]
  exact @cached_density_rule_contains density0 hk7_0_14 (tableDensity false) (fullFactor false 7 14) density0_contains hk7_0_14_contains
noncomputable def atomAnswer : CBox := ⟨⟨(-3092268153396314434257635),(-3092268153396314433760501)⟩,⟨(-219635173470286306953079),(-219635173470286306573096)⟩⟩
lemma atomChecked : tableAtomBox false ha7_0_14 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom false false 7 14) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains false false ha7_0_14 7 14 ha7_0_14_contains
 def realAnswer : RBox := ⟨(-5800864557356160475916372),(-5800864557356029933745398)⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment false false 7 14) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm7_0_0_14
namespace hm7_1_0_14
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density1 j i k).mul (hk7_0_14 j i k))
noncomputable def s0_0 : CBox := ⟨⟨8276488998626,8276488998642⟩,⟨26642779358640,26642779358656⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨23163119984460,23163119984476⟩,⟨59371696300755,59371696300771⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨29756811720738,29756811720754⟩,⟨53133220163320,53133220163337⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨23677096765966,23677096765983⟩,⟨27270571981701,27270571981717⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨11872765405720,11872765405736⟩,⟨7814888779478,7814888779495⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨3673913503451,3673913503467⟩,⟨878573800074,878573800090⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨669146723807,669146723824⟩,⟨(-120728857492),(-120728857476)⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨65660435768,65660435784⟩,⟨(-47800237736),(-47800237717)⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨2848577932,2848577949⟩,⟨(-5341083139),(-5341083122)⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨16463221,16463237⟩,⟨(-252306359),(-252306343)⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨(-1586704),(-1586688)⟩,⟨(-4801478),(-4801462)⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨(-23491),(-23475)⟩,⟨(-30336),(-30320)⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨(-72),(-54)⟩,⟨(-55),(-39)⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),0⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),0⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),0⟩⟩
lemma c0_15 : chunk 0 15 = s0_15 := by decide +kernel
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
lemma s0_eq (i : Fin 16) : chunk 0 i = s0 i := by
  fin_cases i
  · exact c0_0
  · exact c0_1
  · exact c0_2
  · exact c0_3
  · exact c0_4
  · exact c0_5
  · exact c0_6
  · exact c0_7
  · exact c0_8
  · exact c0_9
  · exact c0_10
  · exact c0_11
  · exact c0_12
  · exact c0_13
  · exact c0_14
  · exact c0_15
noncomputable def s1_0 : CBox := ⟨⟨291714393994955958,291714393994957291⟩,⟨(-223486040936506088),(-223486040936504757)⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨696066140347289694,696066140347294135⟩,⟨(-634136152966494026),(-634136152966489586)⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨706732703197376395,706732703197385145⟩,⟨(-905525585549046864),(-905525585549038113)⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨408327519803360448,408327519803374380⟩,⟨(-932203609180827341),(-932203609180813408)⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨65878376951033802,65878376951051233⟩,⟨(-722535438689106340),(-722535438689088911)⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨(-123485422493434035),(-123485422493418138)⟩,⟨(-419273219154142850),(-419273219154126952)⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨(-146932966508837583),(-146932966508823350)⟩,⟨(-175216576676411693),(-175216576676397464)⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨(-95417089440084682),(-95417089440075273)⟩,⟨(-45619756903725772),(-45619756903716364)⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨(-44087630806493381),(-44087630806489423)⟩,⟨(-778397441117596),(-778397441113636)⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨(-15681494520965997),(-15681494520964893)⟩,⟨6589118655524328,6589118655525432⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨(-4436657218531051),(-4436657218530811)⟩,⟨4419996891443614,4419996891443852⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨(-985450108384021),(-985450108383953)⟩,⟨2046822202630707,2046822202630775⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨(-141335906168144),(-141335906168116)⟩,⟨823124714562531,823124714562558⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨13520622887804,13520622887821⟩,⟨316257786903825,316257786903844⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨22209330641102,22209330641118⟩,⟨117438102021523,117438102021540⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨8010567098296,8010567098312⟩,⟨30117520257493,30117520257509⟩⟩
lemma c1_15 : chunk 1 15 = s1_15 := by decide +kernel
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
lemma s1_eq (i : Fin 16) : chunk 1 i = s1 i := by
  fin_cases i
  · exact c1_0
  · exact c1_1
  · exact c1_2
  · exact c1_3
  · exact c1_4
  · exact c1_5
  · exact c1_6
  · exact c1_7
  · exact c1_8
  · exact c1_9
  · exact c1_10
  · exact c1_11
  · exact c1_12
  · exact c1_13
  · exact c1_14
  · exact c1_15
noncomputable def s2_0 : CBox := ⟨⟨(-95686685351981768730),(-95686685351981768660)⟩,⟨(-58688163015095327075),(-58688163015095327010)⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨(-272375046058645726147),(-272375046058645725974)⟩,⟨(-139189709403740007954),(-139189709403740007792)⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨(-397819303533810285121),(-397819303533810284865)⟩,⟨(-132918171238603952649),(-132918171238603952402)⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨(-433504414403794669185),(-433504414403794668882)⟩,⟨(-46609287046681984170),(-46609287046681983877)⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨(-369488176062300288487),(-369488176062300288193)⟩,⟨63566948829634342260,63566948829634342550⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨(-242750605468687766551),(-242750605468687766309)⟩,⟨135657139186169263038,135657139186169263284⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨(-113928578421772717416),(-113928578421772717240)⟩,⟨145103561383244432961,145103561383244433144⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨(-25925127709522006011),(-25925127709522005857)⟩,⟨110279885362987953982,110279885362987954138⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨14161418514759478016,14161418514759478345⟩,⟨64576838236773879421,64576838236773879754⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨22411649237133472814,22411649237133473915⟩,⟨29730506270009570864,29730506270009571965⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨17539982236968478426,17539982236968481533⟩,⟨10360223284631530209,10360223284631533314⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨10668782491788243366,10668782491788249380⟩,⟨2076040771263527747,2076040771263533760⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨5652420494282629677,5652420494282639303⟩,⟨(-546693707832640451),(-546693707832630827)⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨2739359369005012770,2739359369005025461⟩,⟨(-936881418786187231),(-936881418786174541)⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨1195907163319480005,1195907163319490717⟩,⟨(-649365426296208391),(-649365426296197678)⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨332537001090525628,332537001090529768⟩,⟨(-220842549011874784),(-220842549011870641)⟩⟩
lemma c2_15 : chunk 2 15 = s2_15 := by decide +kernel
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
lemma s2_eq (i : Fin 16) : chunk 2 i = s2 i := by
  fin_cases i
  · exact c2_0
  · exact c2_1
  · exact c2_2
  · exact c2_3
  · exact c2_4
  · exact c2_5
  · exact c2_6
  · exact c2_7
  · exact c2_8
  · exact c2_9
  · exact c2_10
  · exact c2_11
  · exact c2_12
  · exact c2_13
  · exact c2_14
  · exact c2_15
noncomputable def s3_0 : CBox := ⟨⟨389984003191939363703,389984003191968312490⟩,⟨5355713233025234217699,5355713233025263166621⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨2163579629569601656531,2163579629569663888450⟩,⟨14618579627209499592984,14618579627209561825362⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨6035365457343804381238,6035365457343855920046⟩,⟨19859890520562461064711,19859890520562512604404⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨11160029626572695913947,11160029626572719427814⟩,⟨19695173974426761822898,19695173974426785338054⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨15247585931731067544029,15247585931731075122382⟩,⟨14717207295706527736184,14717207295706535315648⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨16266684904152482178244,16266684904152484054102⟩,⟨7392801409258576341806,7392801409258578218169⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨13908802115564692312442,13908802115564692610994⟩,⟨721950584935488141526,721950584935488440097⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨9593335751226126569553,9593335751226126608796⟩,⟨(-3374479233544212093744),(-3374479233544212054737)⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨5232392392264354171180,5232392392264354179354⟩,⟨(-4690140639456883361765),(-4690140639456883353875)⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨2046381102742445123037,2046381102742445127034⟩,⟨(-4176940479533952842308),(-4176940479533952838449)⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨271786322213277540975,271786322213277543393⟩,⟨(-2977825730131951967405),(-2977825730131951965019)⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨(-447270030572355175725),(-447270030572355174340)⟩,⟨(-1832810055176084412849),(-1832810055176084411457)⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨(-581159181667219830883),(-581159181667219830130)⟩,⟨(-1013388703144724186734),(-1013388703144724185967)⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨(-468965637747576424260),(-468965637747576423872)⟩,⟨(-512781396869399997286),(-512781396869399996883)⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨(-285396399575959510993),(-285396399575959510806)⟩,⟨(-230488565904160895154),(-230488565904160894963)⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨(-94268013045799176900),(-94268013045799176836)⟩,⟨(-64907311394570204906),(-64907311394570204838)⟩⟩
lemma c3_15 : chunk 3 15 = s3_15 := by decide +kernel
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
lemma s3_eq (i : Fin 16) : chunk 3 i = s3 i := by
  fin_cases i
  · exact c3_0
  · exact c3_1
  · exact c3_2
  · exact c3_3
  · exact c3_4
  · exact c3_5
  · exact c3_6
  · exact c3_7
  · exact c3_8
  · exact c3_9
  · exact c3_10
  · exact c3_11
  · exact c3_12
  · exact c3_13
  · exact c3_14
  · exact c3_15
noncomputable def s4_0 : CBox := ⟨⟨59530679856269003517145,59530679856270940439933⟩,⟨(-45098391123704918453837),(-45098391123702981534408)⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨158621275088165263523158,158621275088172344308923⟩,⟨(-142754072940565013716016),(-142754072940557932937171)⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨201002445747212104946632,201002445747228628750334⟩,⟨(-250642165742115255806636),(-250642165742098732005346)⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨164836503970834835133818,164836503970868574257070⟩,⟨(-345962567872698328286234),(-345962567872664589152345)⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨58696680835476147837096,58696680835534585331360⟩,⟨(-390538246157457724375505),(-390538246157399286853780)⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨(-74851651164457913145209),(-74851651164378327285550)⟩,⟨(-358904803510826178336437),(-358904803510746592436940)⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨(-180514936436015252544953),(-180514936435899323765344)⟩,⟨(-260232241097304994806134),(-260232241097189065999367)⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨(-223265793510514739153700),(-223265793510384378672528)⟩,⟨(-134222844554712397573652),(-134222844554582037084668)⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨(-204624549840507773591901),(-204624549840408703233677)⟩,⟨(-25301009982341253735087),(-25301009982242183381892)⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨(-151585448529952279291498),(-151585448529900723804589)⟩,⟨41656252339160035488797,41656252339211590965370⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨(-93792021586671989923326),(-93792021586651164622179)⟩,⟨66642546126312789432330,66642546126333614724465⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨(-48765483572987540322997),(-48765483572977956414394)⟩,⟨63934024130640900975564,63934024130650484880283⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨(-20727276470207160113032),(-20727276470203455088886)⟩,⟨49132129314985467887302,49132129314989172910416⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨(-6478178262404812958396),(-6478178262403496989402)⟩,⟨32373109674015245636412,32373109674016561605535⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨(-955987203323328714714),(-955987203322878704618)⟩,⟨17776007059466903412841,17776007059467353423282⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨121880328443640886072,121880328443750278932⟩,⟨5604222663599305296770,5604222663599414689786⟩⟩
lemma c4_15 : chunk 4 15 = s4_15 := by decide +kernel
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
lemma s4_eq (i : Fin 16) : chunk 4 i = s4 i := by
  fin_cases i
  · exact c4_0
  · exact c4_1
  · exact c4_2
  · exact c4_3
  · exact c4_4
  · exact c4_5
  · exact c4_6
  · exact c4_7
  · exact c4_8
  · exact c4_9
  · exact c4_10
  · exact c4_11
  · exact c4_12
  · exact c4_13
  · exact c4_14
  · exact c4_15
noncomputable def s5_0 : CBox := ⟨⟨(-1801209708908287102754),(-1801209708908286968354)⟩,⟨(-23173299116674437461361),(-23173299116674437266021)⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨(-25120264343499189219953),(-25120264343499188782729)⟩,⟨(-59667814734353815021196),(-59667814734353814422174)⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨(-92884519893112512793133),(-92884519893112511978838)⟩,⟨(-40939349835556880103996),(-40939349835556879094500)⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨(-187894174997662890560689),(-187894174997662889314089)⟩,⟨112457743704949144218449,112457743704949145613375⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨(-240534653447183411821082),(-240534653447183410128978)⟩,⟨441714874599201243256962,441714874599201244994859⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨(-158439298909712373040940),(-158439298909712370965445)⟩,⟨866324228109875302024192,866324228109875304035248⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨101045901610418556968240,101045901610418559418905⟩,⟨1204256466382718938292281,1204256466382718940600380⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨469947509050980462496841,469947509050980466660581⟩,⟨1296109840607659168541001,1296109840607659172573821⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨799459174918575750200382,799459174918575768469256⟩,⟨1112238955342616535833495,1112238955342616554060203⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨963933330404937180132850,963933330404937277146477⟩,⟨754826788301268547302352,754826788301268644315505⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨935048881040093935793590,935048881040094322075876⟩,⟨374175914888913501603517,374175914888913887891879⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨771282487645523581516732,771282487645524593061802⟩,⟨81517083711955803623228,81517083711956815169670⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨558002790991457116047837,558002790991459246818687⟩,⟨(-83272904096469648080560),(-83272904096467517311798)⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨357323819200165474730201,357323819200168957011529⟩,⟨(-134320210113957346934951),(-134320210113953864655988)⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨193135417651013323765256,193135417651016750660938⟩,⟨(-107909544493796545059226),(-107909544493793118164962)⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨60408383275481572364737,60408383275483005706316⟩,⟨(-40143710237160084845393),(-40143710237158651504269)⟩⟩
lemma c5_15 : chunk 5 15 = s5_15 := by decide +kernel
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
lemma s5_eq (i : Fin 16) : chunk 5 i = s5 i := by
  fin_cases i
  · exact c5_0
  · exact c5_1
  · exact c5_2
  · exact c5_3
  · exact c5_4
  · exact c5_5
  · exact c5_6
  · exact c5_7
  · exact c5_8
  · exact c5_9
  · exact c5_10
  · exact c5_11
  · exact c5_12
  · exact c5_13
  · exact c5_14
  · exact c5_15
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma sums_eq (j : Fin 6) (i : Fin 16) : chunk j i = sums j i := by
  fin_cases j
  · exact s0_eq i
  · exact s1_eq i
  · exact s2_eq i
  · exact s3_eq i
  · exact s4_eq i
  · exact s5_eq i
noncomputable def ans : CBox := ⟨⟨703120923921228930500907,703120923921335994550636⟩,⟨690220352275027877422577,690220352275134941523614⟩⟩
lemma checked : cachedMomentRuleBox density1 hk7_0_14 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule true false 7 14) := by
  rw [← checked]
  exact @cached_density_rule_contains density1 hk7_0_14 (tableDensity true) (fullFactor false 7 14) density1_contains hk7_0_14_contains
noncomputable def atomAnswer : CBox := ⟨⟨4043735277518257336456040,4043735277518257337106138⟩,⟨287215226845759016287896,287215226845759016784795⟩⟩
lemma atomChecked : tableAtomBox true ha7_0_14 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom true false 7 14) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains true false ha7_0_14 7 14 ha7_0_14_contains
 def realAnswer : RBox := ⟨4746856201439486166956947,4746856201439593431656774⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment true false 7 14) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm7_1_0_14
namespace hm7_0_0_15
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density0 j i k).mul (hk7_0_15 j i k))
noncomputable def s0_0 : CBox := ⟨⟨(-5143809151933),(-5143809151917)⟩,⟨2380618229933,2380618229949⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨(-11035528882487),(-11035528882470)⟩,⟨6194688441064,6194688441081⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨(-9151910461633),(-9151910461615)⟩,⟨7170180568060,7170180568077⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨(-4164735639015),(-4164735638996)⟩,⟨5100089505765,5100089505781⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨(-974326458161),(-974326458142)⟩,⟨2271100466449,2271100466467⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨(-49421485880),(-49421485861)⟩,⟨617234915826,617234915845⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨27951431241,27951431261⟩,⟨97426856685,97426856704⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨6378271576,6378271593⟩,⟨8199916046,8199916065⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨542653998,542654018⟩,⟨309205346,309205367⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨19805112,19805132⟩,⟨2575242,2575260⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨284095,284113⟩,⟨(-70271),(-70253)⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨1285,1305⟩,⟨(-865),(-846)⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨0,16⟩,⟨(-16),12⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨0,16⟩,⟨(-16),16⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨0,16⟩,⟨(-16),16⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨0,16⟩,⟨(-16),16⟩⟩
lemma c0_15 : chunk 0 15 = s0_15 := by decide +kernel
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
lemma s0_eq (i : Fin 16) : chunk 0 i = s0 i := by
  fin_cases i
  · exact c0_0
  · exact c0_1
  · exact c0_2
  · exact c0_3
  · exact c0_4
  · exact c0_5
  · exact c0_6
  · exact c0_7
  · exact c0_8
  · exact c0_9
  · exact c0_10
  · exact c0_11
  · exact c0_12
  · exact c0_13
  · exact c0_14
  · exact c0_15
noncomputable def s1_0 : CBox := ⟨⟨149741482761754770,149741482761754898⟩,⟨67122968618584946,67122968618585073⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨396700666857981694,396700666857982082⟩,⟨144046266954185232,144046266954185618⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨506334499538983441,506334499538984175⟩,⟨105174056572159434,105174056572160168⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨457584837853550180,457584837853551306⟩,⟨(-1790000911582106),(-1790000911580981)⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨309224675368549029,309224675368550384⟩,⟨(-85768178810128678),(-85768178810127322)⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨154828610995955662,154828610995956847⟩,⟨(-102775053910234679),(-102775053910233496)⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨53929986891640852,53929986891641861⟩,⟨(-73693055013736032),(-73693055013735024)⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨9818851777778885,9818851777779518⟩,⟨(-37735931865952508),(-37735931865951874)⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨(-1953570082894419),(-1953570082894158)⟩,⟨(-14696169346987024),(-14696169346986760)⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨(-2535197347836235),(-2535197347836151)⟩,⟨(-4495495690942784),(-4495495690942705)⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨(-1305336004033450),(-1305336004033420)⟩,⟨(-1089747096572426),(-1089747096572396)⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨(-514402582956855),(-514402582956835)⟩,⟨(-197672877863098),(-197672877863080)⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨(-182229372337918),(-182229372337902)⟩,⟨(-15290638870675),(-15290638870657)⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨(-63250262856621),(-63250262856604)⟩,⟨9021651931810,9021651931829⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨(-21818968172850),(-21818968172834)⟩,⟨6714731873742,6714731873759⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨(-5379521768540),(-5379521768524)⟩,⟨2142609140636,2142609140652⟩⟩
lemma c1_15 : chunk 1 15 = s1_15 := by decide +kernel
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
lemma s1_eq (i : Fin 16) : chunk 1 i = s1 i := by
  fin_cases i
  · exact c1_0
  · exact c1_1
  · exact c1_2
  · exact c1_3
  · exact c1_4
  · exact c1_5
  · exact c1_6
  · exact c1_7
  · exact c1_8
  · exact c1_9
  · exact c1_10
  · exact c1_11
  · exact c1_12
  · exact c1_13
  · exact c1_14
  · exact c1_15
noncomputable def s2_0 : CBox := ⟨⟨(-74240046691219488),(-74240046691219462)⟩,⟨(-51983795966097807010),(-51983795966097806975)⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨(-11720869963136606352),(-11720869963136606313)⟩,⟨(-140096407578661724288),(-140096407578661724225)⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨(-46132554856292179559),(-46132554856292179499)⟩,⟨(-185155851075433507624),(-185155851075433507538)⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨(-90572697476978797249),(-90572697476978797171)⟩,⟨(-175584142459400528196),(-175584142459400528107)⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨(-119243550940386751152),(-119243550940386751073)⟩,⟨(-123366578223917733577),(-123366578223917733491)⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨(-116370879702523136113),(-116370879702523136045)⟩,⟨(-58138915260826283709),(-58138915260826283642)⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨(-87817818679871043207),(-87817818679871043148)⟩,⟨(-7963598038764867352),(-7963598038764867304)⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨(-52008952325920719720),(-52008952325920719672)⟩,⟨16283982358736072742,16283982358736072779⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨(-23858131363493251010),(-23858131363493250949)⟩,⟨20290142790178864742,20290142790178864801⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨(-7758679740751808495),(-7758679740751808362)⟩,⟨15215425537421501246,15215425537421501376⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨(-888764328733627541),(-888764328733627221)⟩,⟨8977866841474851555,8977866841474851874⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨1106698414213160127,1106698414213160705⟩,⟨4569683147321182899,4569683147321183479⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨1220446194139900365,1220446194139901251⟩,⟨2116820508925857969,2116820508925858853⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨851427542529394007,851427542529395143⟩,⟨921608949082906786,921608949082907919⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨465692075341572715,465692075341573658⟩,⟨370878914306020036,370878914306020976⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨145376957248888342,145376957248888711⟩,⟨98442047328920732,98442047328921103⟩⟩
lemma c2_15 : chunk 2 15 = s2_15 := by decide +kernel
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
lemma s2_eq (i : Fin 16) : chunk 2 i = s2 i := by
  fin_cases i
  · exact c2_0
  · exact c2_1
  · exact c2_2
  · exact c2_3
  · exact c2_4
  · exact c2_5
  · exact c2_6
  · exact c2_7
  · exact c2_8
  · exact c2_9
  · exact c2_10
  · exact c2_11
  · exact c2_12
  · exact c2_13
  · exact c2_14
  · exact c2_15
noncomputable def s3_0 : CBox := ⟨⟨(-1693979744084350950335),(-1693979744084346144877)⟩,⟨1466035888379516018466,1466035888379520824094⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨(-4382513284154010904282),(-4382513284154000613346)⟩,⟨4425453932651996316562,4425453932652006608086⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨(-5255325695096076841394),(-5255325695096068382023)⟩,⟨7202789834807203959627,7202789834807212420136⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨(-3998789964390068255451),(-3998789964390064436952)⟩,⟨9117639710962591529806,9117639710962595350017⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨(-1304038158632610277737),(-1304038158632609063628)⟩,⟨9415758532600609910826,9415758532600611126475⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨1504392306600960794891,1504392306600961091978⟩,⟨7933654717272328105354,7933654717272328403183⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨3272363450661638552341,3272363450661638600304⟩,⟨5337705753885340577558,5337705753885340625550⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨3636156715326777170392,3636156715326777177819⟩,⟨2682283134311384747347,2682283134311384754375⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨2991776011859758578089,2991776011859758580318⟩,⟨744939514438467462215,744939514438467463928⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨1995927848405488212671,1995927848405488213885⟩,⟨(-276745470062745720619),(-276745470062745719678)⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨1121925381466064436038,1121925381466064436741⟩,⟨(-606219203640976946415),(-606219203640976945778)⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨539632078586955739564,539632078586955739946⟩,⟨(-573911686163704159795),(-573911686163704159393)⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨220411131779505405727,220411131779505405921⟩,⟨(-421462100595624123951),(-421462100595624123711)⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨72822748259104769750,72822748259104769846⟩,⟨(-266147594667915534666),(-266147594667915534529)⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨16916972215658004762,16916972215658004811⟩,⟨(-141810608941920500266),(-141810608941920500187)⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨1892204094498195356,1892204094498195383⟩,⟨(-44035878744282103074),(-44035878744282103041)⟩⟩
lemma c3_15 : chunk 3 15 = s3_15 := by decide +kernel
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
lemma s3_eq (i : Fin 16) : chunk 3 i = s3 i := by
  fin_cases i
  · exact c3_0
  · exact c3_1
  · exact c3_2
  · exact c3_3
  · exact c3_4
  · exact c3_5
  · exact c3_6
  · exact c3_7
  · exact c3_8
  · exact c3_9
  · exact c3_10
  · exact c3_11
  · exact c3_12
  · exact c3_13
  · exact c3_14
  · exact c3_15
noncomputable def s4_0 : CBox := ⟨⟨22284743584632440664683,22284743584632851609956⟩,⟨32777256015474596152599,32777256015475007096255⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨70391338959181811696778,70391338959183307962691⟩,⟨85249821400342153578349,85249821400343649841001⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨122600901651708475897712,122600901651711940327547⟩,⟨102577987573380317906825,102577987573383782335621⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨166149082768756302162394,166149082768763296442558⟩,⟨75953973542339164710147,75953973542346158995561⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨181400747441793529597039,181400747441805472197040⟩,⟨16323179445061614180135,16323179445073556793631⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨157602797334529616952476,157602797334545610573057⟩,⟨(-49224454150113218858630),(-49224454150097225218205)⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨103496443901315390910121,103496443901338242951674⟩,⟨(-92801726938462087935628),(-92801726938439235880446)⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨42082878979988058085669,42082878980013254790007⟩,⟨(-101892698743670995440698),(-101892698743645798732392)⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨(-5089685328960037633893),(-5089685328941274140819)⟩,⟨(-83214892408768560004617),(-83214892408749796514377)⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨(-29301647410326036475335),(-29301647410316465746126)⟩,⟨(-53274175294429951131793),(-53274175294420380408780)⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨(-34273379816678165514001),(-34273379816674376053810)⟩,⟨(-26233247479438120911928),(-26233247479434331457503)⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨(-28770986687671249317726),(-28770986687669536202480)⟩,⟨(-8358968888727214678198),(-8358968888725501565519)⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨(-20197512054122000598214),(-20197512054121348489687)⟩,⟨553941897216369662480,553941897217021770304⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨(-12419797533304775187281),(-12419797533304546447232)⟩,⟨3378743922183030766861,3378743922183259507004⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨(-6484729687421855493773),(-6484729687421777961872)⟩,⟨2944045198881700817740,2944045198881778349893⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨(-1988946712150767673003),(-1988946712150748912080)⟩,⟨1104378591288376250221,1104378591288395011262⟩⟩
lemma c4_15 : chunk 4 15 = s4_15 := by decide +kernel
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
lemma s4_eq (i : Fin 16) : chunk 4 i = s4 i := by
  fin_cases i
  · exact c4_0
  · exact c4_1
  · exact c4_2
  · exact c4_3
  · exact c4_4
  · exact c4_5
  · exact c4_6
  · exact c4_7
  · exact c4_8
  · exact c4_9
  · exact c4_10
  · exact c4_11
  · exact c4_12
  · exact c4_13
  · exact c4_14
  · exact c4_15
noncomputable def s5_0 : CBox := ⟨⟨163520847405134816729009,163520847405134816810769⟩,⟨(-4926985155045642121580),(-4926985155045642064815)⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨458086222038465570271174,458086222038465570519806⟩,⟨(-68725511884320153687718),(-68725511884320153503735)⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨646579069956215804850447,646579069956215805267272⟩,⟨(-257086192412174558268923),(-257086192412174557927422)⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨653901807151896304111777,653901807151896304684755⟩,⟨(-546172899109304842123801),(-546172899109304841605571)⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨449141008211563810911576,449141008211563811602114⟩,⟨(-816007735214482319979426),(-816007735214482319304932)⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨92701649410275676037361,92701649410275676789743⟩,⟨(-923388688038044820353670),(-923388688038044819582032)⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨(-274523288678127066159499),(-274523288678127065377646)⟩,⟨(-803905016944515956026164),(-803905016944515955206025)⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨(-511112141668967745661251),(-511112141668967744532288)⟩,⟨(-515648195750962694217697),(-515648195750962693058247)⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨(-559519697801774864179877),(-559519697801774859832508)⟩,⟨(-189777883676006723344210),(-189777883676006718989197)⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨(-461208114890190053304022),(-461208114890190031102948)⟩,⟨59191607482769419310960,59191607482769441512370⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨(-303931330332412599324254),(-303931330332412512500951)⟩,⟨187171912936958142535309,187171912936958229361139⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨(-160728576477415789294358),(-160728576477415565344149)⟩,⟨213042782013863541544217,213042782013863765500789⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨(-64158829497308118460251),(-64158829497307653178122)⟩,⟨180458549528368771931623,180458549528369237220290⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨(-14213424530706814863704),(-14213424530706062511583)⟩,⟨126872784864649588244183,126872784864650340600116⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨3079156202878373646146,3079156202879108519810⟩,⟨72613454093617899146810,72613454093618634022221⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨2810378505998606417623,2810378505998912604801⟩,⟨23364541405288026714880,23364541405288332902535⟩⟩
lemma c5_15 : chunk 5 15 = s5_15 := by decide +kernel
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
lemma s5_eq (i : Fin 16) : chunk 5 i = s5 i := by
  fin_cases i
  · exact c5_0
  · exact c5_1
  · exact c5_2
  · exact c5_3
  · exact c5_4
  · exact c5_5
  · exact c5_6
  · exact c5_7
  · exact c5_8
  · exact c5_9
  · exact c5_10
  · exact c5_11
  · exact c5_12
  · exact c5_13
  · exact c5_14
  · exact c5_15
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma sums_eq (j : Fin 6) (i : Fin 16) : chunk j i = sums j i := by
  fin_cases j
  · exact s0_eq i
  · exact s1_eq i
  · exact s2_eq i
  · exact s3_eq i
  · exact s4_eq i
  · exact s5_eq i
noncomputable def ans : CBox := ⟨⟨141015988075566283318901,141015988075587249064853⟩,⟨(-551956305668231062791738),(-551956305668210097059238)⟩⟩
lemma checked : cachedMomentRuleBox density0 hk7_0_15 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule false false 7 15) := by
  rw [← checked]
  exact @cached_density_rule_contains density0 hk7_0_15 (tableDensity false) (fullFactor false 7 15) density0_contains hk7_0_15_contains
noncomputable def atomAnswer : CBox := ⟨⟨38075133827727417528810,38075133827727417604002⟩,⟨(-634506425035256600835795),(-634506425035256600734143)⟩⟩
lemma atomChecked : tableAtomBox false ha7_0_15 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom false false 7 15) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains false false ha7_0_15 7 15 ha7_0_15_contains
 def realAnswer : RBox := ⟨179091121903293600847711,179091121903314766668855⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment false false 7 15) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm7_0_0_15
namespace hm7_1_0_15
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density1 j i k).mul (hk7_0_15 j i k))
noncomputable def s0_0 : CBox := ⟨⟨(-925654099834),(-925654099817)⟩,⟨287520942114,287520942130⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨(-2025255915993),(-2025255915977)⟩,⟨789510060913,789510060929⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨(-1746832319935),(-1746832319919)⟩,⟨976656549136,976656549152⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨(-847960064036),(-847960064018)⟩,⟨734172107538,734172107554⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨(-225505628040),(-225505628023)⟩,⟨340901847130,340901847146⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨(-23203031488),(-23203031472)⟩,⟨95600368754,95600368771⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨2710493838,2710493856⟩,⟨15412100976,15412100992⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨939184501,939184517⟩,⟨1303962092,1303962108⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨87781824,87781840⟩,⟨47404480,47404496⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨3334137,3334153⟩,⟨233701,233717⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨48616,48632⟩,⟨(-15859),(-15842)⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨213,230⟩,⟨(-179),(-162)⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨0,16⟩,⟨(-16),12⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨0,16⟩,⟨(-16),16⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨0,16⟩,⟨(-16),16⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨0,16⟩,⟨(-16),16⟩⟩
lemma c0_15 : chunk 0 15 = s0_15 := by decide +kernel
noncomputable def s0 : Fin 16 → CBox := ![s0_0,s0_1,s0_2,s0_3,s0_4,s0_5,s0_6,s0_7,s0_8,s0_9,s0_10,s0_11,s0_12,s0_13,s0_14,s0_15]
lemma s0_eq (i : Fin 16) : chunk 0 i = s0 i := by
  fin_cases i
  · exact c0_0
  · exact c0_1
  · exact c0_2
  · exact c0_3
  · exact c0_4
  · exact c0_5
  · exact c0_6
  · exact c0_7
  · exact c0_8
  · exact c0_9
  · exact c0_10
  · exact c0_11
  · exact c0_12
  · exact c0_13
  · exact c0_14
  · exact c0_15
noncomputable def s1_0 : CBox := ⟨⟨15564956860411197,15564956860411304⟩,⟨20317537311166089,20317537311166199⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨43747626246472541,43747626246472860⟩,⟨48035094303108280,48035094303108602⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨61307640913497584,61307640913498191⟩,⟨47890446585705351,47890446585705958⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨61386527556259170,61386527556260101⟩,⟨26947163074978810,26947163074979742⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨45882844753197257,45882844753198377⟩,⟨4240159767140003,4240159767141122⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨25470907813560007,25470907813560986⟩,⟨(-7456594679648885),(-7456594679647909)⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨10111353516981396,10111353516982231⟩,⟨(-8445493039342601),(-8445493039341768)⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨2488558514378607,2488558514379135⟩,⟨(-5175977656945943),(-5175977656945416)⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨44732831241449,44732831241669⟩,⟨(-2244479981479533),(-2244479981479316)⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨(-311780785364885),(-311780785364818)⟩,⟨(-746618256729244),(-746618256729178)⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨(-195850543114604),(-195850543114578)⟩,⟨(-197360042906544),(-197360042906518)⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨(-84931641196104),(-84931641196084)⟩,⟨(-41053441290939),(-41053441290921)⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨(-32150144892473),(-32150144892457)⟩,⟨(-5556072705921),(-5556072705903)⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨(-11739526183994),(-11739526183977)⟩,⟨494659548291,494659548307⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨(-4200846450757),(-4200846450741)⟩,⟨793397672909,793397672926⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨(-1056457759267),(-1056457759251)⟩,⟨280961934605,280961934622⟩⟩
lemma c1_15 : chunk 1 15 = s1_15 := by decide +kernel
noncomputable def s1 : Fin 16 → CBox := ![s1_0,s1_1,s1_2,s1_3,s1_4,s1_5,s1_6,s1_7,s1_8,s1_9,s1_10,s1_11,s1_12,s1_13,s1_14,s1_15]
lemma s1_eq (i : Fin 16) : chunk 1 i = s1 i := by
  fin_cases i
  · exact c1_0
  · exact c1_1
  · exact c1_2
  · exact c1_3
  · exact c1_4
  · exact c1_5
  · exact c1_6
  · exact c1_7
  · exact c1_8
  · exact c1_9
  · exact c1_10
  · exact c1_11
  · exact c1_12
  · exact c1_13
  · exact c1_14
  · exact c1_15
noncomputable def s2_0 : CBox := ⟨⟨6136159314486503978,6136159314486503998⟩,⟨(-10004312499182139148),(-10004312499182139125)⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨14464232373892372854,14464232373892372887⟩,⟨(-28298018108320793274),(-28298018108320793239)⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨13649157240527063191,13649157240527063231⟩,⟨(-40818400327491185823),(-40818400327491185781)⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨4715307288881280080,4715307288881280122⟩,⟨(-43672787136200278419),(-43672787136200278377)⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨(-6227985199334080799),(-6227985199334080757)⟩,⟨(-36351762938558635949),(-36351762938558635907)⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨(-12942479293442640056),(-12942479293442640016)⟩,⟨(-23212757066555110747),(-23212757066555110708)⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨(-13401771999469706273),(-13401771999469706241)⟩,⟨(-10549142675298572350),(-10549142675298572318)⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨(-9825089040671408842),(-9825089040671408814)⟩,⟨(-2324307578905217913),(-2324307578905217884)⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨(-5537118485755289943),(-5537118485755289898)⟩,⟨1205877917768165675,1205877917768165716⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨(-2451366393663823671),(-2451366393663823568)⟩,⟨1842736962134023792,1842736962134023899⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨(-822191244271297193),(-822191244271296933)⟩,⟨1388356194464838774,1388356194464839036⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨(-159235303534467509),(-159235303534467037)⟩,⟨814448455138927415,814448455138927889⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨40147545028905016,40147545028905742⟩,⟨417825399856519197,417825399856519921⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨67374801751887405,67374801751888332⟩,⟨197236220975172598,197236220975173527⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨45872773937920918,45872773937921687⟩,⟨84511953362332917,84511953362333689⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨15454713624663791,15454713624664093⟩,⟨23272057573406146,23272057573406449⟩⟩
lemma c2_15 : chunk 2 15 = s2_15 := by decide +kernel
noncomputable def s2 : Fin 16 → CBox := ![s2_0,s2_1,s2_2,s2_3,s2_4,s2_5,s2_6,s2_7,s2_8,s2_9,s2_10,s2_11,s2_12,s2_13,s2_14,s2_15]
lemma s2_eq (i : Fin 16) : chunk 2 i = s2 i := by
  fin_cases i
  · exact c2_0
  · exact c2_1
  · exact c2_2
  · exact c2_3
  · exact c2_4
  · exact c2_5
  · exact c2_6
  · exact c2_7
  · exact c2_8
  · exact c2_9
  · exact c2_10
  · exact c2_11
  · exact c2_12
  · exact c2_13
  · exact c2_14
  · exact c2_15
noncomputable def s3_0 : CBox := ⟨⟨(-746907944263623995153),(-746907944263619957820)⟩,⟨54381554798554418289,54381554798558455599⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨(-2029134382016561087519),(-2029134382016552447403)⟩,⟨300177079612851373409,300177079612860013457⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨(-2731198317041066350378),(-2731198317041059257977)⟩,⟨829460231321982833168,829460231321989925442⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨(-2672036590463070395148),(-2672036590463067200899)⟩,⟨1512865938850414831401,1512865938850418025473⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨(-1962215931023616995116),(-1962215931023615983395)⟩,⟨2030785660513891483034,2030785660513892494607⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨(-965806677536547558136),(-965806677536547312710)⟩,⟨2121172268955859318754,2121172268955859564115⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨(-93370536908682041000),(-93370536908682002836)⟩,⟨1770642574935262080992,1770642574935262119153⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨417298810062764033125,417298810062764037997⟩,⟨1189749038456457310731,1189749038456457315632⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨564948316832598431344,564948316832598432315⟩,⟨631423624387608791866,631423624387608792870⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨489463883489101457252,489463883489101457721⟩,⟨240327620274397417449,240327620274397417931⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨339665141916256456562,339665141916256456850⟩,⟨31262754340975018958,31262754340975019250⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨203878556031491561737,203878556031491561904⟩,⟨(-49623199436536283111),(-49623199436536282940)⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨110274936348342089686,110274936348342089783⟩,⟨(-63179905015780730594),(-63179905015780730498)⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨54817630730704970890,54817630730704970948⟩,⟨(-50110347405807007008),(-50110347405807006947)⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨24333280646637297772,24333280646637297806⟩,⟨(-30124612746588460935),(-30124612746588460901)⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨6808114747557340856,6808114747557340875⟩,⟨(-9887540544360332880),(-9887540544360332858)⟩⟩
lemma c3_15 : chunk 3 15 = s3_15 := by decide +kernel
noncomputable def s3 : Fin 16 → CBox := ![s3_0,s3_1,s3_2,s3_3,s3_4,s3_5,s3_6,s3_7,s3_8,s3_9,s3_10,s3_11,s3_12,s3_13,s3_14,s3_15]
lemma s3_eq (i : Fin 16) : chunk 3 i = s3 i := by
  fin_cases i
  · exact c3_0
  · exact c3_1
  · exact c3_2
  · exact c3_3
  · exact c3_4
  · exact c3_5
  · exact c3_6
  · exact c3_7
  · exact c3_8
  · exact c3_9
  · exact c3_10
  · exact c3_11
  · exact c3_12
  · exact c3_13
  · exact c3_14
  · exact c3_15
noncomputable def s4_0 : CBox := ⟨⟨7863554395415009658282,7863554395415347384406⟩,⟨10380180667869582282057,10380180667869920008775⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨24795556311321544893689,24795556311322774659952⟩,⟨27554912858155742717911,27554912858156972485404⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨43208130748311875289384,43208130748314723061745⟩,⟨34661772167712295996666,34661772167715143769453⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨58989949154398375347431,58989949154404125601959⟩,⟨28126587699710288737004,28126587699716038989681⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨65661030262400065770966,65661030262409885441514⟩,⟨9897510986631641439917,9897510986641461105753⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨59342437791147871497180,59342437791161022114222⟩,⟨(-12340192403748431038846),(-12340192403735280428516)⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨42226497576004236132818,42226497576023021992063⟩,⟨(-29247309100832122938849),(-29247309100813337084094)⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨21348119314617503695436,21348119314638207090223⟩,⟨(-35449417604530743360270),(-35449417604510039966744)⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨3956522567691547982745,3956522567706953369755⟩,⟨(-31804690800998068541272),(-31804690800982663153469)⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨(-6320631821907647635867),(-6320631821899798012142)⟩,⟨(-23060540362956935787431),(-23060540362949086162109)⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨(-9918751176480417262122),(-9918751176477313311965)⟩,⟨(-13975733078701548210407),(-13975733078698444258883)⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨(-9338431922379088843198),(-9338431922377687516797)⟩,⟨(-7128983600588860240396),(-7128983600587458913419)⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨(-7058915835637243269452),(-7058915835636710523702)⟩,⟨(-2980293527867223503632),(-2980293527866690757733)⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨(-4589795871646456013563),(-4589795871646269341910)⟩,⟨(-919244754592576537223),(-919244754592389865590)⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨(-2496924949663181490169),(-2496924949663118265355)⟩,⟨(-134446153297376290026),(-134446153297313065258)⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨(-783440943675893794122),(-783440943675878501137)⟩,⟨17032303809893940423,17032303809909233387⟩⟩
lemma c4_15 : chunk 4 15 = s4_15 := by decide +kernel
noncomputable def s4 : Fin 16 → CBox := ![s4_0,s4_1,s4_2,s4_3,s4_4,s4_5,s4_6,s4_7,s4_8,s4_9,s4_10,s4_11,s4_12,s4_13,s4_14,s4_15]
lemma s4_eq (i : Fin 16) : chunk 4 i = s4 i := by
  fin_cases i
  · exact c4_0
  · exact c4_1
  · exact c4_2
  · exact c4_3
  · exact c4_4
  · exact c4_5
  · exact c4_6
  · exact c4_7
  · exact c4_8
  · exact c4_9
  · exact c4_10
  · exact c4_11
  · exact c4_12
  · exact c4_13
  · exact c4_14
  · exact c4_15
noncomputable def s5_0 : CBox := ⟨⟨4849548377920294352897,4849548377920294393803⟩,⟨(-376843715088915826000),(-376843715088915797861)⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨12448621565629109768691,12448621565629109893701⟩,⟨(-5237958031915642174682),(-5237958031915642083448)⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨8498562750481910170852,8498562750481910380185⟩,⟨(-19247957559270030580811),(-19247957559270030411944)⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨(-23061200233816155985998),(-23061200233816155699373)⟩,⟨(-38587689573781935276175),(-38587689573781935019978)⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨(-89597200305926154043549),(-89597200305926153690443)⟩,⟨(-48838216079763818984150),(-48838216079763818640337)⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨(-173333774469333738031437),(-173333774469333737628261)⟩,⟨(-31762827638674524102070),(-31762827638674523686113)⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨(-237228433493096249566640),(-237228433493096249111086)⟩,⟨19818767081617938822424,19818767081617939305690⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨(-251064483679403875822236),(-251064483679403875041369)⟩,⟨90919023686032344026377,90919023686032344832013⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨(-211719062750111929095378),(-211719062750111925634585)⟩,⟨152045471507596170481840,152045471507596173950294⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨(-141205734401985469407056),(-141205734401985451312294)⟩,⟨180168803597126081966394,180168803597126100061258⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨(-68850932817211128952249),(-68850932817211058076580)⟩,⟨171863770958324686499532,171863770958324757374413⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨(-14799597914746089025300),(-14799597914745906169951)⟩,⟨139594067274283056193777,139594067274283239049346⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨14847063715069397305711,14847063715069777396432⟩,⟨99651285119503793808503,99651285119504173899970⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨23722671799740340929217,23722671799740955843281⟩,⟨63134590743660082728120,63134590743660697642790⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨18922089346497668548250,18922089346498269408754⟩,⟨33870845488096551839949,33870845488097152700777⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨7013071152640325798758,7013071152640576199840⟩,⟨10553432410379297090026,10553432410379547491208⟩⟩
lemma c5_15 : chunk 5 15 = s5_15 := by decide +kernel
noncomputable def s5 : Fin 16 → CBox := ![s5_0,s5_1,s5_2,s5_3,s5_4,s5_5,s5_6,s5_7,s5_8,s5_9,s5_10,s5_11,s5_12,s5_13,s5_14,s5_15]
lemma s5_eq (i : Fin 16) : chunk 5 i = s5 i := by
  fin_cases i
  · exact c5_0
  · exact c5_1
  · exact c5_2
  · exact c5_3
  · exact c5_4
  · exact c5_5
  · exact c5_6
  · exact c5_7
  · exact c5_8
  · exact c5_9
  · exact c5_10
  · exact c5_11
  · exact c5_12
  · exact c5_13
  · exact c5_14
  · exact c5_15
noncomputable def sums : Fin 6 → Fin 16 → CBox := ![s0,s1,s2,s3,s4,s5]
lemma sums_eq (j : Fin 6) (i : Fin 16) : chunk j i = sums j i := by
  fin_cases j
  · exact s0_eq i
  · exact s1_eq i
  · exact s2_eq i
  · exact s3_eq i
  · exact s4_eq i
  · exact s5_eq i
noncomputable def ans : CBox := ⟨⟨(-140445839273240162862565),(-140445839273222940901351)⟩,⟨130247649867351442410089,130247649867368664360417⟩⟩
lemma checked : cachedMomentRuleBox density1 hk7_0_15 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule true false 7 15) := by
  rw [← checked]
  exact @cached_density_rule_contains density1 hk7_0_15 (tableDensity true) (fullFactor false 7 15) density1_contains hk7_0_15_contains
noncomputable def atomAnswer : CBox := ⟨⟨(-49790559620874315328310),(-49790559620874315229982)⟩,⟨829739171199950939421572,829739171199950939554500⟩⟩
lemma atomChecked : tableAtomBox true ha7_0_15 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom true false 7 15) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains true false ha7_0_15 7 15 ha7_0_15_contains
 def realAnswer : RBox := ⟨(-190236398894114578190875),(-190236398894097156131333)⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment true false 7 15) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm7_1_0_15
end SharpPlanar.CachedData

end OAI
