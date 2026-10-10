import OAI.Analysis.PlanarPacking.Certificate.TableDensityValues
import OAI.Analysis.PlanarPacking.Certificate.HighHeaders16

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace hm16_0_1_2
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density0 j i k).mul (hk16_1_2 j i k))
noncomputable def s0_0 : CBox := ⟨⟨(-46),46⟩,⟨(-46),46⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨(-119),119⟩,⟨(-119),119⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨(-191),191⟩,⟨(-191),191⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨(-259),259⟩,⟨(-259),259⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨(-318),318⟩,⟨(-318),318⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨(-368),368⟩,⟨(-368),368⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨(-401),401⟩,⟨(-401),401⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨(-416),416⟩,⟨(-416),416⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨(-405),405⟩,⟨(-405),405⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨(-375),375⟩,⟨(-375),375⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨(-331),331⟩,⟨(-331),331⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨(-278),278⟩,⟨(-278),278⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨(-205),205⟩,⟨(-205),205⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨(-119),119⟩,⟨(-119),119⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨(-75),75⟩,⟨(-75),75⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨(-30),30⟩,⟨(-30),30⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨(-24),24⟩,⟨(-24),24⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨(-56),56⟩,⟨(-56),56⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨(-87),87⟩,⟨(-87),87⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨(-119),119⟩,⟨(-119),119⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨(-154),154⟩,⟨(-154),154⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨(-188),188⟩,⟨(-188),188⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨(-220),220⟩,⟨(-220),220⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨(-248),248⟩,⟨(-248),248⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨(-267),267⟩,⟨(-267),267⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨(-272),272⟩,⟨(-272),272⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨(-270),270⟩,⟨(-270),270⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨(-248),248⟩,⟨(-248),248⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨(-211),211⟩,⟨(-211),211⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨(-164),164⟩,⟨(-164),164⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨(-104),104⟩,⟨(-104),104⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨(-40),40⟩,⟨(-40),40⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨(-8431346360),(-8431346333)⟩,⟨(-46102476902),(-46102476880)⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨(-26068426128),(-26068426091)⟩,⟨(-82286363817),(-82286363779)⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨(-28438143556),(-28438143499)⟩,⟨(-46476993554),(-46476993496)⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨(-13996533890),(-13996533820)⟩,⟨(-11381040332),(-11381040262)⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨(-3355679954),(-3355679870)⟩,⟨(-953758843),(-953758758)⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨(-413948791),(-413948693)⟩,⟨65814754,65814851⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨(-27753082),(-27752969)⟩,⟨18141580,18141690⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨(-1086378),(-1086244)⟩,⟨1501340,1501473⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨(-27944),(-27799)⟩,⟨75071,75218⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨(-691),(-545)⟩,⟨2863,3013⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨(-90),48⟩,⟨42,179⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨(-78),78⟩,⟨(-44),108⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨(-92),71⟩,⟨(-62),103⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨(-72),57⟩,⟨(-48),81⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨(-52),49⟩,⟨(-43),55⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨(-24),24⟩,⟨(-24),24⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨17927709178847181983,17927709178847224495⟩,⟨12601846825590219909,12601846825590262421⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨43960004695146369451,43960004695146436951⟩,⟨20685051843559295477,20685051843559362967⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨44078448759952296100,44078448759952337108⟩,⟨4469457556064207553,4469457556064248555⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨23373727856435817915,23373727856435831006⟩,⟨(-9609755466389294606),(-9609755466389281519)⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨5254761353531852257,5254761353531853948⟩,⟨(-8454804033568679941),(-8454804033568678247)⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨(-505974023264327582),(-505974023264327400)⟩,⟨(-2805337145146991867),(-2805337145146991686)⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨(-519597785168307267),(-519597785168307201)⟩,⟨(-338400353391873345),(-338400353391873279)⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨(-103165033366576335),(-103165033366576274)⟩,⟨29996350578134164,29996350578134226⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨(-6408415312320465),(-6408415312320406)⟩,⟨14294373052036012,14294373052036071⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨822251013524115,822251013524182⟩,⟨1879690362342030,1879690362342098⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨240733116202391,240733116202454⟩,⟨99566639918893,99566639918956⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨33570940161033,33570940161094⟩,⟨(-9579195579300),(-9579195579238)⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨3625684554081,3625684554130⟩,⟨(-3972094823945),(-3972094823895)⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨318315062156,318315062198⟩,⟨(-968202002005),(-968202001964)⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨8035577618,8035577650⟩,⟨(-237984352342),(-237984352308)⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨(-5269279472),(-5269279451)⟩,⟨(-48312741746),(-48312741724)⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨(-1008740543906043682020917),(-1008740543906010200358720)⟩,⟨(-3555956403219954893617523),(-3555956403219921412395807)⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨(-4001170462074207777808299),(-4001170462074093422958615)⟩,⟨(-8131504027245037708476061),(-8131504027244923354393731)⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨(-7371792145358135275509844),(-7371792145357918753052168)⟩,⟨(-6951837810053776847150719),(-6951837810053560324829716)⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨(-7681101712518467669730194),(-7681101712518189065035174)⟩,⟨(-1819788462534318925053647),(-1819788462534040319669057)⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨(-4301324705273602582738723),(-4301324705273320601281688)⟩,⟨2013313100570559016326999,2013313100570840998403036⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨(-777586534606567621211181),(-777586534606284949368309)⟩,⟨2182529264226698819445214,2182529264226981491241328⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨486033047814686514003079,486033047814837409018747⟩,⟨812316648848314583786680,812316648848465478682306⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨332536543102549051086788,332536543102625974121893⟩,⟨30081538063603577869707,30081538063680500914377⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨67231205900654010360985,67231205900674992859569⟩,⟨(-81029298284740421135486),(-81029298284719438625283)⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨(-8168402505201901785684),(-8168402505196351508055)⟩,⟨(-29829017212435450284868),(-29829017212429900009093)⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨(-8200964779190373416140),(-8200964779189431849499)⟩,⟨(-3368504448447242768156),(-3368504448446301202293)⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨(-2356138870580390582697),(-2356138870580225406956)⟩,⟨1106350454455885905393,1106350454456051081284⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨(-336631724878807292148),(-336631724878784730523)⟩,⟨742545315302273130659,742545315302295692373⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨35260559786695637877,35260559786700663995⟩,⟨275327116691940999541,275327116691946025662⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨47771436983768934454,47771436983770001675⟩,⟨86110300797797278088,86110300797798345300⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨16071939456998029787,16071939456998222729⟩,⟨19114819948808232922,19114819948808425860⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨476857319238352894357061763,476857319238352925697685430⟩,⟨2501945820057651389224284250,2501945820057651420829582011⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨2443433967802858238424065070,2443433967802858330773815813⟩,⟨6244707589019778791007341117,6244707589019778883941163572⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨5832506809537607116727131410,5832506809537607263092587136⟩,⟨6472245312239708618335183511,6472245312239708765092114573⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨8144343667273316842271733901,8144343667273317025931034997⟩,⟨2749703838452608389502287082,2749703838452608573001353406⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨6759806112021903089584385118,6759806112021903286914791849⟩,⟨(-2090863707962858107994115412),(-2090863707962857911151538762)⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨2648886622096720188229542391,2648886622096720369236244096⟩,⟨(-4217589131036162479480839829),(-4217589131036162298637701534)⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨(-664100639690092527714050648),(-664100639690092386300620994)⟩,⟨(-2965732176436999186959856812),(-2965732176436999045461452290)⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨(-1437833638187846609843307667),(-1437833638187846512740192130)⟩,⟨(-806956374569812084216958497),(-806956374569811987069706951)⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨(-768643933695110906116412733),(-768643933695110844269918572)⟩,⟨290549235772246677764932453,290549235772246739601654831⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨(-128578009706631944356805384),(-128578009706631897788375261)⟩,⟨366970532237489641041129276,366970532237489687606490109⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨85569481790172901573476662,85569481790172958163216861⟩,⟨158363389807575743107052522,158363389807575799697410136⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨79088138150521508858743516,79088138150521589496356567⟩,⟨26513398781015933021052262,26513398781016013658206061⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨37231025808312659676494360,37231025808312781047439070⟩,⟨(-12049374119201555482809706),(-12049374119201434112133419)⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨12724307460999668209521977,12724307460999778306409270⟩,⟨(-13351651354184335829125522),(-13351651354184225732160464)⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨3355352670222284256582927,3355352670222350962457628⟩,⟨(-7496573914638761453086871),(-7496573914638694747094750)⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨573366855969241150317203,573366855969266663210600⟩,⟨(-2269896566033197336526212),(-2269896566033171823594145)⟩⟩
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
noncomputable def ans : CBox := ⟨⟨3916824200757836482358211865,3916824200757836999525082805⟩,⟨1446526233913202891651523776,1446526233913203408909195101⟩⟩
lemma checked : cachedMomentRuleBox density0 hk16_1_2 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule false true 16 2) := by
  rw [← checked]
  exact @cached_density_rule_contains density0 hk16_1_2 (tableDensity false) (fullFactor true 16 2) density0_contains hk16_1_2_contains
noncomputable def atomAnswer : CBox := ⟨⟨8937518021205849372111665890,8937518021205849386383714986⟩,⟨(-1268101529829358922072686936),(-1268101529829358907945161414)⟩⟩
lemma atomChecked : tableAtomBox false ha16_1_2 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom false true 16 2) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains false true ha16_1_2 16 2 ha16_1_2_contains
 def realAnswer : RBox := ⟨12854342221963685854369877755,12854342221963686386008797791⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment false true 16 2) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm16_0_1_2
namespace hm16_1_1_2
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density1 j i k).mul (hk16_1_2 j i k))
noncomputable def s0_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨(-28),28⟩,⟨(-28),28⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨(-40),40⟩,⟨(-40),40⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨(-49),49⟩,⟨(-49),49⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨(-64),64⟩,⟨(-64),64⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨(-64),64⟩,⟨(-64),64⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨(-64),64⟩,⟨(-64),64⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨(-64),64⟩,⟨(-64),64⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨(-64),64⟩,⟨(-64),64⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨(-64),64⟩,⟨(-64),64⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨(-64),64⟩,⟨(-64),64⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨(-53),53⟩,⟨(-53),53⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨(-44),44⟩,⟨(-44),44⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨(-30),30⟩,⟨(-30),30⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨(-17),17⟩,⟨(-17),17⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨(-32),32⟩,⟨(-32),32⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨(-32),32⟩,⟨(-32),32⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨(-32),32⟩,⟨(-32),32⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨(-48),48⟩,⟨(-48),48⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨(-34),34⟩,⟨(-34),34⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨(-27),27⟩,⟨(-27),27⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨3833003496,3833003514⟩,⟨(-9862204472),(-9862204454)⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨4805170910,4805170931⟩,⟨(-18911627475),(-18911627453)⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨204663691,204663718⟩,⟨(-12296290479),(-12296290448)⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨(-1212014157),(-1212014124)⟩,⟨(-3834802846),(-3834802814)⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨(-483828558),(-483828524)⟩,⟨(-578770258),(-578770222)⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨(-78047636),(-78047601)⟩,⟨(-37002873),(-37002839)⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨(-6470958),(-6470922)⟩,⟨(-16860),(-16823)⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨(-318242),(-318206)⟩,⟨134950,134992⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨(-10982),(-10945)⟩,⟨9554,9592⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨(-354),(-316)⟩,⟨407,442⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨(-26),7⟩,⟨(-2),31⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨2286294367484266017,2286294367484301695⟩,⟨6960062152694878434,6960062152694914111⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨7498545633314763796,7498545633314820373⟩,⟨14147093717158378052,14147093717158434631⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨10420488004054470015,10420488004054504315⟩,⟨9656374298605924973,9656374298605959271⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨7563012279806080643,7563012279806091551⟩,⟨1961561488004630419,1961561488004641324⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨2751055924492221215,2751055924492222599⟩,⟨(-1104506681497105669),(-1104506681497104284)⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨349964069792511599,349964069792511732⟩,⟨(-746306717708936197),(-746306717708936065)⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨(-66775256176148515),(-66775256176148479)⟩,⟨(-162703161951674113),(-162703161951674078)⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨(-28547717756131451),(-28547717756131420)⟩,⟨(-9321185414311607),(-9321185414311575)⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨(-3672984622639413),(-3672984622639382)⟩,⟨2261659562430481,2261659562430512⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨(-101086440546672),(-101086440546637)⟩,⟨546890377411933,546890377411966⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨38811228957176,38811228957209⟩,⟨57943526378139,57943526378170⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨8880627447809,8880627447840⟩,⟨2752759005051,2752759005083⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨1387220401287,1387220401316⟩,⟨(-371507373959),(-371507373928)⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨211470887187,211470887211⟩,⟨(-174465305727),(-174465305701)⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨36151621608,36151621630⟩,⟨(-53472178685),(-53472178663)⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨5774161118,5774161135⟩,⟨(-11910155012),(-11910154995)⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨(-390866058871357253819302),(-390866058871329799111063)⟩,⟨(-1149755615511681865404806),(-1149755615511654410606003)⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨(-1457341014033795754803639),(-1457341014033701922550897)⟩,⟨(-2665345920127380444063875),(-2665345920127286611632642)⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨(-2606108914307459848790552),(-2606108914307282049267167)⟩,⟨(-2351010785252271851538363),(-2351010785252094051939839)⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨(-2738676950560615768653841),(-2738676950560386870788344)⟩,⟨(-689022484837646362957927),(-689022484837417465203039)⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨(-1608984790191166541436416),(-1608984790190934781925757)⟩,⟨643266121529659434118444,643266121529891193502609⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨(-361006750089291403173062),(-361006750089059026530509)⟩,⟨770941048134796935229641,770941048135029311873608⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨141379017156152784857471,141379017156276813356282⟩,⟨320033071923053655805223,320033071923177684329038⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨121757659704096444587863,121757659704159647244362⟩,⟨29503272506472353841388,29503272506535556496559⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨31011940560208156853634,31011940560225383041888⟩,⟨(-25991553731697636868404),(-25991553731680410682625)⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨(-452633705601182867808),(-452633705596630680291)⟩,⟨(-12163930538696729803827),(-12163930538692177615983)⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨(-2733298551935456449081),(-2733298551934685245516)⟩,⟨(-2232278504175205177518),(-2232278504174433973806)⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨(-1021742630774715033375),(-1021742630774579924816)⟩,⟨75211991939292522529,75211991939427631063⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨(-233288022650341376249),(-233288022650322949061)⟩,⟨204592771339262309271,204592771339280736440⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨(-33322041231127246057),(-33322041231123145737)⟩,⟨95537324512437940180,95537324512442040501⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨915035659881017714,915035659881887511⟩,⟨34594626840660006705,34594626840660876501⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨1826860361779002184,1826860361779159338⟩,⟨8406919150070158955,8406919150070316110⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨17663171838133888593726572,17663171838133890065004839⟩,⟨73620036710004168863563505,73620036710004170497020283⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨113177609687565922446871899,113177609687565927181878639⟩,⟨158805404496994724655363125,158805404496994729736014786⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨259268112468946696125573660,259268112468946704046192698⟩,⟨17770985330096588486401774,17770985330096596602572320⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨202902746004645594821111002,202902746004645606618030638⟩,⟨(-393582162893704968343046368),(-393582162893704956711519674)⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨(-239720992583103994166375290),(-239720992583103970878128719)⟩,⟨(-723206741464647332799849505),(-723206741464647309897825192)⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨(-758954456812015651484838951),(-758954456812015617033120822)⟩,⟨(-546806138631741424026234995),(-546806138631741389684973132)⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨(-846265961093133155715478745),(-846265961093133118646126183)⟩,⟨(-7181976850564292109068541),(-7181976850564254943432751)⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨(-484644905499695510183611629),(-484644905499695478320619880)⟩,⟨361638952152762170793096383,361638952152762202701112089⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨(-88582469946630912006116337),(-88582469946630887372134934)⟩,⟨351521515235228365986982630,351521515235228390601877163⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨83581728111340929386001994,83581728111340954386005848⟩,⟨172603353143332851661387148,172603353143332876653679395⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨85019100213065442108348491,85019100213065481884080751⟩,⟨39155389923604057747138095,39155389923604097525881931⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨42900038035173537901807157,42900038035173600597462337⟩,⟨(-9600532844012279389419027),(-9600532844012216692122429)⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨14299943882086525975443452,14299943882086623630464012⟩,⟨(-14828463348090201764836199),(-14828463348090104110040594)⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨2785964951916696464532252,2785964951916785756484373⟩,⟨(-9336116184131675068748069),(-9336116184131585777117552)⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨(-203246206420066898818105),(-203246206420012655693037)⟩,⟨(-4378991939098149914763304),(-4378991939098095671807871)⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨(-274367959972251551606752),(-274367959972230769548371)⟩,⟨(-1230342622622555149436018),(-1230342622622534367413990)⟩⟩
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
noncomputable def ans : CBox := ⟨⟨(-267653543590245522507715100),(-267653543590245227718764335)⟩,⟨(-90027859965373872853987825),(-90027859965373578038396597)⟩⟩
lemma checked : cachedMomentRuleBox density1 hk16_1_2 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule true true 16 2) := by
  rw [← checked]
  exact @cached_density_rule_contains density1 hk16_1_2 (tableDensity true) (fullFactor true 16 2) density1_contains hk16_1_2_contains
noncomputable def atomAnswer : CBox := ⟨⟨(-11687523566192264582194088828),(-11687523566192264563530640010)⟩,⟨1658286615930700110389826465,1658286615930700128864282917⟩⟩
lemma atomChecked : tableAtomBox true ha16_1_2 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom true true 16 2) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains true true ha16_1_2 16 2 ha16_1_2_contains
 def realAnswer : RBox := ⟨(-11955177109782510104801803928),(-11955177109782509791149404345)⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment true true 16 2) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm16_1_1_2
namespace hm16_0_1_3
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density0 j i k).mul (hk16_1_3 j i k))
noncomputable def s0_0 : CBox := ⟨⟨(-98),98⟩,⟨(-98),98⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨(-281),281⟩,⟨(-281),281⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨(-469),469⟩,⟨(-469),469⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨(-665),665⟩,⟨(-665),665⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨(-860),860⟩,⟨(-860),860⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨(-1040),1040⟩,⟨(-1040),1040⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨(-1183),1183⟩,⟨(-1183),1183⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨(-1267),1267⟩,⟨(-1267),1267⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨(-1271),1271⟩,⟨(-1271),1271⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨(-1196),1196⟩,⟨(-1196),1196⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨(-1059),1059⟩,⟨(-1059),1059⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨(-877),877⟩,⟨(-877),877⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨(-638),638⟩,⟨(-638),638⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨(-359),359⟩,⟨(-359),359⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨(-214),214⟩,⟨(-214),214⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨(-76),76⟩,⟨(-76),76⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨(-62),62⟩,⟨(-62),62⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨(-168),168⟩,⟨(-168),168⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨(-273),273⟩,⟨(-273),273⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨(-380),380⟩,⟨(-380),380⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨(-479),479⟩,⟨(-479),479⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨(-567),567⟩,⟨(-567),567⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨(-635),635⟩,⟨(-635),635⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨(-679),679⟩,⟨(-679),679⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨(-685),685⟩,⟨(-685),685⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨(-654),654⟩,⟨(-654),654⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨(-589),589⟩,⟨(-589),589⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨(-504),504⟩,⟨(-504),504⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨(-450),450⟩,⟨(-450),450⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨(-363),363⟩,⟨(-363),363⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨(-237),237⟩,⟨(-237),237⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨(-87),87⟩,⟨(-87),87⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨(-70551284011),(-70551283985)⟩,⟨57968830575,57968830600⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨(-115402508741),(-115402508693)⟩,⟨123092526610,123092526656⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨(-51692408979),(-51692408905)⟩,⟨93924595117,93924595193⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨(-5452304023),(-5452303926)⟩,⟨35423604907,35423605004⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨1858007207,1858007331⟩,⟨6768513902,6768514022⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨564876879,564877034⟩,⟨643423420,643423579⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨63243755,63243949⟩,⟨27360861,27361056⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨3923464,3923719⟩,⟨77969,78222⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨166385,166684⟩,⟨(-47265),(-46964)⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨5794,6121⟩,⟨(-3033),(-2703)⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨52,379⟩,⟨(-288),40⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨(-138),249⟩,⟨(-242),146⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨(-170),275⟩,⟨(-237),209⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨(-138),220⟩,⟨(-193),165⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨(-126),149⟩,⟨(-143),134⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨(-58),58⟩,⟨(-58),58⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨10332769064159154194,10332769064159213528⟩,⟨(-34009013215342620111),(-34009013215342560771)⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨9383296810502205800,9383296810502324330⟩,⟨(-78481842688105955339),(-78481842688105836799)⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨(-16237174995221978972),(-16237174995221901440)⟩,⟨(-70669339760410439813),(-70669339760410362277)⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨(-27697540533249037036),(-27697540533249015752)⟩,⟨(-31207329762563435153),(-31207329762563413869)⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨(-16262730590200617955),(-16262730590200615438)⟩,⟨(-3445081742528343404),(-3445081742528340888)⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨(-4140051709780821065),(-4140051709780820750)⟩,⟨2479343933843132845,2479343933843133157⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨(-212230667497937150),(-212230667497937054)⟩,⟨1044807337993632590,1044807337993632683⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨117701225205210561,117701225205210652⟩,⟨146444471392142206,146444471392142296⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨27884366143683015,27884366143683103⟩,⟨259425712140233,259425712140323⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨2473722211348582,2473722211348678⟩,⟨(-2775937113269825),(-2775937113269730)⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨(-27053119682404),(-27053119682314)⟩,⟨(-479622405726328),(-479622405726233)⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨(-44266408709492),(-44266408709408)⟩,⟨(-48164201617055),(-48164201616969)⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨(-9876361499326),(-9876361499254)⟩,⟨(-2624878632039),(-2624878631969)⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨(-1928794217050),(-1928794216992)⟩,⟨339815762320,339815762378⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨(-411871171468),(-411871171427)⟩,⟨207516322120,207516322162⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨(-77277318263),(-77277318236)⟩,⟨54410687578,54410687603⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨(-4607335828839968441821800),(-4607335828839917831383290)⟩,⟨2212906523170658190079806,2212906523170708800947637⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨(-10144576716093312283741836),(-10144576716093144489992258)⟩,⟨7414077112651980083081497,7414077112652147877423217⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨(-7707532360201746995901609),(-7707532360201445606060094)⟩,⟨11833786353005170542537053,11833786353005471932009058⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨(-516651380902076559190712),(-516651380901719365952064)⟩,⟨11074829876547951661163224,11074829876548308853024834⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨3985825322758902418832367,3985825322759337493427144⟩,⟨5431425623522359714685072,5431425623522794788627217⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨3295442552587780187358922,3295442552588169495581725⟩,⟨450553150284620781101847,450553150285010089542219⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨1000265796507695813798341,1000265796507925648777791⟩,⟨(-947055960065521317950883),(-947055960065291482823819)⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨(-69891362319996127803938),(-69891362319888429974859)⟩,⟨(-488106220061571869543827),(-488106220061464171752288)⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨(-142457542712232598226945),(-142457542712198165040719)⟩,⟨(-68119583702571629068130),(-68119583702537195892809)⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨(-40693675696441385881259),(-40693675696433526379126)⟩,⟨23736409221152313253660,23736409221160172760536⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨(-1576893473369505541042),(-1576893473367899327628)⟩,⟨13619118102779109680869,13619118102780715894774⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨2710052597513470438229,2710052597513704393995⟩,⟨3052171910275203867587,3052171910275437822934⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨1283536958343155260572,1283536958343196725877⟩,⟨164629360941610075279,164629360941651540510⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨403595162084144984243,403595162084152953997⟩,⟨(-187166298333921185048),(-187166298333913215278)⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨108467691811594529168,108467691811596034293⟩,⟨(-116127435288431843053),(-116127435288430337914)⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨21327582994643668023,21327582994643920252⟩,⟨(-34359708081025954131),(-34359708081025701895)⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨2983065295398792539222915938,2983065295398792578891020229⟩,⟨(-732578500764598152209390910),(-732578500764598112844332775)⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨7376182124995423083393784717,7376182124995423200420731262⟩,⟨(-3361016363896710397985353379),(-3361016363896710281610247800)⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨7430052439262292547187271897,7430052439262292733199556221⟩,⟨(-7531529636354115032280606600),(-7531529636354114846654547465)⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨2709937911709844287505188871,2709937911709844522314115745⟩,⟨(-10152862770784271588816059208),(-10152862770784271353718795920)⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨(-3175241363304767971576523164),(-3175241363304767716419939874)⟩,⟨(-8126730954067109052535752976),(-8126730954067108796757546411)⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨(-5506322945235212335574343002),(-5506322945235212097737808131)⟩,⟨(-2860532920276041885660310380),(-2860532920276041647664674593)⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨(-3645671105222938463469150373),(-3645671105222938274657908087)⟩,⟨1176977450349327951547593584,1176977450349328140229418672⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨(-835751944671315139576835494),(-835751944671315007830431083)⟩,⟨1931837698366076255354604455,1931837698366076387056072286⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨487151968780747884259121930,487151968780747968807677026⟩,⟨944813396200424508106815883,944813396200424592672114574⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨498480394839343197948827893,498480394839343262520636704⟩,⟨106690683337856863039990687,106690683337856927614605541⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨192788214804320443462118793,192788214804320516713364845⟩,⟨(-141324364420027947608499119),(-141324364420027874358158657)⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨19651685403404910123152623,19651685403405025833519577⟩,⟨(-110356809309844373273028616),(-110356809309844257562075977)⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨(-24010629073290536589239344),(-24010629073290373528729713)⟩,⟨(-47395354412864086755556549),(-47395354412863923694825774)⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨(-20859139468940320489554945),(-20859139468940183134242978)⟩,⟨(-14225265645927506821013655),(-14225265645927369465886788)⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨(-10947272126439097227052393),(-10947272126438998933815218)⟩,⟨(-2832798858133953995308794),(-2832798858133855702226577)⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨(-3223176933757789369362112),(-3223176933757750167833999)⟩,⟨(-249724962754371601089428),(-249724962754332399606254)⟩⟩
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
noncomputable def ans : CBox := ⟨⟨1410056293227238009765232217,1410056293227238718123041471⟩,⟨(-4814060319682210613249389973),(-4814060319682209904962980014)⟩⟩
lemma checked : cachedMomentRuleBox density0 hk16_1_3 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule false true 16 3) := by
  rw [← checked]
  exact @cached_density_rule_contains density0 hk16_1_3 (tableDensity false) (fullFactor true 16 3) density0_contains hk16_1_3_contains
noncomputable def atomAnswer : CBox := ⟨⟨(-2084127723324188297278446329),(-2084127723324188279364772258)⟩,⟨(-10678433405629746759049621141),(-10678433405629746740943173324)⟩⟩
lemma atomChecked : tableAtomBox false ha16_1_3 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom false true 16 3) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains false true ha16_1_3 16 3 ha16_1_3_contains
 def realAnswer : RBox := ⟨(-674071430096950287613214112),(-674071430096949561141730787)⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment false true 16 3) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm16_0_1_3
namespace hm16_1_1_3
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density1 j i k).mul (hk16_1_3 j i k))
noncomputable def s0_0 : CBox := ⟨⟨(-24),24⟩,⟨(-24),24⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨(-56),56⟩,⟨(-56),56⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨(-89),89⟩,⟨(-89),89⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨(-122),122⟩,⟨(-122),122⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨(-153),153⟩,⟨(-153),153⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨(-178),178⟩,⟨(-178),178⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨(-194),194⟩,⟨(-194),194⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨(-208),208⟩,⟨(-208),208⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨(-208),208⟩,⟨(-208),208⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨(-203),203⟩,⟨(-203),203⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨(-185),185⟩,⟨(-185),185⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨(-158),158⟩,⟨(-158),158⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨(-115),115⟩,⟨(-115),115⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨(-68),68⟩,⟨(-68),68⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨(-42),42⟩,⟨(-42),42⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨(-21),21⟩,⟨(-21),21⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨(-29),29⟩,⟨(-29),29⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨(-41),41⟩,⟨(-41),41⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨(-54),54⟩,⟨(-54),54⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨(-68),68⟩,⟨(-68),68⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨(-81),81⟩,⟨(-81),81⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨(-96),96⟩,⟨(-96),96⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨(-105),105⟩,⟨(-105),105⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨(-112),112⟩,⟨(-112),112⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨(-112),112⟩,⟨(-112),112⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨(-103),103⟩,⟨(-103),103⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨(-96),96⟩,⟨(-96),96⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨(-87),87⟩,⟨(-87),87⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨(-74),74⟩,⟨(-74),74⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨(-52),52⟩,⟨(-52),52⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨(-24),24⟩,⟨(-24),24⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨(-20423896661),(-20423896643)⟩,⟨2799768200,2799768218⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨(-36840805128),(-36840805100)⟩,⟨9879755245,9879755273⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨(-21213477313),(-21213477276)⟩,⟨11641706836,11641706869⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨(-5356660734),(-5356660696)⟩,⟨5928902621,5928902659⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨(-491439538),(-491439493)⟩,⟨1435942549,1435942592⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨21124902,21124953⟩,⟨175158653,175158705⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨7379281,7379338⟩,⟨11241608,11241661⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨618836,618900⟩,⟨390751,390812⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨30623,30687⟩,⟨6889,6954⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨1155,1221⟩,⟨(-22),46⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨15,74⟩,⟨(-34),28⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨(-22),46⟩,⟨(-32),28⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨(-32),48⟩,⟨(-32),34⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨(-20),35⟩,⟨(-32),32⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨(-22),28⟩,⟨(-26),27⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨(-16),16⟩,⟨(-16),16⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨9565677624005315348,9565677624005365128⟩,⟨(-7049577868495110961),(-7049577868495061179)⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨17994875336940084982,17994875336940184352⟩,⟨(-18834456904317149291),(-18834456904317049924)⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨9491089238873786234,9491089238873851109⟩,⟨(-21225572136733691949),(-21225572136733627075)⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨(-1056795826884478319),(-1056795826884460587)⟩,⟨(-12856325588364336039),(-12856325588364318309)⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨(-3297829173251727272),(-3297829173251725215)⟩,⟨(-3691776982460220223),(-3691776982460218164)⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨(-1391170416851215337),(-1391170416851215114)⟩,⟨(-107826405143473522),(-107826405143473299)⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨(-217859868350176521),(-217859868350176480)⟩,⟨209694974337013985,209694974337014029⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨4114632860925974,4114632860926014⟩,⟨52354323403109343,52354323403109388⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨6307755618218372,6307755618218414⟩,⟨4378115788772345,4378115788772386⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨977117192997874,977117192997916⟩,⟨(-247159962034862),(-247159962034820)⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨65244867047289,65244867047334⟩,⟨(-110819864337239),(-110819864337198)⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨(-2856799862050),(-2856799862013)⟩,⟨(-17185694044049),(-17185694044010)⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨(-1843549175234),(-1843549175196)⟩,⟨(-2011956644004),(-2011956643970)⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨(-487466100237),(-487466100207)⟩,⟨(-199779718909),(-199779718878)⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨(-124462341190),(-124462341166)⟩,⟨(-11737039177),(-11737039152)⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨(-25703408533),(-25703408514)⟩,⟨1374175773,1374175793⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨(-1474445385189475893773142),(-1474445385189434390740800)⟩,⟨803674198620458329330568,803674198620499832271046⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨(-3290253399831527672346117),(-3290253399831389992378286)⟩,⟨2629389868223623991391407,2629389868223761671205356⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨(-2578635354717675904202438),(-2578635354717428432366968)⟩,⟨4157253946446358614763657,4157253946446606086616993⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨(-239737410069737837866696),(-239737410069444406855354)⟩,⟨3959338326136380672296494,3959338326136674103553027⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨1338109560833928919333776,1338109560834286508130987⟩,⟨2062099509602568089901717,2062099509602925678834386⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨1189495054720465102209803,1189495054720785134970857⟩,⟨280509216257581588705185,280509216257901621430451⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨409933913473287919631061,409933913473476831951664⟩,⟨(-301950613405748108262990),(-301950613405559195973440)⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨980059638330574426593,980059638419062512015⟩,⟨(-185019568785618466827685),(-185019568785529978734935)⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨(-49157100062505907913729),(-49157100062477638683108)⟩,⟨(-35592826748025195482198),(-35592826747996926249216)⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨(-17726681816653255192499),(-17726681816646809118534)⟩,⟨5442952932691389588578,5442952932697835661620⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨(-2177747016736652800276),(-2177747016735337167423)⟩,⟨5004417729484647438196,5004417729485963070952⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨566693502422854149986,566693502423045514663⟩,⟨1503332676913922457441,1503332676914113822192⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨419144736372977110631,419144736373010978962⟩,⟨258620515643105789964,258620515643139658308⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨162099519300682191927,162099519300688693685⟩,⟨4666669002488861114,4666669002495362872⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨52657696252142438397,52657696252143664993⟩,⟨(-18592663439422524919),(-18592663439421298320)⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨12019170894642085115,12019170894642290525⟩,⟨(-7044266877006740075),(-7044266877006534664)⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨87546308611762149765383545,87546308611762151800885143⟩,⟨(-25930533440917549623131101),(-25930533440917547768481305)⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨184182915160918036847203801,184182915160918043184409331⟩,⟨(-147080538363685018159923412),(-147080538363685012195955886)⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨2919561678647789717685882,2919561678647799865889531⟩,⟨(-315492985770623540325444492),(-315492985770623530347822077)⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨(-496487349669481949673724247),(-496487349669481935002163317)⟩,⟨(-216080806231669556524034188),(-216080806231669541582164208)⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨(-868322101674774903845073258),(-868322101674774874255918303)⟩,⟨360024839390834892348314053,360024839390834922423672061⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨(-601920960794444090798648437),(-601920960794444045657359946)⟩,⟨998708986071323650718051491,998708986071323695955085019⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨89150657164256169195305697,89150657164256218698165743⟩,⟨1063589798310290926722807467,1063589798310290976082628063⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨523144447033319226133613384,523144447033319269367812454⟩,⟨568126898628701861694582023,568126898628701904886329918⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨465020370727726243500296206,465020370727726276863126174⟩,⟨61859765703204500034508383,61859765703204533428413138⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨210758271612001736067309491,210758271612001770562738939⟩,⟨(-137191120909227889862855770),(-137191120909227855360664683)⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨36085811559572159759145242,36085811559572210447014264⟩,⟨(-118966722802274711403049392),(-118966722802274660720470574)⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨(-21217285040094639264123999),(-21217285040094549299039551)⟩,⟨(-55137984426477963742010744),(-55137984426477873778591918)⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨(-22903570163289073806258075),(-22903570163288942768383679)⟩,⟨(-16054198254056937494931704),(-16054198254056806456486179)⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨(-13229644599970174477468108),(-13229644599970063227478118)⟩,⟨(-1691566675048472176822732),(-1691566675048360926286997)⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨(-5897760531083984278400728),(-5897760531083904347872275)⟩,⟨1281834756062656087860800,1281834756062736018594069⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨(-1610268912613885403447925),(-1610268912613853465814829)⟩,⟨660984538192309047747837,660984538192340985415312⟩⟩
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
noncomputable def ans : CBox := ⟨⟨(-72915494768919334188159269),(-72915494768918921738264243)⟩,⟨339001412905847388041749360,339001412905847800487382190⟩⟩
lemma checked : cachedMomentRuleBox density1 hk16_1_3 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule true true 16 3) := by
  rw [← checked]
  exact @cached_density_rule_contains density1 hk16_1_3 (tableDensity true) (fullFactor true 16 3) density1_contains hk16_1_3_contains
noncomputable def atomAnswer : CBox := ⟨⟨2725397792039323134553932954,2725397792039323157979506738⟩,⟨13964105222746591892002611270,13964105222746591915680273800⟩⟩
lemma atomChecked : tableAtomBox true ha16_1_3 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom true true 16 3) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains true true ha16_1_3 16 3 ha16_1_3_contains
 def realAnswer : RBox := ⟨2652482297270403800265773685,2652482297270404236341242495⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment true true 16 3) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm16_1_1_3
namespace hm16_0_1_4
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density0 j i k).mul (hk16_1_4 j i k))
noncomputable def s0_0 : CBox := ⟨⟨(-200),200⟩,⟨(-200),200⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨(-573),573⟩,⟨(-573),573⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨(-904),904⟩,⟨(-904),904⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨(-1158),1158⟩,⟨(-1158),1158⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨(-1501),1501⟩,⟨(-1501),1501⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨(-1977),1977⟩,⟨(-1977),1977⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨(-2424),2424⟩,⟨(-2424),2424⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨(-2753),2753⟩,⟨(-2753),2753⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨(-2894),2894⟩,⟨(-2894),2894⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨(-2809),2809⟩,⟨(-2809),2809⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨(-2524),2524⟩,⟨(-2524),2524⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨(-2094),2094⟩,⟨(-2094),2094⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨(-1514),1514⟩,⟨(-1514),1514⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨(-834),834⟩,⟨(-834),834⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨(-487),487⟩,⟨(-487),487⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨(-165),165⟩,⟨(-165),165⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨(-222),222⟩,⟨(-222),222⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨(-352),352⟩,⟨(-352),352⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨(-510),510⟩,⟨(-510),510⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨(-705),705⟩,⟨(-705),705⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨(-922),922⟩,⟨(-922),922⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨(-1145),1145⟩,⟨(-1145),1145⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨(-1347),1347⟩,⟨(-1347),1347⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨(-1500),1500⟩,⟨(-1500),1500⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨(-1565),1565⟩,⟨(-1565),1565⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨(-1527),1527⟩,⟨(-1527),1527⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨(-1380),1380⟩,⟨(-1380),1380⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨(-1142),1142⟩,⟨(-1142),1142⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨(-848),848⟩,⟨(-848),848⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨(-521),521⟩,⟨(-521),521⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨(-181),181⟩,⟨(-181),181⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨124103916746,124103916780⟩,⟨49003502169,49003502203⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨240141261706,240141261785⟩,⟨59359332515,59359332591⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨158191700370,158191700502⟩,⟨(-2446535981),(-2446535849)⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨49649148997,49649149174⟩,⟨(-19674348347),(-19674348169)⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨7281349929,7281350155⟩,⟨(-7691291514),(-7691291285)⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨371892991,371893277⟩,⟨(-1257892828),(-1257892540)⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨(-18728281),(-18727931)⟩,⟨(-105762411),(-105762059)⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨(-3450179),(-3449726)⟩,⟨(-5191011),(-5190557)⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨(-220972),(-220455)⟩,⟨(-173032),(-172514)⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨(-10030),(-9480)⟩,⟨(-5178),(-4634)⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨(-650),(-130)⟩,⟨(-415),112⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨(-420),177⟩,⟨(-316),281⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨(-409),250⟩,⟨(-381),277⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨(-320),188⟩,⟨(-291),219⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨(-210),170⟩,⟨(-200),181⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨(-78),78⟩,⟨(-78),78⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨(-43228198993493228562),(-43228198993493139884)⟩,⟨984205644612653568,984205644612742237⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨(-94486560497608834869),(-94486560497608668602)⟩,⟨19332321950308768986,19332321950308935250⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨(-75751418077703905429),(-75751418077703807509)⟩,⟨46730528232736634002,46730528232736731918⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨(-25182096413630283457),(-25182096413630260182)⟩,⟨45117226345413585892,45117226345413609175⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨2876614147321918899,2876614147321922416⟩,⟨20620451442736997234,20620451442737000754⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨4802271950981694936,4802271950981695300⟩,⟨3804857711129612026,3804857711129612394⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨1353455382140613700,1353455382140613802⟩,⟨(-241406718498071413),(-241406718498071311)⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨118072276438201676,118072276438201772⟩,⟨(-216287997053108923),(-216287997053108829)⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨(-14596833245374098),(-14596833245373998)⟩,⟨(-34248140894713816),(-34248140894713718)⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨(-4832108416088359),(-4832108416088246)⟩,⟨(-1480492032050951),(-1480492032050833)⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨(-581471382789165),(-581471382789040)⟩,⟨321371232996798,321371232996921⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨(-32575960376834),(-32575960376715)⟩,⟨85967898878567,85967898878685⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨3182813201004,3182813201108⟩,⟨14211686640418,14211686640522⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨1744910603021,1744910603107⟩,⟨2218678819812,2218678819894⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨551553513347,551553513406⟩,⟨380270003362,380270003424⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨123973551856,123973551886⟩,⟨60267596510,60267596541⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨3076162128824371499052799,3076162128824426922607479⟩,⟨4316978267127870532850773,4316978267127925956157134⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨9418115566341361542037251,9418115566341540372260843⟩,⟨9056273496563709312717797,9056273496563888142828026⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨13605717088899694952834627,13605717088899999518072680⟩,⟨5728439980496360454474966,5728439980496665020667408⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨11565486433318292172130579,11565486433318651054620021⟩,⟨(-1622837410129249231964153),(-1622837410128890347801337)⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨4845684002818094512950803,4845684002818587052717856⟩,⟨(-5281495289308315921862494),(-5281495289307823381708460)⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨(-252360441500904033450700),(-252360441500513672743637)⟩,⟨(-3572249846250471835307128),(-3572249846250081474975539)⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨(-1246000266805963383890751),(-1246000266805691523552250)⟩,⟨(-841130849244332819549766),(-841130849244060959305790)⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨(-508237810119623297647423),(-508237810119510658470171)⟩,⟨199876846974537455053200,199876846974650094289912⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨(-35188142964339336579783),(-35188142964298467801305)⟩,⟨174093389867937446347634,174093389867978315129269⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨38188070416799341965805,38188070416807872954257⟩,⟨37926247954643182950419,37926247954651713932640⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨15699847299436898611782,15699847299438796828039⟩,⟨(-2521092139258200778718),(-2521092139256302562148)⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨2540038012823962767819,2540038012824222115120⟩,⟨(-4073265254885778248838),(-4073265254885518900996)⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨(-261410532970593733691),(-261410532970541359904)⟩,⟨(-1518128958063078670578),(-1518128958063026296784)⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨(-361021680233431257287),(-361021680233422672900)⟩,⟨(-394520261928144421617),(-394520261928135837279)⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨(-174136521287635782096),(-174136521287634129560)⟩,⟨(-81621191839317286177),(-81621191839315633661)⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨(-47715105671858868929),(-47715105671858502322)⟩,⟨(-11644420498693982813),(-11644420498693616210)⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨(-803245486390737031852580028),(-803245486390736994925379896)⟩,⟨(-2659745236754976613947822381),(-2659745236754976576762602503)⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨(-3407373318575706762991237993),(-3407373318575706653495797881)⟩,⟨(-6511010277277341781478163142),(-6511010277277341671444242770)⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨(-7244566100377142833783862301),(-7244566100377142658111553980)⟩,⟨(-6352488899985117348724022529),(-6352488899985117172783543150)⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨(-9449961478813862969748313272),(-9449961478813862745381658687)⟩,⟨(-1876791138051008566191133985),(-1876791138051008342172321369)⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨(-7283192697161825329263315007),(-7283192697161825082363682714)⟩,⟨3473323484401583336661567492,3473323484401583582983732647⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨(-2244171262667071697874346494),(-2244171262667071465264851508)⟩,⟨5346121326664885284889639673,5346121326664885517393873757⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨1424679952514526153481358346,1424679952514526340295970106⟩,⟨3329779389690996745077948154,3329779389690996932031212076⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨1922210044701668785586487101,1922210044701668917790107172⟩,⟨605503168572918149278907777,605503168572918281514052245⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨856575810542486705156575837,856575810542486790830130805⟩,⟨(-574438318278453818128458790),(-574438318278453732474283090)⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨42385985200461954540382210,42385985200462020496179087⟩,⟨(-499432774487228099274446013),(-499432774487228033320225831)⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨(-165694985433571888932124133),(-165694985433571816953981307)⟩,⟨(-170958671287431203576425206),(-170958671287431131597324140)⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨(-112926743186596409068024789),(-112926743186596286383773294)⟩,⟨(-3272621838921093320480951),(-3272621838920970636740726)⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨(-43879427675250645149651989),(-43879427675250484928337934)⟩,⟨31647952288699194454886826,31647952288699354676139551⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨(-10939953407685834128294558),(-10939953407685699420383378)⟩,⟨23500132538097021586840089,23500132538097156294992504⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨(-998049606149249748471918),(-998049606149137192827926)⟩,⟨11633643231881751580861976,11633643231881864136637499⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨310166258967252089762947,310166258967295629998821⟩,⟨3333650499323508653025542,3333650499323552193296240⟩⟩
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
noncomputable def ans : CBox := ⟨⟨(-4413377135227447825327546193),(-4413377135227447098822866010)⟩,⟨(-969184629902279175236352826),(-969184629902278448700613457)⟩⟩
lemma checked : cachedMomentRuleBox density0 hk16_1_4 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule false true 16 4) := by
  rw [← checked]
  exact @cached_density_rule_contains density0 hk16_1_4 (tableDensity false) (fullFactor true 16 4) density0_contains hk16_1_4_contains
noncomputable def atomAnswer : CBox := ⟨⟨(-9542416176891382681399456729),(-9542416176891382664171312939)⟩,⟨2381030217449562188341065402,2381030217449562205380829250⟩⟩
lemma atomChecked : tableAtomBox false ha16_1_4 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom false true 16 4) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains false true ha16_1_4 16 4 ha16_1_4_contains
 def realAnswer : RBox := ⟨(-13955793312118830506827002922),(-13955793312118829762894178949)⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment false true 16 4) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm16_0_1_4
namespace hm16_1_1_4
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density1 j i k).mul (hk16_1_4 j i k))
noncomputable def s0_0 : CBox := ⟨⟨(-42),42⟩,⟨(-42),42⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨(-107),107⟩,⟨(-107),107⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨(-165),165⟩,⟨(-165),165⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨(-208),208⟩,⟨(-208),208⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨(-261),261⟩,⟨(-261),261⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨(-332),332⟩,⟨(-332),332⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨(-392),392⟩,⟨(-392),392⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨(-439),439⟩,⟨(-439),439⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨(-464),464⟩,⟨(-464),464⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨(-463),463⟩,⟨(-463),463⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨(-432),432⟩,⟨(-432),432⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨(-367),367⟩,⟨(-367),367⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨(-267),267⟩,⟨(-267),267⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨(-148),148⟩,⟨(-148),148⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨(-87),87⟩,⟨(-87),87⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨(-34),34⟩,⟨(-34),34⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨(-18),18⟩,⟨(-18),18⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨(-35),35⟩,⟨(-35),35⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨(-51),51⟩,⟨(-51),51⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨(-71),71⟩,⟨(-71),71⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨(-97),97⟩,⟨(-97),97⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨(-129),129⟩,⟨(-129),129⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨(-165),165⟩,⟨(-165),165⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨(-202),202⟩,⟨(-202),202⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨(-232),232⟩,⟨(-232),232⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨(-253),253⟩,⟨(-253),253⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨(-256),256⟩,⟨(-256),256⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨(-246),246⟩,⟨(-246),246⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨(-212),212⟩,⟨(-212),212⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨(-164),164⟩,⟨(-164),164⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨(-104),104⟩,⟨(-104),104⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨(-40),40⟩,⟨(-40),40⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨18065672722,18065672744⟩,⟨24104831162,24104831184⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨39041868504,39041868537⟩,⟨40034624432,40034624467⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨30437316166,30437316218⟩,⟨18674450528,18674450580⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨11657434825,11657434887⟩,⟨2421057493,2421057554⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨2237347542,2237347614⟩,⟨(-488701394),(-488701322)⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨209678438,209678519⟩,⟨(-170535849),(-170535766)⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨8284565,8284650⟩,⟨(-19251264),(-19251177)⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨(-50321),(-50222)⟩,⟨(-1161287),(-1161188)⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨(-20287),(-20184)⟩,⟨(-46749),(-46647)⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨(-1232),(-1131)⟩,⟨(-1618),(-1519)⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨(-98),(-7)⟩,⟨(-98),(-8)⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨(-64),28⟩,⟨(-58),36⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨(-60),42⟩,⟨(-64),32⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨(-48),32⟩,⟨(-49),32⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨(-33),31⟩,⟨(-34),30⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨(-18),18⟩,⟨(-18),18⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨(-11781944641109893526),(-11781944641109819100)⟩,⟨(-8375094875834345414),(-8375094875834270990)⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨(-28732437188870550461),(-28732437188870411031)⟩,⟨(-13589974025558170865),(-13589974025558031434)⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨(-28414594849380083713),(-28414594849380001754)⟩,⟨(-2667440109356566605),(-2667440109356484649)⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨(-14598964124533204155),(-14598964124533184760)⟩,⟨6481381152030607037,6481381152030626428⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨(-2941521706639703470),(-2941521706639700580)⟩,⟨5457309735614608660,5457309735614611547⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨496052161763357354,496052161763357621⟩,⟨1700638888929754629,1700638888929754894⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨354810576941971407,354810576941971457⟩,⟨161692591552121951,161692591552122002⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨61329353827692858,61329353827692900⟩,⟨(-31346843285814159),(-31346843285814115)⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨1981944703165876,1981944703165923⟩,⟨(-10057368348889900),(-10057368348889857)⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨(-859598126040921),(-859598126040869)⟩,⟨(-1066643192982662),(-1066643192982611)⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨(-177229267020052),(-177229267019998)⟩,⟨(-14841915296712),(-14841915296657)⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨(-19782053922432),(-19782053922381)⟩,⟨14425315322033,14425315322087⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨(-1329671652178),(-1329671652130)⟩,⟨3654588085058,3654588085105⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨78138260246,78138260287⟩,⟨755228607078,755228607119⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨71795128108,71795128143⟩,⟨166803207712,166803207743⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨19886293202,19886293225⟩,⟨31843070501,31843070525⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨1082029951716895273609978,1082029951716940725433065⟩,⟨1364638720896385686035556,1364638720896431137915728⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨3284866007577177546965469,3284866007577324280564387⟩,⟨2896882580071819732649562,2896882580071966466304187⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨4755920993185731062184508,4755920993185981123752761⟩,⟨1879736108613376310467803,1879736108613626371888134⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨4145692280357742263051569,4145692280358037066782693⟩,⟨(-523180647446567722871971),(-523180647446272919454618)⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨1876029090578920226702853,1876029090579325053135943⟩,⟨(-1822408443580547909068475),(-1822408443580143082718188)⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨33175973732796252213319,33175973733117143213367⟩,⟨(-1315470852080757404526016),(-1315470852080436513454403)⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨(-418848015426399746531209),(-418848015426176288099733)⟩,⟨(-365162754604297515048544),(-365162754604074056596751)⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨(-199672781242578053470942),(-199672781242485506567248)⟩,⟨46156558575565605546353,46156558575658152437570⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨(-25329581405169147781502),(-25329581405135594251574)⟩,⟨63397244646623210965922,63397244646656764495099⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨11230218354883011344447,11230218354890007878168⟩,⟨17965829642893792347603,17965829642900788882581⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨6271911020149352287878,6271911020150907140043⟩,⟨858452909166661522351,858452909168216374459⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨1507077912264873344961,1507077912265085469004⟩,⟨(-1139795621820667943183),(-1139795621820455819244)⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨147793525004159595990,147793525004202376380⟩,⟨(-567368558472393993976),(-567368558472351213591)⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨(-53503233952924710789),(-53503233952917707635)⟩,⟨(-187445428595911602648),(-187445428595904599483)⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨(-41030515334737111958),(-41030515334735765262)⟩,⟨(-53704828968654933551),(-53704828968653586855)⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨(-12669692436286393335),(-12669692436286094710)⟩,⟨(-11213951737954204804),(-11213951737953906178)⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨(-27576323578674888370928550),(-27576323578674886625363416)⟩,⟨(-77846436150511506234025755),(-77846436150511504338679892)⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨(-142255363128287889595031248),(-142255363128287883986212526)⟩,⟨(-159428098471780856710287194),(-159428098471780850804546897)⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨(-286925838839650260747390636),(-286925838839650251363926152)⟩,⟨14339231463964529519313606,14339231463964538996685245⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨(-167939389225700759320946995),(-167939389225700745200727832)⟩,⟨467332568748534530292619083,467332568748534544103554373⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨390843531094964595232197909,390843531094964624192379204⟩,⟨777042050626488319812472915,777042050626488348325954610⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨976663498624394222740161743,976663498624394266898062818⟩,⟨484434570306381498821013131,484434570306381542929020488⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨993999531570413273610709663,993999531570413322415286277⟩,⟨(-176526181457404239985568035),(-176526181457404191030430548)⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨489694726306780031497906714,489694726306780074831322813⟩,⟨(-554484661029566411496651609),(-554484661029566368137162111)⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨8019855904559319097146605,8019855904559352771612768⟩,⟨(-455235161804644243979032417),(-455235161804644210339282491)⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨(-159922133774439191210789161),(-159922133774439156127175513)⟩,⟨(-188662391742427746483697807),(-188662391742427711403475663)⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨(-122306621048538004225452317),(-122306621048537954961298535)⟩,⟨(-19411572078508308367846445),(-19411572078508259097473783)⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨(-51837586778307014130608544),(-51837586778306918701858858)⟩,⟨29304994769524419901403064,29304994769524515331198227⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨(-12528342106916781979967396),(-12528342106916653389052621)⟩,⟨25578414509242072556938903,25578414509242201147028777⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨488175930850156325537763,488175930850265348025494⟩,⟨13684689606882873407053739,13684689606882982428934833⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨2321189092925772176270000,2321189092925863738716283⟩,⟨5783776446731535145397834,5783776446731626707690946⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨956960943439683489231014,956960943439718966617598⟩,⟨1527711090316676185450932,1527711090316711662817876⟩⟩
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
noncomputable def ans : CBox := ⟨⟨317708116524651969462445007,317708116524652402022553780⟩,⟨31612491204753997703078817,31612491204754430242948730⟩⟩
lemma checked : cachedMomentRuleBox density1 hk16_1_4 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule true true 16 4) := by
  rw [← checked]
  exact @cached_density_rule_contains density1 hk16_1_4 (tableDensity true) (fullFactor true 16 4) density1_contains hk16_1_4_contains
noncomputable def atomAnswer : CBox := ⟨⟨12478544231319500406993255382,12478544231319500429522366492⟩,⟨(-3113654899741735191651853635),(-3113654899741735169369085525)⟩⟩
lemma atomChecked : tableAtomBox true ha16_1_4 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom true true 16 4) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains true true ha16_1_4 16 4 ha16_1_4_contains
 def realAnswer : RBox := ⟨12796252347844152376355700389,12796252347844152831644920272⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment true true 16 4) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm16_1_1_4
namespace hm16_0_1_5
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density0 j i k).mul (hk16_1_5 j i k))
noncomputable def s0_0 : CBox := ⟨⟨(-392),392⟩,⟨(-392),392⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨(-1159),1159⟩,⟨(-1159),1159⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨(-1894),1894⟩,⟨(-1894),1894⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨(-2552),2552⟩,⟨(-2552),2552⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨(-3046),3046⟩,⟨(-3046),3046⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨(-3252),3252⟩,⟨(-3252),3252⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨(-3577),3577⟩,⟨(-3577),3577⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨(-4477),4477⟩,⟨(-4477),4477⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨(-5052),5052⟩,⟨(-5052),5052⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨(-5141),5141⟩,⟨(-5141),5141⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨(-4743),4743⟩,⟨(-4743),4743⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨(-3980),3980⟩,⟨(-3980),3980⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨(-2872),2872⟩,⟨(-2872),2872⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨(-1563),1563⟩,⟨(-1563),1563⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨(-899),899⟩,⟨(-899),899⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨(-296),296⟩,⟨(-296),296⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨(-142),142⟩,⟨(-142),142⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨(-415),415⟩,⟨(-415),415⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨(-698),698⟩,⟨(-698),698⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨(-990),990⟩,⟨(-990),990⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨(-1279),1279⟩,⟨(-1279),1279⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨(-1534),1534⟩,⟨(-1534),1534⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨(-1710),1710⟩,⟨(-1710),1710⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨(-1770),1770⟩,⟨(-1770),1770⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨(-1771),1771⟩,⟨(-1771),1771⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨(-2079),2079⟩,⟨(-2079),2079⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨(-2286),2286⟩,⟨(-2286),2286⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨(-2270),2270⟩,⟨(-2270),2270⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨(-2024),2024⟩,⟨(-2024),2024⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨(-1582),1582⟩,⟨(-1582),1582⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨(-1005),1005⟩,⟨(-1005),1005⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨(-349),349⟩,⟨(-349),349⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨(-20352511245),(-20352511204)⟩,⟨(-154642774761),(-154642774722)⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨(-76971199379),(-76971199288)⟩,⟨(-279731529348),(-279731529255)⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨(-95076545175),(-95076545019)⟩,⟨(-160768432177),(-160768432019)⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨(-50155959478),(-50155959275)⟩,⟨(-39207012125),(-39207011919)⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨(-12495975085),(-12495974829)⟩,⟨(-2704319043),(-2704318786)⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨(-1547041707),(-1547041391)⟩,⟨437225793,437226099⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨(-97180932),(-97180569)⟩,⟨92158848,92159217⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨(-2920288),(-2919849)⟩,⟨7360618,7361065⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨(-12298),(-11792)⟩,⟨362699,363211⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨2419,3033⟩,⟨13857,14474⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨(-167),509⟩,⟨205,867⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨(-339),520⟩,⟨(-284),568⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨(-496),533⟩,⟨(-385),646⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨(-398),451⟩,⟨(-321),528⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨(-325),343⟩,⟨(-305),364⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨(-136),136⟩,⟨(-136),136⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨14052779583560946017,14052779583561039736⟩,⟨39664858390854425260,39664858390854518982⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨46993128674003521044,46993128674003687934⟩,⟨81575764317425163933,81575764317425330821⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨67345780272527916940,67345780272528005677⟩,⟨55711236618561156044,55711236618561244773⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨50419441825787076998,50419441825787098333⟩,⟨8822316175084390604,8822316175084411933⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨18445295197767027624,18445295197767031467⟩,⟨(-9743861851874838595),(-9743861851874834752)⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨1891402673835500299,1891402673835500648⟩,⟨(-5928752524465035785),(-5928752524465035438)⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨(-745491373183231274),(-745491373183231154)⟩,⟨(-1206542620819247943),(-1206542620819247823)⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨(-257111205671271881),(-257111205671271758)⟩,⟨(-27239650947086482),(-27239650947086358)⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨(-27267688410783133),(-27267688410783006)⟩,⟨28939713135753077,28939713135753205⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨730501457487361,730501457487511⟩,⟨5446533037547580,5446533037547729⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨599396236911990,599396236912144⟩,⟨425471965926375,425471965926528⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨102808497195616,102808497195759⟩,⟨(-10642365169070),(-10642365168925)⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨12694872699007,12694872699135⟩,⟨(-10702202187081),(-10702202186952)⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨1304129720518,1304129720623⟩,⟨(-2981696271335),(-2981696271233)⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨80151562708,80151562776⟩,⟨(-774390496763),(-774390496691)⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨(-8414982817),(-8414982780)⟩,⟨(-160621501557),(-160621501522)⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨3094078975711152444829349,3094078975711199516802268⟩,⟨(-3125592751048655934485037),(-3125592751048608862473771)⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨6064919826342941686876419,6064919826343089580608156⟩,⟨(-9019902408432995167816660),(-9019902408432847274406821)⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨2690503605599607995193141,2690503605599845773067819⟩,⟨(-12048427023089077869642324),(-12048427023088840093012094)⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨(-3146733137755118158374420),(-3146733137754807020349999)⟩,⟨(-9325240437065721963468979),(-9325240437065410826793496)⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨(-5210325169854008322286696),(-5210325169853579855970778)⟩,⟨(-3173347954250383355786988),(-3173347954249954889527972)⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨(-2967062824863518673717352),(-2967062824863195804200080)⟩,⟨843431385378501897240424,843431385378824767147919⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨(-480557424578047366914359),(-480557424577801738738222)⟩,⟨1221417994727234534704912,1221417994727480162899922⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨276101749501022537586271,276101749501119612445658⟩,⟨397403636253383665155118,397403636253480739956689⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨159646703530142871000375,159646703530179349692568⟩,⟨(-7541135808225466362337),(-7541135808188987664627)⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨24489997403660935686552,24489997403668945523039⟩,⟨(-42660694732848731612175),(-42660694732840721770893)⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨(-6200509468738761291468),(-6200509468737094785281)⟩,⟨(-13387341258144695020603),(-13387341258143028515493)⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨(-4352268627572505284873),(-4352268627572236086862)⟩,⟨(-1206589523465941699391),(-1206589523465672501732)⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨(-1308890094743805179468),(-1308890094743756816137)⟩,⟨662606534450988848632,662606534451037212036⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨(-256790680026337106217),(-256790680026329784889)⟩,⟨445561001077762353551,445561001077769674939⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨(-23272463875360651709),(-23272463875358724871)⟩,⟨184741916787393918142,184741916787395844995⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨3660795950062128109,3660795950062527427⟩,⟨47580017356295192741,47580017356295592064⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨(-1891478557201777868657727333),(-1891478557201777840879721716)⟩,⟨681389721504351237924403742,681389721504351265528354458⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨(-4580416458400273463332643431),(-4580416458400273380907321760)⟩,⟨2725245793295427676753807624,2725245793295427758828897445⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨(-4310496322235603635763519387),(-4310496322235603503250730362)⟩,⟨5540877975294708074161944597,5540877975294708206541719328⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨(-924930356811254652740634186),(-924930356811254482694593451)⟩,⟨7005944438236408404563843600,7005944438236408574925059005⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨2953476120156022847504114233,2953476120156023036512329370⟩,⟨5188091055276603455829912354,5188091055276603645255320354⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨4119978939886587273311471026,4119978939886587453661778296⟩,⟨1345821274591514553950136138,1345821274591514734345702573⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨2408682402282733521840460038,2408682402282733668493094021⟩,⟨(-1304399083969573596482107004),(-1304399083969573449942759944)⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨309698257220923646095592185,309698257220923750999526582⟩,⟨(-1512285609214692521397561357),(-1512285609214692416508625242)⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨(-519035722178795939123027158),(-519035722178795870518863939)⟩,⟨(-609457087267900748983777322),(-609457087267900680362920797)⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨(-393923995386629523637775017),(-393923995386629470641031381)⟩,⟨16375067996303942363586287,16375067996303995360660888⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨(-116878051909309781522928488),(-116878051909309723795610992)⟩,⟨149415701814764041421291716,149415701814764099147839172⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨10750863505640821399327323,10750863505640923051788561⟩,⟨90453365516884098350687411,90453365516884200003462793⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨31020062315682454272054500,31020062315682576851560770⟩,⟨31307595238706467021484520,31307595238706589600897596⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨20503204066155774020784465,20503204066155889777864700⟩,⟨5737486202302618208319240,5737486202302733965195518⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨9613077568587111697596002,9613077568587211204667844⟩,⟨(-790576936042131580031077),(-790576936042032073038546)⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨2678603778020794616272048,2678603778020832085770771⟩,⟨(-720808807329863971094126),(-720808807329826501612614)⟩⟩
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
noncomputable def ans : CBox := ⟨⟨(-478377468498897885055034059),(-478377468498897289325980116)⟩,⟨3219785460807603275951979993,3219785460807603871681974203⟩⟩
lemma checked : cachedMomentRuleBox density0 hk16_1_5 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule false true 16 5) := by
  rw [← checked]
  exact @cached_density_rule_contains density0 hk16_1_5 (tableDensity false) (fullFactor true 16 5) density0_contains hk16_1_5_contains
noncomputable def atomAnswer : CBox := ⟨⟨2076588709020843281356357297,2076588709020843294326252487⟩,⟨6802590184860043382346512249,6802590184860043395460968739⟩⟩
lemma atomChecked : tableAtomBox false ha16_1_5 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom false true 16 5) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains false true ha16_1_5 16 5 ha16_1_5_contains
 def realAnswer : RBox := ⟨1598211240521945396201323238,1598211240521946005100272371⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment false true 16 5) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm16_0_1_5
namespace hm16_1_1_5
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density1 j i k).mul (hk16_1_5 j i k))
noncomputable def s0_0 : CBox := ⟨⟨(-74),74⟩,⟨(-74),74⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨(-208),208⟩,⟨(-208),208⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨(-336),336⟩,⟨(-336),336⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨(-451),451⟩,⟨(-451),451⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨(-524),524⟩,⟨(-524),524⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨(-540),540⟩,⟨(-540),540⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨(-576),576⟩,⟨(-576),576⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨(-711),711⟩,⟨(-711),711⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨(-809),809⟩,⟨(-809),809⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨(-848),848⟩,⟨(-848),848⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨(-805),805⟩,⟨(-805),805⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨(-691),691⟩,⟨(-691),691⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨(-500),500⟩,⟨(-500),500⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨(-272),272⟩,⟨(-272),272⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨(-158),158⟩,⟨(-158),158⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨(-56),56⟩,⟨(-56),56⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨(-25),25⟩,⟨(-25),25⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨(-59),59⟩,⟨(-59),59⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨(-93),93⟩,⟨(-93),93⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨(-131),131⟩,⟨(-131),131⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨(-171),171⟩,⟨(-171),171⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨(-209),209⟩,⟨(-209),209⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨(-243),243⟩,⟨(-243),243⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨(-256),256⟩,⟨(-256),256⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨(-270),270⟩,⟨(-270),270⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨(-332),332⟩,⟨(-332),332⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨(-382),382⟩,⟨(-382),382⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨(-400),400⟩,⟨(-400),400⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨(-369),369⟩,⟨(-369),369⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨(-300),300⟩,⟨(-300),300⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨(-197),197⟩,⟨(-197),197⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨(-72),72⟩,⟨(-72),72⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨14381786312,14381786334⟩,⟨(-32143053159),(-32143053134)⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨18572916369,18572916408⟩,⟨(-62901585258),(-62901585219)⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨1337474196,1337474255⟩,⟨(-42136468143),(-42136468084)⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨(-4534774667),(-4534774598)⟩,⟨(-13448819670),(-13448819599)⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨(-1904243057),(-1904242979)⟩,⟨(-2003981836),(-2003981758)⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨(-313868726),(-313868640)⟩,⟨(-105812507),(-105812421)⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨(-25721900),(-25721810)⟩,⟨4605939,4606029⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨(-1175753),(-1175656)⟩,⟨893358,893456⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨(-33432),(-33331)⟩,⟨56807,56908⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨(-743),(-636)⟩,⟨2443,2557⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨(-70),44⟩,⟨47,153⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨(-65),65⟩,⟨(-33),97⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨(-80),64⟩,⟨(-48),96⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨(-64),59⟩,⟨(-46),78⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨(-49),49⟩,⟨(-43),55⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨(-24),24⟩,⟨(-24),24⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨(-4160590022133486444),(-4160590022133407759)⟩,⟨13438611206581762995,13438611206581841678⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨(-3744798342872975929),(-3744798342872835938)⟩,⟨30798979407768153374,30798979407768293364⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨6478814760127832331,6478814760127906609⟩,⟨27265667616905519936,27265667616905594218⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨10827616985905768996,10827616985905786767⟩,⟨11538047395645070662,11538047395645088432⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨6144376830532125075,6144376830532128233⟩,⟨909777876420207685,909777876420210846⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨1437773952139553421,1437773952139553666⟩,⟨(-1081728434577867835),(-1081728434577867588)⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨20367739873841719,20367739873841777⟩,⟨(-401714450511651085),(-401714450511651028)⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨(-55077479443842741),(-55077479443842690)⟩,⟨(-46785005056160516),(-46785005056160465)⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨(-10689795128405883),(-10689795128405828)⟩,⟨2364077699404678,2364077699404732⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨(-663757592898384),(-663757592898321)⟩,⟨1333475617393021,1333475617393083⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨70244105466198,70244105466262⟩,⟨183801433941104,183801433941169⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨24473497450958,24473497451015⟩,⟨12597237262345,12597237262406⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨4395704943629,4395704943683⟩,⟨(-579951430952),(-579951430899)⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨724890326387,724890326433⟩,⟨(-490791015668),(-490791015621)⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨130031649829,130031649865⟩,⟨(-166213527935),(-166213527897)⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨21297391062,21297391083⟩,⟨(-38279705201),(-38279705175)⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨962560405590994276377349,962560405591032881062447⟩,⟨(-1077654860791618320549990),(-1077654860791579715878642)⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨1900861003939433735517840,1900861003939555083626299⟩,⟨(-3108358974058096985079726),(-3108358974057975636927976)⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨839560717406078856202451,839560717406274065565197⟩,⟨(-4193473254933148887771188),(-4193473254932953678179458)⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨(-1079495139926568147849784),(-1079495139926312556209823)⟩,⟨(-3351977030041319630148163),(-3351977030041064038244197)⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨(-1831607401727432398776841),(-1831607401727080230584239)⟩,⟨(-1265425866176275563203111),(-1265425866175923394995613)⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨(-1114925903127070494321888),(-1114925903126805084693572)⟩,⟨204251450487439255514799,204251450487704665063447⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨(-231793442524597558157990),(-231793442524395658269944)⟩,⟨426227525211127989054680,426227525211329888938146⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨80567168777630548183003,80567168777710305807532⟩,⟨162747850046525929094265,162747850046605686731502⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨60890908464638851308799,60890908464668801203155⟩,⟨8176655151408756608310,8176655151438706501575⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨13219609484497144552798,13219609484503713571222⟩,⟨(-14151988510473612530892),(-14151988510467043513480)⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨(-810520469107434559515),(-810520469106069466527)⟩,⟨(-5817874871191583925767),(-5817874871190218832575)⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨(-1430029584031356189643),(-1430029584031136002086)⟩,⟨(-1056347368555787041232),(-1056347368555566853606)⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨(-557842401252447787315),(-557842401252408280846)⟩,⟨24115996907163382688,24115996907202889146⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨(-156295613793763701774),(-156295613793757728904)⟩,⟨103491542544924502170,103491542544930475033⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨(-37239421577696056374),(-37239421577694485753)⟩,⟨53805674737477934472,53805674737479505087⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨(-6528254946117984059),(-6528254946117658715)⟩,⟨15087308008098233339,15087308008098558683⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨(-55205475723623477747355752),(-55205475723623476340406320)⟩,⟨22882097675732229467369917,22882097675732230776236394⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨(-109807936248753364726069657),(-109807936248753360339077679)⟩,⟨109329414488548321829733723,109329414488548326032106620⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨22791547764749974723267289,22791547764749981776098409⟩,⟨208024070629897574393432991,208024070629897581422852139⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨350210794179605089157617923,350210794179605099509333019⟩,⟨100503424424153765637006513,100503424424153776259720781⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨552576090948562597655454731,552576090948562619523632177⟩,⟨(-330508789767043002804947521),(-330508789767042980617535830)⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨301305078103012684195796435,301305078103012718393585419⟩,⟨(-757711646833229244088128985),(-757711646833229209882771688)⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨(-202230253706240442403692633),(-202230253706240404031322513)⟩,⟨(-736678422063431279447938901),(-736678422063431241196874727)⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨(-461296176300413387846958102),(-461296176300413353475835575)⟩,⟨(-329488806345189511090684151),(-329488806345189476728328322)⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨(-351858645409831960093820585),(-351858645409831933198327124)⟩,⟨34253905070444014503417286,34253905070444041427973224⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨(-131430673687731884326625037),(-131430673687731856258095982)⟩,⟨143497373136643857986883206,143497373136643886055572131⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨(-2000320285927533251911751),(-2000320285927493877298192)⟩,⟨98665990885986368485601844,98665990885986407854890710⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨29505321724835861600142658,29505321724835940702173504⟩,⟨37880696576867757702224249,37880696576867836803910370⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨22169457950244914635866477,22169457950245012874464465⟩,⟨6846583053252300466698239,6846583053252398706141231⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨11026320014631530666254355,11026320014631624384643389⟩,⟨(-2217869401969099571551369),(-2217869401969005852710057)⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨4390919323925521009505080,4390919323925601981954639⟩,⟨(-2687802123916310181101035),(-2687802123916229208574146)⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨1113245198276859563320447,1113245198276890097932370⟩,⟨(-995671154676019612460440),(-995671154675989077844952)⟩⟩
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
noncomputable def ans : CBox := ⟨⟨(-3190641624472205457560612),(-3190641624471842615277493)⟩,⟨(-235103614256418686651197737),(-235103614256418323777746246)⟩⟩
lemma checked : cachedMomentRuleBox density1 hk16_1_5 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule true true 16 5) := by
  rw [← checked]
  exact @cached_density_rule_contains density1 hk16_1_5 (tableDensity true) (fullFactor true 16 5) density1_contains hk16_1_5_contains
noncomputable def atomAnswer : CBox := ⟨⟨(-2715539081027256615657407099),(-2715539081027256598696774928)⟩,⟨(-8895694857124672132525882197),(-8895694857124672115376208326)⟩⟩
lemma atomChecked : tableAtomBox true ha16_1_5 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom true true 16 5) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains true true ha16_1_5 16 5 ha16_1_5_contains
 def realAnswer : RBox := ⟨(-2718729722651728821214967711),(-2718729722651728441212052421)⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment true true 16 5) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm16_1_1_5
namespace hm16_0_1_6
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density0 j i k).mul (hk16_1_6 j i k))
noncomputable def s0_0 : CBox := ⟨⟨(-527),527⟩,⟨(-527),527⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨(-1594),1594⟩,⟨(-1594),1594⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨(-2722),2722⟩,⟨(-2722),2722⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨(-3893),3893⟩,⟨(-3893),3893⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨(-4978),4978⟩,⟨(-4978),4978⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨(-5741),5741⟩,⟨(-5741),5741⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨(-5881),5881⟩,⟨(-5881),5881⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨(-5756),5756⟩,⟨(-5756),5756⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨(-7002),7002⟩,⟨(-7002),7002⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨(-7628),7628⟩,⟨(-7628),7628⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨(-7321),7321⟩,⟨(-7321),7321⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨(-6257),6257⟩,⟨(-6257),6257⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨(-4531),4531⟩,⟨(-4531),4531⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨(-2446),2446⟩,⟨(-2446),2446⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨(-1387),1387⟩,⟨(-1387),1387⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨(-452),452⟩,⟨(-452),452⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨(-136),136⟩,⟨(-136),136⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨(-383),383⟩,⟨(-383),383⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨(-611),611⟩,⟨(-611),611⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨(-918),918⟩,⟨(-918),918⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨(-1340),1340⟩,⟨(-1340),1340⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨(-1840),1840⟩,⟨(-1840),1840⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨(-2356),2356⟩,⟨(-2356),2356⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨(-2818),2818⟩,⟨(-2818),2818⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨(-3105),3105⟩,⟨(-3105),3105⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨(-3125),3125⟩,⟨(-3125),3125⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨(-2843),2843⟩,⟨(-2843),2843⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨(-2401),2401⟩,⟨(-2401),2401⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨(-2297),2297⟩,⟨(-2297),2297⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨(-1953),1953⟩,⟨(-1953),1953⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨(-1300),1300⟩,⟨(-1300),1300⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨(-461),461⟩,⟨(-461),461⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨(-122075786853),(-122075786821)⟩,⟨90470698010,90470698044⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨(-201716930782),(-201716930708)⟩,⟨199297459495,199297459570⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨(-91003124466),(-91003124349)⟩,⟨159635474445,159635474565⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨(-8413090696),(-8413090534)⟩,⟨62677463964,62677464125⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨4189577980,4189578206⟩,⟨12159872172,12159872394⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨1220860140,1220860446⟩,⟨1097900916,1097901229⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨135557525,135557946⟩,⟨31488785,31489204⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨8165198,8165794⟩,⟨(-1903020),(-1902424)⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨323704,324433⟩,⟨(-221061),(-220328)⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨10112,10941⟩,⟨(-12303),(-11476)⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨(-77),765⟩,⟨(-944),(-110)⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨(-442),553⟩,⟨(-681),309⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨(-463),659⟩,⟨(-680),442⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨(-369),505⟩,⟨(-542),332⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨(-308),346⟩,⟨(-359),296⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨(-131),131⟩,⟨(-131),131⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨26997721435010329118,26997721435010403604⟩,⟨(-20875996271751830645),(-20875996271751756154)⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨50917653918397301693,50917653918397427479⟩,⟨(-57202057100035000175),(-57202057100034874382)⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨25477243476444529176,25477243476444591612⟩,⟨(-66831985164555606832),(-66831985164555544387)⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨(-6842398085196716318),(-6842398085196695719)⟩,⟨(-41697574586105439177),(-41697574586105418572)⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨(-12893240457410598021),(-12893240457410594897)⟩,⟨(-11710963480091119549),(-11710963480091116426)⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨(-5260164894684489252),(-5260164894684488948)⟩,⟨276069566357914426,276069566357914735⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨(-728465814172019147),(-728465814172019033)⟩,⟨977703116897879377,977703116897879491⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨64348186035948017,64348186035948131⟩,⟨216713364869122751,216713364869122868⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨33323621837645377,33323621837645495⟩,⟨11914274065370891,11914274065371008⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨4208209985997641,4208209985997778⟩,⟨(-2661863207904434),(-2661863207904298)⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨113759923558455,113759923558590⟩,⟨(-668090423656686),(-668090423656549)⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨(-52136410085784),(-52136410085656)⟩,⟨(-81601413815249),(-81601413815121)⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨(-14589331632767),(-14589331632655)⟩,⟨(-6000830636304),(-6000830636196)⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨(-3116941993061),(-3116941992979)⟩,⟨249137960629,249137960716⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨(-695193411552),(-695193411491)⟩,⟨291751017434,291751017490⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨(-132739870475),(-132739870445)⟩,⟨82700207525,82700207558⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨(-2494165674776487692572304),(-2494165674776455347955855)⟩,⟨(-1739437863602867405560991),(-1739437863602835060855312)⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨(-6885981356038053090412822),(-6885981356037954265568015)⟩,⟨(-3059377875631958141556405),(-3059377875631859316209215)⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨(-8595901069655759918196377),(-8595901069655610216781190)⟩,⟨(-351716508041982688040958),(-351716508041832985486492)⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨(-6026962287435826159714535),(-6026962287435587655449493)⟩,⟨3383069163672146062369565,3383069163672384567351053⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨(-1490580812084345179398734),(-1490580812084046330394543)⟩,⟨4062214888847957211276263,4062214888848256060126936⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨1029130781875628260764425,1029130781875861519973084⟩,⟨1960392248887583723437551,1960392248887816982367871⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨943410974463515890329513,943410974463692066570261⟩,⟨148237157062914615308066,148237157063090791581959⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨238555388267072464140189,238555388267146110711530⟩,⟨(-266004773350063620910966),(-266004773349989974302851)⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨(-34715388411923453393897),(-34715388411897594694319)⟩,⟨(-114709510566492469897323),(-114709510566466611207526)⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨(-36203140901271108889851),(-36203140901264374759860)⟩,⟨(-9641234884926128008878),(-9641234884919393880693)⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨(-8663580502729978321993),(-8663580502728788072980)⟩,⟨7421029412887395615221,7421029412888585865460⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨59228032109299617767,59228032109529875116⟩,⟨3540587817493735471718,3540587817493965729147⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨807767658370089610966,807767658370123861522⟩,⟨838481219338980357948,838481219339014608393⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨402543025108545800167,402543025108552511841⟩,⟨88307095453113596039,88307095453120307680⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨147596671497683283242,147596671497684956651⟩,⟨(-28032338452524299603),(-28032338452522626198)⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨35693207961656508193,35693207961656834574⟩,⟨(-14794659816158027450),(-14794659816157701072)⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨470145758743186997368346649,470145758743187014500867008⟩,⟨1117453419190005759110804113,1117453419190005776340081468⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨1795720804148736203184061169,1795720804148736254252189301⟩,⟨2674397686351633776779441513,2674397686351633828033628341⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨3512014818800760944118948392,3512014818800761026885395159⟩,⟨2415120404622145917474665160,2415120404622146000283265099⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨4309894905491776846250724022,4309894905491776953494225601⟩,⟨286867410359892429635447877,286867410359892536650483695⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨3058288048701762818189358424,3058288048701762938564442901⟩,⟨(-2048003795522763590864439436),(-2048003795522763470733023794)⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨626055409250058735458874087,626055409250058851160282266⟩,⟨(-2626390613719151892462773523),(-2626390613719151776768288150)⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨(-958192725252346312812098481),(-958192725252346217888502257)⟩,⟨(-1436106098662666940316349535),(-1436106098662666845318685431)⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨(-980531467275156141470913344),(-980531467275156072902431908)⟩,⟨(-97193746516944144285125956),(-97193746516944075713059586)⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨(-353182642187138070312084914),(-353182642187138025042628743)⟩,⟨378645251215049316237137948,378645251215049361495292444⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨43158102340991210860240438,43158102340991245780128722⟩,⟨254810376065963568890331368,254810376065963603810579004⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨108895084803498213378227898,108895084803498252445929033⟩,⟨63303222012110424189056743,63303222012110463257245708⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨59058345608392802550522622,59058345608392871196427662⟩,⟨(-16064823175455721888859541),(-16064823175455653243080598)⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨17724682284430877604493158,17724682284430954933912038⟩,⟨(-24103735500470166508791962),(-24103735500470089179213594)⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨1599925799755086104692884,1599925799755172976106841⟩,⟨(-14484607166271168609191712),(-14484607166271081737654407)⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨(-1640769122940408818994228),(-1640769122940337747124733)⟩,⟨(-6434008709637325646297021),(-6434008709637254574396230)⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨(-803542834590982941043023),(-803542834590956854138704)⟩,⟨(-1738442141958645097103383),(-1738442141958619010196177)⟩⟩
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
noncomputable def ans : CBox := ⟨⟨1947474032289140992320411143,1947474032289141399387857285⟩,⟨154017095522138020845278079,154017095522138427898620172⟩⟩
lemma checked : cachedMomentRuleBox density0 hk16_1_6 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule false true 16 6) := by
  rw [← checked]
  exact @cached_density_rule_contains density0 hk16_1_6 (tableDensity false) (fullFactor true 16 6) density0_contains hk16_1_6_contains
noncomputable def atomAnswer : CBox := ⟨⟨4029517675034277771881138454,4029517675034277780201075676⟩,⟨(-1461780128661066713045394002),(-1461780128661066704816496682)⟩⟩
lemma atomChecked : tableAtomBox false ha16_1_6 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom false true 16 6) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains false true ha16_1_6 16 6 ha16_1_6_contains
 def realAnswer : RBox := ⟨5976991707323418764101549597,5976991707323419179688932961⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment false true 16 6) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm16_0_1_6
namespace hm16_1_1_6
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density1 j i k).mul (hk16_1_6 j i k))
noncomputable def s0_0 : CBox := ⟨⟨(-98),98⟩,⟨(-98),98⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨(-284),284⟩,⟨(-284),284⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨(-483),483⟩,⟨(-483),483⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨(-684),684⟩,⟨(-684),684⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨(-853),853⟩,⟨(-853),853⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨(-947),947⟩,⟨(-947),947⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨(-941),941⟩,⟨(-941),941⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨(-913),913⟩,⟨(-913),913⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨(-1120),1120⟩,⟨(-1120),1120⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨(-1254),1254⟩,⟨(-1254),1254⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨(-1238),1238⟩,⟨(-1238),1238⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨(-1083),1083⟩,⟨(-1083),1083⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨(-787),787⟩,⟨(-787),787⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨(-421),421⟩,⟨(-421),421⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨(-240),240⟩,⟨(-240),240⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨(-80),80⟩,⟨(-80),80⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨(-24),24⟩,⟨(-24),24⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨(-55),55⟩,⟨(-55),55⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨(-83),83⟩,⟨(-83),83⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨(-121),121⟩,⟨(-121),121⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨(-180),180⟩,⟨(-180),180⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨(-250),250⟩,⟨(-250),250⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨(-333),333⟩,⟨(-333),333⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨(-413),413⟩,⟨(-413),413⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨(-473),473⟩,⟨(-473),473⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨(-496),496⟩,⟨(-496),496⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨(-474),474⟩,⟨(-474),474⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨(-420),420⟩,⟨(-420),420⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨(-415),415⟩,⟨(-415),415⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨(-368),368⟩,⟨(-368),368⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨(-252),252⟩,⟨(-252),252⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨(-96),96⟩,⟨(-96),96⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨(-34176415268),(-34176415245)⟩,⟨2953650622,2953650644⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨(-62505223808),(-62505223773)⟩,⟨14222722052,14222722089⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨(-36655868399),(-36655868351)⟩,⟨19404539157,19404539204⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨(-9249393036),(-9249392979)⟩,⟨10640564235,10640564295⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨(-731129110),(-731129036)⟩,⟨2682983011,2682983083⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨79654539,79654622⟩,⟨328751929,328752017⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨18720266,18720369⟩,⟨19664025,19664125⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨1486561,1486690⟩,⟨483379,483507⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨70751,70893⟩,⟨(-7185),(-7048)⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨2572,2716⟩,⟨(-1148),(-1004)⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨27,165⟩,⟨(-126),7⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨(-54),96⟩,⟨(-98),50⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨(-56),104⟩,⟨(-92),68⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨(-47),80⟩,⟨(-74),52⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨(-42),54⟩,⟨(-53),45⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨(-24),24⟩,⟨(-24),24⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨11407360678569378319,11407360678569440839⟩,⟨(-199474605485020531),(-199474605484958013)⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨24735705285752079989,24735705285752185467⟩,⟨(-5009457433997837010),(-5009457433997731535)⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨19427617444413519991,19427617444413572219⟩,⟨(-12185401376971005250),(-12185401376970953024)⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨6046833279697055441,6046833279697072602⟩,⟨(-11577822305625910656),(-11577822305625893493)⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨(-1032290614587850932),(-1032290614587848374)⟩,⟨(-5082188824876025284),(-5082188824876022725)⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨(-1286560845903125897),(-1286560845903125684)⟩,⟨(-814784328304462577),(-814784328304462365)⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨(-327528121647375906),(-327528121647375849)⟩,⟨110841977611119696,110841977611119751⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨(-19275236362079398),(-19275236362079350)⟩,⟨60173169826354678,60173169826354730⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨5739922615577406,5739922615577452⟩,⟨7873833310527194,7873833310527245⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨1349018987252161,1349018987252217⟩,⟨42100400076532,42100400076590⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨124599098833483,124599098833541⟩,⟨(-131853790108386),(-131853790108328)⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨256809769619,256809769675⟩,⟨(-25786568369296),(-25786568369245)⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨(-2417757854204),(-2417757854155)⟩,⟨(-3449521938505),(-3449521938457)⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨(-744668624519),(-744668624478)⟩,⟨(-391056402949),(-391056402907)⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨(-201645304809),(-201645304777)⟩,⟨(-33240989416),(-33240989383)⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨(-42593997448),(-42593997425)⟩,⟨(-122636219),(-122636197)⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨(-847662690654886349775518),(-847662690654859822118319)⟩,⟨(-528722124132694956936852),(-528722124132668429293964)⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨(-2350337838738402824859714),(-2350337838738321738854478)⟩,⟨(-925131890706247907935718),(-925131890706166822022545)⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨(-2979915828930920926234282),(-2979915828930798035020581)⟩,⟨(-55981288674531525221068),(-55981288674408634234086)⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨(-2173234744777988424119968),(-2173234744777792478730841)⟩,⟨1180468418847023877709617,1180468418847219822949233⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨(-628352028045321866262143),(-628352028045076230737472)⟩,⟨1448698443183655169064845,1448698443183900804619170⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨307539489403400503948599,307539489403592253949334⟩,⟨753270553556528038095733,753270553556719788157044⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨339357335248224667440497,339357335248369481942402⟩,⟨97260118241681045925988,97260118241825860421433⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨103232651059642990694919,103232651059703499591049⟩,⟨(-85586412037702291925604),(-85586412037641783038041)⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨(-5203241362043700839476),(-5203241362022469860488)⟩,⟨(-45779113113697955611789),(-45779113113676724630770)⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨(-13011680477562648976008),(-13011680477557125962651)⟩,⟨(-6949074170827943623893),(-6949074170822420610099)⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨(-4160455918018630349721),(-4160455918017655386805)⟩,⟨1822662102012025259915,1822662102013000222598⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨(-476877765863205788608),(-476877765863017445912)⟩,⟨1309897306551101972059,1309897306551290314732⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨148300808716180728704,148300808716208705748⟩,⟨417577836477892147094,417577836477920124158⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨116892183283619042394,116892183283624517722⟩,⟨94349428101930154115,94349428101935629451⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨50554412375050273345,50554412375051637283⟩,⟨15219566622508981624,15219566622510345562⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨13253667157027295949,13253667157027561829⟩,⟨1225781521770895898,1225781521771161780⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨15525429059766760608267990,15525429059766761422958342⟩,⟨32519309427549085449714600,32519309427549086317167918⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨69600371342343519271212142,69600371342343521884858373⟩,⟨62651272664678796580236040,62651272664678799286545564⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨125237776194890657242902846,125237776194890661613339635⟩,⟨(-21282050047670958715540286),(-21282050047670954358266114)⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨47296513990179526232684572,47296513990179532861217164⟩,⟨(-217687758974054067524844848),(-217687758974054061088258950)⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨(-228209247780659133473857930),(-228209247780659119381315254)⟩,⟨(-325092441558320493022085732),(-325092441558320479113854327)⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨(-486071693169392495936842930),(-486071693169392474023271905)⟩,⟨(-148492819467656270447091554),(-148492819467656248519741283)⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨(-450829906177832477497373589),(-450829906177832452728709512)⟩,⟨169743315736231911123281384,169743315736231935970303744⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨(-178935648423228753406618245),(-178935648423228730954945402)⟩,⟨314688535036539169719257190,314688535036539192169410613⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨48071474359060053657815101,48071474359060071425969401⟩,⟨223635759397474958698560948,223635759397474976447533804⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨104179562054256490365196509,104179562054256508779175500⟩,⟨73651460746475488406214833,73651460746475506821679689⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨65089026194024784171740773,65089026194024810885344872⟩,⟨(-7642417943636863364816880),(-7642417943636836647703014)⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨22270214984001456110216505,22270214984001509547325194⟩,⟨(-23345727055547181005255159),(-23345727055547127568237229)⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨2254280893771198916726937,2254280893771260813258288⟩,⟨(-15589453419044965933240433),(-15589453419044904037367842)⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨(-2721543337131988665730103),(-2721543337131918263504504)⟩,⟨(-7201165414719605147307436),(-7201165414719534745309365)⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨(-2328693333971962987084965),(-2328693333971905137230393)⟩,⟨(-2671587853888282998156456),(-2671587853888225148321191)⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨(-807626429750378588826516),(-807626429750357327579499)⟩,⟨(-641151725275761332034285),(-641151725275740070781431)⟩⟩
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
noncomputable def ans : CBox := ⟨⟨(-143105257921748139159701611),(-143105257921747885408317605)⟩,⟨18179708903631695851091603,18179708903631949574315990⟩⟩
lemma checked : cachedMomentRuleBox density1 hk16_1_6 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule true true 16 6) := by
  rw [← checked]
  exact @cached_density_rule_contains density1 hk16_1_6 (tableDensity true) (fullFactor true 16 6) density1_contains hk16_1_6_contains
noncomputable def atomAnswer : CBox := ⟨⟨(-5269369267352517097186022037),(-5269369267352517086306104132)⟩,⟨1911558629787548767836957200,1911558629787548778597822925⟩⟩
lemma atomChecked : tableAtomBox true ha16_1_6 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom true true 16 6) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains true true ha16_1_6 16 6 ha16_1_6_contains
 def realAnswer : RBox := ⟨(-5412474525274265236445723648),(-5412474525274264971614421737)⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment true true 16 6) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm16_1_1_6
namespace hm16_0_1_7
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density0 j i k).mul (hk16_1_7 j i k))
noncomputable def s0_0 : CBox := ⟨⟨(-485),485⟩,⟨(-485),485⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨(-1507),1507⟩,⟨(-1507),1507⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨(-2763),2763⟩,⟨(-2763),2763⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨(-4305),4305⟩,⟨(-4305),4305⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨(-6038),6038⟩,⟨(-6038),6038⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨(-7625),7625⟩,⟨(-7625),7625⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨(-8532),8532⟩,⟨(-8532),8532⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨(-8228),8228⟩,⟨(-8228),8228⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨(-7953),7953⟩,⟨(-7953),7953⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨(-9419),9419⟩,⟨(-9419),9419⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨(-9532),9532⟩,⟨(-9532),9532⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨(-8364),8364⟩,⟨(-8364),8364⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨(-6100),6100⟩,⟨(-6100),6100⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨(-3281),3281⟩,⟨(-3281),3281⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨(-1845),1845⟩,⟨(-1845),1845⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨(-592),592⟩,⟨(-592),592⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨(-169),169⟩,⟨(-169),169⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨(-502),502⟩,⟨(-502),502⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨(-862),862⟩,⟨(-862),862⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨(-1249),1249⟩,⟨(-1249),1249⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨(-1634),1634⟩,⟨(-1634),1634⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨(-1955),1955⟩,⟨(-1955),1955⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨(-2115),2115⟩,⟨(-2115),2115⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨(-2412),2412⟩,⟨(-2412),2412⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨(-3200),3200⟩,⟨(-3200),3200⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨(-3784),3784⟩,⟨(-3784),3784⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨(-3980),3980⟩,⟨(-3980),3980⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨(-3717),3717⟩,⟨(-3717),3717⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨(-3076),3076⟩,⟨(-3076),3076⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨(-2228),2228⟩,⟨(-2228),2228⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨(-1320),1320⟩,⟨(-1320),1320⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨(-439),439⟩,⟨(-439),439⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨115529519658,115529519690⟩,⟨52438296414,52438296449⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨228268077600,228268077674⟩,⟨65782069161,65782069238⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨154950757284,154950757415⟩,⟨(-78600458),(-78600329)⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨49665174858,49665175039⟩,⟨(-20802069978),(-20802069797)⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨7093302904,7093303144⟩,⟨(-8524304972),(-8524304731)⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨242376043,242376358⟩,⟨(-1416761141),(-1416760819)⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨(-43138448),(-43138047)⟩,⟨(-116199155),(-116198752)⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨(-5643531),(-5643005)⟩,⟨(-5103771),(-5103244)⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨(-342136),(-341541)⟩,⟨(-121924),(-121332)⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨(-15254),(-14649)⟩,⟨(-1325),(-726)⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨(-912),(-290)⟩,⟨(-261),386⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨(-619),270⟩,⟨(-372),526⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨(-722),414⟩,⟨(-565),574⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨(-615),367⟩,⟨(-469),510⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨(-428),356⟩,⟨(-383),401⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨(-161),161⟩,⟨(-161),161⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨(-19648534208497296352),(-19648534208497250809)⟩,⟨(-13294355917976741540),(-13294355917976696000)⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨(-49044449135213774966),(-49044449135213701810)⟩,⟨(-21113280797601390666),(-21113280797601317517)⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨(-50133106346330228684),(-50133106346330180571)⟩,⟨(-1869382393491871633),(-1869382393491823521)⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨(-26260459490960120283),(-26260459490960104732)⟩,⟨14296265522939610870,14296265522939626418⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨(-4738573443371133193),(-4738573443371131192)⟩,⟨11529807158933002673,11529807158933004673⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨1536321196819478466,1536321196819478714⟩,⟨3499093554324628055,3499093554324628305⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨867445087385474469,867445087385474555⟩,⟨233834466166063613,233834466166063693⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨131432238205693216,131432238205693300⟩,⟨(-106909266467810549),(-106909266467810466)⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨(-1860493854596821),(-1860493854596735)⟩,⟨(-26933494688758203),(-26933494688758119)⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨(-3243197123903382),(-3243197123903290)⟩,⟨(-2106677344698102),(-2106677344698013)⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨(-514707973569779),(-514707973569692)⟩,⟨148016645080877,148016645080964⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨(-39768660456642),(-39768660456550)⟩,⟨66824228537990,66824228538085⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨1153823497525,1153823497613⟩,⟨12794678665949,12794678666041⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨1393625011784,1393625011861⟩,⟨2165451411258,2165451411331⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨489370212616,489370212674⟩,⟨390070797073,390070797133⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨113835805605,113835805635⟩,⟨63493268136,63493268168⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨(-763708018959906027893244),(-763708018959887540050760)⟩,⟨1632245206625130248437541,1632245206625148736160578⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨(-1082674763757209208580336),(-1082674763757154458346385)⟩,⟨4344468237078828186715502,4344468237078882936495253⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨706514627781278122968788,706514627781364678895208⟩,⟨5090045144393549047182699,5090045144393635602378300⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨2672373307664695213036914,2672373307664848901968697⟩,⟨3188525915192969315565720,3188525915193123004244444⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨2598590820397447369393816,2598590820397619029309762⟩,⟨409501849159259479544377,409501849159431139667539⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨1050694281029715152029397,1050694281029867009868191⟩,⟨(-867001731631856043907158),(-867001731631704185933224)⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨(-37592910726709766570846),(-37592910726605976000217)⟩,⟨(-594378898298943907291975),(-594378898298840116769433)⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨(-198620804065764125339576),(-198620804065713615999955)⟩,⟨(-108112642197314158734600),(-108112642197263649408277)⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨(-66047200144669791383831),(-66047200144654044178175)⟩,⟨39643174756978790241483,39643174756994537455621⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨15376502417525950225,15376502422073930729⟩,⟨24458065354041078413689,24458065354045626394057⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨6290826720310606677233,6290826720311368710427⟩,⟨4193045177524944793464,4193045177525706825822⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨2270684119097559759165,2270684119097714791182⟩,⟨(-712165626852205296442),(-712165626852050264354)⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨383805267432293514655,383805267432315255926⟩,⟨(-692778698707823534312),(-692778698707801792951)⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨(-25707427690844967665),(-25707427690839877149)⟩,⟨(-281908090339351717194),(-281908090339346626671)⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨(-49875349157218811080),(-49875349157217684003)⟩,⟨(-91145350313907437046),(-91145350313906309977)⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨(-17460267197689039545),(-17460267197688833356)⟩,⟨(-20351177160286268697),(-20351177160286062510)⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨564029567584187927793060897,564029567584187936921366227⟩,⟨(-272963003098922814568558849),(-272963003098922805485750049)⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨1332661916739433826379132616,1332661916739433853597388760⟩,⟨(-1004490684569479659336949871),(-1004490684569479632201217383)⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨1147394769266303037448751913,1147394769266303081621903043⟩,⟨(-1898360113824087549861908793),(-1898360113824087505690302521)⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨3741521475817429523908714,3741521475817486972257231⟩,⟨(-2263015093492957397130490615),(-2263015093492957339544214969)⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨(-1196622636267027775281485665),(-1196622636267027710206735451)⟩,⟨(-1533490056116693869235069163),(-1533490056116693804042532816)⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨(-1424982311640166581018839498),(-1424982311640166517859845955)⟩,⟨(-218658969323816405225550895),(-218658969323816342074370778)⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨(-724941568729834536033172572),(-724941568729834483741300262)⟩,⟨586787895194252879303298045,586787895194252931555195238⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨2382565029581562915221109,2382565029581600922306424⟩,⟨539094003896320775050936821,539094003896320813059381316⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨230968984781396771466905331,230968984781396796762889486⟩,⟨170484190714358636907384189,170484190714358662209565617⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨138973699146230176720573891,138973699146230196130060499⟩,⟨(-42084090950370953107110565),(-42084090950370933698135092)⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨27208948095305751897176591,27208948095305774688022689⟩,⟨(-66322987779670302451823352),(-66322987779670279661218238)⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨(-14144185078156469653414266),(-14144185078156430786384681)⟩,⟨(-32286763291831679002943988),(-32286763291831640135899382)⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨(-15457248467791597159612256),(-15457248467791553027879583)⟩,⟨(-8009814478250173456820670),(-8009814478250129325226040)⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨(-8537567512881682980205486),(-8537567512881628633844487)⟩,⟨451537842316163963439085,451537842316218309740269⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨(-3581638518778180614501614),(-3581638518778138337818903)⟩,⟨1588021000427442962361743,1588021000427485239041013⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨(-933453289295903624410893),(-933453289295888503584326)⟩,⟨642822531945059391575506,642822531945074512406040⟩⟩
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
noncomputable def ans : CBox := ⟨⟨10508268717921547288312125,10508268717921785835172065⟩,⟨(-1004578553930588425959107853),(-1004578553930588187398295772)⟩⟩
lemma checked : cachedMomentRuleBox density0 hk16_1_7 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule false true 16 7) := by
  rw [← checked]
  exact @cached_density_rule_contains density0 hk16_1_7 (tableDensity false) (fullFactor true 16 7) density0_contains hk16_1_7_contains
noncomputable def atomAnswer : CBox := ⟨⟨(-861697752199321759026023941),(-861697752199321754549627606)⟩,⟨(-2039810097211714910012950833),(-2039810097211714905488052252)⟩⟩
lemma atomChecked : tableAtomBox false ha16_1_7 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom false true 16 7) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains false true ha16_1_7 16 7 ha16_1_7_contains
 def realAnswer : RBox := ⟨(-851189483481400211837711816),(-851189483481399968614455541)⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment false true 16 7) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm16_0_1_7
namespace hm16_1_1_7
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density1 j i k).mul (hk16_1_7 j i k))
noncomputable def s0_0 : CBox := ⟨⟨(-92),92⟩,⟨(-92),92⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨(-269),269⟩,⟨(-269),269⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨(-490),490⟩,⟨(-490),490⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨(-755),755⟩,⟨(-755),755⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨(-1032),1032⟩,⟨(-1032),1032⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨(-1256),1256⟩,⟨(-1256),1256⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨(-1364),1364⟩,⟨(-1364),1364⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨(-1300),1300⟩,⟨(-1300),1300⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨(-1273),1273⟩,⟨(-1273),1273⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨(-1544),1544⟩,⟨(-1544),1544⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨(-1614),1614⟩,⟨(-1614),1614⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨(-1443),1443⟩,⟨(-1443),1443⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨(-1057),1057⟩,⟨(-1057),1057⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨(-563),563⟩,⟨(-563),563⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨(-317),317⟩,⟨(-317),317⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨(-105),105⟩,⟨(-105),105⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨(-29),29⟩,⟨(-29),29⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨(-69),69⟩,⟨(-69),69⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨(-114),114⟩,⟨(-114),114⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨(-164),164⟩,⟨(-164),164⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨(-216),216⟩,⟨(-216),216⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨(-266),266⟩,⟨(-266),266⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨(-299),299⟩,⟨(-299),299⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨(-353),353⟩,⟨(-353),353⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨(-488),488⟩,⟨(-488),488⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨(-599),599⟩,⟨(-599),599⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨(-662),662⟩,⟨(-662),662⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨(-648),648⟩,⟨(-648),648⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨(-558),558⟩,⟨(-558),558⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨(-420),420⟩,⟨(-420),420⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨(-256),256⟩,⟨(-256),256⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨(-90),90⟩,⟨(-90),90⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨16010618811,16010618831⟩,⟨23750919333,23750919353⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨35995857168,35995857203⟩,⟨39853163432,39853163465⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨29533122772,29533122821⟩,⟨18735263528,18735263580⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨11798390908,11798390971⟩,⟨2214437854,2214437917⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨2305046011,2305046089⟩,⟨(-659969939),(-659969865)⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨206161262,206161351⟩,⟨(-212537627),(-212537539)⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨5425161,5425262⟩,⟨(-23562192),(-23562094)⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨(-408715),(-408603)⟩,⟨(-1358430),(-1358318)⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨(-44043),(-43928)⟩,⟨(-49084),(-48969)⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨(-2383),(-2273)⟩,⟨(-1410),(-1303)⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨(-154),(-48)⟩,⟨(-89),20⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨(-100),34⟩,⟨(-66),64⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨(-107),60⟩,⟨(-92),64⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨(-90),48⟩,⟨(-75),64⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨(-63),53⟩,⟨(-59),56⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨(-28),28⟩,⟨(-28),28⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨(-2609031392998092498),(-2609031392998054281)⟩,⟨(-7489536218299162114),(-7489536218299123897)⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨(-8753180944644579514),(-8753180944644518199)⟩,⟨(-15265372010773743393),(-15265372010773682079)⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨(-12470026475907172759),(-12470026475907132518)⟩,⟨(-10160335054550504918),(-10160335054550464672)⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨(-9144539453622294167),(-9144539453622281214)⟩,⟨(-1339534728859467647),(-1339534728859454692)⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨(-3168202543170694429),(-3168202543170692796)⟩,⟨1932917271603872826,1932917271603874460⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨(-223034952512160676),(-223034952512160500)⟩,⟨1082042535797599612,1082042535797599788⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨164783736072904002,164783736072904047⟩,⟨194315849235774525,194315849235774569⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨47184820273320899,47184820273320937⟩,⟨(-3982916081706185),(-3982916081706145)⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨3748550022102643,3748550022102683⟩,⟨(-6418837195137371),(-6418837195137329)⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨(-407722844953891),(-407722844953851)⟩,⟨(-965683183653063),(-965683183653022)⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨(-136595196529635),(-136595196529595)⟩,⟨(-43520871566440),(-43520871566402)⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨(-18597295904650),(-18597295904606)⟩,⟨9109472866470,9109472866516⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨(-1581949497737),(-1581949497696)⟩,⟨3043866983095,3043866983139⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨5911192640,5911192677⟩,⟨692667798201,692667798239⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨56109806736,56109806766⟩,⟨160089353124,160089353157⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨17080445365,17080445389⟩,⟨31120624092,31120624116⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨(-223090439458454746348201),(-223090439458439582819878)⟩,⟨548423342088003665777894,548423342088018829328713⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨(-299835876026040012307155),(-299835876025995090618438)⟩,⟨1470643462983956327874777,1470643462984001249653823⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨283701488176299148086771,283701488176370205705374⟩,⟨1757607016614452923980149,1757607016614523981753499⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨940334670342594709541292,940334670342720986094601⟩,⟨1154196895259821470290116,1154196895259947746904086⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨938191933419887188436104,938191933420028284569669⟩,⟨203789405366789792765555,203789405366930888857123⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨414835588051202070021614,414835588051326909377099⟩,⟨(-280209149033066504446001),(-280209149032941665122913)⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨13227477767462288042892,13227477767547603861525⟩,⟨(-219768052076989326558969),(-219768052076904010730521)⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨(-67772071711910905788868),(-67772071711869405727851)⟩,⟨(-51095086227292393608295),(-51095086227250893543760)⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨(-27719037404398245024563),(-27719037404385316266441)⟩,⟨10429412730812155260730,10429412730825084017061⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨(-2192506751294035346187),(-2192506751290305269496)⟩,⟨9377896137056890453193,9377896137060620529867⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨1910327240097733339826,1910327240098357495517⟩,⟨2326805588255635502633,2326805588256259658483⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨935064882238238384740,935064882238365195367⟩,⟨58084526334044083168,58084526334170893783⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨241905852637116208753,241905852637133966056⟩,⟨(-179852244827400183702),(-179852244827382426418)⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨37527342564209048700,37527342564213201525⟩,⟨(-96116341421332755803),(-96116341421328602976)⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨(-750961235459175192),(-750961235458256617)⟩,⟨(-36504272356826730760),(-36504272356825812184)⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨(-2051229946940659960),(-2051229946940492011)⟩,⟨(-9006684426959933831),(-9006684426959765887)⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨16363768589070955679672804,16363768589070956136643891⟩,⟨(-8895221499961541239589184),(-8895221499961540806511767)⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨30434805886742199720293929,30434805886742201146560657⟩,⟨(-37773341771543670987394056),(-37773341771543669599180622)⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨(-14909606860978574389887681),(-14909606860978572090924800)⟩,⟨(-64393676208657486927765342),(-64393676208657484607727239)⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨(-115461940949645272118278930),(-115461940949645268702815454)⟩,⟨(-17262233428145714766205618),(-17262233428145711236812413)⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨(-162632355406385784367464626),(-162632355406385776820737235)⟩,⟨132888218253480620869483533,132888218253480628504114171⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨(-57793900469728406769750674),(-57793900469728394805270350)⟩,⟨265311724863227251339688419,265311724863227263287013016⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨113793331636730452340320740,113793331636730466016752669⟩,⟨234193704752728328311700078,234193704752728341946312917⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨181424920766315456541397881,181424920766315468975173396⟩,⟨79669074654251698465631911,79669074654251710904075847⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨120163761074707022113217023,120163761074707032053419221⟩,⟨(-40682470779662597949654748),(-40682470779662587999190022)⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨33694900627575441728891942,33694900627575451918899649⟩,⟨(-63291607438832638404322644),(-63291607438832628216003391)⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨(-9375630724786302032644841),(-9375630724786286334803271)⟩,⟨(-36106937034134261165657502),(-36106937034134245469630977)⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨(-15182581677141571117246436),(-15182581677141540850837892)⟩,⟨(-10715208995131949011466069),(-10715208995131918744829208)⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨(-9165017771117638260941695),(-9165017771117602925376353)⟩,⟨113050372683838441679712,113050372683873777630567⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨(-3910040739236381746522069),(-3910040739236337664486033)⟩,⟨2260534647378237337731692,2260534647378281419848048⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨(-1325007940832693896394732),(-1325007940832659475637983)⟩,⟨1617827193861601478513349,1617827193861635899261839⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨(-293046645899837918328966),(-293046645899825593125679)⟩,⟨535280111537370304097880,535280111537382629293174⟩⟩
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
noncomputable def ans : CBox := ⟨⟨17966521082009631507472208,17966521082009783687614216⟩,⟨73679024198432332659076402,73679024198432484858277951⟩⟩
lemma checked : cachedMomentRuleBox density1 hk16_1_7 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule true true 16 7) := by
  rw [← checked]
  exact @cached_density_rule_contains density1 hk16_1_7 (tableDensity true) (fullFactor true 16 7) density1_contains hk16_1_7_contains
noncomputable def atomAnswer : CBox := ⟨⟨1126835522106805371334128408,1126835522106805377187877461⟩,⟨2667443973276857953330529868,2667443973276857959247704935⟩⟩
lemma atomChecked : tableAtomBox true ha16_1_7 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom true true 16 7) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains true true ha16_1_7 16 7 ha16_1_7_contains
 def realAnswer : RBox := ⟨1144802043188815002741600616,1144802043188815160975491677⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment true true 16 7) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm16_1_1_7
end SharpPlanar.CachedData

end OAI
