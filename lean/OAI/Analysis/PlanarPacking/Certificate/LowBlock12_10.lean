import OAI.Analysis.PlanarPacking.Certificate.TableDensityValues
import OAI.Analysis.PlanarPacking.Certificate.HighHeaders12

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace hm12_0_1_2
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density0 j i k).mul (hk12_1_2 j i k))
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
noncomputable def s1_0 : CBox := ⟨⟨(-45176),(-45143)⟩,⟨(-110630),(-110598)⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨(-62064),(-61992)⟩,⟨(-196166),(-196094)⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨(-14856),(-14758)⟩,⟨(-112840),(-112739)⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨5043,5173⟩,⟨(-30764),(-30633)⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨2671,2838⟩,⟨(-3966),(-3794)⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨315,519⟩,⟨(-238),(-34)⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨(-76),153⟩,⟨(-72),157⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨(-169),116⟩,⟨(-86),206⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨(-237),196⟩,⟨(-252),186⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨(-212),260⟩,⟨(-260),212⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨(-245),265⟩,⟨(-245),265⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨3933375281322587,3933375281322612⟩,⟨(-641032741258070),(-641032741258049)⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨7980279418444685,7980279418444719⟩,⟨(-2156775332567341),(-2156775332567303)⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨5923025500616306,5923025500616358⟩,⟨(-2940285079604783),(-2940285079604728)⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨2309388892055982,2309388892056049⟩,⟨(-2089913622270054),(-2089913622269985)⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨465385212390093,465385212390173⟩,⟨(-837577805640719),(-837577805640639)⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨31662222607114,31662222607220⟩,⟨(-200986062056746),(-200986062056640)⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨(-5744876625893),(-5744876625772)⟩,⟨(-30749300779456),(-30749300779332)⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨(-1710631607484),(-1710631607354)⟩,⟨(-3258668259327),(-3258668259197)⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨(-231790285734),(-231790285595)⟩,⟨(-269188990143),(-269188990004)⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨(-22932873604),(-22932873458)⟩,⟨(-20317442029),(-20317441883)⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨(-2009397539),(-2009397393)⟩,⟨(-1663554853),(-1663554709)⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨(-178246167),(-178246034)⟩,⟨(-166847084),(-166846949)⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨(-17672892),(-17672774)⟩,⟨(-21529468),(-21529352)⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨(-2102102),(-2102010)⟩,⟨(-3626490),(-3626394)⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨(-310896),(-310829)⟩,⟨(-778714),(-778650)⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨(-45915),(-45880)⟩,⟨(-151509),(-151476)⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨9278763636518935902123,9278763636518952461644⟩,⟨2399208828804281195110,2399208828804297753188⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨22765778207183146500405,22765778207183180784935⟩,⟨2691444712551899666557,2691444712551933948203⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨24047434448597781817525,24047434448597806951594⟩,⟨(-3566757831800230997828),(-3566757831800205865517)⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨14959608855274840889124,14959608855274849711830⟩,⟨(-8780186826889267734075),(-8780186826889258911193)⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨4813251634118498636869,4813251634118500077307⟩,⟨(-7797535539497400091828),(-7797535539497398650400)⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨(-71030283968133102171),(-71030283968132954895)⟩,⟨(-3754643190830310958785),(-3754643190830310811106)⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨(-752516030000133188555),(-752516030000133172966)⟩,⟨(-984360598462251337072),(-984360598462251321502)⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨(-331188010678741659540),(-331188010678741657015)⟩,⟨(-84730482004860512073),(-84730482004860509586)⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨(-75095820486457422545),(-75095820486457421764)⟩,⟨33567660000240299197,33567660000240299975⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨(-8789684214064353736),(-8789684214064353470)⟩,⟨15844358259275940318,15844358259275940588⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨323688308910625495,323688308910625616⟩,⟨3849291392592870458,3849291392592870577⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨477664148347784236,477664148347784309⟩,⟨699400210186004540,699400210186004613⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨173012686670963189,173012686670963245⟩,⟨105350821898332221,105350821898332279⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨53687052612594476,53687052612594522⟩,⟨12179080564477836,12179080564477885⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨16623430731591567,16623430731591599⟩,⟨90897520005967,90897520006003⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨3856615441330025,3856615441330048⟩,⟨(-401075848994442),(-401075848994417)⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨(-22421406012026968763575732),(-22421406012026343393822349)⟩,⟨58446469368387572643014978,58446469368388198007225881⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨(-35479941446680719227009390),(-35479941446678770657572712)⟩,⟨157173524392480702675749587,157173524392482651227119106⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨12542944717118883557726004,12542944717122148506720463⟩,⟨198015935391279839334171332,198015935391283104253311158⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨82490169746125052123394676,82490169746131114347410262⟩,⟨158101076635385486442737836,158101076635391548647462359⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨109851589473476983740302920,109851589473486129125561606⟩,⟨68265830660584973029861564,68265830660594118414312572⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨78979576380505946125546101,78979576380514536127596111⟩,⟨(-5658106669296075724991346),(-5658106669287485714333252)⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨30240176918869271976494583,30240176918876296506255718⟩,⟨(-29221798269463379461940400),(-29221798269456354927750733)⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨1211691627871586554009971,1211691627876142441813003⟩,⟨(-19802160371329624540655507),(-19802160371325068653536027)⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨(-5493880226666148091532586),(-5493880226664535895910199)⟩,⟨(-6534114145242447282821265),(-6534114145240835088274485)⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨(-3428924382365230038152803),(-3428924382364598203149840)⟩,⟨(-414383671402955867828873),(-414383671402324032895466)⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨(-1126895093971247058500823),(-1126895093971106195563471)⟩,⟨759554791985064434196127,759554791985205297269787⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨(-175686776737501477430872),(-175686776737470727602682)⟩,⟨508241010351210898825475,508241010351241648700860⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨46691456452247103356107,46691456452254481156579⟩,⟨214411890331201578075572,214411890331208955875513⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨55399366364010597075053,55399366364012141342680⟩,⟨74262039751896455591824,74262039751897999852997⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨30729018388983395740241,30729018388983728667210⟩,⟨22816640331369738278224,22816640331370071201039⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨9261916328542055399266,9261916328542120548988⟩,⟨4953942909492153858384,4953942909492219006871⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨(-5397682556790723588369101107),(-5397682556790723566564784892)⟩,⟨(-688013313160530264228005345),(-688013313160530242969613349)⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨(-14790129542576210418735493835),(-14790129542576210353881727940)⟩,⟨385017842033094067206428846,385017842033094130381464696⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨(-19428330179568408379791236603),(-19428330179568408273206634709)⟩,⟨6514399383256988650271975022,6514399383256988754862470413⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨(-16367429004378145230050464957),(-16367429004378145087770033690)⟩,⟨15021537809618236881039061104,15021537809618237022120495259⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨(-6550850850572654053972433179),(-6550850850572653887895878334)⟩,⟨19602427667415391926375678395,19602427667415392092477916171⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨4079612283704432288711121766,4079612283704432456845271762⟩,⟨16364566086906822384795569876,16364566086906822553702220505⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨9270552207626707460313702815,9270552207626707612034945158⟩,⟨7927918844958989737928567802,7927918844958989890156073679⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨7974866204358956853852934895,7974866204358956981165824907⟩,⟨354040686608866483369458182,354040686608866610685340170⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨3881161847844302883653783643,3881161847844302994043053033⟩,⟨(-2917176025505803657414096961),(-2917176025505803547125763849)⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨666628849936822127978081086,666628849936822304782960135⟩,⟨(-2736244804371148492008623166),(-2736244804371148315219105794)⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨(-641199196071832091488567946),(-641199196071831672403382827)⟩,⟨(-1456930382867572068597415840),(-1456930382867571649506307813)⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨(-748861187524342660956572119),(-748861187524341917263116007)⟩,⟨(-478953266631154550277359522),(-478953266631153806587191241)⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨(-490007294114885652349826562),(-490007294114884258281601998)⟩,⟨(-37056306148351337317366565),(-37056306148349943254291115)⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨(-252139922479258121394554815),(-252139922479256378182228825)⟩,⟨79886673577165079583311371,79886673577166822793325377⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨(-109041660564449527036921913),(-109041660564448160990215173)⟩,⟨69541579671471209287390204,69541579671472575333742193⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨(-29587852787402706014873829),(-29587852787402205227228341)⟩,⟨24932989602945337037063968,24932989602945837824767184⟩⟩
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
noncomputable def ans : CBox := ⟨⟨(-6447505288331319521766753773),(-6447505288331311014296307911)⟩,⟨9768305359185092716978351661,9768305359185101223733142803⟩⟩
lemma checked : cachedMomentRuleBox density0 hk12_1_2 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule false true 12 2) := by
  rw [← checked]
  exact @cached_density_rule_contains density0 hk12_1_2 (tableDensity false) (fullFactor true 12 2) density0_contains hk12_1_2_contains
noncomputable def atomAnswer : CBox := ⟨⟨(-3036337511847772115291963788),(-3036337511847772095896664141)⟩,⟨18873683542964848637043401044,18873683542964848656585892083⟩⟩
lemma atomChecked : tableAtomBox false ha12_1_2 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom false true 12 2) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains false true ha12_1_2 12 2 ha12_1_2_contains
 def realAnswer : RBox := ⟨(-9483842800179091637158717561),(-9483842800179083110092972052)⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment false true 12 2) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm12_0_1_2
namespace hm12_1_1_2
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density1 j i k).mul (hk12_1_2 j i k))
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
noncomputable def s1_0 : CBox := ⟨⟨2002,2019⟩,⟨(-18539),(-18521)⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨5606,5626⟩,⟨(-31222),(-31199)⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨5547,5572⟩,⟨(-16259),(-16234)⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨2522,2551⟩,⟨(-3832),(-3802)⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨555,591⟩,⟨(-394),(-360)⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨43,82⟩,⟨(-22),21⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨(-18),30⟩,⟨(-16),32⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨(-32),16⟩,⟨(-17),31⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨(-47),33⟩,⟨(-48),32⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨(-36),48⟩,⟨(-48),36⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨(-43),48⟩,⟨(-43),48⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨832158505534274,832158505534293⟩,⟨342093600827068,342093600827086⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨1789720452379850,1789720452379871⟩,⟨537543872155452,537543872155475⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨1483908096536626,1483908096536652⟩,⟨156850297287428,156850297287454⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨685675880779848,685675880779880⟩,⟨(-105790074056623),(-105790074056593)⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨184795865256559,184795865256594⟩,⟨(-92900079943918),(-92900079943885)⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨28696538947871,28696538947911⟩,⟨(-30431700217243),(-30431700217205)⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨2345422972011,2345422972052⟩,⟨(-5620972575119),(-5620972575080)⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨39560160083,39560160124⟩,⟨(-684207380925),(-684207380885)⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨(-13760957013),(-13760956976)⟩,⟨(-62974433174),(-62974433139)⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨(-2081630510),(-2081630473)⟩,⟨(-5099692080),(-5099692045)⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨(-199877774),(-199877738)⟩,⟨(-422217301),(-422217268)⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨(-16350171),(-16350139)⟩,⟨(-39988827),(-39988792)⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨(-1236818),(-1236789)⟩,⟨(-4639860),(-4639831)⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨(-75559),(-75537)⟩,⟨(-694297),(-694269)⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨2903,2926⟩,⟨(-135599),(-135573)⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨2386,2403⟩,⟨(-25084),(-25066)⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨2007238489431523069401,2007238489431536970054⟩,⟨2497205993805767287581,2497205993805781188382⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨5468702813690106743548,5468702813690135501091⟩,⟨5210191719261384671780,5210191719261413429621⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨6841871429869903418836,6841871429869924465560⟩,⟨3726980838322656915068,3726980838322677961975⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨5324565967501843821179,5324565967501851186294⟩,⟨601685029490495155449,601685029490502520546⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨2526438999457965109159,2526438999457966302819⟩,⟨(-1025700344120327796425),(-1025700344120326602870)⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨610308087177606076547,610308087177606193641⟩,⟨(-897391686496019539440),(-897391686496019422390)⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨(-17240356567441021519),(-17240356567441011324)⟩,⟨(-350840978006735535961),(-350840978006735525762)⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨(-63116872409771398282),(-63116872409771397244)⟩,⟨(-71674113497483781207),(-71674113497483780164)⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨(-22282587574094742077),(-22282587574094741790)⟩,⟨(-3982957822915887583),(-3982957822915887295)⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨(-4377900808569853463),(-4377900808569853362)⟩,⟨2220960620395791026,2220960620395791129⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨(-499423260083796524),(-499423260083796469)⟩,⟨905232537048555422,905232537048555476⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨4738266875278995,4738266875279032⟩,⟨225523893591548435,225523893591548470⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨23763378255544861,23763378255544891⟩,⟨48605038289778356,48605038289778385⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨10462804802421013,10462804802421040⟩,⟨10483388441311872,10483388441311899⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨3803270035655196,3803270035655219⟩,⟨2417488189220529,2417488189220558⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨947923314138360,947923314138380⟩,⟨465446827641750,465446827641769⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨(-6372953294873146033005504),(-6372953294872632350679548)⟩,⟨19554624949682726373303471,19554624949683240056464176⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨(-9625531587663125116879534),(-9625531587661524317190315)⟩,⟨53150738705192541044069171,53150738705194141846830956⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨5820536054900905771074718,5820536054903588618922445⟩,⟨68489618813960457413589732,68489618813963140267103171⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨28672905999722498644401030,28672905999727481705894059⟩,⟨56986294822231324445810400,56986294822236307511512784⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨38546985418863727043890063,38546985418871246011664917⟩,⟨27194263462387448206731009,27194263462394967175170363⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨29073561410390271590004596,29073561410397334207039616⟩,⟨724660822616515216774394,724660822623577832235511⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨12424928388933915494763311,12424928388939689918075031⟩,⟨(-9334714223640654552985598),(-9334714223634880130646633)⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨1549607319863745620488529,1549607319867489085360951⟩,⟨(-7281807435706418667229251),(-7281807435702675202254438)⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨(-1621620754551197586670113),(-1621620754549873931951368)⟩,⟨(-2852289081094414703687521),(-2852289081093091048745582)⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨(-1275503771769258719216854),(-1275503771768740506935890)⟩,⟨(-468818518905639515510667),(-468818518905121303211599)⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨(-516909850051423638555257),(-516909850051308250606876)⟩,⟨157727713758057958625762,157727713758173346549354⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨(-136104841415359826776811),(-136104841415334674374519)⟩,⟨161715952576950721561346,161715952576975873954778⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨(-17495923386810371281147),(-17495923386804344370058)⟩,⟨81553009672159378865093,81553009672165405776156⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨5971623771348243743950,5971623771349503750655⟩,⟨33212460771424864980810,33212460771426124988617⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨5874109032562547053047,5874109032562818431889⟩,⟨12095392999571075737617,12095392999571347117167⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨2026530380358671645077,2026530380358724720741⟩,⟨2997449032900130748841,2997449032900183824713⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨(-161254533787172633346022735),(-161254533787172631300838966)⟩,⟨(-12849092806545681585306058),(-12849092806545679903419348)⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨(-414772383363601446366855165),(-414772383363601440480125754)⟩,⟨116420361366268564520670981,116420361366268569288057397⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨(-281395786878824595804296927),(-281395786878824586234293178)⟩,⟨547035070184667768417925479,547035070184667776691666747⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨642265143895295574785828308,642265143895295588691367402⟩,⟨962197628880717194689370329,962197628880717207896071594⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨2135336761713684894691273766,2135336761713684918838214455⟩,⟨683941644000675942244036105,683941644000675966537610757⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨3134690549640759156484005608,3134690549640759191260320347⟩,⟨(-546954996615021195389180546),(-546954996615021159899000114)⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨2757420973150716611131348299,2757420973150716653677391042⟩,⟨(-1997949745232088884188853805),(-1997949745232088841185459742)⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨1325222508583160057843402912,1325222508583160104076223259⟩,⟨(-2613724032996266709466691614),(-2613724032996266663279394295)⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨(-66186862999300351514838849),(-66186862999300298969363196)⟩,⟨(-2140533182548542627257470248),(-2140533182548542574883425181)⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨(-719482368644682681620310137),(-719482368644682560084235861)⟩,⟨(-1186637106119451099939101451),(-1186637106119450978442324756)⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨(-719632097514489292856063890),(-719632097514488964426021338)⟩,⟨(-407101176235853841299951668),(-407101176235853512847701461)⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨(-467931586961764161609233284),(-467931586961763562553444559)⟩,⟨(-12418137406233879236299834),(-12418137406233280158689691)⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨(-236694139048399560492296558),(-236694139048398426290480413)⟩,⟨104187630713177745008687178,104187630713178879215167194⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨(-99522329043234332678054306),(-99522329043232910394695710)⟩,⟨98067418156301442488259269,98067418156302864770323778⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨(-35249807155538362452965086),(-35249807155537246708991522)⟩,⟨59354253747788311276859948,59354253747789427019356571⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨(-8184662235737837504712749),(-8184662235737428305297849)⟩,⟨19158168836559086397841067,19158168836559495596730166⟩⟩
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
noncomputable def ans : CBox := ⟨⟨1146864721306731587926302212,1146864721306738459936466721⟩,⟨(-1020197288315053762021380846),(-1020197288315046890404304961)⟩⟩
lemma checked : cachedMomentRuleBox density1 hk12_1_2 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule true true 12 2) := by
  rw [← checked]
  exact @cached_density_rule_contains density1 hk12_1_2 (tableDensity true) (fullFactor true 12 2) density1_contains hk12_1_2_contains
noncomputable def atomAnswer : CBox := ⟨⟨3970595207800932740787945416,3970595207800932766151029568⟩,⟨(-24680970786954032858612320415),(-24680970786954032833056755212)⟩⟩
lemma atomChecked : tableAtomBox true ha12_1_2 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom true true 12 2) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains true true ha12_1_2 12 2 ha12_1_2_contains
 def realAnswer : RBox := ⟨5117459929107664328614247628,5117459929107671226187496289⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment true true 12 2) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm12_1_1_2
namespace hm12_0_1_3
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density0 j i k).mul (hk12_1_3 j i k))
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
noncomputable def s1_0 : CBox := ⟨⟨(-115564),(-115494)⟩,⟨259421,259492⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨(-233209),(-233013)⟩,⟨431711,431905⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨(-167783),(-167488)⟩,⟨215646,215941⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨(-61204),(-60807)⟩,⟨44308,44708⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨(-11726),(-11211)⟩,⟨2046,2562⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨(-1295),(-704)⟩,⟨(-742),(-147)⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨(-329),314⟩,⟨(-467),176⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨(-231),539⟩,⟨(-469),302⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨(-565),553⟩,⟨(-454),661⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨(-645),483⟩,⟨(-554),573⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨(-560),545⟩,⟨(-585),521⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨(-4812511575754318),(-4812511575754292)⟩,⟨(-6093408818703045),(-6093408818703016)⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨(-11306561332165950),(-11306561332165902)⟩,⟨(-11547199072641335),(-11547199072641286)⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨(-10805549036416347),(-10805549036416275)⟩,⟨(-7254216411028311),(-7254216411028242)⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨(-5905488208544204),(-5905488208544109)⟩,⟨(-1858260391661451),(-1858260391661352)⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨(-1927666141520400),(-1927666141520280)⟩,⟨73867394428487,73867394428609⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨(-381904977417345),(-381904977417178)⟩,⟨164812495075982,164812495076152⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨(-46747554034997),(-46747554034782)⟩,⟨45262379048443,45262379048655⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨(-3600811323292),(-3600811323047)⟩,⟨6920165986053,6920165986300⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨(-173391764772),(-173391764480)⟩,⟨747965824858,747965825149⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨(-4570949266),(-4570948937)⟩,⟨67370809471,67370809803⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨(-55459316),(-55458964)⟩,⟨5857278286,5857278640⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨(-26188080),(-26187736)⟩,⟨557000168,557000510⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨(-10113782),(-10113472)⟩,⟨63752922,63753235⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨(-2926620),(-2926363)⟩,⟨9380469,9380724⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨(-836533),(-836364)⟩,⟨1795962,1796131⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨(-185096),(-185027)⟩,⟨326780,326849⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨(-1005067421989872443992),(-1005067421989840045694)⟩,⟨(-15512755699163533155788),(-15512755699163500756136)⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨(-7525309341075168399889),(-7525309341075104329874)⟩,⟨(-36531361017642543382366),(-36531361017642479310233)⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨(-18171742843237186044082),(-18171742843237142640586)⟩,⟨(-35404031145226940894198),(-35404031145226897490832)⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨(-21836159564580006983124),(-21836159564579993335849)⟩,⟨(-18546032643344461278900),(-18546032643344447634109)⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨(-14988057546311646316044),(-14988057546311644196800)⟩,⟨(-3123822840363079222510),(-3123822840363077105367)⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨(-5906798585521806892361),(-5906798585521806605306)⟩,⟨2361837507486184385353,2361837507486184672193⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨(-1097651455901783941520),(-1097651455901783916661)⟩,⟨1827816332150061581521,1827816332150061606577⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨85919873071768970086,85919873071768974203⟩,⟨592137680535804178757,592137680535804182931⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨108450726013889495860,108450726013889497116⟩,⟨98574016919394077877,98574016919394079127⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨32771627720164214352,32771627720164214768⟩,⟨2474623871885643397,2474623871885643812⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨6139947701263377647,6139947701263377832⟩,⟨(-3621801262412482914),(-3621801262412482731)⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨769478405582541134,769478405582541237⟩,⟨(-1389120052877588931),(-1389120052877588823)⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨25613543534842374,25613543534842450⟩,⟨(-384226753862416351),(-384226753862416275)⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨(-28136615816560552),(-28136615816560492)⟩,⟨(-102006407383314548),(-102006407383314486)⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨(-15298278166993145),(-15298278166993102)⟩,⟨(-28334240836709735),(-28334240836709693)⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨(-4310221321097405),(-4310221321097381)⟩,⟨(-6187169363356570),(-6187169363356544)⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨84923530654620563576754314,84923530654621359654675422⟩,⟨16769602696863698997587019,16769602696864495086125165⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨223151160804464225075854802,223151160804466637758731778⟩,⟨10755473705847637759647719,10755473705850050474868724⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨268508481907607257856632210,268508481907611983158651344⟩,⟨(-66293773191680440400397202),(-66293773191675715058466946)⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨196837594511969704889887489,196837594511978901675643040⟩,⟨(-154965422404387081262441431),(-154965422404377884459524940)⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨64770796389675320491203162,64770796389688133084803207⟩,⟨(-171721405137964768691284933),(-171721405137951956104571602)⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨(-31206014269464195743033955),(-31206014269452691623159589)⟩,⟨(-109357487702817442523093880),(-109357487702805938418727775)⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨(-51094688369686555777968544),(-51094688369675413552561153)⟩,⟨(-33733658066897534157538244),(-33733658066886391935802417)⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨(-28886081205069939027888883),(-28886081205063624537406081)⟩,⟨5002054285112539104731162,5002054285118853597627483⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨(-7495211602811406035287525),(-7495211602808844257948493)⟩,⟨10389908544124621560992975,10389908544127183339667812⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨738069943094036289896253,738069943094995343584913⟩,⟨5212440747304635044740451,5212440747305594098251840⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨1604019263153630289367769,1604019263153831016773289⟩,⟨1359555626156142248832093,1359555626156342975983334⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨842738906675543479892315,842738906675597038192037⟩,⟨38450005176103685736801,38450005176157244006746⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨303629978067108649438840,303629978067119835296872⟩,⟨(-170867299498596653890673),(-170867299498585468012521)⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨86652268234022971161524,86652268234025062979041⟩,⟨(-120621436319407805338721),(-120621436319405713504313)⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨19762103159258872674089,19762103159259446213686⟩,⟨(-58518837922116412681923),(-58518837922115839136415)⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨2961441545201427964892,2961441545201559043850⟩,⟨(-16749134240999004202630),(-16749134240998873122418)⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨(-487158762020187309824480151),(-487158762020187283311388359)⟩,⟨6544270115818862399111730024,6544270115818862426333981689⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨1440048197341659132725270046,1440048197341659212124119065⟩,⟨17826673430532149958507019431,17826673430532150039974079728⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨9282063883519460003366457498,9282063883519460136213003523⟩,⟨23088741466731187265148006034,23088741466731187400269962093⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨19622364063645969866532354640,19622364063645970047196413442⟩,⟨18780800701750534495903963719,18780800701750534677818612962⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨24698138446775937366441803109,24698138446775937581400436445⟩,⟨6307163783781218776892923846,6307163783781218991609403374⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨19911408535967061784553453811,19911408535967062006019671030⟩,⟨(-6730722502079617405753772517),(-6730722502079617185372874879)⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨8880784323296607654175476159,8880784323296607857440593472⟩,⟨(-12558640175536364489324050888),(-12558640175536364286607903191)⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨(-598647802555298998393672176),(-598647802555298826690887918)⟩,⟨(-10177217613535521439194580107),(-10177217613535521267434350475)⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨(-4325196706356886934925928089),(-4325196706356886784747521455)⟩,⟨(-4557934044601750041477597104),(-4557934044601749891157544344)⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨(-3670108604074382730445445491),(-3670108604074382488942202492)⟩,⟨(-415749236572351766498310628),(-415749236572351524983767077)⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨(-1800771720211684653153976612),(-1800771720211684116722505849)⟩,⟨1108485345939374607503102933,1108485345939375143926059235⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨(-489147720410445438606958067),(-489147720410444407440608500)⟩,⟨1090178252990055597008912835,1090178252990056628179882144⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨53625234399220086128296875,53625234399222078886345428⟩,⟨665159602314512058987833925,665159602314514051751727700⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨163883248459794721970686286,163883248459797098958468050⟩,⟨322899988484121189800239787,322899988484123566789803750⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨119455385543375942683596776,119455385543377740303725008⟩,⟨132053591235185616949582115,132053591235187414569403032⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨40848171082804103528042002,40848171082804748821197816⟩,⟨34438911502592445707663729,34438911502593091000498926⟩⟩
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
noncomputable def ans : CBox := ⟨⟨12260770880055968481628848011,12260770880055980597676654575⟩,⟨6828931060071954032727956701,6828931060071966149562050434⟩⟩
lemma checked : cachedMomentRuleBox density0 hk12_1_3 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule false true 12 3) := by
  rw [← checked]
  exact @cached_density_rule_contains density0 hk12_1_3 (tableDensity false) (fullFactor true 12 3) density0_contains hk12_1_3_contains
noncomputable def atomAnswer : CBox := ⟨⟨22886035405279798164259493093,22886035405279798189141244376⟩,⟨2456094325861157821434800458,2456094325861157846092042577⟩⟩
lemma atomChecked : tableAtomBox false ha12_1_3 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom false true 12 3) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains false true ha12_1_3 12 3 ha12_1_3_contains
 def realAnswer : RBox := ⟨35146806285335766645788341104,35146806285335778786917898951⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment false true 12 3) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm12_0_1_3
namespace hm12_1_1_3
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density1 j i k).mul (hk12_1_3 j i k))
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
noncomputable def s1_0 : CBox := ⟨⟨(-35116),(-35094)⟩,⟨27017,27039⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨(-62818),(-62780)⟩,⟨42155,42195⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨(-37162),(-37111)⟩,⟨17916,17968⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨(-10911),(-10850)⟩,⟨2270,2335⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨(-1704),(-1626)⟩,⟨(-330),(-248)⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨(-163),(-71)⟩,⟨(-150),(-58)⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨(-46),52⟩,⟨(-73),34⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨(-33),84⟩,⟨(-71),51⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨(-97),90⟩,⟨(-81),110⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨(-112),88⟩,⟨(-100),100⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨(-98),93⟩,⟨(-102),88⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨(-204457161151654),(-204457161151633)⟩,⟨(-1741018384659903),(-1741018384659884)⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨(-794153269259536),(-794153269259512)⟩,⟨(-3565914242865536),(-3565914242865511)⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨(-1179972486520521),(-1179972486520486)⟩,⟨(-2689373722829627),(-2689373722829595)⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨(-870795673043861),(-870795673043823)⟩,⟨(-1069326215741097),(-1069326215741059)⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨(-352884805996024),(-352884805995983)⟩,⟨(-221038829011010),(-221038829010970)⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨(-83924809658755),(-83924809658703)⟩,⟨(-16355892864612),(-16355892864558)⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨(-12441883314292),(-12441883314236)⟩,⟨2382678131311,2382678131369⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨(-1238407662543),(-1238407662481)⟩,⟨759015341640,759015341700⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨(-92228822998),(-92228822934)⟩,⟨104412441186,104412441249⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨(-6094488586),(-6094488520)⟩,⟨10498406843,10498406910⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨(-453025417),(-453025351)⟩,⟨946021416,946021483⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨(-45325751),(-45325689)⟩,⟨87639999,87640061⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨(-6137247),(-6137190)⟩,⟨9282195,9282253⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨(-1078755),(-1078709)⟩,⟨1231496,1231542⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨(-238044),(-238008)⟩,⟨214553,214587⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨(-47005),(-46981)⟩,⟨36924,36945⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨2830643010761328402464,2830643010761355604852⟩,⟨(-4358219803016209963993),(-4358219803016182761744)⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨5238677471898003769952,5238677471898057522201⟩,⟨(-11116848416651391605723),(-11116848416651337853693)⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨2180960568712437883315,2180960568712474233256⟩,⟨(-12565562823741447016955),(-12565562823741410667001)⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨(-1960559057457851568877),(-1960559057457840178679)⟩,⟨(-8629942897499708750088),(-8629942897499697359635)⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨(-3048711527554447335398),(-3048711527554445582497)⟩,⟨(-3384956309256477168135),(-3384956309256475415028)⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨(-1787472670164406202334),(-1787472670164405972866)⟩,⟨(-429456250866402398962),(-429456250866402169472)⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨(-550300140964523176077),(-550300140964523159787)⟩,⟨249971527258238404397,249971527258238420666⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨(-73346080893399863808),(-73346080893399862066)⟩,⟨150202017169081585463,150202017169081587202⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨9422157912749295330,9422157912749295789⟩,⟨39212707647695175011,39212707647695175469⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨6977898262894512674,6977898262894512828⟩,⟨5530729495845900519,5530729495845900672⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨1904952464155182442,1904952464155182511⟩,⟨105081423246562854,105081423246562930⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨373815597545481151,373815597545481197⟩,⟨(-197833938315397975),(-197833938315397929)⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨61063739786382400,61063739786382437⟩,⟨(-82762244936954564),(-82762244936954523)⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨8254105546406587,8254105546406620⟩,⟨(-27246380445958163),(-27246380445958130)⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨572801303084625,572801303084650⟩,⟨(-8710511726392941),(-8710511726392913)⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨(-99373606264634),(-99373606264613)⟩,⟨(-2051280298297536),(-2051280298297517)⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨28147070808216337852240437,28147070808216991708749666⟩,⟨4072795305396364210514682,4072795305397018065252989⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨74894185258157583362063362,74894185258159565294565282⟩,⟨396780859449913582991493,396780859451895509712338⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨92507366029207751650639015,92507366029211634511081416⟩,⟨(-24963737106457097238560456),(-24963737106453214385796045)⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨71228390566747229097369769,71228390566754788760422019⟩,⟨(-54394379905153484861537394),(-54394379905145925202424634)⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨27241133462075394847017838,27241133462085928757773270⟩,⟨(-61151670731994352871725421),(-61151670731983818960136351)⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨(-7539901901731913133863760),(-7539901901722454677732139)⟩,⟨(-41084469272874516081836269),(-41084469272865057622722116)⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨(-17196880156249297448240067),(-17196880156240138083173153)⟩,⟨(-14706286973286420794775344),(-14706286973277261428873639)⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨(-10998895472815375656476853),(-10998895472810187166028749)⟩,⟨251838331543593816408667,251838331548782306382008⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨(-3556823833141424591878614),(-3556823833139321347181081)⟩,⟨3405519229310457605862319,3405519229312560850278707⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨(-188958931503781689026421),(-188958931502995091417577)⟩,⟨2062861848365761048401791,2062861848366547646041573⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨451771794337890541216809,451771794338054959338347⟩,⟨703730717422772252766430,703730717422936670935409⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨303794642722112857946245,303794642722156667910639⟩,⟨132935157694952458729064,132935157694996268699253⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨131933048685126716378687,131933048685135854122898⟩,⟨(-11474773902071531523119),(-11474773902062393782434)⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨47861343757452570313412,47861343757454277010627⟩,⟨(-25207599548464177310808),(-25207599548462470616554)⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨15652099736732104723643,15652099736732572246083⟩,⟨(-15029154585651231131593),(-15029154585650763610170)⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨3593050133425916870410,3593050133426023671386⟩,⟨(-4628147181119223230581),(-4628147181119116429817)⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨(-5272115208454098630255009),(-5272115208454096647837719)⟩,⟨195019541124296802493371123,195019541124296804943963018⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨167904431128920074047549865,167904431128920079895775570⟩,⟨492903042227481328370591583,492903042227481335581163143⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨683230973662621484827427894,683230973662621495397489816⟩,⟨301781115040972161115002720,301781115040972173126246323⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨1122840516771637315764201558,1122840516771637332558431725⟩,⟨(-860794954991351978246009316),(-860794954991351960771100692)⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨649683192933469310291888782,649683192933469341386781444⟩,⟨(-2689538650551357241099488363),(-2689538650551357210354931284)⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨(-999547397330969491799160464),(-999547397330969445703490095)⟩,⟨(-3839830994698054255321596711),(-3839830994698054210217443254)⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨(-2829866701740903199742224045),(-2829866701740903142413982841)⟩,⟨(-3232213255665021630892425479),(-3232213255665021574039067506)⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨(-3496025314661026916373778233),(-3496025314661026854615352626)⟩,⟨(-1340389233403746800669329172),(-1340389233403746738778277485)⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨(-2743168236130983573370959779),(-2743168236130983502725532035)⟩,⟨402029389084197703641031548,402029389084197774522023773⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨(-1425617400678093722046837239),(-1425617400678093556852252058)⟩,⟨1132093127759930926673346498,1132093127759931091894994660⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨(-405138956710129839899538103),(-405138956710129421433833709)⟩,⟨1021074898689264596218714162,1021074898689265014643258513⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨75739632308756850222725000,75739632308757680459680997⟩,⟨624675366122455249235680204,624675366122456079443507573⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨189680921011100021858312658,189680921011101643056284493⟩,⟨295564025383823935553121890,295564025383825556748491509⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨154574086942093617680606370,154574086942095556807554285⟩,⟨112686295040507559266484361,112686295040509498396880334⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨88674311264274052933278300,88674311264275520983269658⟩,⟨34217941693004242307080086,34217941693005710359845973⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨27986090817601650030305195,27986090817602177240204267⟩,⟨6660530310402665179573742,6660530310403192390406126⟩⟩
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
noncomputable def ans : CBox := ⟨⟨(-1414804637529176889836515858),(-1414804637529167089877446509)⟩,⟨(-1254905379890222710350370433),(-1254905379890212909982973483)⟩⟩
lemma checked : cachedMomentRuleBox density1 hk12_1_3 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule true true 12 3) := by
  rw [← checked]
  exact @cached_density_rule_contains density1 hk12_1_3 (tableDensity true) (fullFactor true 12 3) density1_contains hk12_1_3_contains
noncomputable def atomAnswer : CBox := ⟨⟨(-29927892453058197631953934954),(-29927892453058197599416260198)⟩,⟨(-3211815656895360260274209524),(-3211815656895360228030123677)⟩⟩
lemma atomChecked : tableAtomBox true ha12_1_3 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom true true 12 3) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains true true ha12_1_3 12 3 ha12_1_3_contains
 def realAnswer : RBox := ⟨(-31342697090587374521890450812),(-31342697090587364689193706707)⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment true true 12 3) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm12_1_1_3
namespace hm12_0_1_4
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density0 j i k).mul (hk12_1_4 j i k))
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
noncomputable def s1_0 : CBox := ⟨⟨476415,476506⟩,⟨(-171474),(-171382)⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨844966,845221⟩,⟨(-238078),(-237824)⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨488593,488973⟩,⟨(-58811),(-58437)⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨135712,136249⟩,⟨19631,20163⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨17928,18683⟩,⟨11024,11779⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨360,1320⟩,⟨1389,2346⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨(-746),408⟩,⟨(-357),798⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨(-1099),428⟩,⟨(-815),706⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨(-1091),1348⟩,⟨(-1372),1070⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨(-1202),1491⟩,⟨(-1272),1423⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨(-1458),1414⟩,⟨(-1372),1500⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨(-4370066829232682),(-4370066829232645)⟩,⟨10470790411836704,10470790411836740⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨(-6662415672654170),(-6662415672654095)⟩,⟨22739707092764333,22739707092764406⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨(-1390245550146152),(-1390245550146029)⟩,⟨19160814774021919,19160814774022041⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨2064108792011102,2064108792011280⟩,⟨8995459470255075,8995459470255249⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨1605517143286425,1605517143286648⟩,⟨2430359726715264,2430359726715484⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨526471936368106,526471936368415⟩,⟨359931685048232,359931685048537⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨99133961556633,99133961557020⟩,⟨21848272108892,21848272109278⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨12299662944916,12299662945353⟩,⟨(-1581559023467),(-1581559023028)⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨1144238828743,1144238829245⟩,⟨(-489701975168),(-489701974667)⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨92772432044,92772432594⟩,⟨(-62058795678),(-62058795127)⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨7715717501,7715718062⟩,⟨(-6145947044),(-6145946482)⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨755453170,755453699⟩,⟨(-584449380),(-584448854)⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨94525337,94525793⟩,⟨(-60433365),(-60432906)⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨15626313,15626674⟩,⟨(-7369938),(-7369584)⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨3333787,3334019⟩,⟨(-1102261),(-1102027)⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨648139,648228⟩,⟨(-162896),(-162807)⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨(-17544917062908941575111),(-17544917062908899366501)⟩,⟨7057087389319928830586,7057087389319971038927⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨(-39407414300870582725647),(-39407414300870502397164)⟩,⟨22772394101538698644874,22772394101538778974176⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨(-33998023747322395451538),(-33998023747322345020951)⟩,⟨35087897345439115864904,35087897345439166299332⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨(-12771663520515802174353),(-12771663520515787777100)⟩,⟨33110604725441004135968,33110604725441018538327⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨2716954353645983015048,2716954353645986097587⟩,⟨18991531897605579550564,18991531897605582634701⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨5460945540287470059561,5460945540287470424789⟩,⟨5958239282340512964721,5958239282340513329598⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨2714860204435277586243,2714860204435277613559⟩,⟨447795937966519701363,447795937966519728324⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨674198249725984076512,674198249725984081165⟩,⟨(-402949331333659912532),(-402949331333659907897)⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨62524292387339131009,62524292387339132420⟩,⟨(-185585049366174031509),(-185585049366174030076)⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨(-15573490663255283112),(-15573490663255282594)⟩,⟨(-41908065055455012290),(-41908065055455011767)⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨(-8205039491318740265),(-8205039491318740015)⟩,⟨(-5479053875937859631),(-5479053875937859384)⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨(-2231284382604067629),(-2231284382604067475)⟩,⟨(-89485318203874026),(-89485318203873880)⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨(-502683613215028198),(-502683613215028084)⟩,⟨220785829589529690,220785829589529804⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨(-110425168706999023),(-110425168706998929)⟩,⟨105242199737834178,105242199737834273⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨(-25447338596545192),(-25447338596545126)⟩,⟨39252587826804605,39252587826804671⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨(-4857818196787148),(-4857818196787117)⟩,⟨9867138027362324,9867138027362354⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨2119271336288401173970443,2119271336289131387630307⟩,⟨(-89750634722045972930944905),(-89750634722045242731037427)⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨(-29125695903253131481053631),(-29125695903250742037080631)⟩,⟨(-230491828911465683627295347),(-230491828911463294219529579)⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨(-118126123452733465937798258),(-118126123452727938109112981)⟩,⟨(-263907830201142043323594201),(-263907830201136515526517496)⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨(-198819115874882862551788256),(-198819115874872790799270851)⟩,⟨(-173611155079966413946441886),(-173611155079956342201028387)⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨(-192663965118050553267522829),(-192663965118037614465233955)⟩,⟨(-32144128838794301717532093),(-32144128838781362899699364)⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨(-108402793157040766400442606),(-108402793157028235603963472)⟩,⟨57050048397722516955638094,57050048397735047768797071⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨(-23832985424827308987092997),(-23832985424814724878724000)⟩,⟨62464635699903374787126546,62464635699915958896299823⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨12774047293095713051997750,12774047293102146284795718⟩,⟨29873181322115310537860558,29873181322121743766826804⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨13400579050960016112904490,13400579050963212280533752⟩,⟨5324028532778203164295212,5324028532781399331122631⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨5539209717372819841677882,5539209717373837927742328⟩,⟨(-2352571135304869550565611),(-2352571135303851463988772)⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨1013723314621215098932005,1013723314621465279226928⟩,⟨(-2219493304454509663284137),(-2219493304454259482756975)⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨(-237537358189020122053188),(-237537358188955990523115)⟩,⟨(-963749666520154308565547),(-963749666520090177055554)⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨(-300708894909249059040061),(-300708894909237453489297)⟩,⟨(-285832417350866763803464),(-285832417350855158296957)⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨(-169717571168951033334674),(-169717571168948299931607)⟩,⟨(-55498148635432421729770),(-55498148635429688343640)⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨(-74751634657998302203697),(-74751634657997500755094)⟩,⟨(-946777484149157299145),(-946777484148355854102)⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨(-20452113505763951528634),(-20452113505763777041780)⟩,⟨2906128150689411965962,2906128150689586452351⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨5934350419333120308461485592,5934350419333120333854880129⟩,⟨129542476936097909279866020,129542476936097933988874760⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨16066715107774737673612754026,16066715107774737750191173444⟩,⟨(-2185334635348366238981844272),(-2185334635348366164238859856)⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨20496730939939879825234287912,20496730939939879953065389123⟩,⟨(-9673748166669934197561677270),(-9673748166669934071657018542)⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨16020774432514688013263238310,16020774432514688186691666480⟩,⟨(-19070154009789200492404506321),(-19070154009789200319916725607)⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨4163843328256076221259254411,4163843328256076428009436446⟩,⟨(-23208559163963798733999881467),(-23208559163963798526831568764)⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨(-7788480762778773460525788136),(-7788480762778773245526012914)⟩,⟨(-18035431096465692241295290309),(-18035431096465692025203955392)⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨(-12598422743119904209324728406),(-12598422743119904008404102449)⟩,⟨(-7272024985306018517517954356),(-7272024985306018316168885494)⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨(-9637245093299653583981410475),(-9637245093299653412389158965)⟩,⟨1574049192077834251165269553,1574049192077834422644198553⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨(-3914551595388498798970287008),(-3914551595388498646393982388)⟩,⟨4676854283740283027372694043,4676854283740283179809579175⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨48685654783351110258464894,48685654783351353492055046⟩,⟨3632812928431867910812469846,3632812928431868154043405996⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨1339451946555696671212504671,1339451946555697175131283852⟩,⟨1626242648434190559273091554,1626242648434191063200790555⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨1159522262981503762271181876,1159522262981504876150527068⟩,⟨326521774642845398756404276,326521774642846512631385493⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨660751150254010848820362304,660751150254012930416664852⟩,⟨(-159167037407536793809747684),(-159167037407534712217783415)⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨299887441774421095517948803,299887441774423461534059209⟩,⟨(-219799738438028460020463982),(-219799738438026094004601929)⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨113869843905087683605902424,113869843905089401822465285⟩,⟨(-144376869225219649061357528),(-144376869225217930843639791)⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨27990511777117227636949139,27990511777117828765679206⟩,⟨(-47731164002298719076110698),(-47731164002298117946806778)⟩⟩
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
noncomputable def ans : CBox := ⟨⟨5292808951712440986669810653,5292808951712453941388144891⟩,⟨(-11448541606916075010199942288),(-11448541606916062056108621972)⟩⟩
lemma checked : cachedMomentRuleBox density0 hk12_1_4 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule false true 12 4) := by
  rw [← checked]
  exact @cached_density_rule_contains density0 hk12_1_4 (tableDensity false) (fullFactor true 12 4) density0_contains hk12_1_4_contains
noncomputable def atomAnswer : CBox := ⟨⟨1129031579007567335410018579,1129031579007567358935323860⟩,⟨(-20750496595524991352135163511),(-20750496595524991328363052888)⟩⟩
lemma atomChecked : tableAtomBox false ha12_1_4 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom false true 12 4) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains false true ha12_1_4 12 4 ha12_1_4_contains
 def realAnswer : RBox := ⟨6421840530720008321979829232,6421840530720021300423468751⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment false true 12 4) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm12_0_1_4
namespace hm12_1_1_4
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density1 j i k).mul (hk12_1_4 j i k))
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
noncomputable def s1_0 : CBox := ⟨⟨78087,78111⟩,⟨11818,11845⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨132344,132393⟩,⟨28179,28224⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨69993,70054⟩,⟨24810,24872⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨17027,17110⟩,⟨10830,10910⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨1814,1923⟩,⟨2435,2544⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨(-38),102⟩,⟨222,361⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨(-117),55⟩,⟨(-58),112⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨(-164),68⟩,⟨(-131),98⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨(-168),213⟩,⟨(-210),171⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨(-196),239⟩,⟨(-204),232⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨(-246),236⟩,⟨(-231),251⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨(-2079075765898945),(-2079075765898925)⟩,⟨1496332040235530,1496332040235553⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨(-3991404151476638),(-3991404151476605)⟩,⟨3572304572451758,3572304572451794⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨(-2583871966111706),(-2583871966111657)⟩,⟨3480953672424762,3480953672424812⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨(-718436196456164),(-718436196456105)⟩,⟨1926193563243784,1926193563243844⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨(-8903679587859),(-8903679587787)⟩,⟨628648309772307,628648309772381⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨47544720216571,47544720216659⟩,⟨122160879049753,122160879049836⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨13809716409373,13809716409467⟩,⟨14134318414858,14134318414952⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨2114351847487,2114351847584⟩,⟨927232349297,927232349393⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨224869277860,224869277960⟩,⟨20590968557,20590968655⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨19891346001,19891346104⟩,⟨(-2628310827),(-2628310729)⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨1717588982,1717589077⟩,⟨(-412136588),(-412136491)⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨164624350,164624437⟩,⟨(-38219047),(-38218960)⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨19145440,19145510⟩,⟨(-2735865),(-2735791)⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨2877551,2877611⟩,⟨(-68263),(-68208)⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨566006,566049⟩,⟨46535,46575⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨105261,105282⟩,⟨15173,15197⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨(-6112233784911060756661),(-6112233784911025314117)⟩,⟨(-1614823847219425548630),(-1614823847219390106055)⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨(-14889138117492275227899),(-14889138117492207828519)⟩,⟨(-1788513206296638188932),(-1788513206296570789635)⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨(-15469316773054762665342),(-15469316773054720424457)⟩,⟨2418564712467623071085,2418564712467665311579⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨(-9291621485975004819270),(-9291621485974992800510)⟩,⟨5816601657090050141185,5816601657090062159424⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨(-2686695088003048163169),(-2686695088003045606112)⟩,⟨5036305824083719673340,5036305824083722230236⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨292790356137108536339,292790356137108830122⟩,⟨2317064641693630345241,2317064641693630639060⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨561545262833061808110,561545262833061825993⟩,⟨541355597499367047742,541355597499367065656⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨219026707525019818623,219026707525019820700⟩,⟨13084089483567398409,13084089483567400484⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨42946651649788726661,42946651649788727181⟩,⟨(-32550456668848718307),(-32550456668848717789)⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨2868158754415288410,2868158754415288602⟩,⟨(-11767784695382586965),(-11767784695382586771)⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨(-1013601653378076386),(-1013601653378076290)⟩,⟨(-2438192832495265016),(-2438192832495264922)⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨(-484644066887707231),(-484644066887707171)⟩,⟨(-344717659328997088),(-344717659328997026)⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨(-144877935888688733),(-144877935888688682)⟩,⟨(-22672659006571058),(-22672659006571006)⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨(-40238713686146480),(-40238713686146437)⟩,⟨8076614531975100,8076614531975142⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨(-11501252087545567),(-11501252087545531)⟩,⟨5342868353331123,5342868353331157⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨(-2548539556226042),(-2548539556226021)⟩,⟨1573942012675289,1573942012675311⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨(-815493446472731497872824),(-815493446472131812680991)⟩,⟨(-29484350715087011959824418),(-29484350715086412272210667)⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨(-13066494470436520211936983),(-13066494470434557488467608)⟩,⟨(-76780976555894624784506573),(-76780976555892662054375443)⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨(-42883901104454152523824734),(-42883901104449610124736364)⟩,⟨(-90530596638852064022687759),(-90530596638847521617401952)⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨(-70206523201958542959199499),(-70206523201950264084879436)⟩,⟨(-63155591438064836583416705),(-63155591438056557707213628)⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨(-69475135879516977928049052),(-69475135879506340337024053)⟩,⟨(-15809167843366365981912605),(-15809167843355728393655710)⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨(-41651848074725782120936928),(-41651848074715479566002523)⟩,⟨17021507377345405773791739,17021507377355708325400355⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨(-11595713254430314181669699),(-11595713254419969476906357)⟩,⟨21819793528099653323563581,21819793528109998028103773⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨3081656340119641282328517,3081656340124927302559709⟩,⟨11797732344559920837075819,11797732344565206858113555⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨4695122803614875294865955,4695122803617499425714333⟩,⟨2946093902309666933470256,2946093902312291064492545⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨2334308343712583026827858,2334308343713418054486314⟩,⟨(-399672922157123585524063),(-399672922156288557966134)⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨643952264282080734286237,643952264282285655592970⟩,⟨(-726096582168275872495829),(-726096582168070951233712)⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨48769901807089193244079,48769901807141653061362⟩,⟨(-387122657630482527007405),(-387122657630430067186745)⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨(-59205037323374602866711),(-59205037323365122300485)⟩,⟨(-146164002321644047717776),(-146164002321634567143538)⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨(-46272426183532860748774),(-46272426183530630559056)⟩,⟨(-45698759940337508639511),(-45698759940335278446743)⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨(-23139722602405262535189),(-23139722602404609176449)⟩,⟨(-12422786981528197469428),(-12422786981527544110052)⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨(-6699108731955011170432),(-6699108731954868990067)⟩,⟨(-2399918621679520891028),(-2399918621679378710582)⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨176403724663322862182490759,176403724663322864378593859⟩,⟨(-4492186985636231644669765),(-4492186985636229898001454)⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨437849137741171558703064559,437849137741171565409469373⟩,⟨(-176402028145401743644517785),(-176402028145401738130008359)⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨237528694098046419182995512,237528694098046430440304177⟩,⟨(-637328440680010586658340053),(-637328440680010576588032917)⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨(-855263041552768780614456072),(-855263041552768764222171891)⟩,⟨(-976041943578058476921699843),(-976041943578058460991862426)⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨(-2526409293617666075359423162),(-2526409293617666046175625044)⟩,⟨(-418220567037253175567778525),(-418220567037253145904832905)⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨(-3502463175561324952526590360),(-3502463175561324908835058799)⟩,⟨1225530187145749387996673676,1225530187145749432676061590⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨(-2799055063202115157011180924),(-2799055063202115100657566067)⟩,⟨2947614146131255535916930321,2947614146131255592620678611⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨(-932622522517071390491965888),(-932622522517071329103425069)⟩,⟨3464519682138366014716762843,3464519682138366075908566361⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨692455835580905184117700321,692455835580905255900498895⟩,⟨2601367751368818758484041308,2601367751368818830039462619⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨1281404330036726950722410071,1281404330036727116354565563⟩,⟨1251394870231500583255909824,1251394870231500748884943486⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨1063107954378799962881247510,1063107954378800353907882671⟩,⟨260842213987207741036244062,260842213987208132114652312⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨611790886225377708885343832,611790886225378606032940655⟩,⟨(-167912240451174884741794986),(-167912240451173987568941970)⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨267382068747090177937165743,267382068747091871302045734⟩,⟨(-237593345042454436040259869),(-237593345042452742676278955)⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨88445817218053375798187484,88445817218055305716969879⟩,⟨(-175376552681097621428390432),(-175376552681095691514668159)⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨19560839817536226254806778,19560839817537629259730486⟩,⟨(-96180613484292825627912232),(-96180613484291422626515905)⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨1892066448839242750895893,1892066448839733806481632⟩,⟨(-29733008049098125059023563),(-29733008049097634004589451)⟩⟩
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
noncomputable def ans : CBox := ⟨⟨(-996177614850536563460607307),(-996177614850526071150293956)⟩,⟨1434684247290254661695889999,1434684247290265153702405011⟩⟩
lemma checked : cachedMomentRuleBox density1 hk12_1_4 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule true true 12 4) := by
  rw [← checked]
  exact @cached_density_rule_contains density1 hk12_1_4 (tableDensity true) (fullFactor true 12 4) density1_contains hk12_1_4_contains
noncomputable def atomAnswer : CBox := ⟨⟨(-1476425911009895777069269663),(-1476425911009895746305408912)⟩,⟨27135264778763450198628607623,27135264778763450229715213822⟩⟩
lemma atomChecked : tableAtomBox true ha12_1_4 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom true true 12 4) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains true true ha12_1_4 12 4 ha12_1_4_contains
 def realAnswer : RBox := ⟨(-2472603525860432340629876970),(-2472603525860421817355702868)⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment true true 12 4) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm12_1_1_4
namespace hm12_0_1_5
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density0 j i k).mul (hk12_1_5 j i k))
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
noncomputable def s1_0 : CBox := ⟨⟨(-646865),(-646709)⟩,⟨(-321446),(-321292)⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨(-1086455),(-1085985)⟩,⟨(-632079),(-631611)⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨(-555791),(-555049)⟩,⟨(-441841),(-441099)⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨(-121596),(-120563)⟩,⟨(-159805),(-158774)⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨(-8809),(-7449)⟩,⟨(-31431),(-30074)⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨138,1723⟩,⟨(-3715),(-2130)⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨(-447),1273⟩,⟨(-954),768⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨(-643),1361⟩,⟨(-610),1384⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨(-1743),1133⟩,⟨(-1363),1517⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨(-1918),1667⟩,⟨(-2025),1565⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨(-2068),2242⟩,⟨(-2222),2086⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨13181240297977355,13181240297977397⟩,⟨(-1476537126035954),(-1476537126035914)⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨27088233460214270,27088233460214354⟩,⟨(-6225883183856785),(-6225883183856698)⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨20463233637801821,20463233637801963⟩,⟨(-9793851951266364),(-9793851951266220)⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨8008431004269852,8008431004270055⟩,⟨(-7550838676820234),(-7550838676820033)⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨1503316345468794,1503316345469048⟩,⟨(-3181141516753385),(-3181141516753136)⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨28095027101615,28095027101957⟩,⟨(-781740086134529),(-781740086134199)⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨(-45547762075939),(-45547762075537)⟩,⟨(-118221591884195),(-118221591883790)⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨(-10582629045010),(-10582629044576)⟩,⟨(-11692523554132),(-11692523553704)⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨(-1389177552398),(-1389177551905)⟩,⟨(-821742603193),(-821742602697)⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨(-139919463698),(-139919463076)⟩,⟨(-46966282866),(-46966282248)⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨(-12980466850),(-12980466133)⟩,⟨(-2848326642),(-2848325927)⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨(-1280925178),(-1280924430)⟩,⟨(-268805231),(-268804479)⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨(-150103964),(-150103250)⟩,⟨(-42475124),(-42474411)⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨(-22504625),(-22504033)⟩,⟨(-9171959),(-9171365)⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨(-4377808),(-4377408)⟩,⟨(-2371203),(-2370804)⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨(-804522),(-804376)⟩,⟨(-508081),(-507931)⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨11858614189537509976454,11858614189537549664228⟩,⟨14074606424535588721116,14074606424535628407788⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨33228348947070994582818,33228348947071067107607⟩,⟨29496249217636151512475,29496249217636224033214⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨43361373179973339788794,43361373179973381632249⟩,⟨20554054422454149877490,20554054422454191714048⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨35150126331978973386349,35150126331978988669367⟩,⟨1130905720985847321865,1130905720985862600829⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨16971920011807475481353,16971920011807478839285⟩,⟨(-9046118268757804510709),(-9046118268757801152941)⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨3701161852772061707557,3701161852772062041561⟩,⟨(-7333702273984101816056),(-7333702273984101481133)⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨(-603046825386608320565),(-603046825386608288410)⟩,⟨(-2776036582405087099803),(-2776036582405087067430)⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨(-662854317246012639413),(-662854317246012633500)⟩,⟨(-490881986069688452518),(-490881986069688446656)⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨(-208538276183375565087),(-208538276183375563190)⟩,⟨18368675231212729069,18368675231212730943⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨(-34348869668618621417),(-34348869668618620732)⟩,⟨34459685930477591647,34459685930477592330⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨(-1520391543025182671),(-1520391543025182354)⟩,⟨10817859900528484370,10817859900528484687⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨1037468125914559454,1037468125914559639⟩,⟨2287909121779205334,2287909121779205522⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨488311484514011217,488311484514011354⟩,⟨392068732080587004,392068732080587141⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨167149955531928430,167149955531928542⟩,⟨54869183703003423,54869183703003535⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨54216467456804846,54216467456804924⟩,⟨4053446902302434,4053446902302512⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨12818594672089274,12818594672089309⟩,⟨(-607495390521715),(-607495390521678)⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨(-73674221431466906907246628),(-73674221431466294098550533)⟩,⟨10964685360258611349078317,10964685360259224168864213⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨(-184668924239596753207536097),(-184668924239594508023398540)⟩,⟨57035286139769164677153109,57035286139771409885276351⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨(-199629112067970759900589768),(-199629112067965782608633141)⟩,⟨136477017297127100744661540,136477017297132078053662565⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨(-112809550615934091789186624),(-112809550615925574485107444)⟩,⟨191761823262029605929911246,191761823262038123230598988⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨4999987384562536278266084,4999987384572558254191998⟩,⟨166230376317142267851713074,166230376317152289808004118⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨67271261874780124316960780,67271261874791912137622119⟩,⟨81349552720643676356533607,81349552720655464166191923⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨57787985663267662254187254,57787985663278493400517020⟩,⟨8464038043340639731322364,8464038043351470879771137⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨23161093006203909684661642,23161093006209468478128395⟩,⟨(-17126965080221351208930265),(-17126965080215792411833906)⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨1700798926665218317918659,1700798926668203887972949⟩,⟨(-12871756658752757500767385),(-12871756658749771930666182)⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨(-3385831547707345767543922),(-3385831547706494058264844)⟩,⟨(-4339013527317333633812356),(-4339013527316481925181324)⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨(-2238493657675983678043084),(-2238493657675724583065233)⟩,⟨(-346922722973672139436928),(-346922722973413044558380)⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨(-806626170223198608104399),(-806626170223142114717988)⟩,⟨471456467906295236843237,471456467906351730298981⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨(-176115409514710051144427),(-176115409514699515235894)⟩,⟨353823211318271664725162,353823211318282200678284⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨(-1566026862780733961270),(-1566026862777731474227)⟩,⟨171736141325027353653786,171736141325030356148791⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨21415959052477541494858,21415959052478346015807⟩,⟨69145342276312231702987,69145342276313036223568⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨8861965731783139905080,8861965731783307492354⟩,⟨18008719744971045636375,18008719744971213223028⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨(-131635801923352700702181106),(-131635801923352682285924043)⟩,⟨(-4293169451888760687643680016),(-4293169451888760668721120025)⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨(-2218400010779287736396572039),(-2218400010779287680245847928)⟩,⟨(-11549292901064345737133925762),(-11549292901064345679716513518)⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨(-7913132976703429563748833879),(-7913132976703429468739928742)⟩,⟨(-14495223847142832222732582876),(-14495223847142832126435099722)⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨(-14720951223994231531482339387),(-14720951223994231400456749302)⟩,⟨(-10822264571483192133583361770),(-10822264571483192002024458336)⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨(-17352607891917998931553901196),(-17352607891917998772864170310)⟩,⟨(-1828784926641683052946744153),(-1828784926641682894708894750)⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨(-12965645515779661727557261801),(-12965645515779661560088947287)⟩,⟨6904892149953499015036412926,6904892149953499181660790076⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨(-4602632920444907440689968398),(-4602632920444907282712117308)⟩,⟨9997013456470055853101924306,9997013456470056010828234307⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨1960273551932907352241231917,1960273551932907487650150961⟩,⟨7221245414615854569350103365,7221245414615854704889747312⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨3955659252758122448480046398,3955659252758122571255309582⟩,⟨2603989913821449078348022577,2603989913821449201225498196⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨2831133134388440315467534266,2831133134388440508261498212⟩,⟨(-397888447843072326538124900),(-397888447843072133748478258)⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨1137984545344904211081627390,1137984545344904594103750820⟩,⟨(-1234927232805377785614232435),(-1234927232805377402599316761)⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨123253605143824519581399880,123253605143825483127236312⟩,⟨(-963697371019085529940639961),(-963697371019084566391759396)⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨(-211732731483482737108874926),(-211732731483481040115102103)⟩,⟨(-511695235225117196954398397),(-511695235225115499958697942)⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨(-218101252993741240694794491),(-218101252993739410170052270)⟩,⟨(-213808937822509242885670968),(-213808937822507412362106002)⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨(-133294557096336062869922535),(-133294557096334797375801873)⟩,⟨(-72849302118004487364450887),(-72849302118003221871966128)⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨(-42900911222747508168071125),(-42900911222747056542975652)⟩,⟨(-16161569937636852837308753),(-16161569937636401212843065)⟩⟩
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
noncomputable def ans : CBox := ⟨⟨(-8487504663015275756097303354),(-8487504663015264664964325404)⟩,⟨(-3175649148944182373806372319),(-3175649148944171282291109704)⟩⟩
lemma checked : cachedMomentRuleBox density0 hk12_1_5 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule false true 12 5) := by
  rw [← checked]
  exact @cached_density_rule_contains density0 hk12_1_5 (tableDensity false) (fullFactor true 12 5) density0_contains hk12_1_5_contains
noncomputable def atomAnswer : CBox := ⟨⟨(-15005876779856123279983260758),(-15005876779856123261800700946)⟩,⟨(-28342555260894404754779850),(-28342555260894386783347653)⟩⟩
lemma atomChecked : tableAtomBox false ha12_1_5 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom false true 12 5) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains false true ha12_1_5 12 5 ha12_1_5_contains
 def realAnswer : RBox := ⟨(-23493381442871399036180564112),(-23493381442871387926665026350)⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment false true 12 5) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm12_0_1_5
namespace hm12_1_1_5
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density1 j i k).mul (hk12_1_5 j i k))
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
noncomputable def s1_0 : CBox := ⟨⟨(-64921),(-64886)⟩,⟨(-92108),(-92073)⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨(-102857),(-102788)⟩,⟨(-164198),(-164127)⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨(-45557),(-45451)⟩,⟨(-96979),(-96873)⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨(-6736),(-6591)⟩,⟨(-28765),(-28623)⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨414,602⟩,⟨(-4658),(-4469)⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨145,368⟩,⟨(-468),(-245)⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨(-67),185⟩,⟨(-126),124⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨(-112),193⟩,⟨(-81),208⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨(-266),171⟩,⟨(-218),230⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨(-305),275⟩,⟨(-326),248⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨(-346),377⟩,⟨(-371),352⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨2709211018252201,2709211018252224⟩,⟨1275547374517862,1275547374517887⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨5944480896312409,5944480896312450⟩,⟨2035005742407518,2035005742407554⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨5082679645595669,5082679645595722⟩,⟨611556807052975,611556807053030⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨2415003749646311,2415003749646382⟩,⟨(-423002601412740),(-423002601412672)⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨654732705798023,654732705798100⟩,⟨(-384765172864154),(-384765172864077)⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨95491539666392,95491539666485⟩,⟨(-129344279198374),(-129344279198282)⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨5198094624325,5198094624421⟩,⟨(-24105317696476),(-24105317696379)⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨(-567227551335),(-567227551240)⟩,⟨(-2880386902565),(-2880386902470)⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨(-150780087424),(-150780087326)⟩,⟨(-250996613641),(-250996613540)⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨(-18822805641),(-18822805528)⟩,⟨(-18696150223),(-18696150113)⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨(-1889806478),(-1889806360)⟩,⟨(-1446029099),(-1446028982)⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨(-186131960),(-186131843)⟩,⟨(-137780527),(-137780411)⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨(-20519891),(-20519784)⟩,⟨(-17378523),(-17378416)⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨(-2809025),(-2808934)⟩,⟨(-2915523),(-2915431)⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨(-501989),(-501924)⟩,⟨(-629647),(-629580)⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨(-87761),(-87725)⟩,⟨(-123414),(-123379)⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨365452337218890278154,365452337218923606679⟩,⟨6141713827954596638652,6141713827954629967290⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨2926747724370672970776,2926747724370733824948⟩,⟨14343815322615369171086,14343815322615430025672⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨7129021031837776933352,7129021031837811975990⟩,⟨13625458505421669631931,13625458505421704675278⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨8477071058634044193197,8477071058634056950527⟩,⟨6792546045283515224416,6792546045283527982168⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨5663927255155284856160,5663927255155287642249⟩,⟨812492229047515290431,812492229047518076530⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨2097460354719274046174,2097460354719274313718⟩,⟨(-1111281108642504393086),(-1111281108642504125631)⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨305951365571453162530,305951365571453183639⟩,⟨(-744886628438136071162),(-744886628438136050073)⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨(-75747965658442954495),(-75747965658442951988)⟩,⟨(-217609614811918862395),(-217609614811918859884)⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨(-50290000152715930017),(-50290000152715929341)⟩,⟨(-28093678935230838458),(-28093678935230837778)⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨(-12938706527472802640),(-12938706527472802392)⟩,⟨2516931424799384970,2516931424799385219⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨(-1944574900030760270),(-1944574900030760151)⟩,⟨2183074364300265800,2183074364300265924⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨(-101594353359328258),(-101594353359328181)⟩,⟨661292032841303032,661292032841303108⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨53441427214111427,53441427214111486⟩,⟨158492493050195900,158492493050195962⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨30141017445935780,30141017445935829⟩,⟨36494432893283199,36494432893283247⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨11862695024624574,11862695024624612⟩,⟨8746957815285032,8746957815285070⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨3045723979660179,3045723979660202⟩,⟨1714474881397346,1714474881397369⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨(-23989194443087691259421890),(-23989194443087187978120753)⟩,⟨4837951247551616764536081,4837951247552120043808913⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨(-61033211939804654488892404),(-61033211939802810110118427)⟩,⟨21756594413845810314374917,21756594413847654688593682⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨(-68131527657221152775165412),(-68131527657217062649056551)⟩,⟨48762722920498670433632124,48762722920502760556297235⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨(-41370908215938938017464872),(-41370908215931936873203031)⟩,⟨68005880554440804866913915,68005880554447806011585088⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨(-1721790834366025244854457),(-1721790834357785810919065)⟩,⟨60643245120759426535431659,60643245120767665973241217⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨21715741065635060049668643,21715741065644751815103610⟩,⟨32124602987804169034029314,32124602987813860801762358⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨20807791140857889243429506,20807791140866792978756145⟩,⟨5745936470541779898924487,5745936470550683633828665⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨9548856944917345790358588,9548856944921913213976302⟩,⟨(-5070466173421172077070770),(-5070466173416604654252447)⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨1539750870913390866727022,1539750870915842131168959⟩,⟨(-4747946321530376980042888),(-4747946321527925715619060)⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨(-904003152152086975282654),(-904003152151388420323018)⟩,⟨(-1968399509751344009559535),(-1968399509750645454468020)⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨(-810991590952351717492169),(-810991590952139487980495)⟩,⟨(-392659337190212038629723),(-392659337189999809097317)⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨(-362483782571983196496625),(-362483782571936983624806)⟩,⟨59190752667717751261534,59190752667763964120773⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨(-116533829558432845526719),(-116533829558424238975453)⟩,⟨94812353934501027567958,94812353934509634110958⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨(-28455445340009318969404),(-28455445340006869025885)⟩,⟨55703725483434116467153,55703725483436566409140⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨(-4545105110585838903581),(-4545105110585182987557)⟩,⟨25020642391128713135712,25020642391129369051770⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨(-192525558702322710727),(-192525558702186142547)⟩,⟨6911302312562536229676,6911302312562672797959⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨(-9942844638013122031584291),(-9942844638013120764958533)⟩,⟨(-127300351720624212683963545),(-127300351720624211087119203)⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨(-145093888658585363755603438),(-145093888658585359547622111)⟩,⟨(-310075306511644441017918708),(-310075306511644436000665467)⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨(-473714191724751696980433584),(-473714191724751689344913513)⟩,⟨(-145272659900364327228123882),(-145272659900364318822203657)⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨(-673605307635710984967394431),(-673605307635710972941146835)⟩,⟨673118333383657262026549377,673118333383657274272128132⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨(-172435283370927986962897788),(-172435283370927964459155180)⟩,⟨1888179719857554296935272467,1888179719857554318971529754⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨1128321859545565903943063646,1128321859545565938425359437⟩,⟨2536561645280303036576411281,2536561645280303070301403956⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨2416732980667356437497090267,2416732980667356481924809663⟩,⟨1904501573123267825368506079,1904501573123267869607682859⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨2715422361826073939734762830,2715422361826073987694463651⟩,⟨437585839489221994477326690,437585839489222042639394459⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨1945852983750047532565872183,1945852983750047590353529719⟩,⟨(-765531772070895413088946213),(-765531772070895355137692419)⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨850267701255162677506695885,850267701255162808203430681⟩,⟨(-1124489714672579110319926568),(-1124489714672578979638582059)⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨90124101776646844130057933,90124101776647140196538429⟩,⟨(-867960265536226768721652174),(-867960265536226472702806253)⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨(-206353283762096134283330711),(-206353283762095357657828349)⟩,⟨(-468245872435673796363265278),(-468245872435673019752722348)⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨(-225077076926552307881480183),(-225077076926550927471259217)⟩,⟨(-185156803839270516949977893),(-185156803839269136536364217)⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨(-153935651166049130242421460),(-153935651166047637342075853)⟩,⟨(-48336525537877301843137908),(-48336525537875808937570544)⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨(-81038296014981676900321239),(-81038296014980643750035351)⟩,⟨(-2675145974706218455982152),(-2675145974705185302332083)⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨(-24544087537372448015019673),(-24544087537372079133577149)⟩,⟨2625086864930459646079243,2625086864930828528545348⟩⟩
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
noncomputable def ans : CBox := ⟨⟨1139357867268359398844069954,1139357867268368394272921872⟩,⟨604584416779002450261540894,604584416779011445859112507⟩⟩
lemma checked : cachedMomentRuleBox density1 hk12_1_5 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule true true 12 5) := by
  rw [← checked]
  exact @cached_density_rule_contains density1 hk12_1_5 (tableDensity true) (fullFactor true 12 5) density1_contains hk12_1_5_contains
noncomputable def atomAnswer : CBox := ⟨⟨19623069635196468880816301237,19623069635196468904593494838⟩,⟨37063341495015736562839239,37063341495015760063942881⟩⟩
lemma atomChecked : tableAtomBox true ha12_1_5 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom true true 12 5) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains true true ha12_1_5 12 5 ha12_1_5_contains
 def realAnswer : RBox := ⟨20762427502464828279560371191,20762427502464837298966416710⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment true true 12 5) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm12_1_1_5
namespace hm12_0_1_6
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density0 j i k).mul (hk12_1_6 j i k))
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
noncomputable def s1_0 : CBox := ⟨⟨256187,256331⟩,⟨819214,819360⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨359909,360345⟩,⟨1454715,1455149⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨91759,92407⟩,⟨846804,847455⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨(-30879),(-29925)⟩,⟨240352,241313⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨(-19350),(-17921)⟩,⟨33658,35083⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨(-4250),(-2348)⟩,⟨988,2892⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨(-1662),703⟩,⟨(-1429),937⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨(-1646),1531⟩,⟨(-2270),907⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨(-2139),2907⟩,⟨(-2372),2681⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨(-2718),2648⟩,⟨(-2335),3030⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨(-2819),2520⟩,⟨(-2654),2680⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨(-7491676558188217),(-7491676558188183)⟩,⟨(-10527535633411506),(-10527535633411472)⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨(-18256057279348043),(-18256057279347973)⟩,⟨(-20120935597422143),(-20120935597422073)⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨(-18354839644879865),(-18354839644879751)⟩,⟨(-12708074065206606),(-12708074065206498)⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨(-10499717899136184),(-10499717899136024)⟩,⟨(-3068553356355234),(-3068553356355073)⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨(-3522538862827548),(-3522538862827330)⟩,⟨368054706966894,368054706967119⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨(-690717506917921),(-690717506917593)⟩,⟨402740357151159,402740357151501⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨(-76378190411521),(-76378190411059)⟩,⟨107366869943132,107366869943594⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨(-3767669384076),(-3767669383499)⟩,⟨16282405408071,16282405408646⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨170890273701,170890274414⟩,⟨1735791631858,1735791632566⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨53251649817,53251650652⟩,⟨153667951956,153667952791⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨6706149853,6706150749⟩,⟨13327126660,13327127554⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨714790441,714791310⟩,⟨1312531342,1312532213⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨78696941,78697718⟩,⟨162720322,162721093⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨9930872,9931477⟩,⟨26696950,26697564⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨1504887,1505277⟩,⟨5686096,5686491⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨222098,222240⟩,⟨1106544,1106687⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨7838708396843349494060,7838708396843377347349⟩,⟨(-12702090323772841165289),(-12702090323772813310060)⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨14246183040119539136363,14246183040119587782792⟩,⟨(-33219616912261528408784),(-33219616912261479756779)⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨4532460465560559456539,4532460465560595006703⟩,⟨(-39013251381600914289601),(-39013251381600878734424)⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨(-8689031285549402644249),(-8689031285549388230702)⟩,⟨(-27712313318010347139770),(-27712313318010332724987)⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨(-11935086059963495414047),(-11935086059963492710631)⟩,⟨(-10755560454808245381289),(-10755560454808242679000)⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨(-6918901419976480131259),(-6918901419976479871391)⟩,⟨(-734832420095716550791),(-734832420095716291783)⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨(-2029075046046529888438),(-2029075046046529857752)⟩,⟨1362504005946368831466,1362504005946368862159⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨(-173487026947661577495),(-173487026947661572181)⟩,⟨700665904002411958047,700665904002411963444⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨89526406274334823633,89526406274334825390⟩,⟨163595433977935148662,163595433977935150427⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨41411492101199079073,41411492101199079693⟩,⟨15235047523038769197,15235047523038769810⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨9600504586071286723,9600504586071287004⟩,⟨(-3070509774254375379),(-3070509774254375097)⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨1479431651970865831,1479431651970865993⟩,⟨(-1832371766220610065),(-1832371766220609904)⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨115949645041234953,115949645041235068⟩,⟨(-583833021358568694),(-583833021358568575)⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨(-29450499826461384),(-29450499826461293)⟩,⟨(-166490584962596829),(-166490584962596737)⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨(-21755727100328123),(-21755727100328057)⟩,⟨(-47951084007083125),(-47951084007083064)⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨(-6545635040232896),(-6545635040232864)⟩,⟨(-10623672407790461),(-10623672407790429)⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨16155782517686923187060469,16155782517687400604364742⟩,⟨48900119441840294303730061,48900119441840771715170809⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨61091529089969014970097085,61091529089970716853337345⟩,⟨119254921685618645792614697,119254921685620347664248134⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨118349641861206309628862482,118349641861209914628850076⟩,⟨119996633569191701967471256,119996633569195306962474280⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨147030381445983877719708268,147030381445989672521607067⟩,⟨52952375654939225807128825,52952375654945020617871120⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨115010119537578850864853617,115010119537585580198158157⟩,⟨(-26380684488887462104273595),(-26380684488880732754627128)⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨47270292993709053208784624,47270292993718181209797242⟩,⟨(-59261391383053483484310085),(-59261391383044355478864654)⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨(-3129062054894568121073274),(-3129062054887179342449996)⟩,⟨(-42402095774346182863257366),(-42402095774338794088150752)⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨(-16259082576018070799877913),(-16259082576013700238896705)⟩,⟨(-13733279278689948021302572),(-13733279278685577462469245)⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨(-9677457779895098323719201),(-9677457779892912807584292)⟩,⟨1122412602708317777605735,1122412602710503294213967⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨(-2528826231337724016475714),(-2528826231337082068755258)⟩,⟨3346374196397361434456350,3346374196398003382659842⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨211455769435266347961601,211455769435472590918737⟩,⟨1739631253862607281160570,1739631253862813524098576⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨533938196392871308196580,533938196392910550475377⟩,⟨501990839107537748626269,501990839107576990821768⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨309568738772389524294875,309568738772399309807071⟩,⟨51112931703174452632410,51112931703184238123542⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨131595213335080592856621,131595213335083074601781⟩,⟨(-40392342118593164885357),(-40392342118590683139000)⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨47760674601032552658050,47760674601033161965657⟩,⟨(-33621413340025384065881),(-33621413340024774754807)⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨11627647313109325319127,11627647313109446032128⟩,⟨(-11353174895410339961372),(-11353174895410219247027)⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨(-2581094720770293084783487915),(-2581094720770293073032388302)⟩,⟨215062457367344401738128456,215062457367344413196813510⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨(-6896996371160477763341326610),(-6896996371160477727605237281)⟩,⟨1719676461980651771243485955,1719676461980651806256981334⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨(-8504257630179846916824188897),(-8504257630179846856634710723)⟩,⟨5313225934295352694639015480,5313225934295352754120876276⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨(-6019316835597635875573050904),(-6019316835597635792826995784)⟩,⟨9408637821280695719586307428,9408637821280695802105021055⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨(-349307748432249395606575086),(-349307748432249295291088435)⟩,⟨10754486426885510471944621412,10754486426885510572625402524⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨4947688319526230852908342825,4947688319526230959806618566⟩,⟨7701013403980803605231994743,7701013403980803712655145704⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨6543040228694635986424185098,6543040228694636088649619990⟩,⟨2310225071222307723463273604,2310225071222307825799479835⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨4457720127938529937738443346,4457720127938530025975432712⟩,⟨(-1720109845728691071759900646),(-1720109845728690983633606231)⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨1380869304011637342275748288,1380869304011637423968760441⟩,⟨(-2735746906456210151359736832),(-2735746906456210069723741026)⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨(-492610184795679134209518146),(-492610184795679008915468892)⟩,⟨(-1808915718285420304331394759),(-1808915718285420179030522181)⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨(-915979832107282290847913087),(-915979832107282035607980570)⟩,⟨(-636535878915939364212549488),(-636535878915939108968068457)⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨(-652844571268883370024424818),(-652844571268882692714187371)⟩,⟨13122241372480116896641022,13122241372480794205307969⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨(-320888048234999041767828076),(-320888048234997917082141434)⟩,⟨195987023785247958008668583,195987023785249082694285856⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨(-120217448834621707203220907),(-120217448834620564860114114)⟩,⟨171051784111357230670659212,171051784111358373015539387⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨(-34136871890708749744528138),(-34136871890707898638831895)⟩,⟨98844689760867810150284697,98844689760868661257379160⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨(-5983325104182985368682067),(-5983325104182628364068818)⟩,⟨31081438790890998567727632,31081438790891355572746028⟩⟩
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
noncomputable def ans : CBox := ⟨⟨(-1514959888228964483901187904),(-1514959888228956569796584916)⟩,⟨5206164543057593269769529560,5206164543057601183690619317⟩⟩
lemma checked : cachedMomentRuleBox density0 hk12_1_6 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule false true 12 6) := by
  rw [← checked]
  exact @cached_density_rule_contains density0 hk12_1_6 (tableDensity false) (fullFactor true 12 6) density0_contains hk12_1_6_contains
noncomputable def atomAnswer : CBox := ⟨⟨455194096401413514278243775,455194096401413525731280743⟩,⟨9015661791329172080481849514,9015661791329172092082413611⟩⟩
lemma atomChecked : tableAtomBox false ha12_1_6 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom false true 12 6) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains false true ha12_1_6 12 6 ha12_1_6_contains
 def realAnswer : RBox := ⟨(-1059765791827550969722944129),(-1059765791827543043965304173)⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment false true 12 6) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm12_0_1_6
namespace hm12_1_1_6
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density1 j i k).mul (hk12_1_6 j i k))
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
noncomputable def s1_0 : CBox := ⟨⟨(-25649),(-25614)⟩,⟨131417,131452⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨(-55342),(-55275)⟩,⟨224285,224353⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨(-44381),(-44285)⟩,⟨120660,120755⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨(-18662),(-18530)⟩,⟨30447,30584⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨(-4401),(-4202)⟩,⟨3557,3753⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨(-668),(-404)⟩,⟨(-11),254⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨(-229),112⟩,⟨(-222),118⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨(-225),246⟩,⟨(-337),135⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨(-332),440⟩,⟨(-354),416⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨(-440),418⟩,⟨(-376),481⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨(-471),421⟩,⟨(-446),446⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨(-195016383399638),(-195016383399616)⟩,⟨(-2910596551577684),(-2910596551577662)⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨(-1106168208174589),(-1106168208174554)⟩,⟨(-6041273113789520),(-6041273113789488)⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨(-1957503038429771),(-1957503038429729)⟩,⟨(-4641960635075415),(-4641960635075371)⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨(-1576838839205217),(-1576838839205161)⟩,⟨(-1857636642848127),(-1857636642848069)⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨(-673025538369440),(-673025538369371)⟩,⟨(-362441993053118),(-362441993053050)⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨(-163891707638921),(-163891707638829)⟩,⟨(-11857378312422),(-11857378312329)⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨(-23886615293658),(-23886615293545)⟩,⟨9327797809359,9327797809469⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨(-2162296795059),(-2162296794935)⟩,⟨2236318558195,2236318558318⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨(-122482444059),(-122482443926)⟩,⟨291717706344,291717706479⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨(-3631803897),(-3631803750)⟩,⟨29005887977,29005888122⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨77643239,77643385⟩,⟨2670241262,2670241410⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨18042586,18042720⟩,⟨263816123,263816259⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨731948,732063⟩,⟨31147323,31147436⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨(-288818),(-288727)⟩,⟨4736359,4736452⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨(-135240),(-135176)⟩,⟨941664,941728⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨(-34168),(-34136)⟩,⟨176333,176364⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨4639072846925236261136,4639072846925259647244⟩,⟨(-1837648701887336973837),(-1837648701887313587930)⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨10322511331044134365647,10322511331044175173694⟩,⟨(-5939260143362431654953),(-5939260143362390847481)⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨8687104530525754408941,8687104530525784177429⟩,⟨(-9107349614594480343447),(-9107349614594450575481)⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨2987700559059896869322,2987700559059908901936⟩,⟨(-8458102004298373022180),(-8458102004298360989694)⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨(-973618473918337191602),(-973618473918334951761)⟩,⟨(-4679550435921017457066),(-4679550435921015217112)⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨(-1508741042040834449623),(-1508741042040834244299)⟩,⟨(-1328659123769860610943),(-1328659123769860405533)⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨(-692746896070181842132),(-692746896070181822127)⟩,⟨(-8531232372878249885),(-8531232372878229884)⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨(-150300858376713769210),(-150300858376713766997)⟩,⟨134415508890533001765,134415508890533003966⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨(-4949471537675668286),(-4949471537675667649)⟩,⟨51075501280702488673,51075501280702489308⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨6978299290800737665,6978299290800737893⟩,⟨9705386018238481552,9705386018238481776⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨2593519639180916666,2593519639180916775⟩,⟨741585582607738826,741585582607738932⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨596653160769901761,596653160769901829⟩,⟨(-193373195542575607),(-193373195542575541)⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨110112468097702386,110112468097702441⟩,⟨(-114673943329525209),(-114673943329525157)⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨17218207516835550,17218207516835589⟩,⟨(-42104620042052906),(-42104620042052863)⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨1918331470452484,1918331470452519⟩,⟨(-14145214986701120),(-14145214986701086)⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨26705187679629,26705187679650⟩,⟨(-3398413921356443),(-3398413921356419)⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨6124207082972274884602577,6124207082972667003646575⟩,⟨15773020733031230130515805,15773020733031622250690867⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨22175803191246836121409415,22175803191248234253937539⟩,⟨39065770691943270451319589,39065770691944668586172855⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨41891314904053644854765013,41891314904056607344135451⟩,⟨40684336615293006621276583,40684336615295969111747923⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨52322139380132357597365423,52322139380137120881252373⟩,⟨19722485964597856992849051,19722485964602620275038896⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨42448138492997628417990747,42448138493003160873647893⟩,⟨(-7155149034158969005655946),(-7155149034153436553415567)⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨19382316626918115336983257,19382316626925620325835523⟩,⟨(-19993846810114587908798215),(-19993846810107082920973399)⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨790939578310254280707053,790939578316328251271549⟩,⟨(-15695325522650843711531961),(-15695325522644769740221377)⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨(-5272432142311071515841042),(-5272432142307480429597826)⟩,⟨(-6001507833699817810876724),(-6001507833696226724128796)⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨(-3737267830473120147628515),(-3737267830471325727972704)⟩,⟨(-249933268825005340978744),(-249933268823210921414469)⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨(-1271677008125165575641201),(-1271677008124639083190187)⟩,⟨1052804420910814570766016,1052804420911341063115021⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨(-122245747258728265180333),(-122245747258559324018098)⟩,⟨686330467979718330966914,686330467979887272130633⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨125076672229900976575457,125076672229933077091563⟩,⟨259543023223947910698533,259543023223980011229995⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨99123029494989386855105,99123029494997380513836⟩,⟨66322043698650556305074,66322043698658549967841⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨49450899655096751436158,49450899655098776425259⟩,⟨8253901426200226438420,8253901426202251427408⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨20337225486312973171666,20337225486313469893481⟩,⟨(-2727393548925152362041),(-2727393548924655640805)⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨5367029504538073353029,5367029504538171710327⟩,⟨(-1591671508966363725637),(-1591671508966265368562)⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨(-76342417101874530929140182),(-76342417101874529936408443)⟩,⟨10014553281611997078296324,10014553281611997882605239⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨(-182324244966508548131289904),(-182324244966508545014858475)⟩,⟨97798887018656921574802166,97798887018656924237118231⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨(-71025536168011557231567620),(-71025536168011552021375534)⟩,⟨292296470053448380881719268,292296470053448385683104129⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨437690330651165953903112540,437690330651165961492928529⟩,⟨384081770709038594483310774,384081770709038602012830820⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨1169683434130455048603144931,1169683434130455062393596408⟩,⟨21145881955556108508074546,21145881955556122654936612⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨1518563151951709300657232114,1518563151951709322262255041⟩,⟨(-830599859014835695338565104),(-830599859014835673266341403)⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨1055969033809729537089270415,1055969033809729565760359699⟩,⟨(-1628590108965178285620790515),(-1628590108965178256879545429)⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨99337205292596233280986940,99337205292596264428881585⟩,⟨(-1754282219241642673801589230),(-1754282219241642642814393221)⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨(-636421652050957161973297027),(-636421652050957123233255143)⟩,⟨(-1194586239079631087263998978),(-1194586239079631048613501651)⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨(-801884778769831057398988002),(-801884778769830972868968409)⟩,⟨(-460469492442619202800659243),(-460469492442619118249393318)⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨(-579373678676926668018494816),(-579373678676926470789015734)⟩,⟨19532196857044718091091495,19532196857044915353487536⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨(-290973446219593166985246403),(-290973446219592620742454787)⟩,⟨183371435054623526265072217,183371435054624072514196228⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨(-100461313594254071968210195),(-100461313594253157154490768)⟩,⟨170499757737021765613993018,170499757737022680423779716⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨(-15566053300359323691747196),(-15566053300358392201665114)⟩,⟨109345595102896789488159484,109345595102897720974073838⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨7493067174325757116364310,7493067174326451967021909⟩,⟨55314051900789953833839852,55314051900790648682269893⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨4654884755643566767373262,4654884755643858419691157⟩,⟨16394582777814734278619957,16394582777815025930415281⟩⟩
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
noncomputable def ans : CBox := ⟨⟨285678649104452995149646469,285678649104459422295461946⟩,⟨(-740090852252431595808894959),(-740090852252425168732909571)⟩⟩
lemma checked : cachedMomentRuleBox density1 hk12_1_6 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule true true 12 6) := by
  rw [← checked]
  exact @cached_density_rule_contains density1 hk12_1_6 (tableDensity true) (fullFactor true 12 6) density1_contains hk12_1_6_contains
noncomputable def atomAnswer : CBox := ⟨⟨(-595253818371079225956290203),(-595253818371079210979241860)⟩,⟨(-11789711573276609658877002414),(-11789711573276609643707033980)⟩⟩
lemma atomChecked : tableAtomBox true ha12_1_6 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom true true 12 6) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains true true ha12_1_6 12 6 ha12_1_6_contains
 def realAnswer : RBox := ⟨(-309575169266626230906643734),(-309575169266619788583779914)⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment true true 12 6) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm12_1_1_6
namespace hm12_0_1_7
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density0 j i k).mul (hk12_1_7 j i k))
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
noncomputable def s1_0 : CBox := ⟨⟨421772,421958⟩,⟨(-766169),(-765988)⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨811920,812491⟩,⟨(-1299669),(-1299099)⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨552920,553830⟩,⟨(-681086),(-680176)⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨197251,198547⟩,⟨(-157349),(-156050)⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨38246,39979⟩,⟨(-13774),(-12041)⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨3003,5025⟩,⟨(-203),1821⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨(-833),1290⟩,⟨(-521),1606⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨(-1770),943⟩,⟨(-724),2004⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨(-2852),2354⟩,⟨(-2997),2206⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨(-3005),3516⟩,⟨(-3571),2951⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨(-3593),3901⟩,⟨(-3666),3826⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨(-4647922473340414),(-4647922473340379)⟩,⟨9736640984047527,9736640984047561⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨(-7225691975240901),(-7225691975240828)⟩,⟨21585768628680076,21585768628680148⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨(-1631137497043818),(-1631137497043699)⟩,⟨18759834520204853,18759834520204978⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨2270711644924133,2270711644924313⟩,⟨9037438585958661,9037438585958838⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨1848637171249789,1848637171250025⟩,⟨2433181582983141,2433181582983376⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨621636995977888,621636995978228⟩,⟨322888310300298,322888310300642⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨117390582093329,117390582093767⟩,⟨3938088996136,3938088996578⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨14095154462585,14095154463095⟩,⟨(-5637292051168),(-5637292050656)⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨1203321476124,1203321476700⟩,⟨(-1077961097955),(-1077961097381)⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨84141787521,84141788123⟩,⟨(-128507834678),(-128507834070)⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨5884441266,5884441946⟩,⟨(-13094774332),(-13094773649)⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨524248614,524249394⟩,⟨(-1365623564),(-1365622785)⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨68922779,68923571⟩,⟨(-165755265),(-165754474)⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨12998931,12999614⟩,⟨(-25495393),(-25494713)⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨3148326,3148798⟩,⟨(-5057069),(-5056600)⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨658597,658771⟩,⟨(-939972),(-939796)⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨(-10090242200034911778534),(-10090242200034893593071)⟩,⟨(-2417799189462509883298),(-2417799189462491699367)⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨(-25114646124386804142625),(-25114646124386765715474)⟩,⟨(-2121673681709353819051),(-2121673681709315394900)⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨(-26940881195274872216260),(-26940881195274843245229)⟩,⟨5779961305767866849201,5779961305767895818637⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨(-16490958868597191051543),(-16490958868597180714641)⟩,⟨12274466337362532747902,12274466337362543085533⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨(-4329074648819877693473),(-4329074648819876010645)⟩,⟨10658675276906233669115,10658675276906235353438⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨1278086434463035402540,1278086434463035621756⟩,⟨4886950961588445099445,4886950961588445318961⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨1485540262591954994562,1485540262591955016306⟩,⟨1020662653243980934330,1020662653243980955929⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨535194522279583386456,535194522279583390289⟩,⟨(-82002447780277361743),(-82002447780277357958)⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨86984593506688135269,86984593506688136454⟩,⟨(-112739399347707531254),(-112739399347707530064)⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨(-2699471596402844487),(-2699471596402844089)⟩,⟨(-34193460286356084947),(-34193460286356084546)⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨(-5484678732081565739),(-5484678732081565560)⟩,⟨(-5784872603151042339),(-5784872603151042159)⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨(-1849481727607748315),(-1849481727607748197)⟩,⟨(-400686913322186557),(-400686913322186439)⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨(-465462062901389654),(-465462062901389557)⟩,⟨136084045983623573,136084045983623670⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨(-109398140151019061),(-109398140151018980)⟩,⟨86200651793255230,86200651793255316⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨(-26255213089121895),(-26255213089121832)⟩,⟨34948658027562200,34948658027562264⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨(-5111085829484991),(-5111085829484959)⟩,⟨9057485722922451,9057485722922483⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨26922865227752383286246601,26922865227752689760785573⟩,⟨(-14375711027473864597890758),(-14375711027473558121047504)⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨63516489169773521106219974,63516489169774588277387874⟩,⟨(-48014118839875875028716069),(-48014118839874807853838589)⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨57966383991545193232801367,57966383991547359265282286⟩,⟨(-82325019248023103103219798),(-82325019248020937071960777)⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨14952799945144791593231906,14952799945148046235672068⟩,⟨(-92892730154739711006319760),(-92892730154736456372889045)⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨(-29320480422623415248956618),(-29320480422619189180141098)⟩,⟨(-65497682800244900101125178),(-65497682800240674041688520)⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨(-41668986065473093537074965),(-41668986065467306268123540)⟩,⟨(-20996478525920202965140845),(-20996478525914415696667237)⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨(-25401145014419154020877286),(-25401145014414894983847303)⟩,⟨7657223222855981919036765,7657223222860240959199671⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨(-6088026442437755740673849),(-6088026442434722831425363)⟩,⟨12025011371573877869637214,12025011371576910779595797⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨2221046275350109509497654,2221046275351405348108052⟩,⟨5859039669632173913076247,5859039669633469751085014⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨2538281825160904980732138,2538281825161372134469953⟩,⟨1031708147832313982608356,1031708147832781136144171⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨1072259207174160161532407,1072259207174290568526453⟩,⟨(-447926313988349143250402),(-447926313988218736180606)⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨221940031738862836568290,221940031738888965382344⟩,⟨(-439916294811911681020294),(-439916294811885552152818)⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨(-28649402486052827208207),(-28649402486045689238336)⟩,⟨(-211568904505860305245860),(-211568904505853167273263)⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨(-53769389309865270708298),(-53769389309863672990616)⟩,⟨(-77797529472087153950826),(-77797529472085556239139)⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨(-32295426361579847699682),(-32295426361579494748882)⟩,⟨(-24266663258307380791205),(-24266663258307027844759)⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨(-9997644631449879958148),(-9997644631449809361571)⟩,⟨(-5219982560190482845694),(-5219982560190412250426)⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨180983339354342670977348547,180983339354342677067633609⟩,⟨1326411178817765287052602796,1326411178817765293286486163⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨1084531477457412760572647848,1084531477457412779216673534⟩,⟨3519187789841573811916223482,3519187789841573830910477116⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨3020377581804248194681847874,3020377581804248226468873357⟩,⟨4256123143924427997353654357,4256123143924428029467674897⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨5123897111210087074443722541,5123897111210087118774831200⟩,⟨2828191348370356487363102346,2828191348370356531760389855⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨5683019085611407218574854022,5683019085611407273011959191⟩,⟨(-227889141275217349449420906),(-227889141275217295250297980)⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨3883670334905606567587074761,3883670334905606626271432518⟩,⟨(-2969576481920975574625541911),(-2969576481920975516210724436)⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨918082836207922862057980424,918082836207922918381574987⟩,⟨(-3635791095728924443607324942),(-3635791095728924387316899466)⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨(-1187875257579390721050674184),(-1187875257579390672336167456)⟩,⟨(-2329886943967600324093307199),(-2329886943967600275305326284)⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨(-1595103673298927440799474277),(-1595103673298927394814086056)⟩,⟨(-587090505670631461343852806),(-587090505670631415333476340)⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨(-973792135838105210244428313),(-973792135838105141587824987)⟩,⟨402733597635909420501626452,402733597635909489152291520⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨(-287628259434577127929074408),(-287628259434576977354413961)⟩,⟨566189869332847428477342911,566189869332847579049752649⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨62684046867015630598210929,62684046867016029380655219⟩,⟨370911317297705693246407134,370911317297706092029408028⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨141689220779276299059648485,141689220779276921536578144⟩,⟨166768514153527867154123411,166768514153528489630314512⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨110472273591904013716612212,110472273591904635078046623⟩,⟨53330924588681158504955111,53330924588681779864854672⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨60869416808060505275406799,60869416808061070495428646⟩,⟨10128803041254192020636398,10128803041254757239844592⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨18727819437856247774811729,18727819437856479806409129⟩,⟨376102341572244307873189,376102341572476339255131⟩⟩
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
noncomputable def ans : CBox := ⟨⟨2718555723850720548122455161,2718555723850725390204327801⟩,⟨575235468893375476617035029,575235468893380318769393969⟩⟩
lemma checked : cachedMomentRuleBox density0 hk12_1_7 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule false true 12 7) := by
  rw [← checked]
  exact @cached_density_rule_contains density0 hk12_1_7 (tableDensity false) (fullFactor true 12 7) density0_contains hk12_1_7_contains
noncomputable def atomAnswer : CBox := ⟨⟨4628823061479115557733842141,4628823061479115564085688648⟩,⟨(-476554862995980203086569850),(-476554862995980196820418909)⟩⟩
lemma atomChecked : tableAtomBox false ha12_1_7 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom false true 12 7) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains false true ha12_1_7 12 7 ha12_1_7_contains
 def realAnswer : RBox := ⟨7347378785329836105756297302,7347378785329840954390016449⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment false true 12 7) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm12_0_1_7
namespace hm12_1_1_7
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density1 j i k).mul (hk12_1_7 j i k))
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
noncomputable def s1_0 : CBox := ⟨⟨114713,114751⟩,⟨(-73830),(-73795)⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨204017,204101⟩,⟨(-118990),(-118904)⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨120373,120501⟩,⟨(-54989),(-54865)⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨35937,36109⟩,⟨(-9209),(-9031)⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨5820,6055⟩,⟨183,419⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨370,653⟩,⟨143,428⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨(-140),166⟩,⟨(-70),239⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨(-277),122⟩,⟨(-127),288⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨(-426),371⟩,⟨(-461),329⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨(-471),562⟩,⟨(-562),475⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨(-600),648⟩,⟨(-609),639⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨(-2045649580857558),(-2045649580857536)⟩,⟨1322296457564131,1322296457564152⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨(-3962031172004674),(-3962031172004644)⟩,⟨3283535558800777,3283535558800809⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨(-2581437902346848),(-2581437902346800)⟩,⟨3375385304617582,3375385304617631⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨(-685400923648314),(-685400923648251)⟩,⟨1959229091580883,1959229091580944⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨33982268331507,33982268331582⟩,⟨658637482195972,658637482196045⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨67944105995607,67944105995698⟩,⟨126905907816180,126905907816278⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨18684892071112,18684892071215⟩,⟨13164229890712,13164229890816⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨2788838459054,2788838459166⟩,⟨452134885282,452134885393⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨284981013918,284981014031⟩,⟨(-68194219690),(-68194219576)⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨23778927716,23778927822⟩,⟨(-14027207886),(-14027207778)⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨1947118631,1947118745⟩,⟨(-1678124067),(-1678123951)⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨185109195,185109316⟩,⟨(-180876387),(-180876268)⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨22645201,22645317⟩,⟨(-21084636),(-21084520)⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨3700103,3700206⟩,⟨(-3005909),(-3005809)⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨788239,788315⟩,⟨(-553956),(-553882)⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨153747,153780⟩,⟨(-98597),(-98561)⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨(-2220972111050981321155),(-2220972111050966055746)⟩,⟨(-2664352608243110739056),(-2664352608243095473486)⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨(-6199960039018165133163),(-6199960039018132901035)⟩,⟨(-5524470134446431701542),(-5524470134446399469101)⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨(-8008007049310274701843),(-8008007049310250442428)⟩,⟨(-3719370651902298571630),(-3719370651902274312048)⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨(-6349244166727470503196),(-6349244166727461874790)⟩,⟨(-22641401201276258604),(-22641401201267630273)⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨(-2912672516170588419595),(-2912672516170587026220)⟩,⟨1796893323245098538126,1796893323245099931349⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨(-514698203424136650575),(-514698203424136475821)⟩,⟨1365681351780437535889,1365681351780437710612⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨182428508618743612734,182428508618743626804⟩,⟨477204836401137035500,477204836401137049589⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨136424728643778856041,136424728643778857632⟩,⟨65295175761617815588,65295175761617817183⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨37237350231974578015,37237350231974578453⟩,⟨(-12186996550008134549),(-12186996550008134111)⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨4585664612857133472,4585664612857133620⟩,⟨(-8081400225090786511),(-8081400225090786364)⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨(-362410583972020833),(-362410583972020761)⟩,⟨(-2102276906654674131),(-2102276906654674058)⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨(-354188682056359006),(-354188682056358954)⟩,⟨(-358533693810150798),(-358533693810150746)⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨(-124313047252353111),(-124313047252353064)⟩,⟨(-36368042093313461),(-36368042093313417)⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨(-37269711355642332),(-37269711355642295)⟩,⟨3893634517065060,3893634517065100⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨(-11066248599363542),(-11066248599363510)⟩,⟨4238452506401106,4238452506401141⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨(-2489836261831272),(-2489836261831250)⟩,⟨1350479437944366,1350479437944390⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨8591872099061721268069896,8591872099061973009032096⟩,⟨(-5170172718427066399208834),(-5170172718426814658736438)⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨20584717539242393394519350,20584717539243270147392058⟩,⟨(-16995018829698867142747305),(-16995018829697990390718224)⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨19466327763879191949845771,19466327763880971972574675⟩,⟨(-28950804484130562708614176),(-28950804484128782685740765)⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨5841876172139724496165685,5841876172142399783764910⟩,⟨(-33156256934254812977111179),(-33156256934252137687668494)⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨(-9281299149032624345251521),(-9281299149029149871844727)⟩,⟨(-24480341153618338744351045),(-24480341153614864268853113)⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨(-14492247584703328999526967),(-14492247584698570697321042)⟩,⟨(-9153497614138172763143976),(-9153497614133414460716361)⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨(-9667150646252125085952346),(-9667150646248623922944140)⟩,⟨1647093162868020287293138,1647093162871521449621129⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨(-2928404454581908926264054),(-2928404454579416887972580)⟩,⟨4125761419546604565891019,4125761419549096603988149⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨431518038594575597352317,431518038595639553676270⟩,⟨2370279266853886930676525,2370279266854950887122371⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨878896568802665628597046,878896568803048764286682⟩,⟨625141539858488796377120,625141539858871932111199⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨460076038966384055783255,460076038966490877864253⟩,⟨(-45419726058861174592076),(-45419726058754352524273)⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨143534325440750498224310,143534325440771870394745⟩,⟨(-130090493346375417344727),(-130090493346354045184275)⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨23324687073966911186063,23324687073972742133172⟩,⟨(-77730585695124917073095),(-77730585695119086126620)⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨(-4857965602021513680412),(-4857965602020210065088)⟩,⟨(-34098745997794539377577),(-34098745997793235761243)⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨(-6125826122785547108441),(-6125826122785259409674)⟩,⟨(-12801341888677780000955),(-12801341888677492301446)⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨(-2207952279542315308984),(-2207952279542257796417)⟩,⟨(-3196707286632190523550),(-3196707286632133010760)⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨7239134034625043084436216,7239134034625043520508999⟩,⟨39132517296172394887538766,39132517296172395415029042⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨55747972555804862455736068,55747972555804863892571698⟩,⟨91537907714490060846600950,91537907714490062499841162⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨154018266550114818910052242,154018266550114821486382600⟩,⟨27895449463314228975389042,27895449463314231733061046⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨185862697962643886046281052,185862697962643890068385138⟩,⟨(-242099218341610337174474273),(-242099218341610333159532312)⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨(-33969833829361483239492632),(-33969833829361475658020324)⟩,⟨(-617775234705213826896279116),(-617775234705213819538222501)⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨(-508846204952451651244707584),(-508846204952451639189844922)⟩,⟨(-772450096118138167677861386),(-772450096118138155860966078)⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨(-929389713784352952737498083),(-929389713784352936939793281)⟩,⟨(-487469039472653086839893462),(-487469039472653071053664421)⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨(-961094967369264817952210353),(-961094967369264800909865623)⟩,⟨44886728014353291759962897,44886728014353308904433881⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨(-618027708278256886021558956),(-618027708278256864101036902)⟩,⟨426656650237809209206195807,426656650237809231165041400⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨(-200088796757139224424218796),(-200088796757139178323169549)⟩,⟨479829583409070739148180147,479829583409070785231397354⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨56133912736651362609492274,56133912736651479290552070⟩,⟨325285283855212338658860667,325285283855212455322192108⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨129097756298489009665123875,129097756298489331464717446⟩,⟨150321056343599726190905536,150321056343600047989009759⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨107108859528713457680683365,107108859528713963961579040⟩,⟨42346721736982777192598794,42346721736983283476617030⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨64790385012830014955771875,64790385012830521588027554⟩,⟨(-1389910683029826276638620),(-1389910683029319641821199)⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨31444318935943043844247665,31444318935943505403712401⟩,⟨(-9805836123535777815051631),(-9805836123535316254669014)⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨9095910362242089497610072,9095910362242279081955687⟩,⟨(-4357385196249351585584394),(-4357385196249162001048025)⟩⟩
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
noncomputable def ans : CBox := ⟨⟨(-405144001186144150352966768),(-405144001186140212996960613)⟩,⟨(-102817370836716971255581702),(-102817370836713033879313294)⟩⟩
lemma checked : cachedMomentRuleBox density1 hk12_1_7 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule true true 12 7) := by
  rw [← checked]
  exact @cached_density_rule_contains density1 hk12_1_7 (tableDensity true) (fullFactor true 12 7) density1_contains hk12_1_7_contains
noncomputable def atomAnswer : CBox := ⟨⟨(-6053076311164997276112054385),(-6053076311164997267805793569)⟩,⟨623187128533204872765163189,623187128533204880959360573⟩⟩
lemma atomChecked : tableAtomBox true ha12_1_7 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom true true 12 7) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains true true ha12_1_7 12 7 ha12_1_7_contains
 def realAnswer : RBox := ⟨(-6458220312351141426565021153),(-6458220312351137480702754182)⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment true true 12 7) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm12_1_1_7
end SharpPlanar.CachedData

end OAI
