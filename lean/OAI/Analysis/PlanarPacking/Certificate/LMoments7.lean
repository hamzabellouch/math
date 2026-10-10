import OAI.Analysis.PlanarPacking.Certificate.Columns10
import OAI.Analysis.PlanarPacking.Certificate.KernelValues10

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid
namespace cm1_7_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column1_0 j i k).mul (kernel7_0 j i k))
noncomputable def s0_0 : CBox := ⟨⟨396748,396764⟩,⟨16333,16349⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨796969,796985⟩,⟨277886,277902⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨427494,427511⟩,⟨581734,581753⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨(-115152),(-115135)⟩,⟨375222,375242⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨(-157576),(-157558)⟩,⟨(-2149),(-2131)⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨5198,5216⟩,⟨(-51878),(-51860)⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨13445,13462⟩,⟨8223,8239⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨(-4696),(-4680)⟩,⟨1203,1223⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨1131,1147⟩,⟨(-1225),(-1208)⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨(-212),(-192)⟩,⟨648,670⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨(-80),(-61)⟩,⟨(-359),(-341)⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨167,185⟩,⟨131,150⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨(-160),(-143)⟩,⟨50,68⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨(-42),(-24)⟩,⟨(-121),(-105)⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨47,63⟩,⟨(-59),(-42)⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨18,35⟩,⟨(-16),3⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨(-52607011872052),(-52607011872036)⟩,⟨83803677277,83803677293⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨(-112204261512866),(-112204261512850)⟩,⟨(-5179953784154),(-5179953784137)⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨(-94350884784415),(-94350884784399)⟩,⟨(-14220523176925),(-14220523176907)⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨(-46909343750829),(-46909343750812)⟩,⟨(-15767658989854),(-15767658989837)⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨(-14559515170475),(-14559515170459)⟩,⟨(-9786359556200),(-9786359556183)⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨(-2545962357809),(-2545962357793)⟩,⟨(-3775026749377),(-3775026749360)⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨(-59922996669),(-59922996653)⟩,⟨(-920218988692),(-920218988673)⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨91194445702,91194445720⟩,⟨(-126742252634),(-126742252618)⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨23766078493,23766078512⟩,⟨(-2250491112),(-2250491094)⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨2213420631,2213420649⟩,⟨2814765131,2814765147⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨(-241185779),(-241185763)⟩,⟨519203914,519203933⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨(-104972370),(-104972353)⟩,⟨233669,233685⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨(-11082834),(-11082817)⟩,⟨(-20427639),(-20427621)⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨2581949,2581965⟩,⟨(-5743676),(-5743660)⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨1744145,1744161⟩,⟨(-900390),(-900374)⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨467190,467206⟩,⟨(-57320),(-57304)⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨145358517595637515682,145358517595637516116⟩,⟨(-42431731617065422238),(-42431731617065421809)⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨332057524844012894215,332057524844012895247⟩,⟨(-112746837955505246946),(-112746837955505245921)⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨319284900942391651187,319284900942391652317⟩,⟨(-138873038737390286786),(-138873038737390285667)⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨194037858763936418907,194037858763936419739⟩,⟨(-112607495199543830168),(-112607495199543829337)⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨80817061412123650142,80817061412123650594⟩,⟨(-63324436019256632424),(-63324436019256631973)⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨23641843497284882227,23641843497284882419⟩,⟨(-25189381383555448003),(-25189381383555447813)⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨4817654822162485337,4817654822162485403⟩,⟨(-7173772765790190248),(-7173772765790190178)⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨606706355086453492,606706355086453520⟩,⟨(-1454735067081974808),(-1454735067081974783)⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨(-4972893806980184),(-4972893806980161)⟩,⟨(-192670804427458738),(-192670804427458720)⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨(-33280506349790769),(-33280506349790753)⟩,⟨(-6216279188296889),(-6216279188296873)⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨(-14949560179644272),(-14949560179644255)⟩,⟨5513548359936513,5513548359936529⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨(-5406900360721859),(-5406900360721843)⟩,⟨2224513084252617,2224513084252634⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨(-1886757368387318),(-1886757368387301)⟩,⟨598699500603065,598699500603082⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨(-674060734765317),(-674060734765301)⟩,⟨130678108212501,130678108212518⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨(-242401725816770),(-242401725816754)⟩,⟨21510302074912,21510302074928⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨(-61481687563911),(-61481687563895)⟩,⟨1775536288163,1775536288179⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨(-1145277342774671283107806),(-1145277342774671280807003)⟩,⟨199768091248549466212469,199768091248549468491109⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨(-2934472030278211044281725),(-2934472030278211038522455)⟩,⟨719416352691658984752254,719416352691658990445660⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨(-3521142830946726732587628),(-3521142830946726725178032)⟩,⟨1378576264585819512492797,1378576264585819519817410⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨(-2918525503464382996269739),(-2918525503464382989207463)⟩,⟨1852313162181894270640527,1852313162181894277631517⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨(-1749330849177344210009693),(-1749330849177344204674720)⟩,⟨1835583513486521752080999,1835583513486521757378947⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨(-713868529768179681626136),(-713868529768179678041352)⟩,⟨1383582714915406566384067,1383582714915406569968104⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨(-133460159473929487599712),(-133460159473929485596779)⟩,⟨812319946703148123849143,812319946703148125867126⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨63153747171050792710140,63153747171050793701453⟩,⟨379348010969146914977829,379348010969146915982304⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨77071680774263137767406,77071680774263138273717⟩,⟨143734991106315261030391,143734991106315261541145⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨46622618544121179053749,46622618544121179282522⟩,⟨44895821331738367914267,44895821331738368143752⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨22009202718370939413956,22009202718370939509852⟩,⟨11532944703247267495486,11532944703247267591117⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨9275249292103439699937,9275249292103439739170⟩,⟨2244801205258845347045,2244801205258845385990⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨3768421224045044380906,3768421224045044397257⟩,⟨143338297620044381402,143338297620044397583⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨1537768776960225848176,1537768776960225855474⟩,⟨(-172810279485081547204),(-172810279485081539973)⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨612538701873253815119,612538701873253818278⟩,⟨(-131397711057906260413),(-131397711057906257276)⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨164443379484024329955,164443379484024330851⟩,⟨(-43864230117996377437),(-43864230117996376548)⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨73277388367931618781148930,73277388367931619616667285⟩,⟨268583563795024956084801437,268583563795024956921348742⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨252915317860582817953145690,252915317860582820241190113⟩,⟨705315718043644806307007431,705315718043644808599111560⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨481941734412729448286418379,481941734412729451436199394⟩,⟨883552181165824768403148781,883552181165824771561342726⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨683044419384664585004207054,683044419384664588253937848⟩,⟨763995275237535030449053393,763995275237535033710416859⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨747459846888558018842746045,747459846888558021541976983⟩,⟨447677526667720471854804337,447677526667720474564885419⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨637753178360855897150771458,637753178360855899271923758⟩,⟨111361780754865952876365041,111361780754865955000655515⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨420899524640711735168163823,420899524640711736732216129⟩,⟨(-106693288124311875343626898),(-106693288124311873782343490)⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨205406072268098047358896093,205406072268098048341769936⟩,⟨(-175537035309357270960815485),(-175537035309357269979799845)⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨60612992811333230216354993,60612992811333230749935461⟩,⟨(-147760453411974246009202215),(-147760453411974245475314105)⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨(-6905810491110257375642413),(-6905810491110257099899642)⟩,⟨(-91076233067232181929073275),(-91076233067232181651916011)⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨(-24921275036264449579584554),(-24921275036264449410164018)⟩,⟨(-44739934603627233171113213),(-44739934603627233000692709)⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨(-22075216982145357027907097),(-22075216982145356931113144)⟩,⟨(-17874656760731098711186551),(-17874656760731098614086094)⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨(-14611610560973945020242888),(-14611610560973944968461484)⟩,⟨(-5539283101349091390510009),(-5539283101349091338769324)⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨(-8350553151965318000920790),(-8350553151965317974589250)⟩,⟨(-979453262203226644914054),(-979453262203226618703447)⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨(-4119345082919344864650378),(-4119345082919344852456766)⟩,⟨206592816407806299212559,206592816407806311312636⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨(-1226616782880327681513515),(-1226616782880327677987576)⟩,⟨165922995390425652700564,165922995390425656193325⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨(-22098829958487839500073620),(-22098829958487837503714692)⟩,⟨(-36747153515936201165385663),(-36747153515936199174445852)⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨(-333638127389830767250684189),(-333638127389830761166841116)⟩,⟨(-494441663284683929612976467),(-494441663284683923531084672)⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨(-1425174314468846248116566704),(-1425174314468846237796430696)⟩,⟨(-1725259303092055689353300655),(-1725259303092055679011412160)⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨(-3595081754355302523768364508),(-3595081754355302509316220569)⟩,⟨(-3275704168593371862342870046),(-3275704168593371847861415300)⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨(-6565755010457165979919488716),(-6565755010457165961834474367)⟩,⟨(-4085554294924154174656088806),(-4085554294924154156596205216)⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨(-9370007373145455908509695781),(-9370007373145455887874037103)⟩,⟨(-3300717943353141314176073528),(-3300717943353141293684204050)⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨(-10828291366450421721865098471),(-10828291366450421699145374673)⟩,⟨(-998650740588439958192524236),(-998650740588439935716387439)⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨(-10329504063472585565867667829),(-10329504063472585541126686186)⟩,⟨1829543771967865977978923974,1829543771967866002507396031⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨(-8216490767604687749167528696),(-8216490767604687725373885745)⟩,⟨4004964479870573784679297756,4004964479870573808391860528⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨(-5456431908503848095068820999),(-5456431908503848074625367746)⟩,⟨4903984089807828221738016988,4903984089807828242202479917⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨(-2978778057217478888712096996),(-2978778057217478872234130582)⟩,⟨4636581457298704008968331614,4636581457298704025511126342⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨(-1254566490898395153440087390),(-1254566490898395140662556161)⟩,⟨3712799772796459153729185214,3712799772796459166566277617⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨(-301246546009442458853029794),(-301246546009442449501502035)⟩,⟨2628973298860537768834023985,2628973298860537778220820111⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨90739186763408857554939610,90739186763408863753997623⟩,⟨1666513316099401806969112193,1666513316099401813184459760⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨155860910121838504098711341,155860910121838507581249564⟩,⟨899755154466810002519861882,899755154466810006008247006⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨66495620514518302019204134,66495620514518303133680479⟩,⟨282002103110626762613217852,282002103110626763729077283⟩⟩
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
noncomputable def ans : CBox := ⟨⟨(-9482626601106667910035120798),(-9482626601106667871573594542)⟩,⟨2207910501441997203525887611,2207910501441997241917208773⟩⟩
lemma checked : cachedMomentRuleBox column1_0 kernel7_0 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (momentRuleValue quadraturePoint fejerWeight 1 7 false false) := by
  rw [← checked]
  exact cachedMomentRuleBox_contains column1_0_contains kernel7_0_contains
end cm1_7_0_0
namespace cm1_7_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column1_0 j i k).mul (kernel7_1 j i k))
noncomputable def s0_0 : CBox := ⟨⟨(-2986075),(-2986057)⟩,⟨(-1595841),(-1595825)⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨(-5142289),(-5142265)⟩,⟨(-5065229),(-5065205)⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨(-1269457),(-1269428)⟩,⟨(-6078371),(-6078346)⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨2203594,2203626⟩,⟨(-2594257),(-2594225)⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨1275679,1275713⟩,⟨527427,527460⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨(-198702),(-198666)⟩,⟨416897,416934⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨(-92779),(-92736)⟩,⟨(-106672),(-106630)⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨43858,43902⟩,⟨435,477⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨(-12582),(-12537)⟩,⟨8581,8628⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨2851,2899⟩,⟨(-5688),(-5639)⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨212,258⟩,⟨3266,3313⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨(-1535),(-1488)⟩,⟨(-1457),(-1413)⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨1408,1445⟩,⟨(-487),(-446)⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨267,299⟩,⟨1053,1086⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨(-550),(-525)⟩,⟨448,475⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨(-254),(-233)⟩,⟨26,47⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨260066654559345,260066654559365⟩,⟨270408108523801,270408108523818⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨532289552036665,532289552036684⟩,⟨602496770615760,602496770615779⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨405728898407312,405728898407335⟩,⟨555393760013525,555393760013547⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨163943375033905,163943375033933⟩,⟨321006187051830,321006187051857⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨28944928607654,28944928607683⟩,⟨126195797493846,126195797493875⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨(-4590958354985),(-4590958354956)⟩,⟨33821968523651,33821968523680⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨(-4166717746563),(-4166717746529)⟩,⟨5665731004517,5665731004548⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨(-1165364070162),(-1165364070129)⟩,⟨335325543272,335325543304⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨(-162127279664),(-162127279629)⟩,⟨(-96782158678),(-96782158645)⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨(-1986986142),(-1986986105)⟩,⟨(-28753100234),(-28753100200)⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨3933429636,3933429672⟩,⟨(-2539173051),(-2539173019)⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨751776941,751776974⟩,⟨438390100,438390132⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨(-850268),(-850236)⟩,⟨194787636,194787667⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨(-41702559),(-41702534)⟩,⟨33042992,33043015⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨(-16668819),(-16668793)⟩,⟨242670,242695⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨(-3789576),(-3789558)⟩,⟨(-1304523),(-1304503)⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨(-629325592055550685110),(-629325592055550681982)⟩,⟨(-622368914350535314489),(-622368914350535311362)⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨(-1529333978269271538185),(-1529333978269271530599)⟩,⟨(-1375562107953056226907),(-1375562107953056219332)⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨(-1647505134997676455260),(-1647505134997676447007)⟩,⟨(-1230774603506120741961),(-1230774603506120733737)⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨(-1165367698037464203318),(-1165367698037464197305)⟩,⟨(-658492508196088781101),(-658492508196088775116)⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨(-580741895810386946310),(-580741895810386943124)⟩,⟨(-218802322115551729358),(-218802322115551726197)⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨(-208266041260452923522),(-208266041260452922261)⟩,⟨(-39951147722105553402),(-39951147722105552156)⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨(-53970656472881705393),(-53970656472881704997)⟩,⟨(-334851821645665731),(-334851821645665339)⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨(-9800327240438429316),(-9800327240438429206)⟩,⟨2120632460177050670,2120632460177050776⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨(-987011562705012337),(-987011562705012302)⟩,⟨764259979578828048,764259979578828085⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨102852698012437217,102852698012437241⟩,⟨198874148983996192,198874148983996213⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨92616230189395129,92616230189395150⟩,⟨54586800954658510,54586800954658532⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨35702892065626058,35702892065626081⟩,⟨18278193446377903,18278193446377927⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨11841127954918212,11841127954918235⟩,⟨7035332903130307,7035332903130327⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨3887974798277438,3887974798277460⟩,⟨2867581969785967,2867581969785990⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨1289357090711704,1289357090711724⟩,⟨1146636311427882,1146636311427900⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨311093051172618,311093051172636⟩,⟨308062637348134,308062637348153⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨2664501277399850878347233,2664501277399850891381988⟩,⟨4990398671007334551083510,4990398671007334564212254⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨7850099908016442723558211,7850099908016442758082044⟩,⟨12486219423278739654772354,12486219423278739689531876⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨11968152811018767172162959,11968152811018767216403774⟩,⟨14204757748322771928543923,14204757748322771973038631⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨13438963742269717670353162,13438963742269717710917764⟩,⟨10631077115499876887300307,10631077115499876928013718⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨11645614997910663602261626,11645614997910663631623350⟩,⟨5112521028806102085123151,5112521028806102114478038⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨7867485909248697949326415,7867485909248697968682237⟩,⟨906152396868080801039566,906152396868080820270319⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨4156675554430382149711129,4156675554430382161094490⟩,⟨(-906576176576994670002206),(-906576176576994658741448)⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨1713118364896714867673313,1713118364896714874385509⟩,⟨(-1073811651386207462371666),(-1073811651386207455701645)⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨538918841448604299014860,538918841448604302386125⟩,⟨(-686644106728275222776357),(-686644106728275219408662)⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨115912677662079089830538,115912677662079091329231⟩,⟨(-333041291903275644259377),(-333041291903275642754791)⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨4563540613880503808241,4563540613880504438701⟩,⟨(-137638063372702717727754),(-137638063372702717092211)⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨(-12180111966898482036864),(-12180111966898481760303)⟩,⟨(-52327072323779063139455),(-52327072323779062860944)⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨(-9218521260176859176947),(-9218521260176859053433)⟩,⟨(-19446132272822442235582),(-19446132272822442111514)⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨(-5071922212823141342155),(-5071922212823141286241)⟩,⟨(-7345503895218876326568),(-7345503895218876270512)⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨(-2378629232208719108123),(-2378629232208719083924)⟩,⟨(-2756611714528584152764),(-2756611714528584128538)⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨(-688031384357607601150),(-688031384357607594362)⟩,⟨(-715936392474240888428),(-715936392474240881640)⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨1046057872290777509347993193,1046057872290777513094415311⟩,⟨(-489521445651190271288285890),(-489521445651190267551699342)⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨2707800740824426246011497001,2707800740824426256265085205⟩,⟨(-1543710121473721464586961309),(-1543710121473721454364890177)⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨3278054935019486631251161623,3278054935019486645348434092⟩,⟨(-2640591667665398016511369121),(-2640591667665398002467760907)⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨2632755549437630549181019483,2632755549437630563690647181⟩,⟨(-3425266183390094195409624821),(-3425266183390094180965207973)⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨1252688393469930179674103767,1252688393469930192301456719⟩,⟨(-3492664547377910991341212295),(-3492664547377910978760653887)⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨(-93483773471112291454336075),(-93483773471112280837876771)⟩,⟨(-2789300868904842929183284274),(-2789300868904842918570512793)⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨(-854760441774419174289287700),(-854760441774419166617763751)⟩,⟨(-1694371712031170071170329164),(-1694371712031170063484436265)⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨(-967790264605867924893583664),(-967790264605867920158893184)⟩,⟨(-707195045165789815605769772),(-707195045165789810864094203)⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨(-712295374108013459812920861),(-712295374108013457248741830)⟩,⟨(-102186199883969055787747707),(-102186199883969053227032271)⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨(-394508682526060313633142656),(-394508682526060312117390715)⟩,⟨138088642699690792948302588,138088642699690794458123468⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨(-168623410157038241194321267),(-168623410157038240273360222)⟩,⟨167795066026255841498817118,167795066026255842416924243⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨(-51265678165778633652090510),(-51265678165778633135613819)⟩,⟨123544169861082892411978123,123544169861082892928464532⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨(-4772883215788578116653744),(-4772883215788577843986799)⟩,⟨74307688854575731559632699,74307688854575731833385056⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨7645215413913641700771039,7645215413913641838671996⟩,⟨39713753586813553464165365,39713753586813553603115324⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨7093520358291432413184686,7093520358291432480382449⟩,⟨18667794365029763680322656,18667794365029763748075400⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨2618858857027589729308352,2618858857027589749531444⟩,⟨5413067897556658725979429,5413067897556658746363557⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨(-128588613718258961572767087),(-128588613718258954277569631)⟩,⟨86858424433617221508004661,86858424433617228818144711⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨(-1724770617208646487517897992),(-1724770617208646465185736675)⟩,⟨1306957029441944035054761276,1306957029441944057383340382⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨(-5971701073211342161754693557),(-5971701073211342123602133507)⟩,⟨5556232985152655699961651070,5556232985152655738030362960⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨(-11140909457578838620786190766),(-11140909457578838566930019722)⟩,⟨13945913515204516294462608152,13945913515204516348233941168⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨(-13324343862831064457214924292),(-13324343862831064389180789056)⟩,⟨25341616852881036884172441353,25341616852881036952369299297⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨(-9448069585968104669017780529),(-9448069585968104590324356745)⟩,⟨35947098635969082277957666838,35947098635969082357305003763⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨(-676395121567256471914932),(-676395121567164423684532)⟩,⟨41167824128068835777179959415,41167824128068835870165306401⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨11052037858878191838622657444,11052037858878191940678255493⟩,⟨38676019850997631434426268360,38676019850997631537221386852⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨19108670451570808528048324389,19108670451570808628339822743⟩,⟨29937815771121957676591298746,29937815771121957777091391348⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨21856324324839878685997096097,21856324324839878774188224489⟩,⟨18886221799406654883848860601,18886221799406654971857632832⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨19938970140238073436623832318,19938970140238073509618237502⟩,⟨9240793097451693427840277290,9240793097451693500512152494⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨15559091135000429107409730760,15559091135000429166161302555⟩,⟨2810453943657424728168367924,2810453943657424786689198324⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨10774124148498929530519895539,10774124148498929574008282066⟩,⟨(-450365865289550051585976639),(-450365865289550008220199158)⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨6694886608264095284054622421,6694886608264095313144091564⟩,⟨(-1477397939738677511952647573),(-1477397939738677482912813378)⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨3557195796695357339458943873,3557195796695357355906083662⟩,⟨(-1254896462073120340480268368),(-1254896462073120324047371862)⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨1104733335215963248264682120,1104733335215963253545956041⟩,⟨(-469242995652715262392936418),(-469242995652715257114242144)⟩⟩
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
noncomputable def ans : CBox := ⟨⟨12609352902761952573371327817,12609352902761952733617967940⟩,⟨33829955307250095158872088477,33829955307250095319355653266⟩⟩
lemma checked : cachedMomentRuleBox column1_0 kernel7_1 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (momentRuleValue quadraturePoint fejerWeight 1 7 false true) := by
  rw [← checked]
  exact cachedMomentRuleBox_contains column1_0_contains kernel7_1_contains
end cm1_7_0_1
namespace cm1_7_1_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column1_1 j i k).mul (kernel7_0 j i k))
noncomputable def s0_0 : CBox := ⟨⟨(-1839483),(-1839466)⟩,⟨(-574298),(-574281)⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨(-3236364),(-3236345)⟩,⟨(-2407598),(-2407579)⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨(-823740),(-823716)⟩,⟨(-3230507),(-3230486)⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨1213575,1213598⟩,⟨(-1206043),(-1206023)⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨513441,513464⟩,⟨369344,369370⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨(-139003),(-138977)⟩,⟨127598,127619⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨(-9436),(-9411)⟩,⟨(-49949),(-49923)⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨10795,10821⟩,⟨8628,8654⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨(-4172),(-4149)⟩,⟨(-796),(-766)⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨1531,1555⟩,⟨(-335),(-311)⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨(-603),(-578)⟩,⟨438,463⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨103,121⟩,⟨(-430),(-408)⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨189,210⟩,⟨205,224⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨(-174),(-156)⟩,⟨116,134⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨(-120),(-104)⟩,⟨(-69),(-52)⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨(-30),(-14)⟩,⟨(-49),(-31)⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨103004276318231,103004276318247⟩,⟨(-8869087552656),(-8869087552640)⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨220956212209313,220956212209329⟩,⟨(-4350869963700),(-4350869963681)⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨186613858931588,186613858931606⟩,⟨22543929036332,22543929036350⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨91590419986099,91590419986117⟩,⟨33237551399142,33237551399159⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨26649965621846,26649965621866⟩,⟨21703960950725,21703960950743⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨3616389216637,3616389216657⟩,⟨8041877956558,8041877956578⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨(-333498798192),(-333498798171)⟩,⟨1718426620312,1718426620333⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨(-237341008235),(-237341008216)⟩,⟨163235642367,163235642390⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨(-40128135112),(-40128135091)⟩,⟨(-13983469553),(-13983469532)⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨(-964242040),(-964242024)⟩,⟨(-6045652339),(-6045652321)⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨796180373,796180392⟩,⟨(-497476902),(-497476885)⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨133319326,133319346⟩,⟨97966752,97966771⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨(-6537741),(-6537724)⟩,⟨34765050,34765068⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨(-8473981),(-8473964)⟩,⟨3886892,3886909⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨(-2751012),(-2750996)⟩,⟨(-747246),(-747229)⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨(-546441),(-546425)⟩,⟨(-399615),(-399599)⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨91826740928599303946,91826740928599304968⟩,⟨474270294221630380466,474270294221630381490⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨265155844899936353765,265155844899936356302⟩,⟨1123076172547884584270,1123076172547884586820⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨371247604179903805599,371247604179903808542⟩,⟨1163426369410501399453,1163426369410501402406⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨350197279789034605705,350197279789034608084⟩,⟨796669450388613431585,796669450388613433972⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨235082975779268362090,235082975779268363555⟩,⟨395917203581307977477,395917203581307978943⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨116260720355217644245,116260720355217644959⟩,⟨150063219919379068245,150063219919379068963⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨43966425117461774006,43966425117461774300⟩,⟨45556114911631465367,45556114911631465657⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨13277503670727584340,13277503670727584446⟩,⟨11785473687375682436,11785473687375682546⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨3363422626506961698,3363422626506961745⟩,⟨2798597133068661940,2798597133068661985⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨752927914028808775,752927914028808803⟩,⟨655123910047730889,655123910047730919⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨156680503034253036,156680503034253058⟩,⟨159033113940936482,159033113940936506⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨31693892402611433,31693892402611453⟩,⟨41218380408716477,41218380408716497⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨6452985205729612,6452985205729630⟩,⟨11634462026700464,11634462026700486⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨1349244797054119,1349244797054139⟩,⟨3617016778406490,3617016778406510⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨287528972665643,287528972665664⟩,⟨1194339544567295,1194339544567313⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨49541944094961,49541944094978⟩,⟨290842733477729,290842733477746⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨572147652031307068805129,572147652031307069485608⟩,⟨51803597635449254430852,51803597635449255112209⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨1490661834159439891731462,1490661834159439893457978⟩,⟨40593743439793319607313,40593743439793321335041⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨1853124441829638617390154,1853124441829638619609187⟩,⟨(-179229273230042086090428),(-179229273230042083874092)⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨1631626230058756739558446,1631626230058756741658982⟩,⟨(-461453099331167181449608),(-461453099331167179357396)⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨1084392278653065070715058,1084392278653065072320070⟩,⟨(-596533413486601774581240),(-596533413486601772985960)⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨542916924894224605756844,542916924894224606928255⟩,⟨(-524948531875464994731997),(-524948531875464993565807)⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨193511347939259407043723,193511347939259407775737⟩,⟨(-345939605992034672622269),(-345939605992034671892609)⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨37297644206402194899375,37297644206402195305706⟩,⟨(-179810986215282071243117),(-179810986215282070837646)⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨(-7723810249423060596417),(-7723810249423060379019)⟩,⟨(-76794365550039632878399),(-76794365550039632660970)⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨(-11553306726494166467604),(-11553306726494166363872)⟩,⟨(-28060119020794782897480),(-28060119020794782793618)⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨(-7024374190763230194528),(-7024374190763230148176)⟩,⟨(-9159253652892386134416),(-9159253652892386087992)⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨(-3391487382124725741719),(-3391487382124725721500)⟩,⟨(-2795203945060063549706),(-2795203945060063529451)⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨(-1508452993559073658352),(-1508452993559073649455)⟩,⟨(-833894530404973673928),(-833894530404973665011)⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨(-656164866970207960705),(-656164866970207956703)⟩,⟨(-252135228010942296548),(-252135228010942292539)⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨(-272671003789245453825),(-272671003789245452100)⟩,⟨(-77088970419070967503),(-77088970419070965776)⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨(-74781881195828547652),(-74781881195828547159)⟩,⟨(-17530416094042311050),(-17530416094042310555)⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨(-515302440829115234031783040),(-515302440829115233070870333)⟩,⟨(-414406992202320376770746084),(-414406992202320375804068792)⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨(-1470329251104007427567134230),(-1470329251104007424903839707)⟩,⟨(-1046064796733219308101258276),(-1046064796733219305424949667)⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨(-2181541128162357933543619580),(-2181541128162357929779173952)⟩,⟨(-1198076424705053894782509806),(-1198076424705053891007754090)⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨(-2485370813363338241701660765),(-2485370813363338237635217228)⟩,⟨(-857747688881275951903013286),(-857747688881275947837862243)⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨(-2317968205556185338699545784),(-2317968205556185335060987645)⟩,⟨(-265218051155501433201412001),(-265218051155501429577824420)⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨(-1789725999046351218950851459),(-1789725999046351215893159932)⟩,⟨262990653006971466083843873,262990653006971469120328397⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨(-1136684772673798533695613171),(-1136684772673798531333679525)⟩,⟨532766571446712843988437317,532766571446712846333306128⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨(-580128208017310357803703080),(-580128208017310356191935266)⟩,⟨543448886648507684787264301,543448886648507686393329840⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨(-221559242883210598367848313),(-221559242883210597372149575)⟩,⟨412031072701632218847516682,412031072701632219842982073⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨(-44456843281154330873716249),(-44456843281154330304289655)⟩,⟨256948820755273035444312189,256948820755273036014950807⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨18881907633823264278177045,18881907633823264596111323⟩,⟨139051682067277325946801453,139051682067277326265908299⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨29754967112861121689013873,29754967112861121860756285⟩,⟨67956338323262183445297385,67956338323262183617565895⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨23574573059445311180776376,23574573059445311270335286⟩,⟨30997751969044319249403666,30997751969044319339134125⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨14963294469411228967457791,14963294469411229012608047⟩,⟨13480790330318883371192679,13480790330318883416397133⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨7904614998626519020449142,7904614998626519041342997⟩,⟨5455152119475146875411113,5455152119475146896321878⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨2438889459238626057133493,2438889459238626063179307⟩,⟨1455679655541755855121561,1455679655541755861171229⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨(-14734390623310643288924569281),(-14734390623310643276271345306)⟩,⟨8778179249126714252236530802,8778179249126714264549690451⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨(-40146604511757875184208325291),(-40146604511757875147055959965)⟩,⟨26660883314335502688762578971,26660883314335502725072662293⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨(-54666229960443299213301185596),(-54666229960443299154346188255)⟩,⟨44459013510038592314584371766,44459013510038592372651211912⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨(-55120649484811804583724588715),(-55120649484811804507748112414)⟩,⟨59600329707513396395962175791,59600329707513396471496749985⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨(-43138899909632863942108910316),(-43138899909632863854270482593)⟩,⟨68258945199502935393769201071,68258945199502935481879700269⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨(-24357505575501353367863699603),(-24357505575501353275578520962)⟩,⟨67755333766903706446895780520,67755333766903706540101081667⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨(-5735604997726441073950863407),(-5735604997726440984887057488)⟩,⟨58518983857830671590391353467,58518983857830671680598838773⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨7570612776316334342754181968,7570612776316334423483987917⟩,⟨44017082675901999649104801657,44017082675901999730652524972⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨13889099855100274987913039567,13889099855100275055625822360⟩,⟨28798315373694660379413234301,28798315373694660447406054321⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨14539559549720914870755645988,14539559549720914923033993575⟩,⟨16286374137545318142749242407,16286374137545318195003772282⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨12074257347251544700360814413,12074257347251544739159239818⟩,⟨7800249962685531811379981309,7800249962685531850056445681⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨8708209362969086598157119804,8708209362969086625927655079⟩,⟨2959728009732933575873748948,2959728009732933603535639348⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨5683328934600690030512879149,5683328934600690049238803761⟩,⟨657647856532780428159517647,657647856532780446821261078⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨3392912084928910439908055134,3392912084928910451623747806⟩,⟨(-182749319765219904187445359),(-182749319765219892501202948)⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨1760926656648242293493617333,1760926656648242299836152561⟩,⟨(-304648927818424087211247483),(-304648927818424080879356770)⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨541200698849167243887140411,541200698849167245880321087⟩,⟨(-127600512777876260340005436),(-127600512777876258349402349)⟩⟩
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
noncomputable def ans : CBox := ⟨⟨(-30396325248391578289864374480),(-30396325248391578159140331101)⟩,⟨72069804660600763614346213173,72069804660600763745158905528⟩⟩
lemma checked : cachedMomentRuleBox column1_1 kernel7_0 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (momentRuleValue quadraturePoint fejerWeight 1 7 true false) := by
  rw [← checked]
  exact cachedMomentRuleBox_contains column1_1_contains kernel7_0_contains
end cm1_7_1_0
namespace cm1_7_1_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column1_1 j i k).mul (kernel7_1 j i k))
noncomputable def s0_0 : CBox := ⟨⟨11996763,11996788⟩,⟨11226979,11227005⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨16198751,16198801⟩,⟨30457171,30457221⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨(-5087226),(-5087155)⟩,⟨28224454,28224526⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨(-13805917),(-13805828)⟩,⟨5443679,5443769⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨(-2982699),(-2982588)⟩,⟨(-4670898),(-4670790)⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨1541494,1541611⟩,⟨(-647278),(-647163)⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨(-54592),(-54467)⟩,⟨452155,452281⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨(-74181),(-74056)⟩,⟨(-101206),(-101081)⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨35536,35655⟩,⟨15172,15289⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨(-14565),(-14453)⟩,⟨420,536⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨5902,5999⟩,⟨(-3475),(-3378)⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨(-1418),(-1333)⟩,⟨3730,3815⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨(-1773),(-1703)⟩,⟨(-2120),(-2052)⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨1531,1589⟩,⟨(-1128),(-1074)⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨1012,1051⟩,⟨569,605⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨176,200⟩,⟨352,376⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨(-554023459699548),(-554023459699527)⟩,⟨(-486497314484555),(-486497314484536)⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨(-1123001747165911),(-1123001747165886)⟩,⟨(-1114010152083786),(-1114010152083764)⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨(-831081608422420),(-831081608422393)⟩,⟨(-1070269268837968),(-1070269268837938)⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨(-307601563732960),(-307601563732923)⟩,⟨(-639607911651678),(-639607911651643)⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨(-33815611104091),(-33815611104051)⟩,⟨(-251430487296541),(-251430487296500)⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨19903240970107,19903240970150⟩,⟨(-63040204868477),(-63040204868434)⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨10384135910180,10384135910226⟩,⟨(-8393513065048),(-8393513065003)⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨2232800364179,2232800364228⟩,⟨144573160806,144573160853⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨190545323778,190545323827⟩,⟨276930032998,276930033047⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨(-20965325585),(-20965325539)⟩,⟨44599054571,44599054619⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨(-7678184031),(-7678183986)⟩,⟨(-33838233),(-33838189)⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨(-542697703),(-542697660)⟩,⟨(-1259741131),(-1259741089)⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨188150520,188150559⟩,⟨(-229158061),(-229158025)⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨78680035,78680066⟩,⟨3801042,3801074⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨18086237,18086262⟩,⟨16095762,16095788⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨2691144,2691166⟩,⟨5097211,5097230⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨2162935766546014034381,2162935766546014042366⟩,⟨(-1815132720708515915810),(-1815132720708515907827)⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨4985637028570135670810,4985637028570135690883⟩,⟨(-4578302091059596543102),(-4578302091059596523029)⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨4879562191659919055315,4879562191659919078778⟩,⟨(-5312655300812915851003),(-5312655300812915827528)⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨3042080966110911807315,3042080966110911826467⟩,⟨(-4208608117625301385079),(-4208608117625301365903)⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨1307448941372627514069,1307448941372627525992⟩,⟨(-2457710566032857804370),(-2457710566032857792427)⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨396558236858571424638,396558236858571430526⟩,⟨(-1096206104897859245293),(-1096206104897859239394)⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨85366589993112721781,85366589993112724174⟩,⟨(-386361805019402585998),(-386361805019402583602)⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨13196294879064770393,13196294879064771240⟩,⟨(-112298912048741682650),(-112298912048741681805)⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨1714697996186622502,1714697996186622800⟩,⟨(-28365009705666040175),(-28365009705666039875)⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨378200610947164892,378200610947165023⟩,⟨(-6597896428160246456),(-6597896428160246326)⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨164326613372910531,164326613372910615⟩,⟨(-1496805223687964994),(-1496805223687964904)⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨73864188180858105,73864188180858174⟩,⟨(-348875667057140923),(-348875667057140855)⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨30632419476843770,30632419476843829⟩,⟨(-87342649866922984),(-87342649866922924)⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨12303177857525552,12303177857525602⟩,⟨(-24214396189104758),(-24214396189104708)⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨4767385605697321,4767385605697354⟩,⟨(-7289411703883173),(-7289411703883132)⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨1255258136252947,1255258136252971⟩,⟨(-1683617470482727),(-1683617470482704)⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨(-630321219066246032773871),(-630321219066246028805451)⟩,⟨(-2723527988128059331521334),(-2723527988128059327552605)⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨(-2106723010870573368949648),(-2106723010870573358442299)⟩,⟨(-6967892226482957711187920),(-6967892226482957700671146)⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨(-3757333786460643256000660),(-3757333786460643242527875)⟩,⟨(-8337712118371200821510198),(-8337712118371200808008985)⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨(-4826330272405056169654803),(-4826330272405056157261685)⟩,⟨(-6881880026314874323719577),(-6881880026314874311280346)⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨(-4666199900478968127316980),(-4666199900478968118128321)⟩,⟨(-4094463367711180727397593),(-4094463367711180718161988)⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨(-3474699054511450327990136),(-3474699054511450321287753)⟩,⟨(-1638359060557118310877370),(-1638359060557118304146934)⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨(-2030626382215752538349397),(-2030626382215752533943821)⟩,⟨(-270597320543386697383097),(-270597320543386692965405)⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨(-948044829305334762244993),(-948044829305334759490752)⟩,⟨182688395561764302304137,182688395561764305059034⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨(-359836867240749482238360),(-359836867240749480753749)⟩,⟨202868052964573779298015,202868052964573780781017⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨(-112534449601024508009869),(-112534449601024507295046)⟩,⟨121123328980580983435195,121123328980580984148792⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨(-28805703186675057739051),(-28805703186675057413409)⟩,⟨57121746886687866922522,57121746886687867247554⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨(-5476707520789062484684),(-5476707520789062335923)⟩,⟨24129388432418610213098,24129388432418610361679⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨(-239253294458893175126),(-239253294458893106920)⟩,⟨9833133535048744986003,9833133535048745054178⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨507669981071473191444,507669981071473222484⟩,⟨4023000757323343268784,4023000757323343299819⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨367555074724565697322,367555074724565710718⟩,⟨1605308248395839702922,1605308248395839716321⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨121508926888296799750,121508926888296803506⟩,⟨431336752369879904098,431336752369879907855⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨(-1329474744826521243025970239),(-1329474744826521238456423966)⟩,⟨2399544186089840549968278865,2399544186089840554520561398⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨(-3228035243257201115643881672),(-3228035243257201102947955648)⟩,⟨6776892589389120303924367617,6776892589389120316584459302⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨(-3308904684076887040143049741),(-3308904684076887022108217563)⟩,⟨9869953877809328811592172940,9869953877809328829609080697⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨(-1616794522249675597638107030),(-1616794522249675578007646656)⟩,⟨10966032675953280645379791632,10966032675953280665041261355⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨806872275573821446964598249,806872275573821464880070751⟩,⟨9904468813112325400122279611,9904468813112325418118120333⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨2690397451772640878080872048,2690397451772640893553729268⟩,⟨7320674432217188588861935171,7320674432217188604423619206⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨3352057325124394777148727575,3352057325124394789290860256⟩,⟨4344860955875638208338307946,4344860955875638220542063845⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨2939346398038047856392743590,2939346398038047864856884180⟩,⟨1949464463291258141775067926,1949464463291258150256041085⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨2044289396450264855744299635,2044289396450264861105041267⟩,⟨515002225678957471006457102,515002225678957476364129879⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨1188680592220977944848822979,1188680592220977948041519099⟩,⟨(-106658184594063240874130043),(-106658184594063237688479077)⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨597981257277881680959055932,597981257277881682775845146⟩,⟨(-259543395762589141601331501),(-259543395762589139789457943)⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨267231753090071296620844537,267231753090071297616395521⟩,⟨(-225026152005043792008570751),(-225026152005043791015027090)⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨108197704377275364384613187,108197704377275364910197255⟩,⟨(-150768097022532040450443435),(-150768097022532039925475501)⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨40072010573100973793157075,40072010573100974061002702⟩,⟨(-88203084394597377845839135),(-88203084394597377578167691)⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨13344520004971015890295875,13344520004971016016185635⟩,⟨(-44546060540167981170624250),(-44546060540167981044753239)⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨3037561010255247501791673,3037561010255247538591598⟩,⟨(-13459862078052917231507122),(-13459862078052917194701320)⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨34512531644191759898974583513,34512531644191759945887199617⟩,⟨51571022796167092834595982978,51571022796167092882698457394⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨104484034479299381830369844118,104484034479299381969274073711⟩,⟨140110815845763966933168935460,140110815845763967074969096294⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨173385982575563734357929312679,173385982575563734581836088060⟩,⟨189352357184515736107337785198,189352357184515736334132650003⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨231251889797754403496075053413,231251889797754403790707846608⟩,⟨187685632431073862838260248462,187685632431073863133936245212⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨263504730135060192354438018902,263504730135060192703207401231⟩,⟨141005621852786171921034078175,141005621852786172268040233895⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨259986834361789605998081034811,259986834361789606373502351246⟩,⟨70193603857610848358853530465,70193603857610848730037512023⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨222538107226719778332994683294,222538107226719778704687299159⟩,⟨1332996288346635401683723919,1332996288346635768885261224⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨164869437982251225880301080018,164869437982251226223374242685⟩,⟨(-46190355909085493923259068386),(-46190355909085493583100270804)⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨104986814619671164885868850843,104986814619671165178166392831⟩,⟨(-66371872841151771341024713517),(-66371872841151771049529618468)⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨56420219504510861214449549242,56420219504510861443987433544⟩,⟨(-64836468204716680696427205428),(-64836468204716680466560183101)⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨24237173475945930575730480836,24237173475945930749293144609⟩,⟨(-51938415935140673435650482638),(-51938415935140673261460662522)⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨6662571192882612213745536565,6662571192882612340675033803⟩,⟨(-36499802324151208327634520386),(-36499802324151208200265277103)⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨(-946660380081648013002377820),(-946660380081647925990684117)⟩,⟨(-23294439891131171992992366506),(-23294439891131171905747709410)⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨(-2999404882802227488886041624),(-2999404882802227433712788944)⟩,⟨(-13631373812838253365519923106),(-13631373812838253310250460025)⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨(-2454307644651449696510496042),(-2454307644651449666358033243)⟩,⟨(-6962070351723146812839004962),(-6962070351723146782656553731)⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨(-900482571645913264303803797),(-900482571645913254782719828)⟩,⟨(-2120142842570154985872568707),(-2120142842570154976345202402)⟩⟩
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
noncomputable def ans : CBox := ⟨⟨274014140211337317113140893432,274014140211337317657942979160⟩,⟨87089244485691882239959482876,87089244485691882784054915502⟩⟩
lemma checked : cachedMomentRuleBox column1_1 kernel7_1 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (momentRuleValue quadraturePoint fejerWeight 1 7 true true) := by
  rw [← checked]
  exact cachedMomentRuleBox_contains column1_1_contains kernel7_1_contains
end cm1_7_1_1
namespace cm3_7_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column3_0 j i k).mul (kernel7_0 j i k))
noncomputable def s0_0 : CBox := ⟨⟨(-389701),(-389685)⟩,⟨(-74503),(-74487)⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨(-696504),(-696487)⟩,⟨(-465398),(-465382)⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨(-125938),(-125922)⟩,⟨(-696741),(-696725)⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨324988,325005⟩,⟨(-196059),(-196042)⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨73218,73235⟩,⟨131407,131425⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨(-49119),(-49100)⟩,⟨4526,4542⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨9255,9272⟩,⟨(-11615),(-11597)⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨(-743),(-725)⟩,⟨4488,4507⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨(-237),(-216)⟩,⟨(-1565),(-1544)⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨229,250⟩,⟨599,623⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨(-225),(-205)⟩,⟨(-278),(-256)⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨195,215⟩,⟨66,85⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨(-142),(-126)⟩,⟨78,95⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨(-54),(-35)⟩,⟨(-118),(-101)⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨46,62⟩,⟨(-62),(-44)⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨18,35⟩,⟨(-16),3⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨(-45213062452213),(-45213062452197)⟩,⟨(-26883974185140),(-26883974185124)⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨(-90020154803808),(-90020154803792)⟩,⟨(-67012932749878),(-67012932749862)⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨(-62579422402466),(-62579422402449)⟩,⟨(-71714128737580),(-71714128737562)⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨(-18367529350581),(-18367529350563)⟩,⟨(-45691691533241),(-45691691533223)⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨1573740747331,1573740747349⟩,⟨(-17330125137285),(-17330125137269)⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨2958008226157,2958008226177⟩,⟨(-3391550089459),(-3391550089441)⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨906492596054,906492596070⟩,⟨(-54503781807),(-54503781789)⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨94716842498,94716842514⟩,⟨120533278373,120533278391⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨(-10390322055),(-10390322038)⟩,⟨20957747722,20957747741⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨(-3469224379),(-3469224363)⟩,⟨(-515784765),(-515784747)⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨(-48539054),(-48539037)⟩,⟨(-559424965),(-559424947)⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨98067286,98067302⟩,⟨(-32419910),(-32419893)⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨13827766,13827782⟩,⟨18341154,18341172⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨(-2446741),(-2446722)⟩,⟨5756013,5756030⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨(-1794860),(-1794842)⟩,⟨781448,781465⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨(-470524),(-470508)⟩,⟨5984,6000⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨142711271107927558871,142711271107927559308⟩,⟨(-50634565904028833613),(-50634565904028833167)⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨328333934051400300538,328333934051400301585⟩,⟨(-123323077407555373310),(-123323077407555372254)⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨321882600810144555544,321882600810144556732⟩,⟨(-133093753590427442099),(-133093753590427440899)⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨203927254103900416830,203927254103900417757⟩,⟨(-93864639639967021024),(-93864639639967020098)⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨91846310474000003155,91846310474000003683⟩,⟨(-46088107155743070444),(-46088107155743069916)⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨30734991560591064447,30734991560591064680⟩,⟨(-15847608228285566435),(-15847608228285566205)⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨7830409277585677133,7830409277585677214⟩,⟨(-3672587993148820844),(-3672587993148820761)⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨1505955483308131723,1505955483308131756⟩,⟨(-465865429088762323),(-465865429088762292)⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨189388198456852327,189388198456852345⟩,⟨29004569324060142,29004569324060161⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨(-3448516219977296),(-3448516219977280)⟩,⟨32998264166409051,32998264166409067⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨(-12327023983889563),(-12327023983889546)⟩,⟨9921159741356118,9921159741356135⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨(-5543088723581510),(-5543088723581493)⟩,⟨1791341499414442,1791341499414459⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨(-1974468378198059),(-1974468378198043)⟩,⟨51237065325928,51237065325944⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨(-670231848055741),(-670231848055725)⟩,⟨(-145248653157757),(-145248653157741)⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨(-224891202869564),(-224891202869548)⟩,⟨(-92685275605496),(-92685275605479)⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨(-54377289546610),(-54377289546594)⟩,⟨(-28737742803835),(-28737742803819)⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨191365301131961310581624,191365301131961312184315⟩,⟨1146751173567043270150841,1146751173567043271667979⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨613165967663567636739990,613165967663567640785115⟩,⟨2959414694728023235892926,2959414694728023239712396⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨1048083449361649355019882,1048083449361649360091114⟩,⟨3636301162070688847164576,3636301162070688852011953⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨1319613935180355241502895,1319613935180355246147093⟩,⟨3200118883221563983185409,3200118883221563987718233⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨1286569050356503366147452,1286569050356503369758896⟩,⟨2190984826355299933100992,2190984826355299936699887⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨998042028139204263228913,998042028139204265995822⟩,⟨1200148870133616556667876,1200148870133616559452648⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨631851968877714421183528,631851968877714422972603⟩,⟨531450728787936264137866,531450728787936265940108⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨335627256983260194152073,335627256983260195163532⟩,⟨190147856928851850949244,190147856928851851963422⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨154481432813298012681280,154481432813298013226534⟩,⟨53769824112084789656034,53769824112084790200645⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨63990161165036054969279,63990161165036055223664⟩,⟨10773091280618818467663,10773091280618818722033⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨24894407462405969450833,24894407462405969559039⟩,⟨462473165732541648557,462473165732541757112⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨9505054261967515198730,9505054261967515242806⟩,⟨(-996079357007099976636),(-996079357007099932253)⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨3699609267546609312400,3699609267546609330348⟩,⟨(-748958731361607890943),(-748958731361607872814)⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨1493042585460506199195,1493042585460506206720⟩,⟨(-409564840702740067540),(-409564840702740059944)⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨596601566556667146179,596601566556667149250⟩,⟨(-191503344267648337390),(-191503344267648334295)⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨160951491650449972140,160951491650449972981⟩,⟨(-55330285244504274741),(-55330285244504273892)⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨(-198828428870551092000672196),(-198828428870551091466015005)⟩,⟨194893335961287278627207165,194893335961287279159349783⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨(-524776365951088026617792756),(-524776365951088025102085958)⟩,⟨535408292232981459565251046,535408292232981461090541959⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨(-677490727130252815414155316),(-677490727130252813190378285)⟩,⟨746319888577797422637452761,746319888577797424913911710⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨(-649424632171142341580018969),(-649424632171142339085441183)⟩,⟨796598026371094403037293534,796598026371094405633770025⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨(-508999452322656685899637488),(-508999452322656683624141723)⟩,⟨712061320640145056688678236,712061320640145059082684249⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨(-341617638805254078837346617),(-341617638805254076924133698)⟩,⟨554828359177693710450523901,554828359177693712429238320⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨(-202703036781114269662360116),(-202703036781114268227902012)⟩,⟨387937055870093320256299065,387937055870093321702738330⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨(-108748651079252933617208220),(-108748651079252932740503704)⟩,⟨250001322428200201377051760,250001322428200202251898489⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨(-53178437765545466274678676),(-53178437765545465815069602)⟩,⟨152126119621608454428562029,152126119621608454890710429⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨(-23377061852291348143507237),(-23377061852291347869307357)⟩,⟨89061756048535659920156858,89061756048535660200264117⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨(-8781571188144034984482275),(-8781571188144034814526739)⟩,⟨50793811934624770703054966,50793811934624770875870913⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨(-2380207397620263614643729),(-2380207397620263519392861)⟩,⟨28439075114776709586108777,28439075114776709681609061⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨(-6323751746611636744349),(-6323751746611587401731)⟩,⟨15673057923890205463251984,15673057923890205511872159⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨591485367896410759501681,591485367896410783698133⟩,⟨8400191971592987489564917,8400191971592987512989477⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨500762850665198613360616,500762850665198624219508⟩,⟨4096395841997513323865512,4096395841997513334222360⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨183277654090152277464796,183277654090152280547660⟩,⟨1224224088394006992355924,1224224088394006995270288⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨(-21853358013742303475290218),(-21853358013742301467447120)⟩,⟨(-36894207172153691521011528),(-36894207172153689518562379)⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨(-319842760447592495449790294),(-319842760447592489197343713)⟩,⟨(-503567055035464127054059904),(-503567055035464120803557476)⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨(-1307734918869260499726116292),(-1307734918869260488717127549)⟩,⟨(-1816924304865448219833175334),(-1816924304865448208804039301)⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨(-3169164434075972160957094700),(-3169164434075972144858611151)⟩,⟨(-3693849802624423622263130287),(-3693849802624423606139472953)⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨(-5659660243207189124296306723),(-5659660243207189103357791189)⟩,⟨(-5281813290881484598940144713),(-5281813290881484578020147841)⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨(-8113681633181281743170333180),(-8113681633181281718676041992)⟩,⟨(-5756977292648285988572467209),(-5756977292648285964164355339)⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨(-9741310766865709820825206488),(-9741310766865709793631198351)⟩,⟨(-4874925521151037868548388162),(-4874925521151037841454214618)⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨(-10052388206979729135369294440),(-10052388206979729105934955133)⟩,⟨(-3068683113438647268453651809),(-3068683113438647239054698561)⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨(-9092906484572523225251902941),(-9092906484572523197644168518)⟩,⟨(-1094044470620880874367898112),(-1094044470620880846750799875)⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨(-7337162858914282122372392115),(-7337162858914282099689461207)⟩,⟨432466561974263971213846056,432466561974263993885293414⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨(-5371810039484890016234048565),(-5371810039484889999076945113)⟩,⟨1269671925549798490290170642,1269671925549798507389655463⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨(-3626108958069000298059777196),(-3626108958069000285704029972)⟩,⟨1499550366412101663934469558,1499550366412101676213279673⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨(-2283360861486848428038861645),(-2283360861486848419638667872)⟩,⟨1341828812575973091499519054,1341828812575973099838642160⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨(-1336713156442804337836426705),(-1336713156442804332645890949)⟩,⟨1000680328506954342835866540,1000680328506954347991669877⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨(-686460300181627423250207435),(-686460300181627420492407586)⟩,⟨602435651344740679749840370,602435651344740682493222581⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨(-209972268258374275409236845),(-209972268258374274553483818)⟩,⟨199654687820526639682038839,199654687820526640534101553⟩⟩
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
noncomputable def ans : CBox := ⟨⟨(-11937080664848144278354272055),(-11937080664848144236884717143)⟩,⟨(-2539735172536316454988358812),(-2539735172536316413533465591)⟩⟩
lemma checked : cachedMomentRuleBox column3_0 kernel7_0 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (momentRuleValue quadraturePoint fejerWeight 3 7 false false) := by
  rw [← checked]
  exact cachedMomentRuleBox_contains column3_0_contains kernel7_0_contains
end cm3_7_0_0
namespace cm3_7_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column3_0 j i k).mul (kernel7_1 j i k))
noncomputable def s0_0 : CBox := ⟨⟨2716337,2716357⟩,⟨2016246,2016264⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨3679547,3679575⟩,⟨6147689,6147712⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨(-1502625),(-1502598)⟩,⟨5904140,5904168⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨(-3263299),(-3263267)⟩,⟨446743,446777⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨(-170251),(-170213)⟩,⟨(-1308053),(-1308017)⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨423409,423447⟩,⟨109550,109587⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨(-110691),(-110646)⟩,⟨74168,74214⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨17052,17103⟩,⟨(-37671),(-37617)⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨(-1084),(-1028)⟩,⟨14318,14371⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨(-1236),(-1177)⟩,⟨(-5950),(-5888)⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨1627,1684⟩,⟨2676,2728⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨(-1858),(-1808)⟩,⟨(-886),(-835)⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨1264,1307⟩,⟨(-741),(-698)⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨370,402⟩,⟨1005,1041⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨(-530),(-505)⟩,⟨466,495⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨(-254),(-233)⟩,⟨27,49⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨84743108826101,84743108826118⟩,⟨365442994945671,365442994945689⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨103957626881731,103957626881752⟩,⟨796534548350193,796534548350213⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨(-49986326720248),(-49986326720227)⟩,⟨684385470440688,684385470440709⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨(-137174273838833),(-137174273838813)⟩,⟨331521258181834,331521258181858⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨(-96048623236083),(-96048623236056)⟩,⟨85337035451389,85337035451415⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨(-33489108242450),(-33489108242422)⟩,⟨4205651809737,4205651809768⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨(-5560500683610),(-5560500683578)⟩,⟨(-4135893661219),(-4135893661188)⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨1611017317,1611017351⟩,⟨(-1191292158163),(-1191292158130)⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨164425207898,164425207930⟩,⟨(-85075648462),(-85075648427)⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨20756213394,20756213427⟩,⟨19158386344,19158386377⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨(-2107273036),(-2107273004)⟩,⟨4082642942,4082642971⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨(-837602308),(-837602278)⟩,⟨(-179510091),(-179510059)⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨(-27710161),(-27710131)⟩,⟨(-190568446),(-190568418)⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨40744846,40744874⟩,⟨(-33663884),(-33663856)⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨16604993,16605017⟩,⟨853828,853850⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨3623494,3623511⟩,⟨1709691,1709711⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨(-663730021480418192221),(-663730021480418189033)⟩,⟨(-585566075993627480254),(-585566075993627477059)⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨(-1572774467923960878438),(-1572774467923960870760)⟩,⟨(-1326228560215116901828),(-1326228560215116894129)⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨(-1625502408216275314651),(-1625502408216275305997)⟩,⟨(-1261173900796327421253),(-1261173900796327412560)⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨(-1098825900715496708835),(-1098825900715496702211)⟩,⟨(-766157274985447198449),(-766157274985447191780)⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨(-526349618950218173074),(-526349618950218169382)⟩,⟨(-330001416454351754092),(-330001416454351750372)⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨(-183117177454572377686),(-183117177454572376157)⟩,⟨(-107478065694576102558),(-107478065694576101015)⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨(-46145390866472871135),(-46145390866472870634)⟩,⟨(-28127714688240579095),(-28127714688240578593)⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨(-7909126113307406759),(-7909126113307406624)⟩,⟨(-6179652104582757990),(-6179652104582757854)⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨(-573350778059396623),(-573350778059396585)⟩,⟨(-1104810546805391418),(-1104810546805391380)⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨187501794036957260,187501794036957282⟩,⟨(-116018687708576458),(-116018687708576434)⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨104552088261030493,104552088261030512⟩,⟨22180511215146320,22180511215146342⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨34059341328029331,34059341328029353⟩,⟨20939167586491358,20939167586491383⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨9402296314276401,9402296314276426⟩,⟨10027746737392641,10027746737392666⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨2440994261078195,2440994261078213⟩,⟨4162917804742075,4162917804742095⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨614780123711718,614780123711739⟩,⟨1611436766576900,1611436766576918⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨118983036111591,118983036111607⟩,⟨421314172918545,421314172918561⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨5010000591027544954088986,5010000591027544963062636⟩,⟨(-2627894547289408744586634),(-2627894547289408735276681)⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨12765681989608305129238187,12765681989608305152841211⟩,⟨(-7396200347655734444222134),(-7396200347655734419897920)⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨15263062429399738450689766,15263062429399738480576097⟩,⟨(-10612212230355042432075265),(-10612212230355042401640781)⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨12821635624359939295631221,12821635624359939322615688⟩,⟨(-11406068511926389191236234),(-11406068511926389164174965)⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨8135724891784358639766137,8135724891784358660347177⟩,⟨(-9811571749106434029663218),(-9811571749106434009312540)⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨3915399430469103327882141,3915399430469103343664490⟩,⟨(-6908937611104262374844974),(-6908937611104262359288222)⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨1350262573481070168030591,1350262573481070178751479⟩,⟨(-4048548228467136579330378),(-4048548228467136568704192)⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨244294416348243256507466,244294416348243263367741⟩,⟨(-2013722923317066318811043),(-2013722923317066311957993)⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨(-68235088732460948645898),(-68235088732460944949385)⟩,⟨(-872963476013240984580577),(-872963476013240980884282)⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨(-92484471876703734378080),(-92484471876703732643420)⟩,⟨(-341305534228698069111744),(-341305534228698067381356)⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨(-57635064995048915076797),(-57635064995048914324319)⟩,⟨(-125411137882382575106409),(-125411137882382574358215)⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨(-29058910462155374681580),(-29058910462155374358310)⟩,⟨(-45292435766278934685483),(-45292435766278934364010)⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨(-13551752630234325900811),(-13551752630234325762625)⟩,⟨(-16746262563883671787153),(-16746262563883671649446)⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨(-6153440650191048997263),(-6153440650191048938636)⟩,⟨(-6473182939180085093266),(-6473182939180085034724)⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨(-2640641259589972519388),(-2640641259589972495487)⟩,⟨(-2507792000244979190244),(-2507792000244979166345)⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨(-736728463095145780987),(-736728463095145774505)⟩,⟨(-665752533528924546839),(-665752533528924540353)⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨937310607595260238990493852,937310607595260241436525174⟩,⟨674898453188316107358565498,674898453188316109754096815⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨2571239049667348153276918034,2571239049667348160285911114⟩,⟨1764978002888905502498510583,1764978002888905509305655446⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨3575541116860621729717309223,3575541116860621740178052264⟩,⟨2233831504438872920571699998,2233831504438872930604744346⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨3806625619898351898521692566,3806625619898351910465207322⟩,⟨2070513933129877179266059681,2070513933129877190593969963⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨3395844958354737578011539821,3395844958354737589403847289⟩,⟨1539362849488715926548701564,1539362849488715937401197239⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨2643336000696772189998581900,2643336000696772199890720758⟩,⟨952567535801811779109800057,952567535801811788805584013⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨1848016362273664916315702111,1848016362273664923518561035⟩,⟨497526148827820896225080489,497526148827820903419356511⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨1190851207777081299707079092,1190851207777081304028135402⟩,⟨214502562602708371112097579,214502562602708375450131906⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨723498828606928228322974554,723498828606928230605658194⟩,⟨65295514232674771378995877,65295514232674773645366665⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨421548864608475023909770941,421548864608475025448740752⟩,⟨(-1631770924210242272932507),(-1631770924210240753587864)⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨238251208118706142524122564,238251208118706143472834955⟩,⟨(-24662812521097152510829589),(-24662812521097151566051222)⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨131649570176015398176863724,131649570176015398699835955⟩,⟨(-27170961998838160591987984),(-27170961998838160063322933)⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨71411562991390109007269555,71411562991390109273849500⟩,⟨(-21905711249437448873697490),(-21905711249437448599574127)⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨37662946012482488459408691,37662946012482488588504061⟩,⟨(-14918509596842246909844914),(-14918509596842246774980826)⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨18124357840785480395906541,18124357840785480455533311⟩,⟨(-8414058359203099480912318),(-8414058359203099418574620)⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨5375836776158935476116471,5375836776158935493470583⟩,⟨(-2695366197061567837294809),(-2695366197061567819206360)⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨(-129166912539272848613414338),(-129166912539272841276068349)⟩,⟨85999303692444893702671042,85999303692444901054891881⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨(-1760593375526660080094420511),(-1760593375526660057143533842)⟩,⟨1258792373633443663971498136,1258792373633443686919045481⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨(-6330699735776632124526466764),(-6330699735776632083841348412)⟩,⟨5148542762075321241221186595,5148542762075321281828600723⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨(-12774654331447770855306420310),(-12774654331447770795355431236)⟩,⟨12485512049105907561177559813,12485512049105907621055594537⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨(-17987344546251157018271459596),(-17987344546251156939504278466)⟩,⟨22316858893085807649751152284,22316858893085807728639058676⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨(-18994756856746683319116957894),(-18994756856746683225486503746)⟩,⟨32012838144514896803772959232,32012838144514896897795594802⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨(-14996614343256573923013730150),(-14996614343256573812115943043)⟩,⟨38419410543380937739603188121,38419410543380937850885559692⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨(-7744686360902278854649109637),(-7744686360902278732528478121)⟩,⟨39553945185756633443614263718,39553945185756633565858514389⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨(-188848134858100355923401514),(-188848134858100239443617231)⟩,⟨35588948159395580979364692715,35588948159395581095822723683⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨5318374368060170858307595131,5318374368060170955618278027⟩,⟨28449063597196820282125251355,28449063597196820379529765087⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨7941269043335835582522810174,7941269043335835657644170250⟩,⟨20530909521495599927820367876,20530909521495600003226782856⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨8128888397720339632694798646,8128888397720339688898824124⟩,⟨13585409196630149889076620576,13585409196630149945579831641⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨6846206815282979762310818041,6846206815282979800921122003⟩,⟨8344050874401169581306905710,8344050874401169620130565131⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨4946299039218412023490520637,4946299039218412047581072573⟩,⟨4752423474190357420387656517,4752423474190357444585157244⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨2926754349829947100732375639,2926754349829947113633060099⟩,⟨2380750346705027546391918428,2380750346705027559328724415⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨962396600432809387266519915,962396600432809391286450582⟩,⟨717272946719336515901776086,717272946719336519929030281⟩⟩
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
noncomputable def ans : CBox := ⟨⟨(-3693609673985225332209477137),(-3693609673985225160265891276)⟩,⟨45914427291989569121248806422,45914427291989569293169446181⟩⟩
lemma checked : cachedMomentRuleBox column3_0 kernel7_1 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (momentRuleValue quadraturePoint fejerWeight 3 7 false true) := by
  rw [← checked]
  exact cachedMomentRuleBox_contains column3_0_contains kernel7_1_contains
end cm3_7_0_1
namespace cm3_7_1_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column3_1 j i k).mul (kernel7_0 j i k))
noncomputable def s0_0 : CBox := ⟨⟨(-1921652),(-1921636)⟩,⟨140059,140077⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨(-3867964),(-3867946)⟩,⟨(-1124854),(-1124836)⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨(-1790522),(-1790503)⟩,⟨(-2797799),(-2797782)⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨848487,848509⟩,⟨(-1472238),(-1472217)⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨569545,569567⟩,⟨259201,259224⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨(-121712),(-121686)⟩,⟨140515,140543⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨(-10329),(-10303)⟩,⟨(-48797),(-48772)⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨9863,9891⟩,⟨9231,9259⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨(-3867),(-3842)⟩,⟨(-1497),(-1469)⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨1520,1548⟩,⟨111,132⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨(-713),(-689)⟩,⟨180,204⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨273,296⟩,⟨(-329),(-307)⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨49,71⟩,⟨274,293⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨(-214),(-196)⟩,⟨(-1),19⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨(-62),(-45)⟩,⟨(-127),(-106)⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨0,16⟩,⟨(-52),(-35)⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨(-84095398491818),(-84095398491802)⟩,⟨(-60131574672374),(-60131574672358)⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨(-168153336148768),(-168153336148752)⟩,⟨(-143303636680893),(-143303636680877)⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨(-119268773823496),(-119268773823480)⟩,⟨(-145081900295144),(-145081900295127)⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨(-38428917771458),(-38428917771441)⟩,⟨(-89360721605480),(-89360721605464)⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨(-53819678807),(-53819678791)⟩,⟨(-34275794766267),(-34275794766249)⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨4554351800681,4554351800699⟩,⟨(-7509053620705),(-7509053620687)⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨1653082946497,1653082946515⟩,⟨(-546539296982),(-546539296961)⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨243030716718,243030716738⟩,⟨151032255901,151032255918⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨(-1048305999),(-1048305979)⟩,⟨42154982759,42154982779⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨(-5666348603),(-5666348584)⟩,⟨2181240923,2181240940⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨(-579199038),(-579199019)⟩,⟨(-729207978),(-729207958)⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨93958871,93958888⟩,⟨(-134747046),(-134747027)⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨34204633,34204650⟩,⟨8249158,8249176⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨2918725,2918741⟩,⟨8822596,8822613⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨(-1153411),(-1153395)⟩,⟨2602885,2602903⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨(-487636),(-487620)⟩,⟨469412,469429⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨203033815226659175240,203033815226659176270⟩,⟨438347054534066599635,438347054534066600669⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨507339216726565452365,507339216726565454857⟩,⟨1036593268824468714725,1036593268824468717224⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨579703210039131777138,579703210039131779858⟩,⟨1075259464483322657496,1075259464483322660221⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨451222747508378847207,451222747508378849409⟩,⟨744588201197149547250,744588201197149549454⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨258755607861051765030,258755607861051766467⟩,⟨381178576016731385862,381178576016731387302⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨112949540389169766346,112949540389169767088⟩,⟨152696456672165938174,152696456672165938910⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨38470216201862189232,38470216201862189544⟩,⟨50311322522534496652,50311322522534496965⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨10475188572277739509,10475188572277739626⟩,⟨14334405155719194250,14334405155719194364⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨2328283550786355400,2328283550786355451⟩,⟨3702634191950718707,3702634191950718758⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨423574968281594663,423574968281594691⟩,⟨902863870707686197,902863870707686224⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨58663473211201017,58663473211201042⟩,⟨215167361622741118,215167361622741141⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨2946765959103188,2946765959103209⟩,⟨51854366771911488,51854366771911507⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨(-2209368425533724),(-2209368425533703)⟩,⟨13106795846519263,13106795846519280⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨(-1414978043270909),(-1414978043270889)⟩,⟨3589237796526443,3589237796526462⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨(-628626491929393),(-628626491929377)⟩,⟨1055058972828421,1055058972828438⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨(-172826114626561),(-172826114626545)⟩,⟨239101397151878,239101397151894⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨238623469668421760368088,238623469668421761038531⟩,⟨522599756561183542322134,522599756561183543014246⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨678036507711403941538831,678036507711403943240079⟩,⟨1328488531524459544329647,1328488531524459546090122⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨985209403740648649965239,985209403740648652079573⟩,⟨1580890290294851793524649,1580890290294851795703945⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨1068384920924572925723063,1068384920924572927623194⟩,⟨1318765433514721269703007,1318765433514721271646911⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨920631149859405361386100,920631149859405362774386⟩,⟨829725865232816057037140,829725865232816058444238⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨644387473871118172052789,644387473871118173049187⟩,⟨396375238132952217246891,396375238132952218245199⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨372772177046675661179750,372772177046675661791927⟩,⟨137111529669007568632754,137111529669007569242333⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨182061282746459666989421,182061282746459667361460⟩,⟨26831769062764759809571,26831769062764760180248⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨77214805342202853845169,77214805342202854056276⟩,⟨(-4377863357503217733267),(-4377863357503217522383)⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨29480505447172000170872,29480505447172000275530⟩,⟨(-7419623456393232108047),(-7419623456393232003477)⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨10577946171800141234718,10577946171800141282475⟩,⟨(-4660978202377123931455),(-4660978202377123883798)⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨3736671213716000673376,3736671213716000694323⟩,⟨(-2322266998831810657182),(-2322266998831810636323)⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨1355534851396373743792,1355534851396373752946⟩,⟨(-1066426470290376632384),(-1066426470290376623283)⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨516220776189057773357,516220776189057777397⟩,⟨(-477474788490787369998),(-477474788490787365983)⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨197968058745202997255,197968058745202998968⟩,⟨(-202783114972696042400),(-202783114972696040701)⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨52286430523861215590,52286430523861216073⟩,⟨(-56266674639671938327),(-56266674639671937846)⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨(-654021025901091643218572035),(-654021025901091641994170036)⟩,⟨97695937228271170633901839,97695937228271171856939581⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨(-1773154088627273743901571466),(-1773154088627273740469449973)⟩,⟨336517376947921767677128407,336517376947921771104436639⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨(-2403087628623468435339046797),(-2403087628623468430388246802)⟩,⟨652483212093703050771588346,652483212093703055712615061⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨(-2444837888695291407208615282),(-2444837888695291401725746797)⟩,⟨973605171360203394093877723,973605171360203399561234445⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨(-2020459097116586481717485742),(-2020459097116586476699088973)⟩,⟨1172873189915477668363942139,1172873189915477673362368119⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨(-1384043068127063581227522781),(-1384043068127063577160654843)⟩,⟨1169713732675707346616800549,1169713732675707350666600203⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨(-781564072685822733253211702),(-781564072685822730356570728)⟩,⟨985724947191410151695141321,985724947191410154579901280⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨(-350559213923862184499253625),(-350559213923862182720338718)⟩,⟨715462467024221017509891491,715462467024221019284095723⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨(-108211870542489673987358298),(-108211870542489673028773198)⟩,⟨456244830970328445309211054,456244830970328446267197787⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨(-2917231540610846175427431),(-2917231540610845652777427)⟩,⟨261310676349455742366124256,261310676349455742889534339⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨27964081184852657842420653,27964081184852658157751292⟩,⟨137776393822217858451722271,137776393822217858767988158⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨28399631309898797087093731,28399631309898797265384727⟩,⟨68647699689038553867118915,68647699689038554045881173⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨20592785558038906552604251,20592785558038906647784250⟩,⟨33097854653241135514169745,33097854653241135609593071⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨12766626976458468470283971,12766626976458468518730462⟩,⟨15590888218425742897035631,15590888218425742945640136⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨6725250623319180441514538,6725250623319180463985452⟩,⟨6859286321989089975107172,6859286321989089997671694⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨2078902326825521266438978,2078902326825521272940122⟩,⟨1935386179250777451156842,1935386179250777457689175⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨(-14778342995503827747690044609),(-14778342995503827734354761167)⟩,⟨8704537581602060232641378008,8704537581602060245638266170⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨(-40800131399150093435372214945),(-40800131399150093395538630678)⟩,⟨25662805576015541634590760794,25662805576015541673602959301⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨(-57400205868480359612750908657),(-57400205868480359547620735571)⟩,⟨40915477069409188553130972977,40915477069409188617432594407⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨(-61893697132365331568404215779),(-61893697132365331481465648509)⟩,⟨52621906396278722951107448991,52621906396278723037663706134⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨(-55403762072993472339283917604),(-55403762072993472235578274621)⟩,⟨58862028950561947591550259992,58862028950561947695458644581⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨(-41956613204658772640961828470),(-41956613204658772529772380585)⟩,⟨58639338436718147924806955508,58639338436718148036554732993⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨(-26547819953513155610908697681),(-26547819953513155502776231301)⟩,⟨52578579800310363869797980131,52578579800310363978406873367⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨(-13199295719454989863342913679),(-13199295719454989765890381986)⟩,⟨42757572198068231848307195697,42757572198068231945900097662⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨(-3911184086046714034260704701),(-3911184086046713954911399586)⟩,⟨31795349145069886877028593447,31795349145069886956345390123⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨1240090694458100736707840025,1240090694458100794913641655⟩,⟨21837256880688849242704389348,21837256880688849300923091177⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨3288768872056381017379170602,3288768872056381057635969083⟩,⟨14017003987482194240973290418,14017003987482194281335977654⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨3509357728988619828150863228,3509357728988619854804157534⟩,⟨8514040833254162203898046772,8514040833254162230689859316⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨2897518102851450074242130205,2897518102851450090932682964⟩,⟨4938936228649508907369268317,4938936228649508924170317931⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨2036200516697683405851107387,2036200516697683415598971667⟩,⟨2722161939626788388469447863,2722161939626788398279915654⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨1178802026426182725961787946,1178802026426182730963517298⟩,⟨1343601611682843394310601979,1343601611682843399338554200⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨383156122240127204035684562,383156122240127205561597412⟩,⟨402969404928864572516387355,402969404928864574049176677⟩⟩
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
noncomputable def ans : CBox := ⟨⟨(-52196045145528382780095876377),(-52196045145528382631069611303)⟩,⟨72234204865652978996792756702,72234204865652979145711593580⟩⟩
lemma checked : cachedMomentRuleBox column3_1 kernel7_0 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (momentRuleValue quadraturePoint fejerWeight 3 7 true false) := by
  rw [← checked]
  exact cachedMomentRuleBox_contains column3_1_contains kernel7_0_contains
end cm3_7_1_0
namespace cm3_7_1_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column3_1 j i k).mul (kernel7_1 j i k))
noncomputable def s0_0 : CBox := ⟨⟨15275198,15275225⟩,⟨6046084,6046112⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨25777298,25777347⟩,⟨22856321,22856366⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨4023637,4023708⟩,⟨28291948,28292015⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨(-11813045),(-11812956)⟩,⟨8817360,8817451⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨(-3796716),(-3796605)⟩,⟨(-3957355),(-3957245)⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨1436604,1436720⟩,⟨(-806828),(-806710)⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨(-43962),(-43837)⟩,⟨444860,444986⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨(-64619),(-64494)⟩,⟨(-104351),(-104229)⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨31431,31546⟩,⟨20844,20955⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨(-13773),(-13671)⟩,⟨(-3584),(-3482)⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨6613,6694⟩,⟨(-975),(-894)⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨(-2923),(-2854)⟩,⟨2657,2728⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨(-433),(-368)⟩,⟨(-2686),(-2624)⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨1871,1922⟩,⟨(-49),1⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨457,492⟩,⟨1067,1104⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨(-85),(-64)⟩,⟨390,415⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨105482265891004,105482265891022⟩,⟨729700060354444,729700060354462⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨101034628987608,101034628987628⟩,⟨1578150227006534,1578150227006561⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨(-138263980852684),(-138263980852658)⟩,⟨1346915865602471,1346915865602499⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨(-255155153279649),(-255155153279622)⟩,⟨661092576703423,661092576703454⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨(-172880505815560),(-172880505815526)⟩,⟨184769535393912,184769535393947⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨(-62970177762385),(-62970177762345)⟩,⟨19275816951224,19275816951262⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨(-12334844616842),(-12334844616797)⟩,⟨(-4929193325115),(-4929193325069)⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨(-756958312509),(-756958312464)⟩,⟨(-2090230433339),(-2090230433294)⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨203997253074,203997253123⟩,⟨(-264013979090),(-264013979042)⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨47595752433,47595752482⟩,⟨11159224029,11159224078⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨822780880,822780927⟩,⟨7573278976,7573279022⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨(-1237335743),(-1237335701)⟩,⟨569679463,569679505⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨(-218155971),(-218155935)⟩,⟨(-198509564),(-198509529)⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨12422612,12422641⟩,⟨(-77535005),(-77534975)⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨18623714,18623739⟩,⟨(-15422789),(-15422765)⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨5483549,5483570⟩,⟨(-1773347),(-1773326)⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨1663787671458501521380,1663787671458501529408⟩,⟨(-2281459011923766402185),(-2281459011923766394160)⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨3848559068756934034333,3848559068756934053939⟩,⟨(-5569392171724802442491),(-5569392171724802422896)⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨3817008035135297714511,3817008035135297736067⟩,⟨(-6123633507218590133384),(-6123633507218590111831)⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨2469375554204495273855,2469375554204495291441⟩,⟨(-4571379736790628223949),(-4571379736790628206359)⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨1157335323478790249294,1157335323478790260899⟩,⟨(-2533915491722059235061),(-2533915491722059223454)⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨421290043152237685525,421290043152237691550⟩,⟨(-1087786892342707420772),(-1087786892342707414745)⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨129194251269781291015,129194251269781293552⟩,⟨(-374211858866223283710),(-374211858866223281168)⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨36744412746152633623,36744412746152634536⟩,⟨(-106960259134541411831),(-106960259134541410916)⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨10432662190768935360,10432662190768935683⟩,⟨(-26426868669813912091),(-26426868669813911768)⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨3011793333384940227,3011793333384940362⟩,⟨(-5878280680568555058),(-5878280680568554920)⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨875690082881043989,875690082881044080⟩,⟨(-1223392202695397206),(-1223392202695397115)⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨257417277947440385,257417277947440449⟩,⟨(-246296177933411563),(-246296177933411498)⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨78353197588582350,78353197588582407⟩,⟨(-49125722794176078),(-49125722794176019)⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨25326944352257059,25326944352257103⟩,⟨(-9768008806626219),(-9768008806626177)⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨8501739377451640,8501739377451671⟩,⟨(-1883318143637449),(-1883318143637416)⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨2080735530935806,2080735530935824⟩,⟨(-283760668317330),(-283760668317306)⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨2052985580685302019740410,2052985580685302023861249⟩,⟨(-1897508433037704700061783),(-1897508433037704696028942)⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨5110474535167522289214985,5110474535167522299931069⟩,⟨(-5186078281000751813568212),(-5186078281000751803052464)⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨5800166404294293924226501,5800166404294293937520245⟩,⟨(-7077183618240517208735450),(-7077183618240517195622369)⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨4426380599508839057622552,4426380599508839069322399⟩,⟨(-7155610269848344745646140),(-7155610269848344734026688)⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨2340361196409672205582891,2340361196409672213891002⟩,⟨(-5759711175712004338910104),(-5759711175712004330595440)⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨726688835556587360909526,726688835556587366794572⟩,⟨(-3779588472002422913506556),(-3779588472002422907580259)⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨(-51215569771520496931796),(-51215569771520493192037)⟩,⟨(-2052372615720540146910688),(-2052372615720540143143963)⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨(-237932108673991089986773),(-237932108673991087461553)⟩,⟨(-937972704471044781885823),(-937972704471044779354400)⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨(-187346188611008411592695),(-187346188611008410141895)⟩,⟨(-369171326980522586090914),(-369171326980522584638526)⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨(-103901467947763352871690),(-103901467947763352143057)⟩,⟨(-129017129824566694111083),(-129017129824566693381036)⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨(-48741898322590104836605),(-48741898322590104497404)⟩,⟨(-41590057127663033255766),(-41590057127663032915378)⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨(-21135031372146837442770),(-21135031372146837288110)⟩,⟨(-12920245895559409119896),(-12920245895559408964718)⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨(-8973267125076633718184),(-8973267125076633648255)⟩,⟨(-4045948399896439650301),(-4045948399896439580217)⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨(-3834931114904258273067),(-3834931114904258241810)⟩,⟨(-1322204984200016805734),(-1322204984200016774436)⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨(-1586177594138237046045),(-1586177594138237032770)⟩,⟨(-443751112066818593857),(-443751112066818580574)⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨(-434868722602810791998),(-434868722602810788312)⟩,⟨(-108218738405782428174),(-108218738405782424483)⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨861978145920861488916884170,861978145920861494702518770⟩,⟨2604349949578653805902073064,2604349949578653811701130442⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨2654525976819870932594194453,2654525976819870948865085782⟩,⟨7022946572916161292674074027,7022946572916161308986045486⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨4472429587218614581601636629,4472429587218614605226675777⟩,⟨9406034348862015631378994173,9406034348862015655073360565⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨5939166144012166385565065267,5939166144012166411986206341⟩,⟨9371479871693891104495513605,9371479871693891131009966839⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨6569854828492348944691392287,6569854828492348969419414873⟩,⟨7474244369048726626148292742,7474244369048726650969276882⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨6158729148203204326730682509,6158729148203204347361296715⟩,⟨4808926305406213502369056467,4808926305406213523060041056⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨4948173313915051524192584548,4948173313915051539099458653⟩,⟨2400506193741386216146650777,2400506193741386231091868598⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨3447760000729431391281908123,3447760000729431400585312060⟩,⟨782985575771352330708466258,782985575771352340024480743⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨2113089606289862891129210672,2113089606289862896241018517⟩,⟨(-28691324832979613348386419),(-28691324832979608237969434)⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨1159114421485807556958746092,1159114421485807559883023535⟩,⟨(-295385357835669580714789471),(-295385357835669577796907934)⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨580930748481842987395658495,580930748481842989190056273⟩,⟨(-298516800849755835031909214),(-298516800849755833242543263)⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨272201289034950922921972982,272201289034950923949856496⟩,⟨(-219822033182274585263153568),(-219822033182274584238029756)⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨121951505202760467771691834,121951505202760468327352847⟩,⟨(-140126254565538860940371100),(-140126254565538860386346605)⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨52943977161384710128861871,52943977161384710415080205⟩,⟨(-81197380366830150955655384),(-81197380366830150670483972)⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨21571783280038544660169046,21571783280038544795421561⟩,⟨(-41206883590301285047428580),(-41206883590301284912650732)⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨5796285387951567243313587,5796285387951567282928081⟩,⟨(-12522258556382904593604242),(-12522258556382904554118028)⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨34254775044095117079354779679,34254775044095117128779246470⟩,⟨51743881248723667665227370800,51743881248723667715835842805⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨100998429562001429392771176802,100998429562001429541703628152⟩,⟨142676745802952332329327517799,142676745802952332481083957689⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨161078887360260745829022470921,161078887360260746076367481909⟩,⟨200061309955717135940071989951,200061309955717136190111281364⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨207305936332932053482404884496,207305936332932053819039273220⟩,⟨214151443092192137843285486990,214151443092192138180824636363⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨232094528359908081422520560737,232094528359908081832413460316⟩,⟨188817848818720093424035357717,188817848818720093832607321530⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨231361936344666944997277319517,231361936344666945445683223023⟩,⟨138602094007247947177235679937,138602094007247947623069889807⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨207373513689168959767660078767,207373513689168960214968681800⟩,⟨81858691235209804222409655891,81858691235209804667847147378⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨168252688631056177542572663770,168252688631056177952748542919⟩,⟨33528320325332296039497293506,33528320325332296449173421692⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨124457828858023188711030475853,124457828858023189051262618924⟩,⟨1012186246363067932821490622,1012186246363068273144143658⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨84683710199618262872607213246,84683710199618263127431773033⟩,⟨(-15630876230336643880682664121),(-15630876230336643626020991140)⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨53581601943149198336097169736,53581601943149198516466171984⟩,⟨(-20617709834054583322996234202),(-20617709834054583143170688371)⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨31903881908555119069893040398,31903881908555119192667771390⟩,⟨(-19036410320328298048977221146),(-19036410320328297926767456439)⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨18051101060150728068886379291,18051101060150728146956502374⟩,⟨(-14787193765554489950299761104),(-14787193765554489872633786270)⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨9679190328514990035512580284,9679190328514990081594683580⟩,⟨(-10065758463427754490789276474),(-10065758463427754444914479237)⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨4660055662100827317406401219,4660055662100827341200928469⟩,⟨(-5727025503724757384765155525),(-5727025503724757361046673456)⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨1376567099507235046153058680,1376567099507235053434453796⟩,⟨(-1846935148929465798261563605),(-1846935148929465790997802051)⟩⟩
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
noncomputable def ans : CBox := ⟨⟨285085775776495554129983650437,285085775776495554747509999176⟩,⟨167910031505386290925768457539,167910031505386291543271424721⟩⟩
lemma checked : cachedMomentRuleBox column3_1 kernel7_1 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (momentRuleValue quadraturePoint fejerWeight 3 7 true true) := by
  rw [← checked]
  exact cachedMomentRuleBox_contains column3_1_contains kernel7_1_contains
end cm3_7_1_1
namespace cm4_7_0_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column4_0 j i k).mul (kernel7_0 j i k))
noncomputable def s0_0 : CBox := ⟨⟨(-1662502),(-1662485)⟩,⟨(-14436),(-14417)⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨(-3218038),(-3218021)⟩,⟨(-1317722),(-1317706)⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨(-1160956),(-1160937)⟩,⟨(-2626898),(-2626878)⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨999990,1000013⟩,⟨(-1084379),(-1084358)⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨405552,405572⟩,⟨367873,367896⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨(-148794),(-148772)⟩,⟨70980,71003⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨13998,14020⟩,⟨(-42877),(-42854)⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨2196,2219⟩,⟨12357,12383⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨(-1717),(-1691)⟩,⟨(-3591),(-3565)⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨879,906⟩,⟨1234,1258⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨(-588),(-563)⟩,⟨(-500),(-477)⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨436,461⟩,⟨90,111⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨(-272),(-246)⟩,⟨186,206⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨(-109),(-89)⟩,⟨(-224),(-205)⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨99,116⟩,⟨(-116),(-97)⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨45,61⟩,⟨(-20),0⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨(-267359032183384),(-267359032183367)⟩,⟨(-75241408195159),(-75241408195141)⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨(-551831559658809),(-551831559658791)⟩,⟨(-218212319055248),(-218212319055231)⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨(-419775951902010),(-419775951901993)⟩,⟨(-279461012262475),(-279461012262454)⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨(-158507167454190),(-158507167454170)⟩,⟨(-207573316342401),(-207573316342379)⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨(-16888408645623),(-16888408645601)⟩,⟨(-90527614834168),(-90527614834147)⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨10006136427149,10006136427169⟩,⟨(-21417531590689),(-21417531590670)⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨4427789910256,4427789910278⟩,⟨(-1585686920785),(-1585686920764)⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨632246259261,632246259286⟩,⟨452006749923,452006749947⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨(-20766200023),(-20766199996)⟩,⟨113524459095,113524459120⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨(-16652915300),(-16652915278)⟩,⟨2030449146,2030449170⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨(-867557962),(-867557938)⟩,⟨(-2452702645),(-2452702624)⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨394974388,394974409⟩,⟨(-244272682),(-244272662)⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨76334651,76334672⟩,⟨65594411,65594429⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨(-5461756),(-5461736)⟩,⟨26298169,26298186⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨(-6870516),(-6870498)⟩,⟨4644401,4644420⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨(-1944465),(-1944449)⟩,⟨372701,372717⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨168564747902444172229,168564747902444173143⟩,⟨313723037413293846485,313723037413293847398⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨399151948877800611756,399151948877800613947⟩,⟨754200613406630048348,754200613406630050535⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨413412225445466122568,413412225445466124960⟩,⟨809787002766419851430,809787002766419853816⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨282003428986718832028,282003428986718834094⟩,⟨591845285218357033748,591845285218357035813⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨137160745228856121392,137160745228856122777⟩,⟨325521800604155624777,325521800604155626164⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨48024656532645392782,48024656532645393497⟩,⟨141454099460384635763,141454099460384636476⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨11362913188028625799,11362913188028626092⟩,⟨50214565976572994400,50214565976572994693⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨1160434081555373765,1160434081555373871⟩,⟨14968836995350649022,14968836995350649128⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨(-436305845475554410),(-436305845475554370)⟩,⟨3840579129924670431,3840579129924670474⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨(-315796929949245510),(-315796929949245485)⟩,⟨867112680345121030,867112680345121053⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨(-126218315812253197),(-126218315812253177)⟩,⟨175189449088501450,175189449088501475⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨(-41804716085612496),(-41804716085612473)⟩,⟨31654517204552254,31654517204552274⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨(-13067593658084066),(-13067593658084042)⟩,⟨4784839988470202,4784839988470224⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨(-4142454845030025),(-4142454845030007)⟩,⟨358248697165527,358248697165550⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨(-1341782578591592),(-1341782578591574)⟩,⟨(-153063157442006),(-153063157441990)⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨(-319783318268118),(-319783318268101)⟩,⟨(-71944651355265),(-71944651355247)⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨(-1312344601247183870388489),(-1312344601247183866498471)⟩,⟨1825125573349037147114279,1825125573349037151039665⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨(-3299199497404840385062680),(-3299199497404840375234620)⟩,⟨4848093186029170825324642,4848093186029170835262774⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨(-3843911488719381510617257),(-3843911488719381498053709)⟩,⟨6316077192927469709170701,6316077192927469721880115⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨(-3111619700502930452776269),(-3111619700502930441108816)⟩,⟨6082415964771810029319065,6082415964771810041095027⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨(-1880052647760977853058108),(-1880052647760977844560126)⟩,⟨4720213267864918442423671,4720213267864918450949016⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨(-844136011075097671981078),(-844136011075097666172601)⟩,⟨3055717748566483106109050,3055717748566483111889119⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨(-254730527894980098841182),(-254730527894980095391501)⟩,⟨1687053294499762946448415,1687053294499762949869776⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨(-21581665661724670321164),(-21581665661724668518218)⟩,⟨811681873833413477106321,811681873833413478900135⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨32665728379282645113914,32665728379282646196753⟩,⟨349281853268549670910343,349281853268549671993531⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨28553702084622841294515,28553702084622841846840⟩,⟨138817718112483823028029,138817718112483823580779⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨16170231861492366586660,16170231861492366838153⟩,⟨52892925775956076996754,52892925775956077248113⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨7819539285647973905927,7819539285647974013720⟩,⟨20083785914691347477919,20083785914691347585515⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨3560944822010928418515,3560944822010928464016⟩,⟨7850977783407883713883,7850977783407883759262⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨1591494456275356879215,1591494456275356898682⟩,⟨3196619991623518521237,3196619991623518540653⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨675679789546181461159,675679789546181469160⟩,⟨1288563770714592857301,1288563770714592865287⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨187451354758352619817,187451354758352622002⟩,⟨349460900581154238361,349460900581154240538⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨(-270999512454293134816037792),(-270999512454293133850031773)⟩,⟨68001658724024591629625292,68001658724024592594721107⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨(-740942309007627698247011021),(-740942309007627695550243192)⟩,⟨183535151029225935687985801,183535151029225938385204089⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨(-1028708188376667896569275181),(-1028708188376667892742756235)⟩,⟨249230787289903877682846595,249230787289903881514056588⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨(-1103898199458359069782216103),(-1103898199458359065728967411)⟩,⟨262035765261366241020000411,262035765261366245074945117⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨(-1008515891738953996109986094),(-1008515891738953992740036133)⟩,⟨240173617060242079828259805,240173617060242083183205514⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨(-817252005967211072024136020),(-817252005967211069465478986)⟩,⟨205759935096638933373056088,205759935096638935904411885⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨(-599870878009485723956211636),(-599870878009485721846489974)⟩,⟨171277404227615852677947693,171277404227615854771717870⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨(-403438969084448253012196155),(-403438969084448251504937477)⟩,⟨138961872845864972637109946,138961872845864974146033240⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨(-250637457827368671377549249),(-250637457827368670444371361)⟩,⟨107853975597875638275434242,107853975597875639215955817⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨(-145181803492103531337309461),(-145181803492103530808506761)⟩,⟨78726569799365878642025720,78726569799365879174348836⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨(-79433957966047688805080223),(-79433957966047688505475585)⟩,⟨53818465978892868410123442,53818465978892868709492425⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨(-41718946316117027770520830),(-41718946316117027609009206)⟩,⟨34676422905803482782417384,34676422905803482943389518⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨(-21346584430025374428862165),(-21346584430025374335733714)⟩,⟨21225523902032847662951209,21225523902032847755949590⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨(-10651033376732711653920170),(-10651033376732711604312293)⟩,⟨12263580299862173723593122,12263580299862173773230863⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨(-4908524660679556042230878),(-4908524660679556018723656)⟩,⟨6279981140066195027598802,6279981140066195051154973⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨(-1421746921558683627895082),(-1421746921558683621036555)⟩,⟨1922808889590429034681237,1922808889590429041559478⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨(-21730209386207884964206049),(-21730209386207884931207623)⟩,⟨(-36967042515433847758327053),(-36967042515433847724354387)⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨(-312843231640108799232305028),(-312843231640108798735134986)⟩,⟨(-507973366517252874132240230),(-507973366517252873623921631)⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨(-1246688850870045897332110841),(-1246688850870045895199820806)⟩,⟨(-1859656445069421567446619037),(-1859656445069421565288267101)⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨(-2937277167038459829745606617),(-2937277167038459824262110476)⟩,⟨(-3882142828274632604371749508),(-3882142828274632598873913478)⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨(-5122526991152624189033750801),(-5122526991152624178448605471)⟩,⟨(-5807751820043859796400197746),(-5807751820043859785850457686)⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨(-7239722126851969555784613521),(-7239722126851969539489392958)⟩,⟨(-6830252434999535089669337186),(-6830252434999535073446974859)⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨(-8676548156363611213879214699),(-8676548156363611193049151662)⟩,⟨(-6596150407579757410677828301),(-6596150407579757389872422442)⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨(-9063063281253700945756744333),(-9063063281253700922739819718)⟩,⟨(-5335513962870821715426036500),(-5335513962870821692345118574)⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨(-8418075196976273924627475407),(-8418075196976273902963731694)⟩,⟨(-3622644485660321398506595461),(-3622644485660321376786701645)⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨(-7072615763295817190172300646),(-7072615763295817172761263249)⟩,⟨(-2016568538147416029502806184),(-2016568538147416012125725367)⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨(-5459385199017528740318791321),(-5459385199017528727615487844)⟩,⟨(-834745250186509303980965894),(-834745250186509291397646667)⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨(-3923323524552257371221775666),(-3923323524552257360670977802)⟩,⟨(-134547026686880554676424543),(-134547026686880544232993196)⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨(-2642996656036470489888986991),(-2642996656036470481520600555)⟩,⟨181556563628359497137040437,181556563628359505449960511⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨(-1650972103350577437813453436),(-1650972103350577432002697328)⟩,⟨251754941711697540562920715,251754941711697546351703099⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨(-893448919848024577011638843),(-893448919848024573667135021)⟩,⟨189767490768327802688521951,189767490768327806026276124⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨(-281498361062673669134993383),(-281498361062673668053888200)⟩,⟨68631195918731401869524332,68631195918731402949197113⟩⟩
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
noncomputable def ans : CBox := ⟨⟨(-11917686106541926966222369562),(-11917686106541926935713893119)⟩,⟨(-5817922791639198605628763719),(-5817922791639198575178191984)⟩⟩
lemma checked : cachedMomentRuleBox column4_0 kernel7_0 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (momentRuleValue quadraturePoint fejerWeight 4 7 false false) := by
  rw [← checked]
  exact cachedMomentRuleBox_contains column4_0_contains kernel7_0_contains
end cm4_7_0_0
namespace cm4_7_0_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column4_0 j i k).mul (kernel7_1 j i k))
noncomputable def s0_0 : CBox := ⟨⟨12712713,12712740⟩,⟨6272054,6272078⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨20048317,20048362⟩,⟨21968428,21968473⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨(-294462),(-294400)⟩,⟨24708687,24708749⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨(-11691419),(-11691339)⟩,⟨5207474,5207555⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨(-2109286),(-2109188)⟩,⟨(-4311798),(-4311699)⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨1454389,1454490⟩,⟨(-145455),(-145356)⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨(-236039),(-235943)⟩,⟨328533,328634⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨9941,10041⟩,⟨(-113574),(-113477)⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨8053,8165⟩,⟨35315,35424⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨(-6179),(-6058)⟩,⟨(-12796),(-12676)⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨4643,4753⟩,⟨5112,5215⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨(-4113),(-4019)⟩,⟨(-1339),(-1247)⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨2456,2528⟩,⟨(-1716),(-1641)⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨828,885⟩,⟨1983,2037⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨(-1021),(-980)⟩,⟨944,982⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨(-490),(-468)⟩,⟨62,89⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨932171613924996,932171613925019⟩,⟨1747729376611210,1747729376611233⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨1627194690805337,1627194690805377⟩,⟨3923506913690522,3923506913690560⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨697531270702366,697531270702419⟩,⟨3568214288260137,3568214288260187⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨(-232274031757854),(-232274031757796)⟩,⟨1888548691934061,1888548691934118⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨(-366560661223363),(-366560661223298)⟩,⟨572654577359541,572654577359604⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨(-162945569132732),(-162945569132658)⟩,⟨69869647246125,69869647246200⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨(-33642107786965),(-33642107786876)⟩,⟨(-12498839273310),(-12498839273221)⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨(-1684630611271),(-1684630611168)⟩,⟨(-5799883137145),(-5799883137044)⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨664072244076,664072244184⟩,⟨(-627056866131),(-627056866024)⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨120050261304,120050261406⟩,⟨61975961685,61975961786⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨(-4710763537),(-4710763450)⟩,⟨20758346627,20758346717⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨(-3850557897),(-3850557821)⟩,⟨90090589,90090662⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨(-296661905),(-296661840)⟩,⟨(-789932182),(-789932117)⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨143275538,143275595⟩,⟨(-176038194),(-176038138)⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨69821271,69821311⟩,⟨(-9299218),(-9299171)⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨16272703,16272728⟩,⟨4402478,4402502⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨1124780225520276704935,1124780225520276711883⟩,⟨(-1751662800660174169560),(-1751662800660174162618)⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨2714132667183149739688,2714132667183149756451⟩,⟨(-4205835062925552989427),(-4205835062925552972686)⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨2942876995883131508854,2942876995883131527100⟩,⟨(-4493092419555421900324),(-4493092419555421882112)⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨2194848459393224276117,2194848459393224292017⟩,⟨(-3239304038435148178202),(-3239304038435148162329)⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨1251890715789731361339,1251890715789731372119⟩,⟨(-1731010476248806264599),(-1731010476248806253833)⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨576469102829056416404,576469102829056422017⟩,⟨(-714043732409950330905),(-714043732409950325300)⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨222421937312026915770,222421937312026918079⟩,⟨(-232702299402383672212),(-232702299402383669901)⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨74021976230515861359,74021976230515862143⟩,⟨(-60606063848623122832),(-60606063848623122050)⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨21792538258902051787,21792538258902052037⟩,⟨(-12484857250906050531),(-12484857250906050282)⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨5823309045279773350,5823309045279773458⟩,⟨(-1860956656187583179),(-1860956656187583074)⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨1454407214438383905,1454407214438383990⟩,⟨(-85904757414075352),(-85904757414075269)⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨351378374156167583,351378374156167651⟩,⟨77167367492864664,77167367492864735⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨85313405416888862,85313405416888927⟩,⟨45812506925268724,45812506925268786⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨21587164998255469,21587164998255523⟩,⟨19747440974301860,19747440974301911⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨5731960685515177,5731960685515214⟩,⟨7670467868805468,7670467868805506⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨1199791923908818,1199791923908843⟩,⟨2001018035906077,2001018035906101⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨10431779856778639754436063,10431779856778639777169268⟩,⟨3291822330294043529240139,3291822330294043551826928⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨27537922236966036982803598,27537922236966037043058766⟩,⟨7820791120512124461077351,7820791120512124520957122⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨35447795692122384496212165,35447795692122384573127988⟩,⟨7919169972662962255806890,7919169972662962332330407⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨33555186030343061842528013,33555186030343061911823721⟩,⟨4625210313712333650358699,4625210313712333719522379⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨25477052926627769877341061,25477052926627769926110293⟩,⟨803716159485840234925888,803716159485840283926115⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨16061892746692412268831568,16061892746692412301760464⟩,⟨(-1480601568528050146687728),(-1480601568528050113380973)⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨8593090878235342098371399,8593090878235342118499598⟩,⟨(-1989116424107095910055405),(-1989116424107095889732930)⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨3984256835120174225987258,3984256835120174238103224⟩,⟨(-1536600092759989095655809),(-1536600092759989083522105)⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨1642654134440216281973705,1642654134440216289274668⟩,⟨(-910551487932790569834485),(-910551487932790562539903)⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨622187409395693070847766,622187409395693074589277⟩,⟨(-457680234329648050632202),(-457680234329648046891290)⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨225186850212343876395831,225186850212343878130724⟩,⟨(-208110164512844412626163),(-208110164512844410889195)⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨81250894176070654405519,81250894176070655190290⟩,⟨(-90151102391590590238041),(-90151102391590589452172)⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨30337708449529965532271,30337708449529965879946⟩,⟨(-38736947576178160553502),(-38736947576178160205548)⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨11911012778271013078782,11911012778271013229638⟩,⟨(-16807688852365028617696),(-16807688852365028466810)⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨4685497089427983611788,4685497089427983674051⟩,⟨(-7039634481893184601122),(-7039634481893184538874)⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨1255535031584592089605,1255535031584592106566⟩,⟨(-1943351353368585947670),(-1943351353368585930717)⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨469662796261536229140382387,469662796261536233416985694⟩,⟨1059672772699959293525978098,1059672772699959297796595057⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨1285038046481683803900405503,1285038046481683815837177455⟩,⟨2903867717984506441661778640,2903867717984506453574281418⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨1790606899702332573951664634,1790606899702332590864495496⟩,⟨4049210236870347255749327108,4049210236870347272623776848⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨1945730369048597901032927180,1945730369048597918858656578⟩,⟨4370450138046370058010492193,4370450138046370075827518041⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨1836413479727672493186072667,1836413479727672508692071611⟩,⟨4016851596590146989349496257,4016851596590147004922792506⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨1589833746855983995147713395,1589833746855984007794455141⟩,⟨3268625310998462178134710071,3268625310998462190872531812⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨1300035564016050039189266481,1300035564016050049539602252⟩,⟨2398432866541674617679580432,2398432866541674628060917985⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨1012344566979399014444473009,1012344566979399021935016621⟩,⟨1600814301682144216968256892,1600814301682144224419937736⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨747107169832254283366950727,747107169832254288099866676⟩,⟨977198518786864566348102025,977198518786864571034714068⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨519552337789268491764264606,519552337789268494695142616⟩,⟨549364466955818926801091997,549364466955818929721539247⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨340740513892895084165140931,340740513892895085800307772⟩,⟨287542028700071425974772988,287542028700071427612782391⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨212290414906855792237660526,212290414906855793101619211⟩,⟨142223262017749605895330039,142223262017749606761606226⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨126573949355797701711458994,126573949355797702210297220⟩,⟨67543795097232465217256110,67543795097232465716302541⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨71716269885461895789072567,71716269885461896056855184⟩,⟨31024645153130027704280923,31024645153130027971641202⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨36248059678016962794458400,36248059678016962927687329⟩,⟨13249549908523651398615219,13249549908523651531525326⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨11025728447972773820727680,11025728447972773860983719⟩,⟨3660420811612808249958305,3660420811612808290112526⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨(-129453641474625084952488634),(-129453641474625084823622862)⟩,⟨85568119800369245402188170,85568119800369245527741952⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨(-1777958393170022286407178216),(-1777958393170022284470945605)⟩,⟨1234309574230238601438800657,1234309574230238603338070544⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨(-6499414906741879326878801098),(-6499414906741879318593438571)⟩,⟨4935555272574767287362791061,4935555272574767295568952042⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨(-13519919290270520771120709715),(-13519919290270520749776768431)⟩,⟨11680952589043566233384157270,11680952589043566254714390304⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨(-20074829974732159538125355948),(-20074829974732159496569038399)⟩,⟨20474250408787299467998381023,20474250408787299509745214392⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨(-23265780889436468926442470001),(-23265780889436468861422364623)⟩,⟨29081027152394047309105779661,29081027152394047374451307534⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨(-21858445783702542627013799108),(-21858445783702542541297055621)⟩,⟨35003197728530417551941855552,35003197728530417637753613329⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨(-16784187051682921966097350154),(-16784187051682921869154415400)⟩,⟨36674177073611471589478537833,36674177073611471686203762343⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨(-10252479807969562719436861949),(-10252479807969562626483000297)⟩,⟨34106847947709855852799440579,34106847947709855945622289640⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨(-4381461956044655688678923865),(-4381461956044655612944564401)⟩,⟨28627980708227990066857111128,28627980708227990142855897206⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨(-325943374170437205211495915),(-325943374170437149264276240)⟩,⟨22023716649450449892118832853,22023716649450449948657650962⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨1782317129549243593772242649,1782317129549243641676691245⟩,⟨15738393316123268687628611366,15738393316123268735946575008⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨2402263362386989828027598826,2402263362386989866687975812⟩,⟨10526007560943852999398359991,10526007560943853038250527471⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨2119547711580035319282359435,2119547711580035346497430879⟩,⟨6525004099992858070038690735,6525004099992858097320068680⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨1388613081189338333799245781,1388613081189338349610365354⟩,⟨3508213156118247229628904136,3508213156118247245456014929⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨477607714309590682592212304,477607714309590687726692422⟩,⟨1101181644842013900749414816,1101181644842013905886381841⟩⟩
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
noncomputable def ans : CBox := ⟨⟨(-16206814430049059077543708288),(-16206814430049058946094144252)⟩,⟨47847303593316784722458158606,47847303593316784854190372356⟩⟩
lemma checked : cachedMomentRuleBox column4_0 kernel7_1 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (momentRuleValue quadraturePoint fejerWeight 4 7 false true) := by
  rw [← checked]
  exact cachedMomentRuleBox_contains column4_0_contains kernel7_1_contains
end cm4_7_0_1
namespace cm4_7_1_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column4_1 j i k).mul (kernel7_0 j i k))
noncomputable def s0_0 : CBox := ⟨⟨(-2605749),(-2605731)⟩,⟨321491,321508⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨(-5325269),(-5325249)⟩,⟨(-1316719),(-1316699)⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨(-2519052),(-2519033)⟩,⟨(-3750674),(-3750652)⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨1161815,1161840⟩,⟨(-1993595),(-1993569)⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨757431,757457⟩,⟨381398,381429⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨(-179325),(-179299)⟩,⟨176188,176216⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨(-5510),(-5482)⟩,⟨(-67076),(-67045)⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨10897,10926⟩,⟨14583,14612⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨(-4616),(-4587)⟩,⟨(-3130),(-3103)⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨1924,1951⟩,⟨714,740⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨(-990),(-964)⟩,⟨(-75),(-45)⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨502,527⟩,⟨(-271),(-246)⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨(-92),(-68)⟩,⟨374,396⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨(-267),(-247)⟩,⟨(-118),(-98)⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨(-3),15⟩,⟨(-185),(-164)⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨29,45⟩,⟨(-56),(-40)⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨(-221232613460073),(-221232613460057)⟩,⟨(-61778577038103),(-61778577038086)⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨(-458156791813672),(-458156791813653)⟩,⟨(-175995217286396),(-175995217286375)⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨(-352887034894511),(-352887034894492)⟩,⟨(-222342015780860),(-222342015780842)⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨(-139038989601338),(-139038989601316)⟩,⟨(-165198969786950),(-165198969786931)⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨(-19581853839432),(-19581853839411)⟩,⟨(-73473827929304),(-73473827929281)⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨6259404487330,6259404487350⟩,⟨(-18435792502801),(-18435792502779)⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨3401029114764,3401029114788⟩,⟨(-1819309790372),(-1819309790349)⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨574868397505,574868397527⟩,⟨266081759263,266081759284⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨4363197178,4363197201⟩,⟨93202638354,93202638377⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨(-12430215104),(-12430215082)⟩,⟨5088174970,5088174994⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨(-1237043486),(-1237043462)⟩,⟨(-1647536686),(-1647536665)⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨228677117,228677140⟩,⟨(-282720151),(-282720130)⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨73346721,73346739⟩,⟨26413356,26413374⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨3701946,3701964⟩,⟨20277573,20277592⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨(-3446847),(-3446828)⟩,⟨5298970,5298986⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨(-1244305),(-1244289)⟩,⟨844412,844429⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨406491154244531355564,406491154244531357187⟩,⟨544767389519974831723,544767389519974833353⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨986410769008623234290,986410769008623238239⟩,⟨1289941603497797178886,1289941603497797182849⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨1071818791596656003219,1071818791596656007549⟩,⟨1343801409181707393559,1343801409181707397905⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨785671294223749168186,785671294223749171375⟩,⟨940030644897890827898,940030644897890831096⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨423890524307178290300,423890524307178292141⟩,⟨490497276892571890433,490497276892571892279⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨174556548940995589426,174556548940995590414⟩,⟨202358207292828758161,202358207292828759148⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨56125537024303666452,56125537024303666878⟩,⟨69204056857789164835,69204056857789165262⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨14310908799188093428,14310908799188093588⟩,⟨20465907921100386626,20465907921100386783⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨2892930912472760300,2892930912472760363⟩,⟨5428343770402876670,5428343770402876733⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨436658141175813131,436658141175813165⟩,⟨1332566630540270537,1332566630540270571⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨30156302696733647,30156302696733671⟩,⟨312107363749218402,312107363749218429⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨(-11386442581727896),(-11386442581727876)⟩,⟨72131305454270652,72131305454270674⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨(-7581317831512231),(-7581317831512210)⟩,⟨17083888903472590,17083888903472610⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨(-3308793154474018),(-3308793154473997)⟩,⟨4300790039444041,4300790039444062⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨(-1284354739115169),(-1284354739115152)⟩,⟨1155635788721109,1155635788721131⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨(-334510668589997),(-334510668589981)⟩,⟨245775101377219,245775101377235⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨(-209242692676991858124994),(-209242692676991856065127)⟩,⟨2133851123085728175628325,2133851123085728177688524⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨(-355519915718631929985803),(-355519915718631924626383)⟩,⟨5555449825888402426877410,5555449825888402432240548⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨16324022038281070557138,16324022038281077552227⟩,⟨6953201965380183889321245,6953201965380183896330184⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨620793173041595844206191,620793173041595850840556⟩,⟨6305832018783481902409289,6305832018783481909066901⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨1005676445668129577488278,1005676445668129582588762⟩,⟨4517057395769391871940720,4517057395769391877061682⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨993435476847887480270954,993435476847887484285617⟩,⟨2644803460993155195091478,2644803460993155199115623⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨726379441075908196508675,726379441075908199244486⟩,⟨1293382605585161022928711,1293382605585161025669186⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨425824906305331197216667,425824906305331198783253⟩,⟨539511646472152424719459,539511646472152426288493⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨211225590858530754507548,211225590858530755300232⟩,⟨197001802860637746352464,197001802860637747146439⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨92992857457578978543184,92992857457578978887017⟩,⟨65113029862215245831158,65113029862215246175690⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨38082475339765544330091,38082475339765544465590⟩,⟨20311144621743413681474,20311144621743413817196⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨15178464268181721008741,15178464268181721070595⟩,⟨6275503867023682760835,6275503867023682822754⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨6114510355965104475757,6114510355965104505397⟩,⟨2015501732725459942787,2015501732725459972454⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨2531077173728113024174,2531077173728113038098⟩,⟨694306585374910632575,694306585374910646506⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨1028135141552200383849,1028135141552200389959⟩,⟨248241274445997167484,248241274445997173595⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨279588336343023021991,279588336343023023718⟩,⟨63282988974934035727,63282988974934037457⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨(-894524036130383419815431425),(-894524036130383418077846145)⟩,⟨232322684715650216558070760,232322684715650218292465851⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨(-2421809509745085614032466232),(-2421809509745085609145864562)⟩,⟨705713870432836194629629098,705713870432836199510576902⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨(-3279335812066825370910452202),(-3279335812066825363829605126)⟩,⟨1166786503386497845580218895,1166786503386497852659232539⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨(-3347668096506270193902604502),(-3347668096506270186042963016)⟩,⟨1525837965992429485306517704,1525837965992429493167102899⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨(-2803598694411208775768755218),(-2803598694411208768605717557)⟩,⟨1676475286217746677380898344,1676475286217746684538176200⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨(-1982287602644255919091130492),(-1982287602644255913346682496)⟩,⟨1578819725058391764364893587,1578819725058391770092184110⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨(-1194534356139618431563406208),(-1194534356139618427570702871)⟩,⟨1291794050837731546273682696,1291794050837731550246834252⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨(-611983810857585385358089276),(-611983810857585383028793430)⟩,⟨931341134615081890155853766,931341134615081892478472031⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨(-261199081971901814485791651),(-261199081971901813121847933)⟩,⟨601623007517780529798452484,601623007517780531165524620⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨(-86192538587219867300658494),(-86192538587219866445266544)⟩,⟨355203587621030967610766509,355203587621030968469935613⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨(-14552215296022526398327147),(-14552215296022525892383387)⟩,⟨196072514290436982368268399,196072514290436982875698488⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨7790909045199584503454756,7790909045199584781759545⟩,⟨103588155955341965051579245,103588155955341965330133511⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨10975745448140786320936018,10975745448140786464841795⟩,⟨53381931705045799792520604,53381931705045799936416933⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨8418216723030901499477340,8418216723030901570453174⟩,⟨26880901501587539961068815,26880901501587540032048927⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨4892311234484714709069441,4892311234484714741158247⟩,⟨12503425095318431896814272,12503425095318431928923673⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨1576481955729109830731671,1576481955729109839882949⟩,⟨3643206233087380473092706,3643206233087380482253889⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨(-14800134802001044989775612149),(-14800134802001044976411463518)⟩,⟨8667606918266091664924641849,8667606918266091677950222162⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨(-41116479937924688182994495622),(-41116479937924688142725864091)⟩,⟨25157026602335566086042592726,25157026602335566125498409824⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨(-58677541823308254464195142308),(-58677541823308254397418556829)⟩,⟨39077010606262413128694024737,39077010606262413194672044378⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨(-64947907281547828610858594984),(-64947907281547828520435167218)⟩,⟨48832700061615094093841616859,48832700061615094183915618226⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨(-60799186837746392736709287856),(-60799186837746392627864558016)⟩,⟨53312853016705686688658546977,53312853016705686797670043429⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨(-49645911691252820955271707252),(-49645911691252820838712095346)⟩,⟨52335534190017811727344770589,52335534190017811844263410005⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨(-35783650155141791766741447004),(-35783650155141791655064667978)⟩,⟨46826512159019740877281027233,46826512159019740989066457216⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨(-22801830134081845659917207783),(-22801830134081845562268651815)⟩,⟨38536059701521531235704262234,38536059701521531333130135988⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨(-12727354327381433018737890885),(-12727354327381432943103259029)⟩,⟨29420958726941680573102031701,29420958726941680648545159083⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨(-6033764919954170699442148919),(-6033764919954170647844214966)⟩,⟨21037885816284852696504039747,21037885816284852748134762076⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨(-2194378906110103092421624282),(-2194378906110103059637433594)⟩,⟨14237375152092577491851636779,14237375152092577524840165149⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨(-323632108891384260751139590),(-323632108891384236301945149)⟩,⟨9207202632208303728552063855,9207202632208303753183976840⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨389430568123544560641177540,389430568123544578568046443⟩,⟨5714580487639899166427230340,5714580487639899184450814178⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨511570453093278268293181286,511570453093278280047795820⟩,⟨3361310732489021295469037464,3361310732489021307262317910⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨371197176962316149243226770,371197176962316155758710470⟩,⟨1748559074680646071636378907,1748559074680646078163956412⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨131705477114560560902492513,131705477114560562969300461⟩,⟨540232466220961893604365722,540232466220961895673826319⟩⟩
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
noncomputable def ans : CBox := ⟨⟨(-64218051052305356758980047929),(-64218051052305356606916392687)⟩,⟨68084272669427889495926466365,68084272669427889647730241971⟩⟩
lemma checked : cachedMomentRuleBox column4_1 kernel7_0 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (momentRuleValue quadraturePoint fejerWeight 4 7 true false) := by
  rw [← checked]
  exact cachedMomentRuleBox_contains column4_1_contains kernel7_0_contains
end cm4_7_1_0
namespace cm4_7_1_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (column4_1 j i k).mul (kernel7_1 j i k))
noncomputable def s0_0 : CBox := ⟨⟨21200725,21200754⟩,⟨7188179,7188213⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨36338825,36338886⟩,⟨29675711,29675769⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨6322826,6322913⟩,⟨38353115,38353203⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨(-16100280),(-16100165)⟩,⟨11895993,11896109⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨(-4930399),(-4930253)⟩,⟨(-5562416),(-5562273)⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨2024473,2024626⟩,⟨(-931408),(-931256)⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨(-134760),(-134596)⟩,⟨588116,588280⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨(-61012),(-60862)⟩,⟨(-153677),(-153528)⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨34840,34973⟩,⟨36925,37055⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨(-16497),(-16375)⟩,⟨(-9734),(-9613)⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨8835,8956⟩,⟨1646,1765⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨(-5014),(-4907)⟩,⟨1909,2019⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨889,982⟩,⟨(-3560),(-3469)⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨2313,2382⟩,⟨1028,1101⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨(-102),(-51)⟩,⟨1588,1635⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨(-352),(-323)⟩,⟨431,458⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨773827766881393,773827766881416⟩,⟨1443820959756658,1443820959756679⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨1377581283915724,1377581283915757⟩,⟨3231667332879612,3231667332879645⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨650906564897399,650906564897445⟩,⟨2935707802515709,2935707802515752⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨(-117691680723061),(-117691680723008)⟩,⟨1568633663869780,1568633663869834⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨(-265848090160392),(-265848090160331)⟩,⟨494444532799734,494444532799791⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨(-127077227588284),(-127077227588220)⟩,⟨71896670161726,71896670161785⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨(-28793154867145),(-28793154867073)⟩,⟨(-6087692104975),(-6087692104902)⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨(-2228751525182),(-2228751525100)⟩,⟨(-4388556274595),(-4388556274511)⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨408511379919,408511380008⟩,⟨(-615026355400),(-615026355310)⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨105794167027,105794167117⟩,⟨22473616857,22473616947⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨1362750689,1362750768⟩,⟨16800018758,16800018840⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨(-2822001186),(-2822001113)⟩,⟨1062915560,1062915633⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨(-432645855),(-432645796)⟩,⟨(-489843520),(-489843462)⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨51108378,51108419⟩,⟨(-166515231),(-166515186)⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨46268616,46268650⟩,⟨(-27238063),(-27238033)⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨12673957,12673978⟩,⟨(-1820205),(-1820182)⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨1630225595003449909111,1630225595003449921849⟩,⟨(-3623134205056332973048),(-3623134205056332960312)⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨3770703565156063014786,3770703565156063046010⟩,⟨(-8747416393272445301437),(-8747416393272445270209)⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨3752953642064753459144,3752953642064753493633⟩,⟨(-9434713485066512623229),(-9434713485066512588724)⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨2465406457444674708794,2465406457444674734369⟩,⟨(-6883238494063656159310),(-6883238494063656133717)⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨1204009126976956284971,1204009126976956299895⟩,⟨(-3730632959029496655526),(-3730632959029496640589)⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨476721135832226608259,476721135832226616349⟩,⟨(-1570721713492098275828),(-1570721713492098267734)⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨166674480782088873206,166674480782088876725⟩,⟨(-531486068014215491393),(-531486068014215487870)⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨54828085227312017904,54828085227312019181⟩,⟨(-149351476894065770484),(-149351476894065769207)⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨17300920748200753799,17300920748200754247⟩,⟨(-36020782897486823443),(-36020782897486822997)⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨5210363800280381850,5210363800280382032⟩,⟨(-7688947404781800223),(-7688947404781800040)⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨1504436580539201868,1504436580539201984⟩,⟨(-1487213818875379775),(-1487213818875379662)⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨427078163955873107,427078163955873184⟩,⟨(-261810543846218463),(-261810543846218386)⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨123877309963694557,123877309963694618⟩,⟨(-39588869530934119),(-39588869530934057)⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨38033184712319147,38033184712319198⟩,⟨(-3349168390839998),(-3349168390839945)⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨12208305508367329,12208305508367366⟩,⟨1012769194006459,1012769194006501⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨2909172063211070,2909172063211094⟩,⟨516547608949815,516547608949838⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨10181930654627772370178144,10181930654627772382409244⟩,⟨(-2276655771918258962964521),(-2276655771918258950748820)⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨26283167850884753558177216,26283167850884753591022179⟩,⟨(-6904951755340082536027990),(-6904951755340082503243438)⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨32321589038507771968521816,32321589038507772011576266⟩,⟨(-11044635769592722230730207),(-11044635769592722187783553)⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨28500490438140201513078553,28500490438140201553538634⟩,⟨(-13210179925842821172571619),(-13210179925842821132245405)⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨19587370201467926177899809,19587370201467926208820506⟩,⟨(-12460568845574751854902313),(-12460568845574751824101071)⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨10799068053525886222642227,10799068053525886247333327⟩,⟨(-9486243519321053712869158),(-9486243519321053688252758)⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨4831951784799318753837840,4831951784799318771273272⟩,⟨(-5954017855471120741513976),(-5954017855471120724111745)⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨1757989122101558223677307,1757989122101558234395750⟩,⟨(-3158056890152077893354553),(-3158056890152077882645226)⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨512244891350538191625512,512244891350538197114990⟩,⟨(-1458915407304076439692419),(-1458915407304076434207112)⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨110450865825209865006919,110450865825209867414412⟩,⟨(-608705980936113677437565),(-608705980936113675032194)⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨9724399088229559598631,9724399088229560562111⟩,⟨(-239059017665090978744725),(-239059017665090977781935)⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨(-6832032016459042851290),(-6832032016459042392503)⟩,⟨(-92230670112808174069466),(-92230670112808173610801)⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨(-5932741794363913324508),(-5932741794363913096782)⟩,⟨(-36262003667046051571025),(-36262003667046051343290)⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨(-3372232562400758176805),(-3372232562400758068358)⟩,⟨(-14760446641199831858531),(-14760446641199831750072)⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨(-1602164782009884296148),(-1602164782009884248246)⟩,⟨(-5934793428174708400707),(-5934793428174708352798)⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨(-465816814822970053123),(-465816814822970039592)⟩,⟨(-1606278928355294600450),(-1606278928355294586916)⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨1582414281558697599713995402,1582414281558697607887113721⟩,⟨3492233171396261695800657170,3492233171396261703981694596⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨4633877099267363567252718540,4633877099267363590328576180⟩,⟨9415093934865229102377306802,9415093934865229125463851710⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨7240756818238990402261714230,7240756818238990435951229320⟩,⟨12630548574689579411780436975,12630548574689579445465533879⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨8930711842711318261284680361,8930711842711318299071067289⟩,⟨12682536475375448702493111440,12682536475375448740271946920⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨9321009625430327412857974758,9321009625430327448135911398⟩,⟨10331534383033166722594805188,10331534383033166757900255728⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨8413565056766075066964170179,8413565056766075096103294721⟩,⟨6973468559488315157159041536,6973468559488315186363505506⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨6646251891411285573688884826,6646251891411285594167831084⟩,⟨3873233483636437861509653500,3873233483636437882050031155⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨4647232341344574301619435198,4647232341344574313748041120⟩,⟨1691792066118138562699601005,1691792066118138574833881972⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨2916853089351015207696599382,2916853089351015214974477275⟩,⟨480340802150928945046880990,480340802150928952297945093⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨1672709583035076850666950535,1672709583035076855462220972⟩,⟨(-37764665043786380555638461),(-37764665043786375776588274)⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨895214043524682935090736144,895214043524682937964843119⟩,⟨(-181740621057619314074890341),(-181740621057619311205629662)⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨457530559778322804696945638,457530559778322806293246313⟩,⟨(-173317440264706921683385754),(-173317440264706920087547033)⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨227820089806066995065198662,227820089806066995898537245⟩,⟨(-124701903456365625554702275),(-124701903456365624721288856)⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨111037287359644246809934048,111037287359644247224864440⟩,⟨(-77661312870528841417142171),(-77661312870528841002348653)⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨50305381731319088207312136,50305381731319088398759404⟩,⟨(-41177740981703885735584728),(-41177740981703885544307065)⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨14440753094601620034877456,14440753094601620090265784⟩,⟨(-12781960389809240185460609),(-12781960389809240130138206)⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨34125464632316889634797123407,34125464632316889684331480568⟩,⟨51829665050217486004542248316,51829665050217486055260559302⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨99229123029618315999937244266,99229123029618316150563286610⟩,⟨143923318622252339724085707794,143923318622252339877504435909⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨154663215786960129734621770452,154663215786960129988403810572⟩,⟨205103848880815257814196469008,205103848880815258070572652447⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨194154452552660590931140086989,194154452552660591281404670447⟩,⟨226238591691273545666500197035,226238591691273546017588778694⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨213048377552524775347756123270,213048377552524775777638843022⟩,⟨210230595669361184097547727533,210230595669361184526342087222⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨210197513903497917166858787617,210197513903497917635729012293⟩,⟨169199157115985330268439378139,169199157115985330735654889006⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨188893022521103815774577725668,188893022521103816234920218650⟩,⟨118677240625379405084974895565,118677240625379405544887469251⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨155931892559008242142406131266,155931892559008242551736338364⟩,⟨71821063947466727367621907553,71821063947466727777742940728⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨119202205125403170371606632509,119202205125403170694832940369⟩,⟨36101571753731333677049682277,36101571753731334000816342844⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨85157750339526394885399361511,85157750339526395110782635286⟩,⟨13180777573744099624595615064,13180777573744099849568448189⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨57437598634190510478911199965,57437598634190510625754973134⟩,⟨924948462141109699399348736,924948462141109845193179104⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨36936529629770801692671230213,36936529629770801805512561644⟩,⟨(-4148206597839016457883774510),(-4148206597839016345786064381)⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨22759929866397976847697896483,22759929866397976931407653178⟩,⟨(-5180174950408104319648689640),(-5180174950408104236291578872)⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨13285037316035972930343342983,13285037316035972985735014275⟩,⟨(-4310847063758989516747121350),(-4310847063758989461482355258)⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨6865974511714149008294228249,6865974511714149039197962227⟩,⟨(-2716757554133394109328278236),(-2716757554133394078458710856)⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨2113316072407938084029160786,2113316072407938093866825546⟩,⟨(-916561110686129654088014371),(-916561110686129644256784621)⟩⟩
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
noncomputable def ans : CBox := ⟨⟨275316337516000579836137268570,275316337516000580465934025397⟩,⟨215135480070185675335622976031,215135480070185675965910767012⟩⟩
lemma checked : cachedMomentRuleBox column4_1 kernel7_1 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (momentRuleValue quadraturePoint fejerWeight 4 7 true true) := by
  rw [← checked]
  exact cachedMomentRuleBox_contains column4_1_contains kernel7_1_contains
end cm4_7_1_1
end SharpPlanar.CachedData

end OAI
