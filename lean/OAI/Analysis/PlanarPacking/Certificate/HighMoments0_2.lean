import OAI.Analysis.PlanarPacking.Certificate.TableDensityValues
import OAI.Analysis.PlanarPacking.Certificate.HighHeaders0

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace hm0_0_0_16
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density0 j i k).mul (hk0_0_16 j i k))
noncomputable def s0_0 : CBox := ⟨⟨149087058571,149087058587⟩,⟨108907862135,108907862151⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨329742516935,329742516952⟩,⟨235056336932,235056336949⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨296821953132,296821953148⟩,⟨201613393259,201613393275⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨162426768887,162426768903⟩,⟨102910071009,102910071026⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨57829333139,57829333158⟩,⟨33629623389,33629623405⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨13437180865,13437180882⟩,⟨7095108459,7095108475⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨1987280003,1987280019⟩,⟨943867559,943867576⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨178713490,178713506⟩,⟨75450372,75450390⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨9113334,9113351⟩,⟨3369032,3369048⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨237370,237387⟩,⟨75536,75552⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨2687,2704⟩,⟨719,735⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨7,23⟩,⟨0,16⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨0,16⟩,⟨0,16⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨0,16⟩,⟨0,16⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨0,16⟩,⟨0,16⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨0,16⟩,⟨0,16⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨6124596500321996,6124596500322019⟩,⟨8792486009322056,8792486009322078⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨15723982995823449,15723982995823483⟩,⟨22334942402686521,22334942402686555⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨19189879128235036,19189879128235085⟩,⟨26698518476599123,26698518476599171⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨16862687066790889,16862687066790952⟩,⟨22763554595356280,22763554595356346⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨11703426822014325,11703426822014405⟩,⟨15192260695529193,15192260695529272⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨6682084812432542,6682084812432618⟩,⟨8268345641248888,8268345641248964⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨3222582650468017,3222582650468077⟩,⟨3772127678621963,3772127678622023⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨1342594313556408,1342594313556446⟩,⟨1479279239642161,1479279239642197⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨494704451848879,494704451848903⟩,⟨512277723234320,512277723234346⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨165820821968576,165820821968596⟩,⟨161596803783154,161596803783173⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨52361340155389,52361340155409⟩,⟨48167143774328,48167143774345⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨16239950200855,16239950200873⟩,⟨14154184648791,14154184648808⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨5169008770941,5169008770957⟩,⟨4289114249979,4289114249995⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨1742289969808,1742289969824⟩,⟨1387012674884,1387012674901⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨606192036098,606192036114⟩,⟨468303317730,468303317746⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨151582889807,151582889823⟩,⟨115275951161,115275951177⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨(-81620565486128729),(-81620565486128712)⟩,⟨5095114823244180889,5095114823244180907⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨(-36842124509172079),(-36842124509172063)⟩,⟨13702377536293646727,13702377536293646746⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨425253242219363559,425253242219363582⟩,⟨18381975460261418716,18381975460261418737⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨1105752650102959609,1105752650102959627⟩,⟨18682239987333936493,18682239987333936515⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨1608422381275254008,1608422381275254027⟩,⟨15807780762099393414,15807780762099393433⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨1706264294696895797,1706264294696895814⟩,⟨11591915298497819097,11591915298497819119⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨1462081740653776838,1462081740653776855⟩,⟨7548778619870001460,7548778619870001480⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨1073149608224819360,1073149608224819377⟩,⟨4455963909473912468,4455963909473912486⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨702132304049443389,702132304049443408⟩,⟨2434201071137394992,2434201071137395012⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨422516758377108496,422516758377108515⟩,⟨1257923662620969377,1257923662620969399⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨240203278881044428,240203278881044460⟩,⟨629117219851074606,629117219851074641⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨131839014276713662,131839014276713711⟩,⟨311102002511669966,311102002511670018⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨70764566362531433,70764566362531505⟩,⟨154306035977815171,154306035977815243⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨36947458109840716,36947458109840792⟩,⟨76328937975579954,76328937975580032⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨17647958481016098,17647958481016161⟩,⟨35292044392606212,35292044392606272⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨5214506205506086,5214506205506117⟩,⟨10271890278894892,10271890278894924⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨(-100797813437231679030),(-100797813437231216944)⟩,⟨275030726626140567576,275030726626141029718⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨(-273050886680257853211),(-273050886680256846549)⟩,⟨763559871427789220008,763559871427790226833⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨(-371582652431859795865),(-371582652431858927683)⟩,⟨1089494549248037180874,1089494549248038049282⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨(-385306461378558944476),(-385306461378558508069)⟩,⟨1209399852272060896323,1209399852272061332980⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨(-333309490295963022206),(-333309490295962885226)⟩,⟨1144483640274365733461,1144483640274365870677⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨(-248943240490235907679),(-248943240490235880047)⟩,⟨960699394411417263808,960699394411417291637⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨(-163726575588394152582),(-163726575588394148683)⟩,⟨733638474936034719607,733638474936034723653⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨(-96637331705528442646),(-96637331705528442143)⟩,⟨519614226946720028171,519614226946720028781⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨(-52255813756065492258),(-52255813756065492141)⟩,⟨346793169239546985656,346793169239546985842⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨(-26425382011651012208),(-26425382011651012150)⟩,⟨221154258985174912525,221154258985174912630⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨(-12717882198045909199),(-12717882198045909162)⟩,⟨136440909365843931615,136440909365843931684⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨(-5882826175170325039),(-5882826175170325012)⟩,⟨82232896730708270317,82232896730708270362⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨(-2614864951305898175),(-2614864951305898156)⟩,⟨48559689893688629899,48559689893688629932⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨(-1105965984779990898),(-1105965984779990878)⟩,⟨27664323393124408866,27664323393124408888⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨(-427861963782778928),(-427861963782778911)⟩,⟨14134553086661248571,14134553086661248593⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨(-109361830379905537),(-109361830379905521)⟩,⟨4333045150817440983,4333045150817441002⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨(-6469524570790559622288),(-6469524570790510672631)⟩,⟨362718140420641427154,362718140420690377573⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨(-17960263204485806128158),(-17960263204485631201504)⟩,⟨1440824466491875383525,1440824466492050312314⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨(-25679058999027663467498),(-25679058999027266992815)⟩,⟨3312287995770461350982,3312287995770857828806⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨(-28737506869287714053715),(-28737506869286910701723)⟩,⟨5796283691423565171458,5796283691424368527110⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨(-27687138865934966865121),(-27687138865933503714853)⟩,⟨8163808111624463234312,8163808111625926388303⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨(-23895439354980831473385),(-23895439354978549102675)⟩,⟨9636216922726758602721,9636216922729040976823⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨(-18870652220344679726127),(-18870652220341823354767)⟩,⟨9881599115871482263329,9881599115874338637541⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨(-13840829169230514466462),(-13840829169227801101245)⟩,⟨9079682641889741888593,9079682641892455256065⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨(-9555640323513585620778),(-9555640323511613991454)⟩,⟨7663035617953003434889,7663035617954975065928⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨(-6292155766394217650594),(-6292155766393104997032)⟩,⟨6058372937011686848053,6058372937012799502873⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨(-4004229364416095059393),(-4004229364415603652661)⟩,⟨4554871730379619077035,4554871730380110484661⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨(-2493399072164610821210),(-2493399072164427259994)⟩,⟨3283763057447896733548,3283763057448080295383⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨(-1527241853665775260617),(-1527241853665711988029)⟩,⟨2262813200180057664586,2262813200180120937584⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨(-903821406954426549052),(-903821406954405006692)⟩,⟨1455803894435253449337,1455803894435274991953⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨(-476807623232619130340),(-476807623232611800138)⟩,⟨808217686025901811143,808217686025909141490⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨(-148846019296700011648),(-148846019296698220057)⟩,⟨258364357116296136397,258364357116297928030⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨(-404718168288345455431),(-404718168288345447533)⟩,⟨(-32097699979178100185597),(-32097699979178100172609)⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨(-5629765067960911051273),(-5629765067960911027950)⟩,⟨(-90516900858415674060845),(-90516900858415674023358)⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨(-20996640810770345960086),(-20996640810770345922537)⟩,⟨(-133977081237414383409162),(-133977081237414383351887)⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨(-44736300146582111746568),(-44736300146582111697200)⟩,⟨(-158643234498574838396812),(-158643234498574838326336)⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨(-68568905607376545435989),(-68568905607376545378002)⟩,⟨(-164623287848070648479266),(-164623287848070648402382)⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨(-84359148884277569183599),(-84359148884277569118782)⟩,⟨(-153767925502678380319982),(-153767925502678380240170)⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨(-89557942618166260520827),(-89557942618166260442889)⟩,⟨(-130381062011606027336523),(-130381062011606027248036)⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨(-86068185223224973741483),(-86068185223224973599307)⟩,⟨(-101381530407361227394825),(-101381530407361227246427)⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨(-76953180919624143312882),(-76953180919624142769152)⟩,⟨(-73370570885237444749419),(-73370570885237444203056)⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨(-64992535189405605670722),(-64992535189405602936007)⟩,⟨(-50248699758429532496566),(-50248699758429529761581)⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨(-52288738342989031583986),(-52288738342989020227667)⟩,⟨(-33154932252830909158213),(-33154932252830897802865)⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨(-40120559796276892581211),(-40120559796276858573246)⟩,⟨(-21451359068298823660252),(-21451359068298789653648)⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨(-29093517041902146044467),(-29093517041902075766763)⟩,⟨(-13700898041596101169919),(-13700898041596030893512)⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨(-19425565625545545139399),(-19425565625545445811946)⟩,⟨(-8435699468189535567720),(-8435699468189436241271)⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨(-11042457458364207905459),(-11042457458364117051229)⟩,⟨(-4582550141738868163763),(-4582550141738777310150)⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨(-3570544734928965427999),(-3570544734928928540770)⟩,⟨(-1452060287756146588243),(-1452060287756109701222)⟩⟩
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
noncomputable def ans : CBox := ⟨⟨(-148069530568928368193935),(-148069530568925877936844)⟩,⟨(-181681551727449574851405),(-181681551727447084571473)⟩⟩
lemma checked : cachedMomentRuleBox density0 hk0_0_16 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule false false 0 16) := by
  rw [← checked]
  exact @cached_density_rule_contains density0 hk0_0_16 (tableDensity false) (fullFactor false 0 16) density0_contains hk0_0_16_contains
noncomputable def atomAnswer : CBox := ⟨⟨(-105739889332786839573670),(-105739889332786839567658)⟩,⟨10333719027224876911619,10333719027224876912284⟩⟩
lemma atomChecked : tableAtomBox false ha0_0_16 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom false false 0 16) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains false false ha0_0_16 0 16 ha0_0_16_contains
 def realAnswer : RBox := ⟨(-253809419901715307767605),(-253809419901712617504502)⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment false false 0 16) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm0_0_0_16
namespace hm0_1_0_16
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density1 j i k).mul (hk0_0_16 j i k))
noncomputable def s0_0 : CBox := ⟨⟨22815433910,22815433926⟩,⟨21824361365,21824361381⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨50452329251,50452329267⟩,⟨47867126976,47867126992⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨45127367438,45127367454⟩,⟨42151762998,42151763014⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨24256925354,24256925370⟩,⟨22002147153,22002147169⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨8429495462,8429495479⟩,⟨7173825747,7173825763⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨1933764613,1933764629⟩,⟨1450194665,1450194681⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨290231959,290231975⟩,⟨177545161,177545177⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨27216036,27216052⟩,⟨12729523,12729539⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨1467587,1467603⟩,⟨507036,507052⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨40383,40399⟩,⟨10295,10311⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨470,486⟩,⟨84,100⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨0,16⟩,⟨0,16⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨0,16⟩,⟨0,16⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨0,16⟩,⟨0,16⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨0,16⟩,⟨0,16⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨0,16⟩,⟨0,16⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨188064503067088,188064503067107⟩,⟨1660693577754896,1660693577754914⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨544302601207084,544302601207115⟩,⟨4170342699048320,4170342699048349⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨813707700275459,813707700275504⟩,⟨4881417265389306,4881417265389348⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨908078194423486,908078194423542⟩,⟨4054120637647175,4054120637647228⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨798572535496228,798572535496293⟩,⟨2639482021785038,2639482021785103⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨561422734908638,561422734908707⟩,⟨1413196011804698,1413196011804765⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨320227732040778,320227732040832⟩,⟨641262927400879,641262927400932⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨152084959632645,152084959632678⟩,⟨252291177175249,252291177175282⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨62257553988258,62257553988282⟩,⟨88171692108036,88171692108062⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨22815489614838,22815489614857⟩,⟨28260134722737,28260134722755⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨7779349890746,7779349890762⟩,⟨8653049754154,8653049754171⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨2565486283398,2565486283414⟩,⟨2648115846554,2648115846570⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨851111193225,851111193241⟩,⟨843077579306,843077579322⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨293323879853,293323879869⟩,⟨285676134828,285676134844⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨102999606179,102999606195⟩,⟨99821666037,99821666053⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨25827950067,25827950083⟩,⟨25008696664,25008696680⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨(-618518814547636808),(-618518814547636790)⟩,⟨970032739534032890,970032739534032906⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨(-1641786602152806300),(-1641786602152806283)⟩,⟨2626398665145061967,2626398665145061983⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨(-2144778882642536635),(-2144778882642536617)⟩,⟨3548692139083852641,3548692139083852657⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨(-2082014114109288029),(-2082014114109288009)⟩,⟨3601244533037245077,3601244533037245094⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨(-1626173723495681266),(-1626173723495681247)⟩,⟨3003110047251307635,3003110047251307651⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨(-1044400155798567158),(-1044400155798567141)⟩,⟨2155101074716017165,2155101074716017185⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨(-557429699404587111),(-557429699404587093)⟩,⟨1380561080646322880,1380561080646322896⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨(-250105340543964597),(-250105340543964578)⟩,⟨812706326642732794,812706326642732810⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨(-95326911164926306),(-95326911164926290)⟩,⟨448975262188832082,448975262188832099⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨(-31047644314711146),(-31047644314711127)⟩,⟨236423453694570405,236423453694570427⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨(-8559158914340568),(-8559158914340542)⟩,⟨120170025389663055,120170025389663087⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨(-1751928277583596),(-1751928277583553)⟩,⟨59617433224622600,59617433224622645⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨98349632284740,98349632284801⟩,⟨29167665887239181,29167665887239241⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨487007274826350,487007274826414⟩,⟨14081968129939026,14081968129939092⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨400735410615820,400735410615872⟩,⟨6361806386038309,6361806386038360⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨147236390460869,147236390460899⟩,⟨1827086339438841,1827086339438872⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨(-81968064093929074383),(-81968064093928686105)⟩,⟨53564253043262432329,53564253043262820600⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨(-222778371159058920390),(-222778371159058075070)⟩,⟨147284210075606060716,147284210075606906019⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨(-304783332743175340782),(-304783332743174612708)⟩,⟨207162537091302669194,207162537091303397242⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨(-318489668837949937152),(-318489668837949571902)⟩,⟨227761819230714195609,227761819230714560832⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨(-280397711471479211167),(-280397711471479096830)⟩,⟨216524903081126134643,216524903081126248962⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨(-218595838700377928403),(-218595838700377905416)⟩,⟨185307491749035707667,185307491749035730637⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨(-155945138639105710027),(-155945138639105706798)⟩,⟨144988371186135007879,144988371186135011095⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨(-103866998203471649539),(-103866998203471649127)⟩,⟨104713587339470894150,104713587339470894556⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨(-65413579120801550379),(-65413579120801550284)⟩,⟨70787292212526781797,70787292212526781890⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨(-39418402023054913459),(-39418402023054913412)⟩,⟨45607896834152779627,45607896834152779673⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨(-23051120103164118116),(-23051120103164118082)⟩,⟨28509638685133334362,28509638685133334392⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨(-13272588392407097341),(-13272588392407097318)⟩,⟨17500826850698771391,17500826850698771415⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨(-7578619750720062458),(-7578619750720062434)⟩,⟨10557821002489684468,10557821002489684487⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨(-4227758531970640698),(-4227758531970640681)⟩,⟨6137177391105445488,6137177391105445505⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨(-2136596736209925937),(-2136596736209925920)⟩,⟨3183925174257361598,3183925174257361614⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨(-652184109407439371),(-652184109407439355)⟩,⟨984026426429727577,984026426429727593⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨(-2116692209339728993383),(-2116692209339688763891)⟩,⟨227775776575433464036,227775776575473693239⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨(-5995359011514740566665),(-5995359011514596792562)⟩,⟨737065647514031260844,737065647514175034129⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨(-8869419349004652103382),(-8869419349004326194832)⟩,⟨1326292124273420398849,1326292124273746306201⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨(-10304560890553451476374),(-10304560890552791005134)⟩,⟨1900983130496580602537,1900983130497241072400⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨(-10244465802940220205840),(-10244465802939017139912)⟩,⟨2362576838116721518177,2362576838117924582751⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨(-9067633560343151679011),(-9067633560341275015077)⟩,⟨2661925227452896866459,2661925227454773529201⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨(-7369850250880401117759),(-7369850250878052975777)⟩,⟨2748117818616499897913,2748117818618848038929⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨(-5643921775326297044266),(-5643921775324067537123)⟩,⟨2585963719605158132592,2585963719607387639013⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨(-4148451805757381143771),(-4148451805755762379256)⟩,⟨2214832917678802997434,2214832917680421761447⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨(-2957534375484926185743),(-2957534375484013633599)⟩,⟨1735716878482092526553,1735716878483005078365⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨(-2049896088244764765821),(-2049896088244362244252)⟩,⟨1255329134981942091838,1255329134982344613193⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨(-1374023180306704038815),(-1374023180306553882381)⟩,⟨847607302044172030189,847607302044322186485⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨(-881312788331408882059),(-881312788331357189972)⟩,⟨541540159600575507549,541540159600627199548⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨(-530289247079595924166),(-530289247079578343307)⟩,⟨326951866921403959098,326951866921421539908⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨(-279470032494421959241),(-279470032494415981466)⟩,⟨174467311315368154855,174467311315374132604⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨(-86853101179354395871),(-86853101179352935386)⟩,⟨54819019410478594902,54819019410480055378⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨(-57278634912907667672),(-57278634912907662370)⟩,⟨(-952982644185032300832),(-952982644185032292978)⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨(-812828485327559739219),(-812828485327559723611)⟩,⟨(-2524158432253511678985),(-2524158432253511656109)⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨(-3315830245942940256904),(-3315830245942940231893)⟩,⟨(-2481822876616237398291),(-2481822876616237362855)⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨(-8709465802369696109086),(-8709465802369696076230)⟩,⟨898341853905838522163,898341853905838566596⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨(-18100861123397394858394),(-18100861123397394819379)⟩,⟨7309583923456421493903,7309583923456421544014⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨(-30433335350757615961648),(-30433335350757615916577)⟩,⟨13175697446127061407864,13175697446127061462485⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨(-41449695124966961471594),(-41449695124966961413906)⟩,⟨14993534969910466921496,14993534969910466986569⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨(-46935697040277254852132),(-46935697040277254738716)⟩,⟨12685135997429728009338,12685135997429728127666⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨(-45857776553993653816391),(-45857776553993653370415)⟩,⟨8544786600806265935903,8544786600806266384505⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨(-39975921038719781881676),(-39975921038719779642284)⟩,⟨4748083361543568930451,4748083361543571170892⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨(-31929209979832983490254),(-31929209979832974211193)⟩,⟨2304353443297972439927,2304353443297981719166⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨(-23861315264673562139203),(-23861315264673534363882)⟩,⟨1187211494569030826995,1187211494569058602185⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨(-16886199289952712003516),(-16886199289952654588183)⟩,⟨834656130371590922950,834656130371648338077⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨(-11165823848052355260564),(-11165823848052274075087)⟩,⟨684060140256665094158,684060140256746279445⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨(-6364852575011948220126),(-6364852575011873932650)⟩,⟨469437394946505862331,469437394946580149673⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨(-2068704841104325297286),(-2068704841104295130236)⟩,⟨166992989050362550913,166992989050392717915⟩⟩
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
noncomputable def ans : CBox := ⟨⟨(-66949533502838726289792),(-66949533502836680612009)⟩,⟨14205747792719762362336,14205747792721808049867⟩⟩
lemma checked : cachedMomentRuleBox density1 hk0_0_16 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule true false 0 16) := by
  rw [← checked]
  exact @cached_density_rule_contains density1 hk0_0_16 (tableDensity true) (fullFactor false 0 16) density1_contains hk0_0_16_contains
noncomputable def atomAnswer : CBox := ⟨⟨138275239896721251742322,138275239896721251750183⟩,⟨(-13513324881755608269909),(-13513324881755608269040)⟩⟩
lemma atomChecked : tableAtomBox true ha0_0_16 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom true false 0 16) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains true false ha0_0_16 0 16 ha0_0_16_contains
 def realAnswer : RBox := ⟨71325706393882425452530,71325706393884671138174⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment true false 0 16) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm0_1_0_16
namespace hm0_0_0_17
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density0 j i k).mul (hk0_0_17 j i k))
noncomputable def s0_0 : CBox := ⟨⟨(-3338699817),(-3338699801)⟩,⟨4570393564,4570393580⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨(-7075582615),(-7075582599)⟩,⟨9924874818,9924874834⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨(-5849369233),(-5849369217)⟩,⟨8609497119,8609497135⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨(-2822772356),(-2822772340)⟩,⟨4453279739,4453279755⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨(-854523812),(-854523795)⟩,⟨1468470510,1468470526⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨(-163389850),(-163389833)⟩,⟨309174914,309174932⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨(-19229642),(-19229626)⟩,⟨40444519,40444536⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨(-1323433),(-1323416)⟩,⟨3130678,3130695⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨(-49300),(-49284)⟩,⟨133134,133152⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨(-895),(-878)⟩,⟨2777,2794⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨(-18),(-2)⟩,⟨17,34⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨(-16),0⟩,⟨0,16⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨(-16),0⟩,⟨0,16⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨(-16),0⟩,⟨0,16⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨(-16),0⟩,⟨0,16⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨(-16),0⟩,⟨0,16⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨(-540333886957147),(-540333886957131)⟩,⟨376380441945224,376380441945240⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨(-1359819324199667),(-1359819324199651)⟩,⟨957305445243998,957305445244015⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨(-1595556361963527),(-1595556361963509)⟩,⟨1146766096997046,1146766096997065⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨(-1323295547465821),(-1323295547465804)⟩,⟨980171048815915,980171048815938⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨(-851582290272045),(-851582290272023)⟩,⟨655921316089457,655921316089474⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨(-443206455427721),(-443206455427702)⟩,⟨358102380574426,358102380574445⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨(-191886308028917),(-191886308028896)⟩,⟨163887047942853,163887047942872⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨(-70938278812675),(-70938278812657)⟩,⟨64363710164690,64363710164709⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨(-23035248463873),(-23035248463855)⟩,⟨22237820725408,22237820725424⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨(-6789739982290),(-6789739982274)⟩,⟨6965004213714,6965004213731⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨(-1888980315148),(-1888980315129)⟩,⟨2052861052809,2052861052828⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨(-519127139334),(-519127139317)⟩,⟨595473530732,595473530749⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨(-147957981070),(-147957981054)⟩,⟨178275607826,178275607842⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨(-45448642793),(-45448642777)⟩,⟨57083064444,57083064462⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨(-14782856263),(-14782856247)⟩,⟨19134594857,19134594874⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨(-3567962092),(-3567962076)⟩,⟨4691687609,4691687625⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨(-470040996808374791),(-470040996808374775)⟩,⟨(-7530618305962334),(-7530618305962318)⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨(-1256187332426893103),(-1256187332426893087)⟩,⟨(-3397679773915028),(-3397679773915012)⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨(-1664386121093014282),(-1664386121093014266)⟩,⟨38434884281706495,38434884281706511⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨(-1660831067781077175),(-1660831067781077158)⟩,⟨98180011872305421,98180011872305437⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨(-1372138092889117768),(-1372138092889117751)⟩,⟨139476403636023476,139476403636023492⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨(-977552886953582248),(-977552886953582232)⟩,⟨143772268416564469,143772268416564485⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨(-615819763359850272),(-615819763359850256)⟩,⟨119190568159023895,119190568159023911⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨(-350456268071181892),(-350456268071181874)⟩,⟨84349845875320350,84349845875320367⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨(-184149762757321064),(-184149762757321047)⟩,⟨53088544290071822,53088544290071838⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨(-91449843205380873),(-91449843205380856)⟩,⟨30702671116397646,30702671116397664⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨(-43979196396323226),(-43979196396323207)⟩,⟨16785657974577024,16785657974577041⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨(-20962489612623207),(-20962489612623186)⟩,⟨8881211317160015,8881211317160032⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨(-10064617473267805),(-10064617473267785)⟩,⟨4614897910657455,4614897910657475⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨(-4848752438332562),(-4848752438332540)⟩,⟨2346885793444753,2346885793444776⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨(-2200441658510839),(-2200441658510819)⟩,⟨1100312569136748,1100312569136768⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨(-634282962666902),(-634282962666884)⟩,⟨321991668340464,321991668340480⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨(-33843300001526015943),(-33843300001525959059)⟩,⟨(-12403484057261719800),(-12403484057261662927)⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨(-93515492976742796994),(-93515492976742673644)⟩,⟨(-33442104016141278831),(-33442104016141155501)⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨(-132194195305064699256),(-132194195305064593810)⟩,⟨(-45088687160955321726),(-45088687160955216303)⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨(-144744277215472180433),(-144744277215472128091)⟩,⟨(-46119379053489381554),(-46119379053489329244)⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨(-134565304253781852295),(-134565304253781836117)⟩,⟨(-39196271714614498207),(-39196271714614482053)⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨(-110574472125325587313),(-110574472125325584082)⟩,⟨(-28660163674009279608),(-28660163674009276402)⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨(-82415200334545837426),(-82415200334545836953)⟩,⟨(-18399190086437529276),(-18399190086437528825)⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨(-56846318522860113876),(-56846318522860113794)⟩,⟨(-10576962331514791848),(-10576962331514791777)⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨(-36898728941002387853),(-36898728941002387816)⟩,⟨(-5562882586902586406),(-5562882586902586379)⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨(-22878135320648308654),(-22878135320648308625)⟩,⟨(-2735180446393904966),(-2735180446393904944)⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨(-13734322726678166946),(-13734322726678166923)⟩,⟨(-1280908501329138748),(-1280908501329138731)⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨(-8070792738641363375),(-8070792738641363357)⟩,⟨(-577681079162379561),(-577681079162379545)⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨(-4661734508434115538),(-4661734508434115521)⟩,⟨(-251147651947223118),(-251147651947223102)⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨(-2609028429169979698),(-2609028429169979680)⟩,⟨(-104342200604053969),(-104342200604053952)⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨(-1316548025217955685),(-1316548025217955668)⟩,⟨(-39860316875605997),(-39860316875605981)⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨(-401017633084353759),(-401017633084353743)⟩,⟨(-10121560576543936),(-10121560576543920)⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨(-55803252371947981065),(-55803252371940450051)⟩,⟨(-995354017036017891637),(-995354017036010360738)⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨(-220791271253980011717),(-220791271253953204516)⟩,⟨(-2752822222346672918174),(-2752822222346646111287)⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨(-503726850371575228698),(-503726850371514935970)⟩,⟨(-3906677681252005483829),(-3906677681251945191566)⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨(-871841953248890564631),(-871841953248769756035)⟩,⟨(-4324438417162385532634),(-4324438417162264724576)⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨(-1210737216985913128175),(-1210737216985696214988)⟩,⟨(-4108014925358721175053),(-4108014925358504262409)⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨(-1405227664744254554340),(-1405227664743921851091)⟩,⟨(-3486124795499913941940),(-3486124795499581239182)⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨(-1413773561906606206918),(-1413773561906197632410)⟩,⟨(-2700940954085657587606),(-2700940954085249013503)⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨(-1272422990445670920772),(-1272422990445290618471)⟩,⟨(-1940377941446414954132),(-1940377941446034652145)⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨(-1050939685723665011451),(-1050939685723394502766)⟩,⟨(-1310953355393555823548),(-1310953355393285315097)⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨(-813030643527763774888),(-813030643527614337379)⟩,⟨(-844666985604334674546),(-844666985604185237204)⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨(-598599957851981576184),(-598599957851916929927)⟩,⟨(-526373587257546114103),(-526373587257481467964)⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨(-423320205188774914295),(-423320205188751226636)⟩,⟨(-321495973092668791289),(-321495973092645103711)⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨(-286875068124584784554),(-286875068124576756208)⟩,⟨(-193645031945291670083),(-193645031945283641791)⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨(-182118296375489784512),(-182118296375487088123)⟩,⟨(-113073348880389513886),(-113073348880386817532)⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨(-100169982259983214704),(-100169982259982305969)⟩,⟨(-59096481407941858461),(-59096481407940949742)⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨(-31868753992775933109),(-31868753992775712095)⟩,⟨(-18359915987072414704),(-18359915987072193692)⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨5926919681547839062057,5926919681547839064489⟩,⟨(-74712304801146818884),(-74712304801146817413)⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨16661543025554120591624,16661543025554120598588⟩,⟨(-1035787364879743381356),(-1035787364879743377049)⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨24508331959433336347889,24508331959433336358459⟩,⟨(-3839086564561748782116),(-3839086564561748775224)⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨28757230399217837147340,28757230399217837160226⟩,⟨(-8105942506628377000596),(-8105942506628376991606)⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨29493433356331505166275,29493433356331505180162⟩,⟨(-12280326005847442866172),(-12280326005847442855728)⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨27166751621363806695333,27166751621363806709538⟩,⟨(-14899534051862173155996),(-14899534051862173144484)⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨22675037052342327846489,22675037052342327861962⟩,⟨(-15570725782513647244058),(-15570725782513647230444)⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨17334141557320784934524,17334141557320784959933⟩,⟨(-14711337566998080822733),(-14711337566998080798401)⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨12324860905951920644592,12324860905951920736179⟩,⟨(-12922609984197466618989),(-12922609984197466527845)⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨8292666346317380141267,8292666346317380591416⟩,⟨(-10722667168021549211353),(-10722667168021548761237)⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨5379266274174728246612,5379266274174730084794⟩,⟨(-8481495012311643252830),(-8481495012311641414481)⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨3426446061543542372251,3426446061543547795250⟩,⟨(-6407332299331289605086),(-6407332299331284181856)⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨2159086110369005404572,2159086110369016468005⟩,⟨(-4584294459707356825793),(-4584294459707345762141)⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨1315139082381107157341,1315139082381122634576⟩,⟨(-3028338551725784130221),(-3028338551725768652823)⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨709105162309956837503,709105162309970893704⟩,⟨(-1708688181625577515073),(-1708688181625563458772)⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨223832381417518735064,223832381417524421035⟩,⟨(-550391960043140074272),(-550391960043134388269)⟩⟩
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
noncomputable def ans : CBox := ⟨⟨32504090440524224182703,32504090440524578951699⟩,⟨(-24461566452059493397210),(-24461566452059138632198)⟩⟩
lemma checked : cachedMomentRuleBox density0 hk0_0_17 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule false false 0 17) := by
  rw [← checked]
  exact @cached_density_rule_contains density0 hk0_0_17 (tableDensity false) (fullFactor false 0 17) density0_contains hk0_0_17_contains
noncomputable def atomAnswer : CBox := ⟨⟨(-1595932729921965585253),(-1595932729921965585145)⟩,⟨(-19732628104434754804278),(-19732628104434754803107)⟩⟩
lemma atomChecked : tableAtomBox false ha0_0_17 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom false false 0 17) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains false false ha0_0_17 0 17 ha0_0_17_contains
 def realAnswer : RBox := ⟨30908157710602158597450,30908157710602713366554⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment false false 0 17) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm0_0_0_17
namespace hm0_1_0_17
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density1 j i k).mul (hk0_0_17 j i k))
noncomputable def s0_0 : CBox := ⟨⟨(-669046908),(-669046892)⟩,⟨699426608,699426624⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨(-1440795709),(-1440795693)⟩,⟨1518564851,1518564868⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨(-1222801121),(-1222801105)⟩,⟨1309011473,1309011489⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨(-603465003),(-603464987)⟩,⟨665145619,665145635⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨(-182316631),(-182316615)⟩,⟨214084516,214084532⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨(-33414655),(-33414639)⟩,⟨44493097,44493113⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨(-3620566),(-3620550)⟩,⟨5904859,5904875⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨(-223542),(-223526)⟩,⟨476498,476514⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨(-7435),(-7419)⟩,⟨21419,21435⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨(-130),(-114)⟩,⟨466,482⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨(-16),0⟩,⟨1,17⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨(-16),0⟩,⟨0,16⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨(-16),0⟩,⟨0,16⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨(-16),0⟩,⟨0,16⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨(-16),0⟩,⟨0,16⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨(-16),0⟩,⟨0,16⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨(-102056596494409),(-102056596494393)⟩,⟨11556999556852,11556999556868⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨(-253908405489456),(-253908405489440)⟩,⟨33131291681300,33131291681317⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨(-291737659071125),(-291737659071107)⟩,⟨48603894373657,48603894373675⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨(-235692389481630),(-235692389481610)⟩,⟨52747959180309,52747959180327⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨(-147963553310567),(-147963553310549)⟩,⟨44721227010109,44721227010129⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨(-75754425596523),(-75754425596505)⟩,⟨30064383150331,30064383150351⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨(-32620736969930),(-32620736969912)⟩,⟨16274435392608,16274435392628⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨(-12098125629908),(-12098125629891)⟩,⟨7286709591351,7286709591368⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨(-3964500707817),(-3964500707800)⟩,⟨2797171368001,2797171368018⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨(-1187258828205),(-1187258828189)⟩,⟨957895992233,957895992249⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨(-339286456057),(-339286456041)⟩,⟨304882281335,304882281351⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨(-97101123470),(-97101123454)⟩,⟨94045366602,94045366619⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨(-29076599237),(-29076599221)⟩,⟨29350390593,29350390610⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨(-9359504062),(-9359504046)⟩,⟨9609783130,9609783146⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨(-3150873654),(-3150873638)⟩,⟨3251172051,3251172067⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨(-774051202),(-774051186)⟩,⟨799408011,799408027⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨(-89488592953578354),(-89488592953578338)⟩,⟨(-57060484778210416),(-57060484778210400)⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨(-240777604709624518),(-240777604709624502)⟩,⟨(-150515776044391935),(-150515776044391919)⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨(-321312553486829901),(-321312553486829885)⟩,⟨(-194206684882919199),(-194206684882919183)⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨(-320151527530292395),(-320151527530292378)⟩,⟨(-185108817041145888),(-185108817041145872)⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨(-260686097381766387),(-260686097381766371)⟩,⟨(-141187110030689705),(-141187110030689689)⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨(-181750956288700319),(-181750956288700303)⟩,⟨(-88112925238081198),(-88112925238081182)⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨(-112627704025366733),(-112627704025366717)⟩,⟨(-45505760686538569),(-45505760686538553)⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨(-63917318557953364),(-63917318557953348)⟩,⟨(-19689907480014572),(-19689907480014556)⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨(-33963571054267772),(-33963571054267756)⟩,⟨(-7221067948045000),(-7221067948044984)⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨(-17186674770150862),(-17186674770150846)⟩,⟨(-2260899458913585),(-2260899458913568)⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨(-8400348224310964),(-8400348224310948)⟩,⟨(-599595561017611),(-599595561017595)⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨(-4017174794604100),(-4017174794604084)⟩,⟨(-118446763166188),(-118446763166169)⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨(-1902559312716526),(-1902559312716506)⟩,⟨6272880350390,6272880350411⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨(-894591289144525),(-894591289144504)⟩,⟨30887766403863,30887766403883⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨(-396664267077835),(-396664267077818)⟩,⟨24975014935129,24975014935146⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨(-112821770212018),(-112821770212000)⟩,⟨9091364652431,9091364652447⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨(-6591238137521400241),(-6591238137521352447)⟩,⟨(-10086421162757440307),(-10086421162757392517)⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨(-18038489456219645439),(-18038489456219541875)⟩,⟨(-27284865922277544753),(-27284865922277441186)⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨(-25136485417385122510),(-25136485417385034100)⟩,⟨(-36982886039598144346),(-36982886039598055935)⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨(-27259292757195649395),(-27259292757195605616)⟩,⟨(-38121188681775420418),(-38121188681775376638)⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨(-25457858347849624284),(-25457858347849610798)⟩,⟨(-32972499998281901188),(-32972499998281887703)⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨(-21327509046068991767),(-21327509046068989099)⟩,⟨(-25163385259520459043),(-25163385259520456374)⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨(-16286851659299195615),(-16286851659299195239)⟩,⟨(-17520900777342688351),(-17520900777342687972)⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨(-11455364765674315520),(-11455364765674315460)⟩,⟨(-11364675521690993906),(-11364675521690993846)⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨(-7531571844112648447),(-7531571844112648417)⟩,⟨(-6960919405768777095),(-6960919405768777067)⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨(-4717962047993863269),(-4717962047993863251)⟩,⟨(-4078306839520394832),(-4078306839520394815)⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨(-2869718792571535242),(-2869718792571535222)⟩,⟨(-2320610502713506329),(-2320610502713506312)⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨(-1717558799762932311),(-1717558799762932293)⟩,⟨(-1302746779201127420),(-1302746779201127403)⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨(-1013515902713875533),(-1013515902713875516)⟩,⟨(-727580091277292569),(-727580091277292553)⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨(-578785465537559694),(-578785465537559678)⟩,⟨(-398728336884198455),(-398728336884198439)⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨(-296560606047278581),(-296560606047278565)⟩,⟨(-199012113385968461),(-199012113385968445)⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨(-91070253638424337),(-91070253638424321)⟩,⟨(-60358811709230961),(-60358811709230945)⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨(-35043436724368658025),(-35043436724362468765)⟩,⟨(-325658318648676410588),(-325658318648670221284)⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨(-112960999047165881200),(-112960999047143848465)⟩,⟨(-918913553592044589372),(-918913553592022556512)⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨(-201736463502592934044),(-201736463502543373032)⟩,⟨(-1349306803763290849042),(-1349306803763241287847)⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨(-285985097001196043790),(-285985097001096722370)⟩,⟨(-1550578231709140270288),(-1550578231709040948657)⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨(-350421871125387735997),(-350421871125209381194)⟩,⟨(-1519944613910096601980),(-1519944613909918246972)⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨(-388190365976167397515),(-388190365975893835056)⟩,⟨(-1322834531274207424810),(-1322834531273933862174)⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨(-393162683369799617558),(-393162683369463740308)⟩,⟨(-1054779512560355931242),(-1054779512560020053854)⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨(-362381168156323428250),(-362381168156010942971)⟩,⟨(-791160034377243636114),(-791160034376931150737)⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨(-303748618547844953966),(-303748618547622858415)⟩,⟨(-569057826190880841716),(-569057826190658746098)⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨(-232942207550572160209),(-232942207550449597706)⟩,⟨(-396962971583362375817),(-396962971583239813273)⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨(-164990074160014653795),(-164990074159961700704)⟩,⟨(-269430538783986131938),(-269430538783933178815)⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨(-109279991702946521071),(-109279991702927144177)⟩,⟨(-177148738060926785551),(-177148738060907408636)⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨(-68661675158452307651),(-68661675158445748741)⟩,⟨(-111741027147919133878),(-111741027147912574958)⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨(-40903053797738479095),(-40903053797736278586)⟩,⟨(-66342005016137541233),(-66342005016135340715)⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨(-21623709175211666231),(-21623709175210925175)⟩,⟨(-34638171582792577938),(-34638171582791836879)⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨(-6761832729500232456),(-6761832729500052291)⟩,⟨(-10713196010549852389),(-10713196010549672222)⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨175970821692632622375,175970821692632623842⟩,⟨(-10573821486290197578),(-10573821486290196583)⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨464651324446290336702,464651324446290340932⟩,⟨(-149545472728080233268),(-149545472728080230381)⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨454248264805498427176,454248264805498433672⟩,⟨(-606222705715702669517),(-606222705715702664928)⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨(-162011767424934259342),(-162011767424934251273)⟩,⟨(-1577734555852064875361),(-1577734555852064869388)⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨(-1308184916115478176567),(-1308184916115478167574)⟩,⟨(-3240623581589837805795),(-3240623581589837798783)⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨(-2326523925126832208055),(-2326523925126832198387)⟩,⟨(-5373179562847325475408),(-5373179562847325467414)⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨(-2606952999821659829301),(-2606952999821659817969)⟩,⟨(-7204455358247532670489),(-7204455358247532660426)⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨(-2168899464736851790181),(-2168899464736851769967)⟩,⟨(-8021107281309986876227),(-8021107281309986856829)⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨(-1435671475433755040515),(-1435671475433754965348)⟩,⟨(-7700165616808454640929),(-7700165616808454566180)⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨(-783898498650856435102),(-783898498650856066369)⟩,⟨(-6595267786134674912351),(-6595267786134674543770)⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨(-374032496801346149853),(-374032496801344647761)⟩,⟨(-5179225933092908941275),(-5179225933092907439190)⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨(-189652353826136158373),(-189652353826131729099)⟩,⟨(-3810832659420631666379),(-3810832659420627237070)⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨(-131497742180637697822),(-131497742180628659113)⟩,⟨(-2660822889686592842165),(-2660822889686583803415)⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨(-106622963846556938571),(-106622963846544288134)⟩,⟨(-1740692543448814977508),(-1740692543448802327034)⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨(-72634868043441642877),(-72634868043430149689)⟩,⟨(-984882002382943756343),(-984882002382932263127)⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨(-25741426406166485599),(-25741426406161835490)⟩,⟨(-318886328615205513942),(-318886328615200863821)⟩⟩
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
noncomputable def ans : CBox := ⟨⟨(-2308046052120346439097),(-2308046052120055000398)⟩,⟨(-10976644087913814676841),(-10976644087913523239912)⟩⟩
lemma checked : cachedMomentRuleBox density1 hk0_0_17 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule true false 0 17) := by
  rw [← checked]
  exact @cached_density_rule_contains density1 hk0_0_17 (tableDensity true) (fullFactor false 0 17) density1_contains hk0_0_17_contains
noncomputable def atomAnswer : CBox := ⟨⟨2086988954513339611343,2086988954513339611485⟩,⟨25804205982722371665601,25804205982722371667132⟩⟩
lemma atomChecked : tableAtomBox true ha0_0_17 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom true false 0 17) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains true false ha0_0_17 0 17 ha0_0_17_contains
 def realAnswer : RBox := ⟨(-221057097607106827754),(-221057097606615388913)⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment true false 0 17) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm0_1_0_17
namespace hm0_0_0_18
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density0 j i k).mul (hk0_0_18 j i k))
noncomputable def s0_0 : CBox := ⟨⟨(-132326567),(-132326551)⟩,⟨(-96666348),(-96666332)⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨(-282151131),(-282151115)⟩,⟨(-201168075),(-201168059)⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨(-235895801),(-235895785)⟩,⟨(-160309371),(-160309355)⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨(-115357092),(-115357076)⟩,⟨(-73153342),(-73153326)⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨(-35239734),(-35239718)⟩,⟨(-20519783),(-20519766)⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨(-6724889),(-6724872)⟩,⟨(-3556875),(-3556857)⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨(-778407),(-778390)⟩,⟨(-370480),(-370464)⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨(-51894),(-51875)⟩,⟨(-21969),(-21953)⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨(-1850),(-1834)⟩,⟨(-690),(-672)⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨(-40),(-23)⟩,⟨(-21),(-5)⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨(-16),0⟩,⟨(-16),0⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨(-16),0⟩,⟨(-16),0⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨(-16),0⟩,⟨(-16),0⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨(-16),0⟩,⟨(-16),0⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨(-16),0⟩,⟨(-16),0⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨(-16),0⟩,⟨(-16),0⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨(-21845091203613),(-21845091203597)⟩,⟨(-31361005065206),(-31361005065190)⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨(-55045568202540),(-55045568202524)⟩,⟨(-78191841896071),(-78191841896053)⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨(-64725315228318),(-64725315228302)⟩,⟨(-90060393282309),(-90060393282293)⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨(-53813594954357),(-53813594954339)⟩,⟨(-72658861609901),(-72658861609885)⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨(-34723865362326),(-34723865362309)⟩,⟨(-45088756367451),(-45088756367434)⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨(-18128638293911),(-18128638293893)⟩,⟨(-22441706857117),(-22441706857101)⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨(-7873601424883),(-7873601424867)⟩,⟨(-9221236565738),(-9221236565722)⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨(-2915067550230),(-2915067550213)⟩,⟨(-3213819762549),(-3213819762532)⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨(-944424724857),(-944424724840)⟩,⟨(-978606234466),(-978606234449)⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨(-276401749015),(-276401748999)⟩,⟨(-269531475525),(-269531475506)⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨(-76039904327),(-76039904311)⟩,⟨(-69990026352),(-69990026334)⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨(-20627912907),(-20627912888)⟩,⟨(-17987751499),(-17987751483)⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨(-5808444230),(-5808444212)⟩,⟨(-4821608534),(-4821608518)⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨(-1766594587),(-1766594571)⟩,⟨(-1406708132),(-1406708116)⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨(-570469233),(-570469217)⟩,⟨(-440751049),(-440751031)⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨(-137147439),(-137147423)⟩,⟨(-104299319),(-104299303)⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨656203362878729,656203362878745⟩,⟨(-40953807730690421),(-40953807730690405)⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨295926831377904,295926831377920⟩,⟨(-108765859475513506),(-108765859475513490)⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨(-3280860043140320),(-3280860043140304)⟩,⟨(-142331584883311936),(-142331584883311920)⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨(-8233433036381525),(-8233433036381509)⟩,⟨(-139448880001820731),(-139448880001820715)⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨(-11423618194646457),(-11423618194646441)⟩,⟨(-112493385669459756),(-112493385669459739)⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨(-11442373890799954),(-11442373890799937)⟩,⟨(-77864095322631766),(-77864095322631750)⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨(-9177691826006140),(-9177691826006124)⟩,⟨(-47451667986821325),(-47451667986821308)⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨(-6262343357922756),(-6262343357922740)⟩,⟨(-26034789048235272),(-26034789048235255)⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨(-3791537271232679),(-3791537271232663)⟩,⟨(-13158852555615135),(-13158852555615117)⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨(-2107371168458408),(-2107371168458392)⟩,⟨(-6279771550914324),(-6279771550914307)⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨(-1107964604153418),(-1107964604153402)⟩,⟨(-2903960787173551),(-2903960787173535)⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨(-565092644890217),(-565092644890201)⟩,⟨(-1334141550067615),(-1334141550067597)⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨(-284259891203240),(-284259891203223)⟩,⟨(-620038682963399),(-620038682963382)⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨(-140797116094935),(-140797116094919)⟩,⟨(-290914381060681),(-290914381060664)⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨(-64791971330522),(-64791971330506)⟩,⟨(-129576550892781),(-129576550892765)⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨(-18778172315005),(-18778172314989)⟩,⟨(-36990734961938),(-36990734961922)⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨1441494196030071168,1441494196030077791⟩,⟨(-3933152766611887571),(-3933152766611880947)⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨3868315209808809132,3868315209808823416⟩,⟨(-10816887170940605126),(-10816887170940590841)⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨5167269494321820715,5167269494321832819⟩,⟨(-15148899258790095315),(-15148899258790083210)⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨5213702086611546822,5213702086611552759⟩,⟨(-16361326650177760372),(-16361326650177754432)⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨4353437753392852320,4353437753392854132⟩,⟨(-14943322315595394032),(-14943322315595392216)⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨3116394753967386901,3116394753967387261⟩,⟨(-12020369758822546763),(-12020369758822546397)⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨1952891454510842356,1952891454510842417⟩,⟨(-8744452514916858541),(-8744452514916858477)⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨1093402478199980753,1093402478199980772⟩,⟨(-5873906557464466754),(-5873906557464466732)⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨559332034082169280,559332034082169297⟩,⟨(-3708149039249359305),(-3708149039249359288)⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨267395787926689048,267395787926689064⟩,⟨(-2235374137673127432),(-2235374137673127416)⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨121849136623596379,121849136623596395⟩,⟨(-1305783934410895302),(-1305783934410895285)⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨53578012056550733,53578012056550749⟩,⟨(-748141007005026154),(-748141007005026137)⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨22782397958467915,22782397958467931⟩,⟨(-422678211625933010),(-422678211625932994)⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨9297425163394978,9297425163394994⟩,⟨(-232392533212627733),(-232392533212627717)⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨3507174593999452,3507174593999468⟩,⟨(-115816632419152002),(-115816632419151986)⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨884720253199141,884720253199157⟩,⟨(-35051814708823777),(-35051814708823761)⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨144630314118775148798,144630314118776243072⟩,⟨(-8108234405371250196),(-8108234405370155910)⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨398493487324623426521,398493487324627306377⟩,⟨(-31954373300805981450),(-31954373300802101551)⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨561326602144273393707,561326602144282053110⟩,⟨(-72350517962929937033),(-72350517962921277567)⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨614600046110442090558,614600046110459248630⟩,⟨(-123853449846920797814),(-123853449846903639668)⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨575666889531823205254,575666889531853576755⟩,⟨(-169586898573308789581),(-169586898573278418008)⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨480351560304113392756,480351560304159197985⟩,⟨(-193541994298530843871),(-193541994298485038574)⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨365118874707084759317,365118874707139956652⟩,⟨(-191039670023007858570),(-191039670022952661181)⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨256923249117600945022,256923249117651288338⟩,⟨(-168416752587898668919),(-168416752587848325564)⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨169866702894407092004,169866702894442145385⟩,⟨(-136128296629755137598),(-136128296629720084181)⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨107093856692778560155,107093856692797516351⟩,⟨(-103050689613441558887),(-103050689613422602669)⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨65352218488793863239,65352218488801895453⟩,⟨(-74299927154757505009),(-74299927154749472779)⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨39151413346817244024,39151413346820131047⟩,⟨(-51541183670077171917),(-51541183670074284887)⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨23189400125105229606,23189400125106191706⟩,⟨(-34349588442862568711),(-34349588442861606601)⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨13360384533609985101,13360384533610303857⟩,⟨(-21517180221381985395),(-21517180221381666634)⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨6917645042971138472,6917645042971244879⟩,⟨(-11725329636740200476),(-11725329636740094066)⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨2138852213249526101,2138852213249551864⟩,⟨(-3712566061590448826),(-3712566061590423064)⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨13025909152642946554,13025909152642946823⟩,⟨1033619464292891034758,1033619464292891035196⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨179981591560705061436,179981591560705062200⟩,⟨2896529759433128065196,2896529759433128066429⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨662955694288899089433,662955694288899090639⟩,⟨4234241195294275698727,4234241195294275700581⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨1387162545652370252390,1387162545652370253947⟩,⟨4923262528881075933074,4923262528881075935309⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨2077184479479380105841,2077184479479380107628⟩,⟨4990475344156562776906,4990475344156562779286⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨2485408425837080165308,2485408425837080167249⟩,⟨4533088996623461083002,4533088996623461085400⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨2556818828353579283193,2556818828353579285451⟩,⟨3724498593107272639918,3724498593107272642482⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨2374921251747007378929,2374921251747007382872⟩,⟨2799196063354076267110,2799196063354076271229⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨2049565664452328988522,2049565664452329002966⟩,⟨1955374871216700771231,1955374871216700785742⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨1670819856991574873486,1670819856991574943469⟩,⟨1292560704237494430668,1292560704237494500653⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨1299339901042546152691,1299339901042546433766⟩,⟨824297555452016437769,824297555452016718816⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨966432700273557018411,966432700273557835227⟩,⟨516912541825932740082,516912541825933556862⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨682229542645291485734,682229542645293130727⟩,⟨321345795498295617180,321345795498297262136⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨445876511977514759689,445876511977517037449⟩,⟨193642947821857366531,193642947821859644269⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨249710881665112065156,249710881665114119047⟩,⟨103631465539633998527,103631465539636052400⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨80128355986634279891,80128355986635107684⟩,⟨32586501056527101259,32586501056527929044⟩⟩
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
noncomputable def ans : CBox := ⟨⟨3838821993789645378527,3838821993789693194102⟩,⟨5480453586526703089346,5480453586526750905583⟩⟩
lemma checked : cachedMomentRuleBox density0 hk0_0_18 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule false false 0 18) := by
  rw [← checked]
  exact @cached_density_rule_contains density0 hk0_0_18 (tableDensity false) (fullFactor false 0 18) density0_contains hk0_0_18_contains
noncomputable def atomAnswer : CBox := ⟨⟨3471739243130349748593,3471739243130349748809⟩,⟨(-232647668234464728159),(-232647668234464728141)⟩⟩
lemma atomChecked : tableAtomBox false ha0_0_18 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom false false 0 18) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains false false ha0_0_18 0 18 ha0_0_18_contains
 def realAnswer : RBox := ⟨7310561236919895127120,7310561236920142942911⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment false false 0 18) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm0_0_0_18
namespace hm0_1_0_18
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density1 j i k).mul (hk0_0_18 j i k))
noncomputable def s0_0 : CBox := ⟨⟨(-20250489),(-20250473)⟩,⟨(-19370975),(-19370959)⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨(-43171009),(-43170993)⟩,⟨(-40961342),(-40961326)⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨(-35868032),(-35868016)⟩,⟨(-33508607),(-33508591)⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨(-17232145),(-17232129)⟩,⟨(-15637948),(-15637932)⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨(-5138296),(-5138280)⟩,⟨(-4378722),(-4378706)⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨(-967764),(-967748)⟩,⟨(-727818),(-727802)⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨(-113618),(-113602)⟩,⟨(-69823),(-69807)⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨(-7901),(-7884)⟩,⟨(-3724),(-3708)⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨(-302),(-286)⟩,⟨(-112),(-96)⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨(-17),(-1)⟩,⟨(-16),0⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨(-16),0⟩,⟨(-16),0⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨(-16),0⟩,⟨(-16),0⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨(-16),0⟩,⟨(-16),0⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨(-16),0⟩,⟨(-16),0⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨(-16),0⟩,⟨(-16),0⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨(-16),0⟩,⟨(-16),0⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨(-670749891045),(-670749891029)⟩,⟨(-5923384217836),(-5923384217820)⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨(-1904672028738),(-1904672028722)⟩,⟨(-14600451026260),(-14600451026244)⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨(-2742019457367),(-2742019457351)⟩,⟨(-16467805803735),(-16467805803719)⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨(-2894032807501),(-2894032807485)⟩,⟨(-12942237479043),(-12942237479027)⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨(-2365654704372),(-2365654704356)⟩,⟨(-7834804099604),(-7834804099588)⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨(-1520822007735),(-1520822007719)⟩,⟨(-3835976401115),(-3835976401099)⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨(-781344273370),(-781344273354)⟩,⟨(-1567613550905),(-1567613550889)⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨(-329829405431),(-329829405414)⟩,⟨(-548080846638),(-548080846622)⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨(-118734331076),(-118734331060)⟩,⟨(-168413043156),(-168413043140)⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨(-37996661832),(-37996661816)⟩,⟨(-47125180463),(-47125180447)⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨(-11288998826),(-11288998810)⟩,⟨(-12568885114),(-12568885098)⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨(-3257023173),(-3257023157)⟩,⟨(-3363772245),(-3363772229)⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨(-956147657),(-956147641)⟩,⟨(-947333703),(-947333687)⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨(-297387414),(-297387398)⟩,⟨(-289650659),(-289650643)⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨(-96927785),(-96927769)⟩,⟨(-93937956),(-93937940)⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨(-23368289),(-23368273)⟩,⟨(-22627061),(-22627045)⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨4971584035592467,4971584035592483⟩,⟨(-7796968011274060),(-7796968011274043)⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨13032479246757793,13032479246757809⟩,⟨(-20847368180059305),(-20847368180059289)⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨16608526758925087,16608526758925103⟩,⟨(-27477192495126714),(-27477192495126698)⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨15544027214588643,15544027214588659⟩,⟨(-26881381801381597),(-26881381801381581)⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨11577778570333397,11577778570333413⟩,⟨(-21373060507216143),(-21373060507216127)⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨7021401468357166,7021401468357183⟩,⟨(-14477635908799708),(-14477635908799692)⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨3508833284693746,3508833284693762⟩,⟨(-8678721633809879),(-8678721633809862)⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨1464168312494097,1464168312494113⟩,⟨(-4748227954287813),(-4748227954287797)⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨516674833588623,516674833588639⟩,⟨(-2426814059921730),(-2426814059921714)⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨155511708998250,155511708998266⟩,⟨(-1180117990727719),(-1180117990727702)⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨39674326832491,39674326832507⟩,⟨(-554659149888841),(-554659149888825)⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨7563820880178,7563820880194⟩,⟨(-255674336645690),(-255674336645673)⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨(-377713675282),(-377713675265)⟩,⟨(-117214634260902),(-117214634260886)⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨(-1850254985409),(-1850254985392)⟩,⟨(-53676023992008),(-53676023991992)⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨(-1470067613684),(-1470067613668)⟩,⟨(-23358729789734),(-23358729789718)⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨(-530176206597),(-530176206581)⟩,⟨(-6579668126319),(-6579668126303)⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨1172211944479460459,1172211944479466026⟩,⟨(-766012005461772446),(-766012005461766878)⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨3156086398479301932,3156086398479313927⟩,⟨(-2086519291496404479),(-2086519291496392484)⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨4238300524007493508,4238300524007503662⟩,⟨(-2880575460090092782),(-2880575460090082633)⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨4309462691242041671,4309462691242046639⟩,⟨(-3081299202090147353),(-3081299202090142386)⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨3662012432286470115,3662012432286471630⟩,⟨(-2827004166102384244),(-2827004166102382727)⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨2735846906194915875,2735846906194916181⟩,⟨(-2318370834387857964),(-2318370834387857660)⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨1859263938772955835,1859263938772955886⟩,⟨(-1727989951668511526),(-1727989951668511473)⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨1174464266075882500,1174464266075882522⟩,⟨(-1183636086452132651),(-1183636086452132629)⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨699632737050163807,699632737050163824⟩,⟨(-756869250311993437),(-756869250311993420)⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨398533640150513860,398533640150513877⟩,⟨(-460970505296926933),(-460970505296926916)⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨220655037995615664,220655037995615680⟩,⟨(-272827675760593493),(-272827675760593477)⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨120770543370101721,120770543370101737⟩,⟨(-159206699738714680),(-159206699738714664)⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨65972384220741738,65972384220741755⟩,⟨(-91891966429046745),(-91891966429046729)⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨35516374426247756,35516374426247772⟩,⟨(-51552669745534266),(-51552669745534250)⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨17507174669089851,17507174669089867⟩,⟨(-26088173324699053),(-26088173324699037)⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨5275795249314201,5275795249314217⟩,⟨(-7960184127784041),(-7960184127784025)⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨47319831590055206613,47319831590056105949⟩,⟨(-5091929652122519623),(-5091929652121620294)⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨133018398279270189132,133018398279273378029⟩,⟨(-16350403327456670956),(-16350403327453482078)⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨193867852263739918172,193867852263747036336⟩,⟨(-28980720450749069686),(-28980720450741951549)⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨220363732472207802089,220363732472221908497⟩,⟨(-40634113450702149481),(-40634113450688043106)⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨212986224828749012018,212986224828773984787⟩,⟨(-49088730189387361800),(-49088730189362389062)⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨182265915487857234882,182265915487894897934⟩,⟨(-53466539066276534236),(-53466539066238871209)⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨142579059990980345136,142579059991025721353⟩,⟨(-53125168698885422971),(-53125168698840046771)⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨104746759152917928123,104746759152959294115⟩,⟨(-47962493956714850803),(-47962493956673484825)⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨73725950904959091536,73725950904987871477⟩,⟨(-39344253635765779992),(-39344253635737000060)⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨50322619325527600558,50322619325543147708⟩,⟨(-29526402528013402885),(-29526402527997855743)⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨33446674012486726081,33446674012493305467⟩,⟨(-20480906012258288432),(-20480906012251709048)⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨21570998316694863429,21570998316697225075⟩,⟨(-13306835579271575482),(-13306835579269213835)⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨13380731593037170166,13380731593037956185⟩,⟨(-8222099648030784354),(-8222099648029998340)⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨7838725106984716063,7838725106984976207⟩,⟨(-4832910115950756577),(-4832910115950496436)⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨4054645493802193641,4054645493802280419⟩,⟨(-2531188752223890401),(-2531188752223803625)⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨1248042556967613435,1248042556967634439⟩,⟨(-787724233902249070),(-787724233902228068)⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨1843519630333553644,1843519630333553829⟩,⟨30688300705571705808,30688300705571706076⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨25985122287781425521,25985122287781426035⟩,⟨80782069430289182482,80782069430289183233⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨104676841241383134929,104676841241383135734⟩,⟨78522510231819921141,78522510231819922276⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨269933443136416588280,269933443136416589318⟩,⟨(-27594408093225664835),(-27594408093225663437)⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨547949289162569722431,547949289162569723630⟩,⟨(-221119862432080877579),(-221119862432080876047)⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨895978683531252655018,895978683531252656368⟩,⟨(-387994807129264043508),(-387994807129264041880)⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨1182680079184507360795,1182680079184507362464⟩,⟨(-428103372907781891682),(-428103372907781889809)⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨1294651550321768150603,1294651550321768153750⟩,⟨(-350244353421081770795),(-350244353421081767518)⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨1221167013329274944760,1221167013329274956606⟩,⟨(-227822529788655885123),(-227822529788655873220)⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨1027670360681961782351,1027670360681961839656⟩,⟨(-122233015190100418553),(-122233015190100361225)⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨793464765117147040860,793464765117147270522⟩,⟨(-57339712203030998867),(-57339712203030769205)⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨574816833841627729454,574816833841628396573⟩,⟨(-28613602340127056032),(-28613602340126388920)⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨395987759811157431271,395987759811158775195⟩,⟨(-19566393931573140661),(-19566393931571796749)⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨256290663065260268888,256290663065262130620⟩,⟨(-15695915005150817719),(-15695915005148955997)⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨143932087996011871479,143932087996013550854⟩,⟨(-10614271527345412456),(-10614271527343733082)⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨46424776181011823460,46424776181012500445⟩,⟨(-3747516275494774357),(-3747516275494097372)⟩⟩
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
noncomputable def ans : CBox := ⟨⟨1708355815549640799164,1708355815549680080208⟩,⟨(-357210839316967611406),(-357210839316928330061)⟩⟩
lemma checked : cachedMomentRuleBox density1 hk0_0_18 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule true false 0 18) := by
  rw [← checked]
  exact @cached_density_rule_contains density1 hk0_0_18 (tableDensity true) (fullFactor false 0 18) density1_contains hk0_0_18_contains
noncomputable def atomAnswer : CBox := ⟨⟨(-4539966702555072748442),(-4539966702555072748161)⟩,⟨304231566152761567569,304231566152761567592⟩⟩
lemma atomChecked : tableAtomBox true ha0_0_18 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom true false 0 18) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains true false ha0_0_18 0 18 ha0_0_18_contains
 def realAnswer : RBox := ⟨(-2831610887005531949278),(-2831610887005292667953)⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment true false 0 18) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm0_1_0_18
namespace hm0_0_0_19
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density0 j i k).mul (hk0_0_19 j i k))
noncomputable def s0_0 : CBox := ⟨⟨2651513,2651530⟩,⟨(-3629640),(-3629624)⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨5418814,5418830⟩,⟨(-7599553),(-7599537)⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨4163039,4163055⟩,⟨(-6124434),(-6124418)⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨1796683,1796699⟩,⟨(-2831996),(-2831980)⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨467087,467103⟩,⟨(-801665),(-801649)⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨73413,73429⟩,⟨(-138709),(-138693)⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨6762,6778⟩,⟨(-14219),(-14202)⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨337,353⟩,⟨(-824),(-808)⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨4,20⟩,⟨(-35),(-18)⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨0,16⟩,⟨(-16),0⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨0,16⟩,⟨(-16),0⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨0,16⟩,⟨(-16),0⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨0,16⟩,⟨(-16),0⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨0,16⟩,⟨(-16),0⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨0,16⟩,⟨(-16),0⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨0,16⟩,⟨(-16),0⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨1724397864333,1724397864350⟩,⟨(-1201158759705),(-1201158759689)⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨4259592236775,4259592236792⟩,⟨(-2998613833786),(-2998613833770)⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨4816091139086,4816091139103⟩,⟨(-3461088424815),(-3461088424799)⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨3779877312140,3779877312156⟩,⟨(-2799236547327),(-2799236547310)⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨2261984386632,2261984386648⟩,⟨(-1741743916706),(-1741743916690)⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨1076738251970,1076738251987⟩,⟨(-869617010182),(-869617010166)⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨419917275875,419917275892⟩,⟨(-358453070144),(-358453070127)⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨137979414339,137979414357⟩,⟨(-125114898074),(-125114898056)⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨39399613236,39399613252⟩,⟨(-38011279851),(-38011279832)⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨10140115875,10140115893⟩,⟨(-10395333713),(-10395333696)⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨2457639872,2457639889⟩,⟨(-2669303738),(-2669303721)⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨590657534,590657551⟩,⟨(-677180864),(-677180848)⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨148891573,148891590⟩,⟨(-179329971),(-179329955)⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨41254548,41254564⟩,⟨(-51802605),(-51802589)⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨12450146,12450162⟩,⟨(-16113570),(-16113553)⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨2888444,2888460⟩,⟨(-3798124),(-3798108)⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨3380431258155301,3380431258155318⟩,⟨54170835663333,54170835663349⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨8921810117531516,8921810117531532⟩,⟨24417039874535,24417039874551⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨11531246739420111,11531246739420128⟩,⟨(-265323985886653),(-265323985886637)⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨11092773157446682,11092773157446698⟩,⟨(-654145140614761),(-654145140614745)⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨8737775029187303,8737775029187319⟩,⟨(-886444214234550),(-886444214234534)⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨5876091677274106,5876091677274122⟩,⟨(-862803289158003),(-862803289157987)⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨3464277393372181,3464277393372198⟩,⟨(-669558952581080),(-669558952581063)⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨1832503073201334,1832503073201351⟩,⟨(-440514704094799),(-440514704094782)⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨890921317695667,890921317695684⟩,⟨(-256569399197413),(-256569399197396)⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨408582024074866,408582024074882⟩,⟨(-137050592714801),(-137050592714785)⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨181678820086025,181678820086041⟩,⟨(-69292121170147),(-69292121170131)⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨80449314997351,80449314997369⟩,⟨(-34066593508200),(-34066593508184)⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨36190108896267,36190108896283⟩,⟨(-16588944613466),(-16588944613450)⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨16536257640947,16536257640964⟩,⟨(-8002624667108),(-8002624667092)⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨7228846014369,7228846014386⟩,⟨(-3614534031487),(-3614534031471)⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨2043725681515,2043725681531⟩,⟨(-1037484778076),(-1037484778060)⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨433040023932062508,433040023932063249⟩,⟨158708875713205366,158708875713206110⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨1185336833614945567,1185336833614947149⟩,⟨423907270109099837,423907270109101417⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨1644650511802016894,1644650511802018224⟩,⟨561020180301828418,561020180301829749⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨1752119549594595472,1752119549594596124⟩,⟨558389259315976300,558389259315976950⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨1572151036917355092,1572151036917355299⟩,⟨458092196797914752,458092196797914959⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨1237994869709560153,1237994869709560207⟩,⟨321043734341394270,321043734341394323⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨879023480561604542,879023480561604562⟩,⟨196381162536827461,196381162536827483⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨575039337007238544,575039337007238564⟩,⟨107088949473494017,107088949473494033⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨353061456695302048,353061456695302064⟩,⟨53282727242560931,53282727242560947⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨206931473733880407,206931473733880423⟩,⟨24766774159140716,24766774159140732⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨117619487134439022,117619487134439038⟩,⟨10981717930188852,10981717930188868⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨65703703906995841,65703703906995859⟩,⟨4707863134707039,4707863134707055⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨36308253358362586,36308253358362602⟩,⟨1957954831393935,1957954831393951⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨19610678200258942,19610678200258958⟩,⟨784860277121653,784860277121669⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨9652220827265470,9652220827265486⟩,⟨292345279384903,292345279384919⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨2902530660731385,2902530660731401⟩,⟨73262836691853,73262836691869⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨1116123149016531698,1116123149016682347⟩,⟨19909489402399754984,19909489402399905631⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨4381257471747371820,4381257471747903833⟩,⟨54649270902389869818,54649270902390401819⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨9844875099203624239,9844875099204802505⟩,⟨76409212196977601407,76409212196978779665⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨16668754719344077761,16668754719346386473⟩,⟨82752322072989293894,82752322072991602597⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨22504143728370508783,22504143728374537602⟩,⟨76425497968932055874,76425497968936084683⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨25254258201067622617,25254258201073597174⟩,⟨62705600064803041946,62705600064809016498⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨24456867171940108724,24456867171947173528⟩,⟨46761342365124376056,46761342365131440851⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨21119055644967533043,21119055644973846853⟩,⟨32229666513264486375,32229666513270800180⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨16705334527949567400,16705334527953870847⟩,⟨20852845202865215350,20852845202869518794⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨12374579372221543479,12374579372223821625⟩,⟨12864089551047741538,12864089551050019679⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨8737229626052181719,8737229626053127233⟩,⟨7687058042939236034,7687058042940181547⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨5945254715560863938,5945254715561197310⟩,⟨4516999000677717765,4516999000678051132⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨3896524261759288857,3896524261759398103⟩,⟨2630872284455096242,2630872284455205486⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨2408466993105452844,2408466993105488555⟩,⟨1495550972807717237,1495550972807752951⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨1300269063714446304,1300269063714458122⟩,⟨767141765835319865,767141765835331682⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨409734381096436343,409734381096439200⟩,⟨236053245533755380,236053245533758239⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨(-170769895395537222228),(-170769895395537222141)⟩,⟨2151507780555675200,2151507780555675255⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨(-477046255940294134486),(-477046255940294134267)⟩,⟨29628195191732182201,29628195191732182339⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨(-693040343940933608688),(-693040343940933608369)⟩,⟨108458129189612342655,108458129189612342868⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨(-798512752927666053492),(-798512752927666053115)⟩,⟨224892026337837118304,224892026337837118568⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨(-799988057728859305018),(-799988057728859304621)⟩,⟨332862771572612415981,332862771572612416280⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨(-716601709871904831144),(-716601709871904830751)⟩,⟨392780496496383512263,392780496496383512584⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨(-579584048912833461467),(-579584048912833461054)⟩,⟨397758887834078777245,397758887834078777612⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨(-428246934997609284107),(-428246934997609283463)⟩,⟨363225465770259447767,363225465770259448387⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨(-293905956196841728689),(-293905956196841726500)⟩,⟨307966771440966035140,307966771440966037319⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨(-190869958310384613923),(-190869958310384603603)⟩,⟨246652981458097240269,246652981458097250586⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨(-119666760746880352639),(-119666760746880311914)⟩,⟨188582652840449867892,188582652840449908617⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨(-73878285228055906734),(-73878285228055790178)⟩,⟨138099648980120033276,138099648980120149838⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨(-45310566901828196808),(-45310566901827965086)⟩,⟨96186198474275384668,96186198474275616393⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨(-27011804027350959552),(-27011804027350641974)⟩,⟨62193739471317483969,62193739471317801551⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨(-14348043742425501867),(-14348043742425217541)⟩,⟨34572611024647225994,34572611024647510323⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨(-4494398564104513356),(-4494398564104399174)⟩,⟨11051453985137756503,11051453985137870688⟩⟩
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
noncomputable def ans : CBox := ⟨⟨(-874334236798414875766),(-874334236798408759476)⟩,⟨573805631417274708723,573805631417280824904⟩⟩
lemma checked : cachedMomentRuleBox density0 hk0_0_19 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule false false 0 19) := by
  rw [← checked]
  exact @cached_density_rule_contains density0 hk0_0_19 (tableDensity false) (fullFactor false 0 19) density0_contains hk0_0_19_contains
noncomputable def atomAnswer : CBox := ⟨⟨32114598548245550981,32114598548245550984⟩,⟨577846356976628256196,577846356976628256235⟩⟩
lemma atomChecked : tableAtomBox false ha0_0_19 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom false false 0 19) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains false false ha0_0_19 0 19 ha0_0_19_contains
 def realAnswer : RBox := ⟨(-842219638250269324785),(-842219638250063208492)⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment false false 0 19) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm0_0_0_19
namespace hm0_1_0_19
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density1 j i k).mul (hk0_0_19 j i k))
noncomputable def s0_0 : CBox := ⟨⟨531327,531343⟩,⟨(-555464),(-555448)⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨1103294,1103310⟩,⟨(-1162794),(-1162778)⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨870072,870088⟩,⟨(-931274),(-931258)⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨384044,384060⟩,⟨(-423109),(-423093)⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨99683,99699⟩,⟨(-116915),(-116899)⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨15026,15042⟩,⟨(-19968),(-19952)⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨1271,1287⟩,⟨(-2084),(-2067)⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨52,68⟩,⟨(-132),(-116)⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨0,16⟩,⟨(-16),0⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨0,16⟩,⟨(-16),0⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨0,16⟩,⟨(-16),0⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨0,16⟩,⟨(-16),0⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨0,16⟩,⟨(-16),0⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨0,16⟩,⟨(-16),0⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨0,16⟩,⟨(-16),0⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨0,16⟩,⟨(-16),0⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨325700528335,325700528351⟩,⟨(-36880420256),(-36880420240)⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨795393084616,795393084632⟩,⟨(-103735738976),(-103735738960)⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨880679987874,880679987890⟩,⟨(-146557921269),(-146557921253)⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨673333915352,673333915368⟩,⟨(-150438522166),(-150438522150)⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨393080195917,393080195933⟩,⟨(-118568590858),(-118568590842)⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨184055265443,184055265459⟩,⟨(-72897134674),(-72897134658)⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨71386104309,71386104325⟩,⟨(-35547608515),(-35547608499)⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨23530068838,23530068854⟩,⟨(-14148214821),(-14148214805)⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨6780037739,6780037756⟩,⟨(-4776448966),(-4776448950)⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨1772712111,1772712127⟩,⟨(-1428408054),(-1428408038)⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨441266639,441266655⟩,⟨(-396145125),(-396145109)⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨110429580,110429597⟩,⟨(-106896033),(-106896017)⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨29247411,29247427⟩,⟨(-29516277),(-29516261)⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨8493385,8493401⟩,⟨(-8720012),(-8719996)⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨2653360,2653376⟩,⟨(-2737815),(-2737799)⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨626617,626633⟩,⟨(-647159),(-647143)⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨643580828693680,643580828693696⟩,⟨410367903841454,410367903841470⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨1710049085207422,1710049085207438⟩,⟨1069040735702869,1069040735702885⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨2226100652200098,2226100652200114⟩,⟨1345630479129323,1345630479129339⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨2138371310432046,2138371310432062⟩,⟨1236617730936954,1236617730936970⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨1660199333152588,1660199333152604⟩,⟨899497496958009,899497496958025⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨1092629456712451,1092629456712467⟩,⟨530104993380142,530104993380159⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨633621050489818,633621050489835⟩,⟨256343037465834,256343037465850⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨334206609662107,334206609662123⟩,⟨103159029984181,103159029984197⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨164298732076959,164298732076975⟩,⟨35027198744834,35027198744850⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨76777436591722,76777436591738⟩,⟨10134828970841,10134828970857⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨34699657259548,34699657259564⟩,⟨2487292239088,2487292239104⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨15417533293670,15417533293687⟩,⟨457628151789,457628151805⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨6841873027739,6841873027755⟩,⟨(-21537431036),(-21537431020)⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨3051215257552,3051215257568⟩,⟨(-105005776382),(-105005776366)⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨1303170868198,1303170868214⟩,⟨(-81977537619),(-81977537603)⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨363525428756,363525428772⟩,⟨(-29290792191),(-29290792175)⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨84337992924338139,84337992924338769⟩,⟨129060783751699525,129060783751700152⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨228646938267486452,228646938267487778⟩,⟨345857096135198900,345857096135200230⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨312735954490962313,312735954490963428⟩,⟨460157543554700069,460157543554701187⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨329975176516511364,329975176516511913⟩,⟨461538469219609046,461538469219609594⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨297415830130944272,297415830130944446⟩,⟨385319292013352717,385319292013352889⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨238761203198693973,238761203198694022⟩,⟨281807489518770317,281807489518770362⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨173695212952022709,173695212952022728⟩,⟨186925325720951393,186925325720951412⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨115870616253267176,115870616253267192⟩,⟨114992186283908283,114992186283908299⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨72061527571630201,72061527571630217⟩,⟨66622497426670187,66622497426670203⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨42671566184494685,42671566184494701⟩,⟨36897481689823485,36897481689823501⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨24574314747114300,24574314747114316⟩,⟨19877843664354000,19877843664354016⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨13981385634806529,13981385634806545⟩,⟨10607209064728003,10607209064728019⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨7893283591397063,7893283591397079⟩,⟨5667306649613024,5667306649613041⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨4350225744077257,4350225744077274⟩,⟨2997141399777685,2997141399777701⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨2174182381254436,2174182381254452⟩,⟨1459065226378363,1459065226378379⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨659157126633588,659157126633604⟩,⟨436872245312685,436872245312701⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨700934014694372920,700934014694496732⟩,⟨6513932309761393889,6513932309761517699⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨2242066526841930544,2242066526842367804⟩,⟨18241848841494501490,18241848841494938751⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨3944173420571562997,3944173420572531544⟩,⟨26389000591045815584,26389000591046784132⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨5469692492411348983,5469692492413247065⟩,⟨29669572407823085107,29669572407824983198⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨6514786845262729216,6514786845266041876⟩,⟨28275029080570148667,28275029080573461334⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨6976704003947822546,6976704003952735087⟩,⟨23792290635552315859,23792290635557228402⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨6800830130681462606,6800830130687270383⟩,⟨18259266410375811481,18259266410381619261⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨6014137035961423374,6014137035966611296⟩,⟨13138694767458134490,13138694767463322413⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨4828191059254855637,4828191059258388908⟩,⟨9049414267040446696,9049414267043979970⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨3545752453940643583,3545752453942512035⟩,⟨6043826626461989325,6043826626463857776⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨2408652386127334908,2408652386128109403⟩,⟨3933622487810499018,3933622487811273514⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨1535110289921615626,1535110289921888333⟩,⟨2488473881485955726,2488473881486228436⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨932777746261839552,932777746261928808⟩,⟨1518008336245843669,1518008336245932919⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨540985048373406446,540985048373435596⟩,⟨877456979765867863,877456979765897008⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨280698166979246388,280698166979256028⟩,⟨449646815810334793,449646815810344431⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨86936689890316792,86936689890319124⟩,⟨137739609975914036,137739609975916368⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨(-5070187454928231353),(-5070187454928231296)⟩,⟨304496653580810947,304496653580810992⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨(-13305232978221025424),(-13305232978221025287)⟩,⟨4277557816897290245,4277557816897290343⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨(-12859259583298941761),(-12859259583298941561)⟩,⟨17123400255878021169,17123400255878021315⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨4452537706467998901,4452537706467999139⟩,⟨43752440078896622102,43752440078896622285⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨35408783365682641525,35408783365682641784⟩,⟨87776258980807164608,87776258980807164814⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨61301524319274232440,61301524319274232711⟩,⟨141543852609172180168,141543852609172180395⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨66602858184624264234,66602858184624264540⟩,⟨183934082982445426847,183934082982445427123⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨53583708935670001705,53583708935670002217⟩,⟨197970952031523368649,197970952031523369146⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨34250624407400379240,34250624407400381042⟩,⟨183476511527342992974,183476511527342994763⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨18057053606537473940,18057053606537482395⟩,⟨151706837499513163036,151706837499513171490⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨8327796170947598785,8327796170947632064⟩,⟨115164605967656729989,115164605967656763271⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨4089907408291963064,4089907408292058267⟩,⟨82142073884364139188,82142073884364234393⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨2758211508083961853,2758211508084151170⟩,⟨55830533664770389492,55830533664770578810⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨2188993319876204204,2188993319876463781⟩,⟨35749124211532118105,35749124211532377684⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨1469451627538113743,1469451627538346228⟩,⟨19927421629752616379,19927421629752848867⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨516860666174044866,516860666174138251⟩,⟨6402989257726069644,6402989257726163026⟩⟩
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
noncomputable def ans : CBox := ⟨⟨52759434826122700528,52759434826127725227⟩,⟨253062847441519849025,253062847441524873674⟩⟩
lemma checked : cachedMomentRuleBox density1 hk0_0_19 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule true false 0 19) := by
  rw [← checked]
  exact @cached_density_rule_contains density1 hk0_0_19 (tableDensity true) (fullFactor false 0 19) density1_contains hk0_0_19_contains
noncomputable def atomAnswer : CBox := ⟨⟨(-41996013486167258979),(-41996013486167258975)⟩,⟨(-755645236046360027384),(-755645236046360027334)⟩⟩
lemma atomChecked : tableAtomBox true ha0_0_19 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom true false 0 19) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains true false ha0_0_19 0 19 ha0_0_19_contains
 def realAnswer : RBox := ⟨10763421339855441549,10763421340060466252⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment true false 0 19) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm0_1_0_19
namespace hm0_0_0_20
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density0 j i k).mul (hk0_0_20 j i k))
noncomputable def s0_0 : CBox := ⟨⟨94573,94589⟩,⟨69085,69101⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨194458,194474⟩,⟨138668,138684⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨151075,151092⟩,⟨102713,102731⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨66063,66080⟩,⟨41929,41945⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨17327,17344⟩,⟨10100,10117⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨2710,2727⟩,⟨1432,1450⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨238,255⟩,⟨110,127⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨6,22⟩,⟨1,17⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨0,16⟩,⟨0,16⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨0,16⟩,⟨0,16⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨0,16⟩,⟨0,16⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨0,16⟩,⟨0,16⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨0,16⟩,⟨0,16⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨0,16⟩,⟨0,16⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨0,16⟩,⟨0,16⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨0,16⟩,⟨0,16⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨62743884229,62743884245⟩,⟨90076067413,90076067429⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨155185010935,155185010952⟩,⟨220447742974,220447742990⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨175830854635,175830854651⟩,⟨244680524018,244680524035⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨138340479623,138340479640⟩,⟨186822342891,186822342907⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨83008958841,83008958857⟩,⟨107818964108,107818964124⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨39636933216,39636933232⟩,⟨49087751453,49087751469⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨15506911529,15506911546⟩,⟨18170703222,18170703239⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨5103005282,5103005298⟩,⟨5629407477,5629407496⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨1453888566,1453888582⟩,⟨1507468556,1507468572⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨371550320,371550336⟩,⟨362540640,362540656⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨89049644,89049660⟩,⟨82011923,82011942⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨21125845,21125861⟩,⟨18431208,18431226⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨5261074,5261091⟩,⟨4368942,4368959⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨1443290,1443308⟩,⟨1149547,1149563⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨432410,432426⟩,⟨334115,334131⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨99918,99934⟩,⟨75983,75999⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨(-4248313791883),(-4248313791867)⟩,⟨265078134323394,265078134323410⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨(-1913873856258),(-1913873856242)⟩,⟨695248803214195,695248803214211⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨20384342912159,20384342912175⟩,⟨887531389865892,887531389865908⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨49375019125835,49375019125851⟩,⟨838311553054871,838311553054887⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨65350456924452,65350456924468⟩,⟨644798622379430,644798622379446⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨61811141956967,61811141956983⟩,⟨421307180268102,421307180268119⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨46410107663157,46410107663173⟩,⟨240293348758399,240293348758416⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨29441470033579,29441470033596⟩,⟨122549159682260,122549159682277⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨16495822311548,16495822311565⟩,⟨57311224758113,57311224758129⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨8468380744864,8468380744880⟩,⟨25257695985179,25257695985195⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨4117341219797,4117341219813⟩,⟨10799222980959,10799222980978⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨1951209858340,1951209858356⟩,⟨4609022055800,4609022055817⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨919763708115,919763708131⟩,⟨2006851503658,2006851503676⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨432128299448,432128299464⟩,⟨892998672080,892998672096⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨191564109632,191564109648⟩,⟨383126534279,383126534296⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨54454600449,54454600465⟩,⟨107269602958,107269602975⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨(-16600200937251840),(-16600200937251749)⟩,⟨45293832941771652,45293832941771745⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨(-44131157939771055),(-44131157939770874)⟩,⟨123397599053844806,123397599053844984⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨(-57866125289120138),(-57866125289119986)⟩,⟨169626900514607025,169626900514607177⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨(-56814695054068104),(-56814695054068024)⟩,⟨178255015859077259,178255015859077339⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨(-45794267072047443),(-45794267072047407)⟩,⟨157137231252360285,157137231252360323⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨(-31420894530825470),(-31420894530825451)⟩,⟨121133038416855108,121133038416855130⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨(-18761542203823016),(-18761542203822999)⟩,⟨83949004229351927,83949004229351945⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨(-9964589717275294),(-9964589717275278)⟩,⟨53483346385581055,53483346385581073⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨(-4822306341337573),(-4822306341337557)⟩,⟨31937097874812741,31937097874812758⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨(-2179391605851997),(-2179391605851981)⟩,⟨18199282749843180,18199282749843196⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨(-940299588883837),(-940299588883821)⟩,⟨10065510319608860,10065510319608876⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨(-393010822887176),(-393010822887160)⟩,⟨5482012897191394,5482012897191410⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨(-159861362360534),(-159861362360518)⟩,⟨2963048191191240,2963048191191256⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨(-62943901721442),(-62943901721426)⟩,⟨1572153107864730,1572153107864746⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨(-23150562295527),(-23150562295511)⟩,⟨764205846433788,764205846433804⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨(-5763488919502),(-5763488919486)⟩,⟨228332166243414,228332166243430⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨(-2603662290745647234),(-2603662290745627519)⟩,⟨145955906161320141,145955906161339855⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨(-7119873855776887665),(-7119873855776818349)⟩,⟨570679163409734446,570679163409803760⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨(-9881038107210378293),(-9881038107210225975)⟩,⟨1272639799867138075,1272639799867290394⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨(-10585154907507886715),(-10585154907507591586)⟩,⟨2131216695911506538,2131216695911801670⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨(-9639128904178443364),(-9639128904177935636)⟩,⟨2837038172634161083,2837038172634668812⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨(-7776586202668186141),(-7776586202667445790)⟩,⟨3130614586593654964,3130614586594395317⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨(-5689548921609627235),(-5689548921608768170)⟩,⟨2974516270585679282,2974516270586538349⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨(-3841034723684080448),(-3841034723683328152)⟩,⟨2515960490866256258,2515960490867008553⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨(-2431997420090831169),(-2431997420090329228)⟩,⟨1947613532196539632,1947613532197041573⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨(-1468025814468482699),(-1468025814468222581)⟩,⟨1411725421916495481,1411725421916755601⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨(-859010066148037692),(-859010066147931941)⟩,⟨976107073638576995,976107073638682746⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨(-495094247630887461),(-495094247630850879)⟩,⟨651511262219197091,651511262219233673⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨(-283557939139631399),(-283557939139619603)⟩,⟨419918535119889661,419918535119901457⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨(-159041967457909852),(-159041967457906036)⟩,⟨256108683532531096,256108683532534909⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨(-80819914562395578),(-80819914562394321)⟩,⟨136983041381342939,136983041381344201⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨(-24749303776265064),(-24749303776264754)⟩,⟨42959027014601561,42959027014601874⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨(-337599242485120782),(-337599242485120760)⟩,⟨(-26803138051722589909),(-26803138051722589881)⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨(-4633473015185331570),(-4633473015185331536)⟩,⟨(-74639274684755965234),(-74639274684755965185)⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨(-16856422884516326178),(-16856422884516326131)⟩,⟨(-107762392884328966017),(-107762392884328965955)⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨(-34637643024579794413),(-34637643024579794356)⟩,⟨(-123037739283625602804),(-123037739283625602733)⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨(-50673985908564651169),(-50673985908564651107)⟩,⟨(-121830155989632556208),(-121830155989632556133)⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨(-58970367350707880875),(-58970367350707880813)⟩,⟨(-107620051038177794974),(-107620051038177794900)⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨(-58785926351143602013),(-58785926351143601948)⟩,⟨(-85683762922860265707),(-85683762922860265635)⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨(-52776196213468153562),(-52776196213468153457)⟩,⟨(-62242906849540766512),(-62242906849540766403)⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨(-43962360591711988113),(-43962360591711987787)⟩,⟨(-41968340114340218784),(-41968340114340218460)⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨(-34592165271366287264),(-34592165271366285808)⟩,⟨(-26776806211991657735),(-26776806211991656275)⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨(-26002434170069068319),(-26002434170069062702)⟩,⟨(-16504269539378862252),(-16504269539378856635)⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨(-18747563023974587999),(-18747563023974572186)⟩,⟨(-10031082634102126884),(-10031082634102111070)⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨(-12883205143644452287),(-12883205143644421263)⟩,⟨(-6069533107731174119),(-6069533107731143094)⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨(-8241482695733584103),(-8241482695733542024)⟩,⟨(-3579580218887726025),(-3579580218887683948)⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨(-4547279535369997772),(-4547279535369960367)⟩,⟨(-1887202505392817687),(-1887202505392780283)⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨(-1448025949420589406),(-1448025949420574434)⟩,⟨(-588883210853611159),(-588883210853596186)⟩⟩
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
noncomputable def ans : CBox := ⟨⟨(-81887349206783366297),(-81887349206782621604)⟩,⟨(-132432644427025591707),(-132432644427024846993)⟩⟩
lemma checked : cachedMomentRuleBox density0 hk0_0_20 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule false false 0 20) := by
  rw [← checked]
  exact @cached_density_rule_contains density0 hk0_0_20 (tableDensity false) (fullFactor false 0 20) density0_contains hk0_0_20_contains
noncomputable def atomAnswer : CBox := ⟨⟨(-91264053655252246533),(-91264053655252246525)⟩,⟨4209893462666587758,4209893462666587760⟩⟩
lemma atomChecked : tableAtomBox false ha0_0_20 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom false false 0 20) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains false false ha0_0_20 0 20 ha0_0_20_contains
 def realAnswer : RBox := ⟨(-173151402862135612830),(-173151402861934868129)⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment false false 0 20) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm0_0_0_20
namespace hm0_1_0_20
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density1 j i k).mul (hk0_0_20 j i k))
noncomputable def s0_0 : CBox := ⟨⟨14467,14483⟩,⟨13837,13853⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨29746,29762⟩,⟨28225,28241⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨22969,22985⟩,⟨21458,21474⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨9866,9882⟩,⟨8957,8973⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨2519,2535⟩,⟨2151,2167⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨383,399⟩,⟨288,304⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨28,44⟩,⟨14,30⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨0,16⟩,⟨0,16⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨0,16⟩,⟨0,16⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨0,16⟩,⟨0,16⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨0,16⟩,⟨0,16⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨0,16⟩,⟨0,16⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨0,16⟩,⟨0,16⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨0,16⟩,⟨0,16⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨0,16⟩,⟨0,16⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨0,16⟩,⟨0,16⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨1926440264,1926440280⟩,⟨17013413577,17013413593⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨5367445837,5367445853⟩,⟨41165025883,41165025899⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨7442040890,7442040906⟩,⟨44744982632,44744982648⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨7429800298,7429800314⟩,⟨33282316984,33282317000⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨5646420043,5646420059⟩,⟨18737787461,18737787477⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨3320113178,3320113194⟩,⟨8391300129,8391300146⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨1536787841,1536787857⟩,⟨3089027677,3089027693⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨576729401,576729417⟩,⟨959969658,959969674⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨182603496,182603512⟩,⟨259394690,259394706⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨51031954,51031970⟩,⟨63372991,63373008⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨13210888,13210904⟩,⟨14722536,14722552⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨3333975,3333991⟩,⟨3445114,3445130⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨865812,865828⟩,⟨858019,858036⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨242934,242950⟩,⟨236626,236642⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨73460,73476⟩,⟨71196,71212⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨17016,17032⟩,⟨16478,16494⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨(-32179253242683),(-32179253242667)⟩,⟨50466643302008,50466643302024⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨(-83308316718922),(-83308316718905)⟩,⟨133257852665282,133257852665298⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨(-103574533637920),(-103574533637904)⟩,⟨171336429593608,171336429593624⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨(-93464686599297),(-93464686599281)⟩,⟨161605022584184,161605022584200⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨(-66393240837147),(-66393240837131)⟩,⟨122518901779261,122518901779277⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨(-38024061720038),(-38024061720022)⟩,⟨78344245100013,78344245100030⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨(-17792923798369),(-17792923798353)⟩,⟨43951261173707,43951261173723⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨(-6905528485168),(-6905528485152)⟩,⟨22349794322837,22349794322854⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨(-2256161525216),(-2256161525200)⟩,⟨10568443134934,10568443134950⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨(-627546172122),(-627546172106)⟩,⟨4745925624538,4745925624554⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨(-148154420455),(-148154420439)⟩,⟨2062523292808,2062523292825⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨(-26305235568),(-26305235552)⟩,⟨883300759243,883300759259⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨1166154963,1166154979⟩,⟨379421882093,379421882109⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨5661559066,5661559082⟩,⟨164780901645,164780901661⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨4342933060,4342933076⟩,⟨69069163756,69069163772⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨1537327615,1537327631⟩,⟨19080512279,19080512295⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨(-13499145136636494),(-13499145136636415)⟩,⟨8821344024692849,8821344024692928⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨(-36005591212552669),(-36005591212552516)⟩,⟨23803116670420418,23803116670420571⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨(-47462421661039506),(-47462421661039374)⟩,⟨32255585266912608,32255585266912734⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨(-46959716954068254),(-46959716954068184)⟩,⟨33570783403545720,33570783403545791⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨(-38517614653275747),(-38517614653275712)⟩,⟨29726203940023738,29726203940023770⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨(-27577568116775259),(-27577568116775239)⟩,⟨23360782245765689,23360782245765708⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨(-17854282400826284),(-17854282400826267)⟩,⟨16587530162971025,16587530162971042⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨(-10696637334101078),(-10696637334101062)⟩,⟨10776530110594270,10776530110594286⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨(-6027311257351716),(-6027311257351700)⟩,⟨6518356255236687,6518356255236703⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨(-3245486261510179),(-3245486261510163)⟩,⟨3752800172229199,3752800172229215⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨(-1701269782233935),(-1701269782233919)⟩,⟨2102921161821929,2102921161821945⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨(-885085063267748),(-885085063267732)⟩,⟨1166495101089845,1166495101089861⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨(-462518485391666),(-462518485391650)⟩,⟨644133286160760,644133286160776⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨(-240279997734607),(-240279997734591)⟩,⟨348741968127016,348741968127032⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨(-115520787135065),(-115520787135049)⟩,⟨172137330563667,172137330563684⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨(-34367263195534),(-34367263195518)⟩,⟨51853581985242,51853581985258⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨(-851857654549793358),(-851857654549777153)⟩,⟨91663326632222641,91663326632238844⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨(-2376570895492746241),(-2376570895492689270)⟩,⟨292074270055037644,292074270055094613⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨(-3412454287221273001),(-3412454287221147788)⟩,⟨509952326927249302,509952326927374513⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨(-3795000916922618018),(-3795000916922375377)⟩,⟨699462554179814171,699462554180056814⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨(-3566047251131578683),(-3566047251131161206)⟩,⟨821393275027370799,821393275027788278⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨(-2950547442217713081),(-2950547442217104327)⟩,⟨864876560776069411,864876560776678163⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨(-2221514284545338326),(-2221514284544632110)⟩,⟨827107202688411327,827107202689117543⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨(-1565683280571494077),(-1565683280570875928)⟩,⟨716448538021483978,716448538022102126⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨(-1055264550027448211),(-1055264550027036099)⟩,⟨562896323246122084,562896323246534201⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨(-689605892631360991),(-689605892631147648)⟩,⟨404526060617364958,404526060617578303⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨(-439511995259149324),(-439511995259062698)⟩,⟨269114685851844001,269114685851930630⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨(-272728976620885020),(-272728976620855091)⟩,⟨168244053692655309,168244053692685237⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨(-163606385019634301),(-163606385019624661)⟩,⟨100532252571174606,100532252571184248⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨(-93311353210777248),(-93311353210774132)⟩,⟨57529429349129723,57529429349132839⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨(-47371328042018368),(-47371328042017338)⟩,⟨29571954318389361,29571954318390391⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨(-14441493694796624),(-14441493694796364)⟩,⟨9114981806409756,9114981806410013⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨(-47779428215346413),(-47779428215346393)⟩,⟨(-795790754293872160),(-795790754293872134)⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨(-668946431681915683),(-668946431681915653)⟩,⟨(-2081873838245384498),(-2081873838245384461)⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨(-2661062651394756933),(-2661062651394756899)⟩,⟨(-2000614177628944072),(-2000614177628944028)⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨(-6737137235940816267),(-6737137235940816226)⟩,⟨682512712215214923,682512712215214975⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨(-13358060027241540732),(-13358060027241540688)⟩,⟨5386709952624013920,5386709952624013974⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨(-21243010473069679420),(-21243010473069679374)⟩,⟨9201281302261568192,9201281302261568244⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨(-27176319930734598804),(-27176319930734598745)⟩,⟨9843976129116747066,9843976129116747124⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨(-28759726589742879391),(-28759726589742879305)⟩,⟨7788054854074569181,7788054854074569267⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨(-26189125327335180943),(-26189125327335180675)⟩,⟨4891873654868929354,4891873654868929624⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨(-21276054946567084214),(-21276054946567083019)⟩,⟨2534192542575775973,2534192542575777172⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨(-15879751213872348639),(-15879751213872344045)⟩,⟨1149046914809822354,1149046914809826947⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨(-11151496006496897877),(-11151496006496884958)⟩,⟨555374263423679397,555374263423692312⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨(-7478090551724961506),(-7478090551724936156)⟩,⟨369379948704222792,369379948704248138⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨(-4737231803044018873),(-4737231803043984477)⟩,⟨290020599443256724,290020599443291119⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨(-2621014085074032992),(-2621014085074002404)⟩,⟨193261415413577827,193261415413608414⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨(-838956542730658453),(-838956542730646206)⟩,⟨67721594638047993,67721594638060242⟩⟩
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
noncomputable def ans : CBox := ⟨⟨(-35765168450483269785),(-35765168450482657941)⟩,⟨7449016185810987244,7449016185811599093⟩⟩
lemma checked : cachedMomentRuleBox density1 hk0_0_20 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule true false 0 20) := by
  rw [← checked]
  exact @cached_density_rule_contains density1 hk0_0_20 (tableDensity true) (fullFactor false 0 20) density1_contains hk0_0_20_contains
noncomputable def atomAnswer : CBox := ⟨⟨119345300933791399302,119345300933791399312⟩,⟨(-5505245297333230147),(-5505245297333230145)⟩⟩
lemma atomChecked : tableAtomBox true ha0_0_20 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom true false 0 20) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains true false ha0_0_20 0 20 ha0_0_20_contains
 def realAnswer : RBox := ⟨83580132483208129517,83580132483408741371⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment true false 0 20) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm0_1_0_20
namespace hm0_0_0_21
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density0 j i k).mul (hk0_0_21 j i k))
noncomputable def s0_0 : CBox := ⟨⟨(-1723),(-1707)⟩,⟨2338,2354⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨(-3390),(-3374)⟩,⟨4733,4749⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨(-2423),(-2407)⟩,⟨3542,3558⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨(-940),(-924)⟩,⟨1459,1475⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨(-217),(-199)⟩,⟨351,367⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨(-36),(-19)⟩,⟨42,58⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨(-16),0⟩,⟨0,16⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨(-16),0⟩,⟨0,16⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨(-16),0⟩,⟨0,16⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨(-16),0⟩,⟨0,16⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨(-16),0⟩,⟨0,16⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨(-16),0⟩,⟨0,16⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨(-16),0⟩,⟨0,16⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨(-16),0⟩,⟨0,16⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨(-16),0⟩,⟨0,16⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨(-16),0⟩,⟨0,16⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨(-4481185189),(-4481185173)⟩,⟨3121432303,3121432320⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨(-10865792973),(-10865792956)⟩,⟨7648867612,7648867628⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨(-11839545392),(-11839545376)⟩,⟨8507626663,8507626679⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨(-8794860018),(-8794860000)⟩,⟨6511904931,6511904947⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨(-4895215269),(-4895215252)⟩,⟨3768226040,3768226056⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨(-2131726805),(-2131726788)⟩,⟨1720948703,1720948720⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨(-749030545),(-749030528)⟩,⟨639055891,639055907⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨(-218802740),(-218802723)⟩,⟨198283085,198283105⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨(-54949371),(-54949355)⟩,⟨52979638,52979654⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨(-12349141),(-12349124)⟩,⟨12652136,12652153⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨(-2607352),(-2607335)⟩,⟨2830276,2830292⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨(-547930),(-547914)⟩,⟨627860,627877⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨(-122130),(-122114)⟩,⟨147025,147041⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨(-30519),(-30503)⟩,⟨38295,38312⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨(-8549),(-8533)⟩,⟨11045,11061⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨(-1911),(-1895)⟩,⟨2497,2513⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨(-19796425134058),(-19796425134042)⟩,⟨(-317306306454),(-317306306438)⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨(-51599027109503),(-51599027109487)⟩,⟨(-142867185154),(-142867185138)⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨(-65059503925459),(-65059503925443)⟩,⟨1491541778528,1491541778544⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨(-60338994600280),(-60338994600264)⟩,⟨3549502892434,3549502892450⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨(-45319360569920),(-45319360569903)⟩,⟨4588623503892,4588623503908⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨(-28771013604562),(-28771013604546)⟩,⟨4217626538553,4217626538569⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨(-15875438857919),(-15875438857903)⟩,⟨3064021139545,3064021139561⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨(-7806167911537),(-7806167911520)⟩,⟨1874222313169,1874222313185⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨(-3511607433363),(-3511607433346)⟩,⟨1010205255285,1010205255301⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨(-1487216497702),(-1487216497682)⟩,⟨498409552363,498409552380⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨(-611423770628),(-611423770612)⟩,⟨233030016948,233030016964⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨(-251505919531),(-251505919514)⟩,⟨106446768151,106446768167⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨(-105994144156),(-105994144140)⟩,⟨48570790286,48570790302⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨(-45929637416),(-45929637400)⟩,⟨22223968795,22223968813⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨(-19338967366),(-19338967350)⟩,⟨9669271805,9669271821⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨(-5362190874),(-5362190857)⟩,⟨2722067820,2722067836⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨(-4511916131317569),(-4511916131317549)⟩,⟨(-1653622539756079),(-1653622539756053)⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨(-12234442500021743),(-12234442500021712)⟩,⟨(-4375546713693448),(-4375546713693416)⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨(-16662166812746378),(-16662166812746350)⟩,⟨(-5684417466614320),(-5684417466614290)⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨(-17271882626992827),(-17271882626992805)⟩,⟨(-5505593898328486),(-5505593898328466)⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨(-14958523901195855),(-14958523901195839)⟩,⟨(-4360076180903869),(-4360076180903853)⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨(-11288499067777279),(-11288499067777263)⟩,⟨(-2928886720457272),(-2928886720457256)⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨(-7635982224179287),(-7635982224179271)⟩,⟨(-1707148440574983),(-1707148440574967)⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨(-4737804594159768),(-4737804594159751)⟩,⟨(-883103056976079),(-883103056976063)⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨(-2751564231684232),(-2751564231684213)⟩,⟨(-415682536352575),(-415682536352558)⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨(-1524475471930601),(-1524475471930585)⟩,⟨(-182658164260724),(-182658164260708)⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨(-820404311632041),(-820404311632025)⟩,⟨(-76682698592948),(-76682698592932)⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨(-435633364230491),(-435633364230474)⟩,⟨(-31247530580535),(-31247530580519)⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨(-230301633628385),(-230301633628369)⟩,⟨(-12431084930239),(-12431084930223)⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨(-120037222518274),(-120037222518258)⟩,⟨(-4807659617976),(-4807659617960)⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨(-57624523550515),(-57624523550498)⟩,⟨(-1745986397746),(-1745986397730)⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨(-17106786902691),(-17106786902675)⟩,⟨(-431815534357),(-431815534341)⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨(-18177831131982811),(-18177831131980342)⟩,⟨(-324279890555088519),(-324279890555086048)⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨(-70794109003244198),(-70794109003235586)⟩,⟨(-883429921431287736),(-883429921431279123)⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨(-156680378534221705),(-156680378534202938)⟩,⟨(-1216951516657968957),(-1216951516657950192)⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨(-259518645669374727),(-259518645669338781)⟩,⟨(-1289527977144904409),(-1289527977144868464)⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨(-340633575341252522),(-340633575341191569)⟩,⟨(-1157862197222624486),(-1157862197222563534)⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨(-369613026938864750),(-369613026938777359)⟩,⟨(-918531976585125664),(-918531976585038276)⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨(-344553940809562248),(-344553940809462747)⟩,⟨(-659316532675068093),(-659316532674968590)⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨(-285469913382449815),(-285469913382364433)⟩,⟨(-435981187100581631),(-435981187100496246)⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨(-216261053645406243),(-216261053645350472)⟩,⟨(-270139882544228492),(-270139882544172719)⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨(-153390109204959158),(-153390109204930859)⟩,⟨(-159556885692436241),(-159556885692407941)⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨(-103859590459576911),(-103859590459565631)⟩,⟨(-91424310868231373),(-91424310868220093)⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨(-67997956635993747),(-67997956635989910)⟩,⟨(-51683056465933155),(-51683056465929316)⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨(-43099438352987578),(-43099438352986352)⟩,⟨(-29107354971727972),(-29107354971726748)⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨(-25937210498902098),(-25937210498901697)⟩,⟨(-16107851315457006),(-16107851315456604)⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨(-13743991575703702),(-13743991575703561)⟩,⟨(-8109118494891467),(-8109118494891326)⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨(-4289605690806143),(-4289605690806098)⟩,⟨(-2471308164636841),(-2471308164636796)⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨4006551847489869802,4006551847489869818⟩,⟨(-50451114910507393),(-50451114910507377)⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨11122075703778258650,11122075703778258675⟩,⟨(-690111884888829069),(-690111884888829049)⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨15958380541925202788,15958380541925202809⟩,⟨(-2495063075782110263),(-2495063075782110244)⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨18055501184317927756,18055501184317927783⟩,⟨(-5080860538235648932),(-5080860538235648911)⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨17670258271026534930,17670258271026534954⟩,⟨(-7347197076077048027),(-7347197076077048003)⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨15393146345616572165,15393146345616572192⟩,⟨(-8432116857066575114),(-8432116857066575092)⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨12064274877388963641,12064274877388963666⟩,⟨(-8274608786384601053),(-8274608786384601030)⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨8616030287286301576,8616030287286301608⟩,⟨(-7303342955542195681),(-7303342955542195655)⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨5707649989612041042,5707649989612041101⟩,⟨(-5976960150602906404),(-5976960150602906345)⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨3577681101150223694,3577681101150223900⟩,⟨(-4620519983075799657),(-4620519983075799449)⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨2167900863911385201,2167900863911385954⟩,⟨(-3414653668266339607),(-3414653668266338857)⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨1297170805496564424,1297170805496566480⟩,⟨(-2423904206698500802),(-2423904206698498746)⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨774331777284665421,774331777284669390⟩,⟨(-1643429586035139392),(-1643429586035135423)⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨451777198580321249,451777198580326568⟩,⟨(-1040106315477633695),(-1040106315477628373)⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨236404735995629120,236404735995633822⟩,⟨(-569617051010412043),(-569617051010407344)⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨73484813353779752,73484813353781633⟩,⟨(-180694154332446422),(-180694154332444540)⟩⟩
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
noncomputable def ans : CBox := ⟨⟨19100506825596237651,19100506825596324365⟩,⟨(-11180987027657074136),(-11180987027656987427)⟩⟩
lemma checked : cachedMomentRuleBox density0 hk0_0_21 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule false false 0 21) := by
  rw [← checked]
  exact @cached_density_rule_contains density0 hk0_0_21 (tableDensity false) (fullFactor false 0 21) density0_contains hk0_0_21_contains
noncomputable def atomAnswer : CBox := ⟨⟨(-525440759828809341),(-525440759828809340)⟩,⟨(-13714740390635844949),(-13714740390635844947)⟩⟩
lemma atomChecked : tableAtomBox false ha0_0_21 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom false false 0 21) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains false false ha0_0_21 0 21 ha0_0_21_contains
 def realAnswer : RBox := ⟨18575066065667428310,18575066065867515025⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment false false 0 21) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm0_0_0_21
namespace hm0_1_0_21
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density1 j i k).mul (hk0_0_21 j i k))
noncomputable def s0_0 : CBox := ⟨⟨(-351),(-335)⟩,⟨351,367⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨(-697),(-681)⟩,⟨718,734⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨(-513),(-496)⟩,⟨533,549⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨(-207),(-191)⟩,⟨210,226⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨(-53),(-37)⟩,⟨44,60⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨(-16),0⟩,⟨1,17⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨(-16),0⟩,⟨0,16⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨(-16),0⟩,⟨0,16⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨(-16),0⟩,⟨0,16⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨(-16),0⟩,⟨0,16⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨(-16),0⟩,⟨0,16⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨(-16),0⟩,⟨0,16⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨(-16),0⟩,⟨0,16⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨(-16),0⟩,⟨0,16⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨(-16),0⟩,⟨0,16⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨(-16),0⟩,⟨0,16⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨(-846400662),(-846400646)⟩,⟨95835571,95835587⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨(-2029051699),(-2029051683)⟩,⟨264499637,264499653⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨(-2165217150),(-2165217133)⟩,⟨359919913,359919929⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨(-1566915446),(-1566915430)⟩,⟨349498030,349498046⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨(-850797993),(-850797976)⟩,⟨256123165,256123181⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨(-364422872),(-364422855)⟩,⟨144043086,144043102⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨(-127335580),(-127335563)⟩,⟨63290635,63290651⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨(-37310728),(-37310710)⟩,⟨22396838,22396854⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨(-9454724),(-9454708)⟩,⟨6650796,6650812⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨(-2158432),(-2158416)⟩,⟨1736996,1737013⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨(-467988),(-467972)⟩,⟨419729,419745⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨(-102403),(-102387)⟩,⟨99055,99071⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨(-23986),(-23970)⟩,⟨24185,24201⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨(-6288),(-6272)⟩,⟨6441,6457⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨(-1827),(-1811)⟩,⟨1871,1887⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨(-422),(-406)⟩,⟨419,435⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨(-3768919055684),(-3768919055668)⟩,⟨(-2403198296128),(-2403198296112)⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨(-9889880272317),(-9889880272301)⟩,⟨(-6182960223072),(-6182960223056)⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨(-12559553343794),(-12559553343778)⟩,⟨(-7592760732759),(-7592760732743)⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨(-11631986119356),(-11631986119340)⟩,⟨(-6728013915427),(-6728013915411)⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨(-8611570350994),(-8611570350978)⟩,⟨(-4667496695846),(-4667496695830)⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨(-5350412444220),(-5350412444204)⟩,⟨(-2597769712431),(-2597769712415)⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨(-2903808531963),(-2903808531947)⟩,⟨(-1176324294158),(-1176324294142)⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨(-1423619726603),(-1423619726587)⟩,⟨(-440298203424),(-440298203407)⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨(-647520969424),(-647520969408)⟩,⟨(-138419891878),(-138419891862)⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨(-279430827069),(-279430827053)⟩,⟨(-37011587163),(-37011587147)⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨(-116770774793),(-116770774777)⟩,⟨(-8405427671),(-8405427655)⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨(-48200912215),(-48200912199)⟩,⟨(-1440179165),(-1440179149)⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨(-20040611500),(-20040611484)⟩,⟨60107302,60107318⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨(-8475581369),(-8475581353)⟩,⟨290728254,290728270⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨(-3486461078),(-3486461062)⟩,⟨219123619,219123635⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨(-953798849),(-953798833)⟩,⟨76844576,76844592⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨(-878733464982290),(-878733464982265)⟩,⟨(-1344711576652141),(-1344711576652117)⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨(-2360015226648604),(-2360015226648573)⟩,⟨(-3569897494978682),(-3569897494978651)⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨(-3168456058598386),(-3168456058598360)⟩,⟨(-4662393063777622),(-4662393063777596)⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨(-3252831606675437),(-3252831606675416)⟩,⟨(-4550539739098709),(-4550539739098686)⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨(-2829695160227325),(-2829695160227307)⟩,⟨(-3667100299740776),(-3667100299740759)⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨(-2176911879937650),(-2176911879937634)⟩,⟨(-2570331681837283),(-2570331681837267)⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨(-1508724381608500),(-1508724381608484)⟩,⟨(-1624242497476007),(-1624242497475991)⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨(-954601573070159),(-954601573070143)⟩,⟨(-947684291367876),(-947684291367860)⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨(-561580217456829),(-561580217456813)⟩,⟨(-519356179459066),(-519356179459050)⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨(-314348044869720),(-314348044869704)⟩,⟨(-271894976438125),(-271894976438109)⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨(-171395814049675),(-171395814049659)⟩,⟨(-138679625173524),(-138679625173508)⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨(-92692912434243),(-92692912434227)⟩,⟨(-70339575091958),(-70339575091942)⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨(-50063215185867),(-50063215185851)⟩,⟨(-35950622167968),(-35950622167952)⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨(-26626587671613),(-26626587671597)⟩,⟨(-18346231828703),(-18346231828687)⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨(-12979801221094),(-12979801221078)⟩,⟨(-8710828365431),(-8710828365415)⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨(-3884898176572),(-3884898176556)⟩,⟨(-2574817847240),(-2574817847224)⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨(-11416288280277304),(-11416288280275271)⟩,⟨(-106096645502284830),(-106096645502282798)⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨(-36236811865031448),(-36236811865024367)⟩,⟨(-294879495163380966),(-294879495163373885)⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨(-62793834013931595),(-62793834013916165)⟩,⟨(-420266325334259302),(-420266325334243875)⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨(-85188811654158464),(-85188811654128911)⟩,⟨(-462305443339264409),(-462305443339234857)⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨(-98632874244415901),(-98632874244365782)⟩,⟨(-428342045849072174),(-428342045849022056)⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨(-102112910403441168),(-102112910403369309)⟩,⟨(-348491015890339903),(-348491015890268047)⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨(-95804749468199409),(-95804749468117607)⟩,⟨(-257418755306066928),(-257418755305985127)⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨(-81287522815538284),(-81287522815468123)⟩,⟨(-177698085044525995),(-177698085044455834)⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨(-62502917458432465),(-62502917458386672)⟩,⟨(-117200671542241625),(-117200671542195833)⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨(-43955365879502548),(-43955365879479335)⟩,⟨(-74940609099179196),(-74940609099155982)⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨(-28636903873883249),(-28636903873874009)⟩,⟨(-46770733941920693),(-46770733941911452)⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨(-17561528055672263),(-17561528055669123)⟩,⟨(-28467669903504504),(-28467669903501364)⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨(-10319330921250400),(-10319330921249392)⟩,⟨(-16793655027733151),(-16793655027732147)⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨(-5826533179517840),(-5826533179517508)⟩,⟨(-9450580659930215),(-9450580659929884)⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨(-2967105424337114),(-2967105424336996)⟩,⟨(-4753046883654134),(-4753046883654017)⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨(-910163508617772),(-910163508617731)⟩,⟨(-1442036617210304),(-1442036617210264)⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨118955507692781038,118955507692781057⟩,⟨(-7140196014888345),(-7140196014888329)⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨310240036190598621,310240036190598643⟩,⟨(-99631855929242387),(-99631855929242371)⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨296430854317892745,296430854317892764⟩,⟨(-393851931205588184),(-393851931205588166)⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨(-99636280759141472),(-99636280759141450)⟩,⟨(-988014090702016548),(-988014090702016528)⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨(-780463535189694611),(-780463535189694592)⟩,⟨(-1936093990907651514),(-1936093990907651493)⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨(-1315358433682001675),(-1315358433682001656)⟩,⟨(-3036406614678806982),(-3036406614678806958)⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨(-1385698662064608485),(-1385698662064608465)⟩,⟨(-3824191959426444413),(-3824191959426444392)⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨(-1078069904430063749),(-1078069904430063724)⟩,⟨(-3979145636783495403),(-3979145636783495382)⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨(-665432441011039003),(-665432441011038953)⟩,⟨(-3560276406543911310),(-3560276406543911257)⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨(-338730085108473651),(-338730085108473477)⟩,⟨(-2841834401256668225),(-2841834401256668050)⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨(-150996060106822777),(-150996060106822162)⟩,⟨(-2085396989778373719),(-2085396989778373102)⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨(-71825134917314355),(-71825134917312676)⟩,⟨(-1441846343222849601),(-1441846343222847918)⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨(-47112390379369779),(-47112390379366533)⟩,⟨(-953950144014076801),(-953950144014073561)⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨(-36595439141129185),(-36595439141124833)⟩,⟨(-597857343474595771),(-597857343474591420)⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨(-24207329073161023),(-24207329073157178)⟩,⟨(-328321600515183594),(-328321600515179750)⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨(-8450680880310023),(-8450680880308481)⟩,⟨(-104690431678636550),(-104690431678635008)⟩⟩
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
noncomputable def ans : CBox := ⟨⟨(-1006920740510055001),(-1006920740509983720)⟩,⟨(-4833000246104350993),(-4833000246104279714)⟩⟩
lemma checked : cachedMomentRuleBox density1 hk0_0_21 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule true false 0 21) := by
  rw [← checked]
  exact @cached_density_rule_contains density1 hk0_0_21 (tableDensity true) (fullFactor false 0 21) density1_contains hk0_0_21_contains
noncomputable def atomAnswer : CBox := ⟨⟨687114839776135290,687114839776135292⟩,⟨17934660510831489546,17934660510831489548⟩⟩
lemma atomChecked : tableAtomBox true ha0_0_21 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom true false 0 21) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains true false ha0_0_21 0 21 ha0_0_21_contains
 def realAnswer : RBox := ⟨(-319805900833919711),(-319805900633848428)⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment true false 0 21) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm0_1_0_21
namespace hm0_0_0_22
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density0 j i k).mul (hk0_0_22 j i k))
noncomputable def s0_0 : CBox := ⟨⟨(-64),(-48)⟩,⟨(-49),(-33)⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨(-119),(-103)⟩,⟨(-87),(-70)⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨(-88),(-72)⟩,⟨(-63),(-46)⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨(-41),(-23)⟩,⟨(-27),(-11)⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨(-16),0⟩,⟨(-16),0⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨(-16),0⟩,⟨(-16),0⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨(-16),0⟩,⟨(-16),0⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨(-16),0⟩,⟨(-16),0⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨(-16),0⟩,⟨(-16),0⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨(-16),0⟩,⟨(-16),0⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨(-16),0⟩,⟨(-16),0⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨(-16),0⟩,⟨(-16),0⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨(-16),0⟩,⟨(-16),0⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨(-16),0⟩,⟨(-16),0⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨(-16),0⟩,⟨(-16),0⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨(-16),0⟩,⟨(-16),0⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨(-148229252),(-148229236)⟩,⟨(-212801079),(-212801063)⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨(-359872433),(-359872417)⟩,⟨(-511235791),(-511235775)⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨(-392951185),(-392951169)⟩,⟨(-546874236),(-546874220)⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨(-292618490),(-292618474)⟩,⟨(-395242727),(-395242711)⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨(-163307439),(-163307422)⟩,⟨(-212180382),(-212180365)⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨(-71337391),(-71337372)⟩,⟨(-88383434),(-88383418)⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨(-25145385),(-25145369)⟩,⟨(-29480335),(-29480317)⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨(-7356535),(-7356519)⟩,⟨(-8120256),(-8120239)⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨(-1843455),(-1843438)⟩,⟨(-1912589),(-1912571)⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨(-411407),(-411388)⟩,⟨(-401677),(-401661)⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨(-85904),(-85887)⟩,⟨(-79161),(-79144)⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨(-17826),(-17809)⟩,⟨(-15561),(-15545)⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨(-3933),(-3917)⟩,⟨(-3265),(-3249)⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨(-978),(-962)⟩,⟨(-784),(-768)⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨(-280),(-264)⟩,⟨(-216),(-199)⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨(-67),(-51)⟩,⟨(-55),(-39)⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨22622354160,22622354176⟩,⟨(-1411226170272),(-1411226170256)⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨10179738284,10179738300⟩,⟨(-3655465403457),(-3655465403441)⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨(-104178609299),(-104178609283)⟩,⟨(-4552429722723),(-4552429722706)⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨(-243579544263),(-243579544247)⟩,⟨(-4145757389428),(-4145757389409)⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨(-307566269804),(-307566269788)⟩,⟨(-3040645232192),(-3040645232175)⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨(-274727243845),(-274727243829)⟩,⟨(-1875613320656),(-1875613320640)⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨(-193113306679),(-193113306661)⟩,⟨(-1001268211090),(-1001268211074)⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨(-113901919540),(-113901919523)⟩,⟨(-474693323385),(-474693323369)⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨(-59060563092),(-59060563075)⟩,⟨(-205411092841),(-205411092825)⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨(-28004293518),(-28004293501)⟩,⟨(-83600018824),(-83600018806)⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨(-12590838555),(-12590838539)⟩,⟨(-33047566928),(-33047566910)⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨(-5543703880),(-5543703864)⟩,⟨(-13101663226),(-13101663208)⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨(-2448506852),(-2448506835)⟩,⟨(-5344113221),(-5344113205)⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨(-1091051064),(-1091051048)⟩,⟨(-2255016567),(-2255016549)⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨(-465883262),(-465883245)⟩,⟨(-931811435),(-931811419)⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨(-129885529),(-129885513)⟩,⟨(-255861721),(-255861705)⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨157237540903982,157237540903999⟩,⟨(-429022218248238),(-429022218248221)⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨414111969292256,414111969292274⟩,⟨(-1157870838708940),(-1157870838708922)⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨533026844241563,533026844241580⟩,⟨(-1562319274602265),(-1562319274602248)⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨509276275533296,509276275533312⟩,⟨(-1597509319591155),(-1597509319591138)⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨396266800113209,396266800113225⟩,⟨(-1359280534897645),(-1359280534897629)⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨260616660558621,260616660558637⟩,⟨(-1004212237348692),(-1004212237348675)⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨148283883787400,148283883787416⟩,⟨(-663031920378671),(-663031920378654)⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨74711321219815,74711321219831⟩,⟨(-400644461574901),(-400644461574883)⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨34205287709376,34205287709392⟩,⟨(-226302209785684),(-226302209785668)⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨14613920514449,14613920514465⟩,⟨(-121902026838197),(-121902026838181)⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨5969659663138,5969659663154⟩,⟨(-63832457701590),(-63832457701572)⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨2371610042376,2371610042392⟩,⟨(-33046006626126),(-33046006626110)⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨922752294462,922752294478⟩,⟨(-17087013775827),(-17087013775811)⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨350524526023,350524526039⟩,⟨(-8748665672696),(-8748665672680)⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨125695558890,125695558906⟩,⟨(-4147669440505),(-4147669440489)⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨30882186465,30882186481⟩,⟨(-1223395206763),(-1223395206747)⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨38552463000854985,38552463000855293⟩,⟨(-2161022067904125),(-2161022067903819)⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨104633246637531069,104633246637532102⟩,⟨(-8383010343827180),(-8383010343826147)⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨143068406711553159,143068406711555377⟩,⟨(-18412953558334195),(-18412953558331976)⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨149957003143586077,149957003143590272⟩,⟨(-30165597996074591),(-30165597996070398)⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨132764341545148785,132764341545155782⟩,⟨(-39040487039215549),(-39040487039208552)⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨103563829418663077,103563829418672939⟩,⟨(-41655612235765793),(-41655612235755936)⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨72932526691566027,72932526691577044⟩,⟨(-38098629180242713),(-38098629180231699)⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨47238952279072949,47238952279082213⟩,⟨(-30919323056668813),(-30919323056659548)⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨28643626633616134,28643626633622062⟩,⟨(-22922800348475065),(-22922800348469138)⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨16554288721736904,16554288721739855⟩,⟨(-15909543217455535),(-15909543217452585)⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨9288303257270295,9288303257271456⟩,⟨(-10548897936374390),(-10548897936373230)⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨5150113796439205,5150113796439601⟩,⟨(-6774514506051445),(-6774514506051049)⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨2852124421504984,2852124421505116⟩,⟨(-4222629647363097),(-4222629647362966)⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨1557272982390874,1557272982390929⟩,⟨(-2507399295685191),(-2507399295685138)⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨776653528160991,776653528161019⟩,⟨(-1316307543511978),(-1316307543511948)⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨235552458861975,235552458861993⟩,⟨(-408862358575325),(-408862358575304)⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨7196755490256328,7196755490256344⟩,⟨571679471281638732,571679471281638748⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨98113714148601458,98113714148601474⟩,⟨1581982641158384094,1581982641158384110⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨352530223347462297,352530223347462313⟩,⟨2255844717584197219,2255844717584197235⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨711421193110914535,711421193110914554⟩,⟨2529189584915031046,2529189584915031065⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨1016859633152678530,1016859633152678547⟩,⟨2446435137911323262,2446435137911323282⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨1150917456481038706,1150917456481038722⟩,⟨2101678895902556913,2101678895902556930⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨1111803698897512405,1111803698897512422⟩,⟨1621475571638942098,1621475571638942115⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨964746088544033312,964746088544033328⟩,⟨1138497861054586937,1138497861054586955⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨775689364923903655,775689364923903677⟩,⟨740970490120779915,740970490120779935⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨589130618767548819,589130618767548859⟩,⟨456301647832899121,456301647832899160⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨428041245493017103,428041245493017212⟩,⟨271824610198281378,271824610198281481⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨299150942701817728,299150942701817995⟩,⟨160121919831727708,160121919831727974⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨200115260718444565,200115260718445060⟩,⟨94297634815949315,94297634815949813⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨125299612971233763,125299612971234419⟩,⟨54427217018608936,54427217018609592⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨68110187949619262,68110187949619840⟩,⟨28267773949957934,28267773949958508⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨21523287512325544,21523287512325784⟩,⟨8753117619312659,8753117619312898⟩⟩
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
noncomputable def ans : CBox := ⟨⟨1463494799333966934,1463494799333976797⟩,⟨2629938336533267407,2629938336533277270⟩⟩
lemma checked : cachedMomentRuleBox density0 hk0_0_22 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule false false 0 22) := by
  rw [← checked]
  exact @cached_density_rule_contains density0 hk0_0_22 (tableDensity false) (fullFactor false 0 22) density0_contains hk0_0_22_contains
noncomputable def atomAnswer : CBox := ⟨⟨1965781686197785318,1965781686197785320⟩,⟨(-62585242822477399),(-62585242822477398)⟩⟩
lemma atomChecked : tableAtomBox false ha0_0_22 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom false false 0 22) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains false false ha0_0_22 0 22 ha0_0_22_contains
 def realAnswer : RBox := ⟨3429276485431752252,3429276485631762117⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment false false 0 22) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm0_0_0_22
namespace hm0_1_0_22
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density1 j i k).mul (hk0_0_22 j i k))
noncomputable def s0_0 : CBox := ⟨⟨(-16),0⟩,⟨(-16),0⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨(-31),(-14)⟩,⟨(-25),(-9)⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨(-16),0⟩,⟨(-16),0⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨(-16),0⟩,⟨(-16),0⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨(-16),0⟩,⟨(-16),0⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨(-16),0⟩,⟨(-16),0⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨(-16),0⟩,⟨(-16),0⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨(-16),0⟩,⟨(-16),0⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨(-16),0⟩,⟨(-16),0⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨(-16),0⟩,⟨(-16),0⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨(-16),0⟩,⟨(-16),0⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨(-16),0⟩,⟨(-16),0⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨(-16),0⟩,⟨(-16),0⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨(-16),0⟩,⟨(-16),0⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨(-16),0⟩,⟨(-16),0⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨(-16),0⟩,⟨(-16),0⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨(-4550889),(-4550873)⟩,⟨(-40193708),(-40193692)⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨(-12441904),(-12441888)⟩,⟨(-95468899),(-95468883)⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨(-16616398),(-16616382)⟩,⟨(-100017360),(-100017344)⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨(-15694517),(-15694501)⟩,⟨(-70422651),(-70422635)⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨(-11091309),(-11091293)⟩,⟨(-36880038),(-36880022)⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨(-5966439),(-5966423)⟩,⟨(-15109950),(-15109934)⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨(-2488706),(-2488690)⟩,⟨(-5011681),(-5011665)⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨(-830492),(-830476)⟩,⟨(-1384644),(-1384628)⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨(-231312),(-231296)⟩,⟨(-329072),(-329056)⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨(-56466),(-56450)⟩,⟨(-70206),(-70190)⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨(-12739),(-12723)⟩,⟨(-14214),(-14197)⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨(-2820),(-2804)⟩,⟨(-2914),(-2898)⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨(-653),(-637)⟩,⟨(-647),(-631)⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨(-171),(-155)⟩,⟨(-167),(-151)⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨(-54),(-38)⟩,⟨(-52),(-36)⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨(-20),(-4)⟩,⟨(-19),(-3)⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨171316911517,171316911533⟩,⟨(-268674336084),(-268674336068)⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨438030595317,438030595333⟩,⟨(-700630693151),(-700630693135)⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨531314792272,531314792289⟩,⟨(-878828540064),(-878828540048)⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨462316448609,462316448625⟩,⟨(-799219513731),(-799219513715)⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨313232112963,313232112979⟩,⟨(-577808444188),(-577808444172)⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨169423694459,169423694475⟩,⟨(-348818272727),(-348818272711)⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨74241465443,74241465459⟩,⟨(-183149315767),(-183149315750)⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨26800502320,26800502336⟩,⟨(-86568958610),(-86568958594)⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨8107295790,8107295806⟩,⟨(-37874631329),(-37874631313)⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨2083906075,2083906091⟩,⟨(-15706503227),(-15706503211)⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨455248029,455248045⟩,⟨(-6311271250),(-6311271234)⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨75269907,75269923⟩,⟨(-2510965023),(-2510965006)⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨(-2955859),(-2955843)⟩,⟨(-1010477514),(-1010477498)⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨(-14251251),(-14251235)⟩,⟨(-416146854),(-416146838)⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨(-10553568),(-10553552)⟩,⟨(-167992218),(-167992202)⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨(-3666556),(-3666540)⟩,⟨(-45511489),(-45511473)⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨127864163633696,127864163633712⟩,⟨(-83555760045660),(-83555760045643)⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨337862508698111,337862508698129⟩,⟨(-223354261082068),(-223354261082051)⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨437189204504132,437189204504150⟩,⟨(-297092721301043),(-297092721301025)⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨420926370946956,420926370946974⟩,⟨(-300862107836672),(-300862107836654)⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨333270495791624,333270495791640⟩,⟨(-257128715247624),(-257128715247607)⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨228685185237177,228685185237193⟩,⟨(-193646680726951),(-193646680726935)⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨141052060073243,141052060073260⟩,⟨(-130996074750660),(-130996074750644)⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨80149982343981,80149982343997⟩,⟨(-80721418960906),(-80721418960890)⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨42720057027014,42720057027030⟩,⟨(-46186011195125),(-46186011195109)⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨21744369378098,21744369378114⟩,⟨(-25135667596789),(-25135667596773)⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨10791294829340,10791294829357⟩,⟨(-13335182208432),(-13335182208416)⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨5336188998122,5336188998138⟩,⟨(-7031159201897),(-7031159201881)⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨2667439393826,2667439393842⟩,⟨(-3714262506939),(-3714262506923)⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨1337152421833,1337152421849⟩,⟨(-1940580218462),(-1940580218446)⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨626987050438,626987050454⟩,⟨(-934245076048),(-934245076032)⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨184138691727,184138691743⟩,⟨(-277828950986),(-277828950970)⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨12613424796562229,12613424796562485⟩,⟨(-1357222297148894),(-1357222297148637)⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨34924979984676531,34924979984677386⟩,⟨(-4291453900304305),(-4291453900303452)⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨49406274439129523,49406274439131351⟩,⟨(-7380812685985984),(-7380812685984157)⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨53758675995504171,53758675995507620⟩,⟨(-9903828141844388),(-9903828141840940)⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨49113378309823528,49113378309829284⟩,⟨(-11305707913318073),(-11305707913312317)⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨39290641011719293,39290641011727400⟩,⟨(-11508422293562824),(-11508422293554714)⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨28473604854350530,28473604854359587⟩,⟨(-10593111535467271),(-10593111535458214)⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨19251945458899878,19251945458907495⟩,⟨(-8803915959217507),(-8803915959209892)⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨12425464145226798,12425464145231671⟩,⟨(-6625001510646802),(-6625001510641930)⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨7774038019065870,7774038019068296⟩,⟨(-4559219435714780),(-4559219435712352)⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨4751042739930435,4751042739931388⟩,⟨(-2908881434946280),(-2908881434945325)⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨2836487718977020,2836487718977348⟩,⟨(-1749819380485068),(-1749819380484741)⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨1645489072418725,1645489072418839⟩,⟨(-1011119447172527),(-1011119447172411)⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨913658209775116,913658209775161⟩,⟨(-563289488886553),(-563289488886507)⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨455225989786898,455225989786922⟩,⟨(-284174001063416),(-284174001063392)⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨137447638400063,137447638400082⟩,⟨(-86752071286373),(-86752071286355)⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨1018535089781193,1018535089781209⟩,⟨16973324985419922,16973324985419938⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨14164538801983921,14164538801983937⟩,⟨44130485017023229,44130485017023246⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨55642875035670663,55642875035670679⟩,⟨41925868255383318,41925868255383334⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨138309313886153751,138309313886153769⟩,⟨(-13883971692090752),(-13883971692090735)⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨267862626119592213,267862626119592229⟩,⟨(-107940393875643758),(-107940393875643742)⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨414293886714354906,414293886714354922⟩,⟨(-179491796731626403),(-179491796731626387)⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨513683052662105447,513683052662105464⟩,⟨(-186197357820400765),(-186197357820400748)⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨525536189708053439,525536189708053455⟩,⟨(-142453275010721372),(-142453275010721354)⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨462013377608978066,462013377608978090⟩,⟨(-86405344977843222),(-86405344977843202)⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨362338144223292837,362338144223292874⟩,⟨(-43219055839692248),(-43219055839692212)⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨261420764059633897,261420764059633989⟩,⟨(-18940853814232978),(-18940853814232888)⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨177954557581485600,177954557581485821⟩,⟨(-8866893344708146),(-8866893344707927)⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨116161594674156525,116161594674156933⟩,⟨(-5735865364429909),(-5735865364429501)⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨72022818844870114,72022818844870656⟩,⟨(-4407828624543191),(-4407828624542648)⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨39257923731720530,39257923731721004⟩,⟨(-2894318772870548),(-2894318772870074)⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨12470138068242639,12470138068242836⟩,⟨(-1006590840343602),(-1006590840343404)⟩⟩
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
noncomputable def ans : CBox := ⟨⟨625686120015028658,625686120015036810⟩,⟨(-130502736788626245),(-130502736788618094)⟩⟩
lemma checked : cachedMomentRuleBox density1 hk0_0_22 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule true false 0 22) := by
  rw [← checked]
  exact @cached_density_rule_contains density1 hk0_0_22 (tableDensity true) (fullFactor false 0 22) density1_contains hk0_0_22_contains
noncomputable def atomAnswer : CBox := ⟨⟨(-2570637589643257726),(-2570637589643257724)⟩,⟨81842240614008905,81842240614008906⟩⟩
lemma atomChecked : tableAtomBox true ha0_0_22 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom true false 0 22) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains true false ha0_0_22 0 22 ha0_0_22_contains
 def realAnswer : RBox := ⟨(-1944951469728229068),(-1944951469528220914)⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment true false 0 22) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm0_1_0_22
namespace hm0_0_0_23
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density0 j i k).mul (hk0_0_23 j i k))
noncomputable def s0_0 : CBox := ⟨⟨0,16⟩,⟨(-16),0⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨0,16⟩,⟨(-16),0⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨0,16⟩,⟨(-16),0⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨0,16⟩,⟨(-16),0⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨0,16⟩,⟨(-16),0⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨0,16⟩,⟨(-16),0⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨0,16⟩,⟨(-16),0⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨0,16⟩,⟨(-16),0⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨0,16⟩,⟨(-16),0⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨0,16⟩,⟨(-16),0⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨0,16⟩,⟨(-16),0⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨0,16⟩,⟨(-16),0⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨0,16⟩,⟨(-16),0⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨0,16⟩,⟨(-16),0⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨0,16⟩,⟨(-16),0⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨0,16⟩,⟨(-16),0⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨9666072,9666088⟩,⟨(-6733024),(-6733007)⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨23008229,23008245⟩,⟨(-16195802),(-16195786)⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨24163217,24163233⟩,⟨(-17361371),(-17361355)⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨16991495,16991511⟩,⟨(-12578501),(-12578485)⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨8798182,8798198⟩,⟨(-6770651),(-6770635)⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨3505804,3505820⟩,⟨(-2829091),(-2829073)⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨1110105,1110121⟩,⟨(-946641),(-946625)⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨288335,288351⟩,⟨(-261155),(-261139)⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨63688,63705⟩,⟨(-61385),(-61368)⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨12492,12508⟩,⟨(-12810),(-12793)⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨2290,2307⟩,⟨(-2502),(-2486)⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨414,430⟩,⟨(-492),(-476)⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨75,91⟩,⟨(-107),(-91)⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨10,26⟩,⟨(-31),(-15)⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨0,16⟩,⟨(-16),0⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨0,16⟩,⟨(-16),0⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨96228050028,96228050044⟩,⟨1542737713,1542737729⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨247709107523,247709107539⟩,⟨693783651,693783667⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨304704912643,304704912659⟩,⟨(-6960242298),(-6960242282)⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨272471515859,272471515876⟩,⟨(-15989149126),(-15989149110)⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨195149852056,195149852072⟩,⟨(-19720398667),(-19720398651)⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨116966489159,116966489175⟩,⟨(-17118502891),(-17118502874)⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨60410708162,60410708180⟩,⟨(-11643191826),(-11643191809)⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨27614304593,27614304609⟩,⟨(-6621973123),(-6621973107)⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨11494538309,11494538327⟩,⟨(-3303208024),(-3303208008)⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨4495606747,4495606763⟩,⟨(-1505265950),(-1505265934)⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨1708764023,1708764039⟩,⟨(-650793670),(-650793654)⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨652892322,652892338⟩,⟨(-276187972),(-276187955)⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨257747660,257747677⟩,⟨(-118073635),(-118073619)⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨105905655,105905671⟩,⟨(-51236724),(-51236708)⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨42946188,42946205⟩,⟨(-21471506),(-21471490)⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨11677871,11677887⟩,⟨(-5928144),(-5928127)⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨39020569375514,39020569375530⟩,⟨14301156368488,14301156368504⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨104817244046653,104817244046669⟩,⟨37488661035713,37488661035729⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨140122505475061,140122505475077⟩,⟨47809255513464,47809255513480⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨141335465125732,141335465125749⟩,⟨45061611465748,45061611465764⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨118151268947356,118151268947373⟩,⟨34450074122856,34450074122872⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨85453281429226,85453281429243⟩,⟨22182758494172,22182758494188⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨55070920142678,55070920142694⟩,⟨12320681298449,12320681298466⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨32408785603082,32408785603098⟩,⟨6046202419765,6046202419781⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨17804142073336,17804142073354⟩,⟨2692448274179,2692448274195⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨9324464804596,9324464804612⟩,⟨1118449550266,1118449550282⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨4750889050804,4750889050820⟩,⟨444550371558,444550371574⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨2397904120964,2397904120981⟩,⟨172181085536,172181085552⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨1212674893759,1212674893776⟩,⟨65519416516,65519416532⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨609916963963,609916963979⟩,⟨24445897101,24445897117⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨285561039273,285561039290⟩,⟨8655596551,8655596567⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨83687446213,83687446229⟩,⟨2112579344,2112579360⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨245737432358545,245737432358592⟩,⟨4384087544756513,4384087544756564⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨949508577891335,949508577891469⟩,⟨11853956242870874,11853956242871008⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨2069808993391670,2069808993391933⟩,⟨16088375628108444,16088375628108709⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨3353945185566130,3353945185566608⟩,⟨16680282353735571,16680282353736047⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨4280029200105491,4280029200106271⟩,⟨14561621114700778,14561621114701560⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨4490622932717278,4490622932718352⟩,⟨11169369924474665,11169369924475742⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨4029683691506295,4029683691507474⟩,⟨7717167632315941,7717167632317117⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨3203398284627594,3203398284628567⟩,⟨4896028849806406,4896028849807380⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨2324176328399130,2324176328399747⟩,⟨2905221260093132,2905221260093746⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨1578445226881365,1578445226881672⟩,⟨1642921558204122,1642921558204428⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨1024889715038790,1024889715038917⟩,⟨902652402268304,902652402268432⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨645605313931298,645605313931350⟩,⟨490898844457103,490898844457156⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨395728581158494,395728581158521⟩,⟨267323545734351,267323545734379⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨231858612277613,231858612277630⟩,⟨144009578549793,144009578549810⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨120586448567249,120586448567266⟩,⟨71150447560786,71150447560802⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨37276226132969,37276226132986⟩,⟨21475507289353,21475507289369⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨(-78024207143099222),(-78024207143099206)⟩,⟨981968674033440,981968674033457⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨(-215235172174475474),(-215235172174475458)⟩,⟨13342447374000727,13342447374000743⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨(-305018801507166900),(-305018801507166884)⟩,⟨47643990656206137,47643990656206153⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨(-338884794447773213),(-338884794447773197)⟩,⟨95282937310795120,95282937310795136⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨(-323985411283854662),(-323985411283854646)⟩,⟨134617416568728075,134617416568728091⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨(-274478489772848737),(-274478489772848720)⟩,⟨150263930645558538,150263930645558554⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨(-208460759058561820),(-208460759058561804)⟩,⟨142893846872875667,142893846872875683⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨(-143900762667185360),(-143900762667185344)⟩,⟨121901852841369448,121901852841369464⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨(-92013330750747415),(-92013330750747398)⟩,⟨96294539449432728,96294539449432744⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨(-55668334552980256),(-55668334552980236)⟩,⟨71851890473085177,71851890473085195⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨(-32601876521417235),(-32601876521417209)⟩,⟨51325017268707135,51325017268707161⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨(-18906315598514586),(-18906315598514541)⟩,⟨35315700139006696,35315700139006743⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨(-10984357677898993),(-10984357677898923)⟩,⟨23308239692348029,23308239692348100⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨(-6271996262974985),(-6271996262974896)⟩,⟨14438416644659461,14438416644659547⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨(-3233129098427587),(-3233129098427505)⟩,⟨7789994951670861,7789994951670940⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨(-997293320232821),(-997293320232781)⟩,⟨2452268888796087,2452268888796128⟩⟩
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
noncomputable def ans : CBox := ⟨⟨(-346488256949073436),(-346488256949072154)⟩,⟨183954184639472185,183954184639473466⟩⟩
lemma checked : cachedMomentRuleBox density0 hk0_0_23 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule false false 0 23) := by
  rw [← checked]
  exact @cached_density_rule_contains density0 hk0_0_23 (tableDensity false) (fullFactor false 0 23) density0_contains hk0_0_23_contains
noncomputable def atomAnswer : CBox := ⟨⟨7129092554256656,7129092554256658⟩,⟨269339847531150708,269339847531150709⟩⟩
lemma atomChecked : tableAtomBox false ha0_0_23 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom false false 0 23) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains false false ha0_0_23 0 23 ha0_0_23_contains
 def realAnswer : RBox := ⟨(-339359164494816780),(-339359164294815496)⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment false false 0 23) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm0_0_0_23
namespace hm0_1_0_23
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density1 j i k).mul (hk0_0_23 j i k))
noncomputable def s0_0 : CBox := ⟨⟨0,16⟩,⟨(-16),0⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨0,16⟩,⟨(-16),0⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨0,16⟩,⟨(-16),0⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨0,16⟩,⟨(-16),0⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨0,16⟩,⟨(-16),0⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨0,16⟩,⟨(-16),0⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨0,16⟩,⟨(-16),0⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨0,16⟩,⟨(-16),0⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨0,16⟩,⟨(-16),0⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨0,16⟩,⟨(-16),0⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨0,16⟩,⟨(-16),0⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨0,16⟩,⟨(-16),0⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨0,16⟩,⟨(-16),0⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨0,16⟩,⟨(-16),0⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨0,16⟩,⟨(-16),0⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨0,16⟩,⟨(-16),0⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨1825716,1825732⟩,⟨(-206719),(-206703)⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨4296672,4296688⟩,⟨(-559832),(-559816)⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨4419401,4419417⟩,⟨(-733816),(-733800)⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨3027686,3027703⟩,⟨(-674199),(-674183)⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨1529354,1529370⟩,⟨(-459496),(-459480)⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨599366,599382⟩,⟨(-236448),(-236432)⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨188712,188728⟩,⟨(-93637),(-93620)⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨49158,49174⟩,⟨(-29475),(-29459)⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨10949,10965⟩,⟨(-7704),(-7688)⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨2176,2192⟩,⟨(-1763),(-1747)⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨402,418⟩,⟨(-376),(-359)⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨71,87⟩,⟨(-86),(-70)⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨7,23⟩,⟨(-23),(-7)⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨0,16⟩,⟨(-16),0⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨0,16⟩,⟨(-16),0⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨0,16⟩,⟨(-16),0⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨18320223698,18320223714⟩,⟨11681700814,11681700831⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨47477234697,47477234714⟩,⟨29683189841,29683189857⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨58821732397,58821732413⟩,⟨35563769825,35563769841⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨52527856597,52527856613⟩,⟨30388072876,30388072893⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨37085648406,37085648422⟩,⟨20107998091,20107998107⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨21754101492,21754101508⟩,⟨10570052424,10570052440⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨11050487103,11050487119⟩,⟨4482329787,4482329803⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨5035889457,5035889474⟩,⟨1560569091,1560569107⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨2119301715,2119301731⟩,⟨454256023,454256039⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨844567847,844567863⟩,⟨112244461,112244477⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨326320962,326320978⟩,⟨23587245,23587261⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨125130422,125130438⟩,⟨3763173,3763189⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨48737980,48737997⟩,⟨(-138974),(-138958)⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨19545025,19545041⟩,⟨(-668246),(-668230)⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨7742745,7742761⟩,⟨(-486202),(-486186)⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨2077204,2077220⟩,⟨(-167348),(-167332)⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨7599598954997,7599598955013⟩,⟨11629568285116,11629568285132⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨20219497938373,20219497938389⟩,⟨30585877602545,30585877602561⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨26646251690862,26646251690878⟩,⟨39212971955274,39212971955290⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨26618123760350,26618123760366⟩,⟨37243746919592,37243746919608⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨22349636105172,22349636105188⟩,⟨28972090841253,28972090841269⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨16477571897063,16477571897079⟩,⟨19462595527988,19462595528006⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨10879903571512,10879903571528⟩,⟨11717265930013,11717265930029⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨6529456938479,6529456938495⟩,⟨6484323947053,6484323947069⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨3633559235438,3633559235454⟩,⟨3361409011846,3361409011862⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨1922616250608,1922616250624⟩,⟨1663469553810,1663469553826⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨992470062931,992470062947⟩,⟨803256180243,803256180259⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨510178716685,510178716701⟩,⟨387237675116,387237675132⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨263594006827,263594006843⟩,⟨189317936649,189317936665⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨135285329004,135285329020⟩,⟨93221902151,93221902167⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨64320827371,64320827387⟩,⟨43167382254,43167382270⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨19005117947,19005117963⟩,⟨12596178516,12596178532⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨154337699406947,154337699406989⟩,⟨1434363975041720,1434363975041763⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨486132819749160,486132819749273⟩,⟨3956614877695798,3956614877695909⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨829830433007669,829830433007888⟩,⟨5555685001206492,5555685001206713⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨1101347338196713,1101347338197111⟩,⟨5979553905996125,5979553905996523⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨1239588643330294,1239588643330939⟩,⟨5386573935883115,5386573935883761⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨1240674226407562,1240674226408447⟩,⟨4237340926795115,4237340926796006⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨1120390826253674,1120390826254643⟩,⟨3012687819315898,3012687819316870⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨912093204595580,912093204596384⟩,⟨1995160113308693,1995160113309495⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨671712928326654,671712928327164⟩,⟨1260106129583649,1260106129584157⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨452356162113083,452356162113339⟩,⟨771413978212390,771413978212646⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨282641215544540,282641215544650⟩,⟨461650391169125,461650391169233⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨166774907328718,166774907328766⟩,⟨270343831350418,270343831350464⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨94766842667030,94766842667058⟩,⟨154222521638509,154222521638532⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨52089785105260,52089785105281⟩,⟨84490624601641,84490624601661⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨26033487489780,26033487489797⟩,⟨41704089407462,41704089407479⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨7909250626226,7909250626242⟩,⟨12531219214827,12531219214843⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨(-2316563639253635),(-2316563639253619)⟩,⟨138975025630086,138975025630102⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨(-6004477379864356),(-6004477379864340)⟩,⟨1926203762746665,1926203762746681⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨(-5672017349025489),(-5672017349025473)⟩,⟨7519398104846791,7519398104846807⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨1850535928461737,1850535928461753⟩,⟨18519893833838845,18519893833838861⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨14279597715784301,14279597715784317⟩,⟨35448566750020048,35448566750020064⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨23428690439170753,23428690439170769⟩,⟨54070462574230675,54070462574230691⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨23932216799755904,23932216799755920⟩,⟨66001763488375195,66001763488375211⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨18005441371782239,18005441371782255⟩,⟨66392857725271434,66392857725271451⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨10732066797602783,10732066797602799⟩,⟨57349775805920986,57349775805921002⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨5274755546224534,5274755546224552⟩,⟨44191138948577664,44191138948577680⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨2272677384808006,2272677384808032⟩,⟨31346996309570553,31346996309570580⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨1047053995442414,1047053995442455⟩,⟨21008825108979330,21008825108979371⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨667979252828811,667979252828874⟩,⟨13530056548283223,13530056548283285⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨507832265425851,507832265425930⟩,⟨8299281722935696,8299281722935775⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨331010560252768,331010560252835⟩,⟨4490050213360691,4490050213360761⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨114685687772816,114685687772852⟩,⟨1420792024001614,1420792024001653⟩⟩
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
noncomputable def ans : CBox := ⟨⟨16239213633378225,16239213633379327⟩,⟨77743581338484812,77743581338485916⟩⟩
lemma checked : cachedMomentRuleBox density1 hk0_0_23 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule true false 0 23) := by
  rw [← checked]
  exact @cached_density_rule_contains density1 hk0_0_23 (tableDensity true) (fullFactor false 0 23) density1_contains hk0_0_23_contains
noncomputable def atomAnswer : CBox := ⟨⟨(-9322659494027937),(-9322659494027935)⟩,⟨(-352213646771504773),(-352213646771504772)⟩⟩
lemma atomChecked : tableAtomBox true ha0_0_23 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom true false 0 23) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains true false ha0_0_23 0 23 ha0_0_23_contains
 def realAnswer : RBox := ⟨6916554039350288,6916554239351392⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains : realAnswer.Contains (fullMoment true false 0 23) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm0_1_0_23
end SharpPlanar.CachedData

end OAI
