import OAI.Analysis.PlanarPacking.Certificate.KernelValues10
import OAI.Analysis.PlanarPacking.Certificate.TableDensityValues
import OAI.Analysis.PlanarPacking.TableRuleBridge
import OAI.Analysis.PlanarPacking.Certificate.AtomKernels

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace tm0_7_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density0 j i k).mul (kernel7_0 j i k))
noncomputable def s0_0 : CBox := ⟨⟨1539434,1539451⟩,⟨339993,340009⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨2847185,2847204⟩,⟨1681589,1681608⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨1060896,1060917⟩,⟨2533390,2533409⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨(-783327),(-783305)⟩,⟨1187262,1187280⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨(-501375),(-501352)⟩,⟨(-180817),(-180795)⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨72970,72997⟩,⟨(-144213),(-144193)⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨26266,26291⟩,⟨35621,35644⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨(-12162),(-12137)⟩,⟨(-1605),(-1584)⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨3402,3425⟩,⟨(-1695),(-1669)⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨(-848),(-827)⟩,⟨1155,1179⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨43,67⟩,⟨(-692),(-671)⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨241,261⟩,⟨307,327⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨(-284),(-261)⟩,⟨39,59⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨(-36),(-16)⟩,⟨(-205),(-186)⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨92,111⟩,⟨(-78),(-59)⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨35,51⟩,⟨(-6),11⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨(-240893496939230),(-240893496939213)⟩,⟨(-43274226767668),(-43274226767652)⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨(-510123911851399),(-510123911851380)⟩,⟨(-119285153681734),(-119285153681716)⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨(-420858353187185),(-420858353187164)⟩,⟨(-149631040516078),(-149631040516060)⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨(-200542529638357),(-200542529638339)⟩,⟨(-117097303410945),(-117097303410923)⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨(-56605662673762),(-56605662673740)⟩,⟨(-59563331873121),(-59563331873101)⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨(-7430392378025),(-7430392378000)⟩,⟨(-19796589260928),(-19796589260907)⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨763663786584,763663786610⟩,⟨(-4142268182664),(-4142268182640)⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨536385917887,536385917910⟩,⟨(-443587452820),(-443587452799)⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨101780216706,101780216726⟩,⟨16938642841,16938642863⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨5949687782,5949687803⟩,⟨13698538575,13698538595⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨(-1451063720),(-1451063698)⟩,⟨1782583931,1782583953⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨(-394859166),(-394859142)⟩,⟨(-93847070),(-93847045)⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨(-23746191),(-23746169)⟩,⟨(-83532019),(-83531998)⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨13438168,13438189⟩,⟨(-18533609),(-18533589)⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨6721670,6721688⟩,⟨(-1959492),(-1959476)⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨1659482,1659498⟩,⟨106825,106841⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨(-100604803925571854159),(-100604803925571853465)⟩,⟨(-323634156508143957295),(-323634156508143956577)⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨(-289914652935443896154),(-289914652935443894454)⟩,⟨(-759375407410018500682),(-759375407410018498930)⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨(-405493924002755726572),(-405493924002755724581)⟩,⟨(-767555209430897938595),(-767555209430897936563)⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨(-382411765169183107148),(-382411765169183105494)⟩,⟨(-498599019948878623320),(-498599019948878621646)⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨(-256159945410949100807),(-256159945410949099755)⟩,⟨(-223729118537419268205),(-223729118537419267152)⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨(-125942672519681985010),(-125942672519681984477)⟩,⟨(-70247252081286905613),(-70247252081286905079)⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨(-47242447223062030035),(-47242447223062029808)⟩,⟨(-15090123390447427938),(-15090123390447427711)⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨(-14211220366411580108),(-14211220366411580019)⟩,⟨(-1970122281285136634),(-1970122281285136545)⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨(-3646026578755884170),(-3646026578755884126)⟩,⟨(-38841078742971920),(-38841078742971877)⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨(-855415036589945491),(-855415036589945460)⟩,⟨52084930192312191,52084930192312222⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨(-196863134307552306),(-196863134307552278)⟩,⟨14347258431906382,14347258431906408⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨(-47272434957905145),(-47272434957905118)⟩,⟨1435425821840870,1435425821840897⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨(-12408335987845460),(-12408335987845436)⟩,⟨(-641376779010148),(-641376779010121)⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨(-3644220158913936),(-3644220158913913)⟩,⟨(-550652063016583),(-550652063016560)⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨(-1157779365535812),(-1157779365535790)⟩,⟨(-279522473330094),(-279522473330076)⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨(-276443664505579),(-276443664505562)⟩,⟨(-81778720480090),(-81778720480071)⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨(-688372743224836779855815),(-688372743224834008398266)⟩,⟨1465600209863387751720993,1465600209863390523428537⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨(-1485990613483959526554353),(-1485990613483954085197203)⟩,⟨3967119847836198864138486,3967119847836204306191092⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨(-1071127071571651049015345),(-1071127071571646509020302)⟩,⟨5261219950637883904635953,5261219950637888445413528⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨131984627558196016259191,131984627558198221103130⟩,⟨4990145577882804719994255,4990145577882806925361053⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨1153600027076870023899521,1153600027076870635762450⟩,⟨3550082321950546898586323,3550082321950547510630256⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨1418229410490137446685589,1418229410490137544740477⟩,⟨1860315305572060778896090,1860315305572060876902140⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨1080315118973696391647703,1080315118973696402370789⟩,⟨657508448975718334522393,657508448975718345130275⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨598218876370293868357555,598218876370293870092775⟩,⟨94028687614746173095671,94028687614746174750598⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨256500693179993853245281,256500693179993853929172⟩,⟨(-61168805774330422249834),(-61168805774330421587618)⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨88338405721490514577860,88338405721490514884599⟩,⟨(-61126018193869638794036),(-61126018193869638489304)⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨24819050605491833104904,24819050605491833239990⟩,⟨(-34164574295974140388471),(-34164574295974140251685)⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨5458840089865646845327,5458840089865646904065⟩,⟨(-15610628686718619628044),(-15610628686718619567895)⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨646106535203212718780,646106535203212744616⟩,⟨(-6601615307898688495671),(-6601615307898688469080)⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨(-229758708293679033444),(-229758708293679021864)⟩,⟨(-2741215666966755634377),(-2741215666966755622508)⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨(-228125487618324907308),(-228125487618324902343)⟩,⟨(-1097794842323440476281),(-1097794842323440471211)⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨(-80204508351379945102),(-80204508351379943707)⟩,⟨(-294911153101677340908),(-294911153101677339489)⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨186732741459047350830017273,186732741459050021235340998⟩,⟨166146814727226741205578892,166146814727229411613347707⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨547728880228295625561136604,547728880228304931925907399⟩,⟨403091647121351255423673347,403091647121360561804990927⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨841632960383831594144903169,841632960383851352895447757⟩,⟨407524070809015642475309970,407524070809035401275465501⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨973428344498812220244308477,973428344498847218415673088⟩,⟨179509087686436341468519913,179509087686471339732711947⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨878132216561948946658377333,878132216561998742616079018⟩,⟨(-141251125101789332291069685),(-141251125101739536208334402)⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨599542855534389877719644531,599542855534462961566864537⟩,⟨(-374267106799051128344591355),(-374267106798978044407923575)⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨275749593021127260972553263,275749593021220157558586345⟩,⟨(-426114825591504138372399941),(-426114825591411241758873181)⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨37348123019552656785502403,37348123019630056712792131⟩,⟨(-332688577840067838460408271),(-332688577839990438540787256)⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨(-72484052804842833549436338),(-72484052804800719604926029)⟩,⟨(-193027288274902819362486605),(-193027288274860705437816679)⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨(-88434513649286627683678487),(-88434513649269706701928546)⟩,⟨(-82177510631668390931614292),(-82177510631651469965754051)⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨(-65166353241205861315687913),(-65166353241198520442538924)⟩,⟨(-20997934572831223628416635),(-20997934572823882760386145)⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨(-38110639889091683308705465),(-38110639889089253539050704)⟩,⟨3084402954624984270423377,3084402954627414039592504⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨(-19411649946167953355050154),(-19411649946167267483956316)⟩,⟨8451472952204420498184578,8451472952205106370092010⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨(-9017669591415615816267893),(-9017669591415429217011380)⟩,⟨7067697615126886317244122,7067697615127072917353029⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨(-3780300088987954762108790),(-3780300088987902507307233)⟩,⟨4187082194995577570054295,4187082194995629825397634⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨(-1023437628510366749916741),(-1023437628510355357798430)⟩,⟨1351817197576822447702020,1351817197576833840000069⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨1827879466123140236120418442,1827879466123140238540429151⟩,⟨(-1126739139817542892558790835),(-1126739139817542890252408424)⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨4776432965880097604395115263,4776432965880097611657002646⟩,⟨(-3712717205347653585881870203),(-3712717205347653578874681999)⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨5795858630337494624896490716,5795858630337494636871453933⟩,⟨(-6874075364583024727956688211),(-6874075364583024716163532340)⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨4319623102910233545677060007,4319623102910233561886010105⟩,⟨(-9918339376820589888102921943),(-9918339376820589871813864629)⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨826761425603034320293702682,826761425603034339870238944⟩,⟨(-11494846672006502269868478066),(-11494846672006502249912195765)⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨(-3233373288266948815456322845),(-3233373288266948794157847001)⟩,⟨(-10597743829771770344512071333),(-10597743829771770322650707332)⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨(-6165809870717808026765198372),(-6165809870717808004616354446)⟩,⟨(-7464137595195215721975932709),(-7464137595195215699343398124)⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨(-6996195237013777232866719681),(-6996195237013777205870168866)⟩,⟨(-3470825697719519566178307932),(-3470825697719519538998062168)⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨(-5933044206750682415236911502),(-5933044206750682358765410178)⟩,⟨(-148997572258449746705916090),(-148997572258449690222348362)⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨(-3969570981950666332301485709),(-3969570981950666129949633728)⟩,⟨1715711877146521574028917913,1715711877146521776355242776⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨(-2093266657941525098204514838),(-2093266657941524455688455285)⟩,⟨2229313251170046341678054668,2229313251170046984187996315⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨(-803222565204542677053940777),(-803222565204540914800268709)⟩,⟨1946899337950684901356935970,1946899337950686663624407677⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨(-128529352967505295144396765),(-128529352967501353334339706)⟩,⟨1394490435375287982603212050,1394490435375291924430309721⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨118500586514969348498439815,118500586514974990739126225⟩,⟨867264719545711968044380137,867264719545717610295577967⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨135583053970910048493843006,135583053970915131788588048⟩,⟨455863825519356961796202724,455863825519362045095291721⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨53830704643173759450965493,53830704643175792338091690⟩,⟨140290702767285288839680155,140290702767287321727886256⟩⟩
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
noncomputable def ans : CBox := ⟨⟨(-1237360778511536634336309595),(-1237360778511461774488015059)⟩,⟨(-7737839670830944557508251842),(-7737839670830869697405599439)⟩⟩
lemma checked : cachedMomentRuleBox density0 kernel7_0 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (tableMomentRule false 7 0) := by
  rw [← checked]
  simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Bool.false_eq_true,ite_false,ite_true] using @tableRule_contains_bridge false 7 false density0 kernel7_0
    density0_contains kernel7_0_contains
noncomputable def atomAnswer : CBox := ⟨⟨(-3623898971532113211317326047),(-3623898971532113208125010435)⟩,⟨(-6932064482439222866706774708),(-6932064482439222863394048234)⟩⟩
lemma atomChecked : tableAtomBox false atomKernel7_0 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (tableMomentAtom false 7 0) := by
  rw [← atomChecked]
  exact tableAtomBox_contains false atomKernel7_0_contains
noncomputable def realAnswer : RBox := ⟨(-4861259750043649845753635642),(-4861259750043574982513025494)⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma KContains : realAnswer.Contains (tableMomentK false 7 0) := by
  rw [← realChecked]
  exact tableMomentK_contains atomContains contains (by norm_num) (by norm_num)
end tm0_7_0

namespace tm0_7_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density0 j i k).mul (kernel7_1 j i k))
noncomputable def s0_0 : CBox := ⟨⟨(-10561145),(-10561119)⟩,⟨(-8315978),(-8315953)⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨(-15848860),(-15848817)⟩,⟨(-23420314),(-23420270)⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨740948,741008⟩,⟨(-23613624),(-23613562)⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨10311750,10311827⟩,⟨(-6770553),(-6770474)⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨3495041,3495134⟩,⟨3095614,3095706⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨(-1040546),(-1040452)⟩,⟨983423,983520⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨(-128291),(-128189)⟩,⟨(-375485),(-375379)⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨102439,102540⟩,⟨42554,42658⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨(-33843),(-33742)⟩,⟨8193,8292⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨9384,9480⟩,⟨(-9309),(-9212)⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨(-1356),(-1269)⟩,⟨6150,6233⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨(-2078),(-2004)⟩,⟨(-3173),(-3099)⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨2509,2567⟩,⟨(-346),(-283)⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨156,202⟩,⟨1782,1830⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨(-974),(-939)⟩,⟨600,634⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨(-403),(-384)⟩,⟨(-5),19⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨966123652340115,966123652340139⟩,⟨1453699018937275,1453699018937299⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨1927956854425152,1927956854425187⟩,⟨3216081273079775,3216081273079814⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨1368277239132940,1368277239132990⟩,⟨2914641328762531,2914641328762582⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨447801102278604,447801102278665⟩,⟨1631098773622906,1631098773622968⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨3870087447172,3870087447246⟩,⟨606449383386370,606449383386446⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨(-57207728386258),(-57207728386176)⟩,⟨147823987222619,147823987222700⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨(-24789446939905),(-24789446939817)⟩,⟨20429920948009,20429920948096⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨(-5404011556141),(-5404011556046)⟩,⟨129717617537,129717617632⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨(-569964095528),(-569964095427)⟩,⟨(-584020601202),(-584020601105)⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨22429816219,22429816317⟩,⟨(-118089181935),(-118089181839)⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨17812938667,17812938756⟩,⟨(-5998058402),(-5998058313)⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨2430419205,2430419289⟩,⟨2326494969,2326495054⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨(-162050223),(-162050153)⟩,⟨709549345,709549417⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨(-172866879),(-172866822)⟩,⟨86757235,86757290⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨(-58520007),(-58519964)⟩,⟨(-10548606),(-10548566)⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨(-12302374),(-12302350)⟩,⟨(-7009365),(-7009338)⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨(-1368267985810438232886),(-1368267985810438227489)⟩,⟨1432509750741735451760,1432509750741735457166⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨(-3053610598304448498228),(-3053610598304448484880)⟩,⟨3661684412632035049619,3661684412632035063031⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨(-2748475019929182887857),(-2748475019929182872190)⟩,⟨4328488070359073703201,4328488070359073719015⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨(-1410405031362118741418),(-1410405031362118728384)⟩,⟨3473959886375903850495,3473959886375903863714⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨(-351325798482549857889),(-351325798482549849575)⟩,⟨2025835946980016088018,2025835946980016096481⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨49486167175186420544,49486167175186424773⟩,⟨884094781730368517539,884094781730368521851⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨84664878103142643369,84664878103142645150⟩,⟨298119201651376845740,298119201651376847552⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨41492003907837615866,41492003907837616527⟩,⟨81398692056437331023,81398692056437331691⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨13818188216848354007,13818188216848354264⟩,⟨19227018156926015981,19227018156926016240⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨3740472309352314125,3740472309352314263⟩,⟨4266571030008875913,4266571030008876053⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨913625541394026019,913625541394026134⟩,⟨968179708114704882,968179708114704998⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨218013763424769013,218013763424769115⟩,⟨240141242483878389,240141242483878490⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨54049571432914334,54049571432914420⟩,⟨67452757080344074,67452757080344160⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨14506588001823470,14506588001823539⟩,⟨21491810050559590,21491810050559657⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨4184784979160439,4184784979160484⟩,⟨7334731785147233,7334731785147277⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨936277374687019,936277374687047⟩,⟨1825989699702375,1825989699702402⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨7821265035394315968979125,7821265035394330914000580⟩,⟨953993818943550348852090,953993818943565292868481⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨20664923216928590966243102,20664923216928623226598036⟩,⟨776328197683043195197178,776328197683075453244797⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨26163805829479733338213060,26163805829479760087184053⟩,⟨(-3318636810667779640325796),(-3318636810667752893436039)⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨23137106322083461006458885,23137106322083473144020741⟩,⟨(-8774906110720157359247687),(-8774906110720145222438116)⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨14768536692105534930407899,14768536692105538046307933⟩,⟨(-11507654692616534187211000),(-11507654692616531070737889)⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨6296951459765052473277480,6296951459765052928980954⟩,⟨(-10095881742460873672881360),(-10095881742460873216020459)⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨1099526673930018835748057,1099526673930018885087081⟩,⟨(-6442366577069025027848474),(-6442366577069024977633871)⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨(-754134273426972210574347),(-754134273426972199388788)⟩,⟨(-3092901635160308934021265),(-3092901635160308922597080)⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨(-851106978784366556180592),(-851106978784366551574300)⟩,⟨(-1125654814946483911535803),(-1125654814946483906926195)⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨(-503833026009235305482805),(-503833026009235303331206)⟩,⟨(-297765088096442940665001),(-297765088096442938550754)⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨(-230304859949997353629668),(-230304859949997352646529)⟩,⟨(-41586114101047265149999),(-41586114101047264193224)⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨(-92317369506644066202967),(-92317369506644065757364)⟩,⟨12052857347875573775060,12052857347875574211562⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨(-35106958081734518242849),(-35106958081734518040455)⟩,⟨14151813737383824866141,14151813737383825066209⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨(-13307117850846857419427),(-13307117850846857327940)⟩,⟨8643409136931900868551,8643409136931900959524⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨(-4960888773960585892706),(-4960888773960585853411)⟩,⟨4225455818319606853901,4225455818319606893119⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨(-1279608626219911998017),(-1279608626219911987042)⟩,⟨1241767203922601960662,1241767203922601971628⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨547071374487599164547335491,547071374487610075788319435⟩,⟨(-880835001208826306193406026),(-880835001208815395002221082)⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨1257391827285988942756782206,1257391827286026579688272532⟩,⟨(-2534163220284551894966103987),(-2534163220284514258212363668)⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨1051237853245581556833678338,1051237853245659703849432359⟩,⟨(-3767018864720407815332183313),(-3767018864720329668675061741)⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨(-15315847448897588530265397),(-15315847448764623176356997)⟩,⟨(-4172757439357829833044252675),(-4172757439357696868236648204)⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨(-1316078831631661625509471928),(-1316078831631451906315638602)⟩,⟨(-3551937848054741160266542168),(-3551937848054531441630572706)⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨(-2109111633996259461220293974),(-2109111633995906989493701018)⟩,⟨(-2199001124673828205611309121),(-2199001124673475734143238404)⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨(-2079897109023901780835485985),(-2079897109023481708291740390)⟩,⟨(-771760232954436590413424517),(-771760232954016517884220553)⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨(-1474413392168482544386599631),(-1474413392168156015550610442)⟩,⟨179064501301142118645217749,179064501301468647587735510⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨(-763588504458331878325235297),(-763588504458165035326534176)⟩,⟨529201173812093291078118923,529201173812260134200150210⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨(-258878913545799282726719658),(-258878913545710187562025792)⟩,⟨488046654963563193770059163,488046654963652288986186744⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨(-11758633435292511921816497),(-11758633435255917410193168)⟩,⟨317808655442907121144555113,317808655442943715662934446⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨64786435347151297225850315,64786435347162491176935062⟩,⟨167991028872480645163300152,167991028872491839106675683⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨65672845088343632885447724,65672845088346554861752816⟩,⟨76581554876269921503773105,76581554876272843470948710⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨45513999055040478574289359,45513999055041218681229433⟩,⟨31076961584234496310431418,31076961584235236410816665⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨24924208862900812517045262,24924208862901048336267081⟩,⟨11171104114260933547517434,11171104114261169363741357⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨7787624343943136191675512,7787624343943194195690022⟩,⟨2683692857647296916498082,2683692857647354919705060⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨(-4417899747386419077856539399),(-4417899747386419069152448055)⟩,⟨(-6390463947482317971877143346),(-6390463947482317962821466913)⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨(-14389329679733437036251267055),(-14389329679733437009734406137)⟩,⟨(-16561986115457039320694385442),(-16561986115457039293434819877)⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨(-26241578592184732884959131666),(-26241578592184732840087915485)⟩,⟨(-19611512886158875008081303329),(-19611512886158874962836004145)⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨(-37334322334861000267687630789),(-37334322334861000205197834591)⟩,⟨(-13459789490746292979947454168),(-13459789490746292918106946489)⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨(-42651975941651769773373090578),(-42651975941651769695959238329)⟩,⟨27491512743930856204852139,27491512743930931861460891⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨(-38517953391621921445876144023),(-38517953391621921359942060178)⟩,⟨15283381379848829288885122172,15283381379848829372434210411⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨(-25986826779131041551425302687),(-25986826779131041458791097656)⟩,⟨25828996921323524379300234116,25828996921323524470252760581⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨(-10474769196572679070899128450),(-10474769196572678959165185764)⟩,⟨28044133960250205324901962690,28044133960250205436095522830⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨2060638431524246320938986559,2060638431524246545540617979⟩,⟨22961693976269153693186395611,22961693976269153917840310577⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨8665887718305558663552004826,8665887718305559427832628855⟩,⟨14652345383400361624579851153,14652345383400362388996395159⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨9946057361021964657682188769,9946057361021967085372874127⟩,⟨7052326716940891321339123967,7052326716940893749051081886⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨8244099586938748043639915378,8244099586938755882287785519⟩,⟨2053009912866615656170746646,2053009912866623494758319011⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨5694822846061527928648340163,5694822846061544926183267221⟩,⟨(-364979914512290652049943658),(-364979914512273654576268146)⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨3436487665607753279221275811,3436487665607777044399562682⟩,⟨(-1057827872888952357935729607),(-1057827872888928592789762677)⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨1763222465621199190898320202,1763222465621220248934927774⟩,⟨(-866390721358062771169645991),(-866390721358041713143257891)⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨535031875092998970157723220,535031875093007316757681088⟩,⟨(-318159606473993682740793324),(-318159606473985336142582197)⟩⟩
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
noncomputable def ans : CBox := ⟨⟨(-27422601230747531087513987375),(-27422601230747204727851294927)⟩,⟨6859251716628407431312716761,6859251716628733789774157220⟩⟩
lemma checked : cachedMomentRuleBox density0 kernel7_1 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (tableMomentRule false 7 1) := by
  rw [← checked]
  simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Bool.false_eq_true,ite_false,ite_true] using @tableRule_contains_bridge false 7 true density0 kernel7_1
    density0_contains kernel7_1_contains
noncomputable def atomAnswer : CBox := ⟨⟨(-24633322160756871695566154255),(-24633322160756871682530163007)⟩,⟨14560444179076651073431782989,14560444179076651086021210683⟩⟩
lemma atomChecked : tableAtomBox false atomKernel7_1 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (tableMomentAtom false 7 1) := by
  rw [← atomChecked]
  exact tableAtomBox_contains false atomKernel7_1_contains
noncomputable def realAnswer : RBox := ⟨(-52055923391504402783180141630),(-52055923391504076410281457934)⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma KContains : realAnswer.Contains (tableMomentK false 7 1) := by
  rw [← realChecked]
  exact tableMomentK_contains atomContains contains (by norm_num) (by norm_num)
end tm0_7_1

namespace tm1_7_0
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density1 j i k).mul (kernel7_0 j i k))
noncomputable def s0_0 : CBox := ⟨⟨253259,253275⟩,⟨92356,92372⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨443656,443672⟩,⟨354000,354016⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨113218,113234⟩,⟨458271,458287⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨(-165438),(-165422)⟩,⟨176504,176520⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨(-76619),(-76601)⟩,⟨(-43822),(-43805)⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨15010,15026⟩,⟨(-21060),(-21044)⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨3519,3538⟩,⟨5953,5970⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨(-1908),(-1890)⟩,⟨(-330),(-312)⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨540,557⟩,⟨(-290),(-274)⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨(-137),(-121)⟩,⟨195,211⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨(-7),10⟩,⟨(-131),(-114)⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨40,57⟩,⟨45,61⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨(-58),(-42)⟩,⟨4,21⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨(-16),0⟩,⟨(-44),(-28)⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨12,30⟩,⟨(-22),(-6)⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨0,16⟩,⟨(-13),5⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨(-29842441108189),(-29842441108173)⟩,⟨(-23809893744636),(-23809893744620)⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨(-61016959934273),(-61016959934257)⟩,⟨(-52830624466894),(-52830624466878)⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨(-46880990583492),(-46880990583475)⟩,⟨(-48319125155599),(-48319125155581)⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨(-19921134928780),(-19921134928764)⟩,⟨(-27716847525317),(-27716847525301)⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨(-4549351477984),(-4549351477968)⟩,⟨(-10937288979541),(-10937288979523)⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨(-161671938576),(-161671938557)⟩,⟨(-3026719601070),(-3026719601054)⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨254456205461,254456205479⟩,⟨(-553760814565),(-553760814549)⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨90557041563,90557041579⟩,⟨(-48516410941),(-48516410923)⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨14837926003,14837926021⟩,⟨4962642809,4962642826⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨660508776,660508793⟩,⟨2247460888,2247460908⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨(-264841168),(-264841151)⟩,⟨266298922,266298938⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨(-65798879),(-65798863)⟩,⟨(-21912926),(-21912910)⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨(-2866782),(-2866765)⟩,⟨(-15194519),(-15194502)⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨2798700,2798716⟩,⟨(-3137190),(-3137174)⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨1291180,1291197⟩,⟨(-223335),(-223318)⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨308643,308659⟩,⟨57257,57273⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨18945342775227063330,18945342775227063568⟩,⟨(-74131559685337354907),(-74131559685337354669)⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨34913292722659182231,34913292722659182804⟩,⟨(-180393964466184914073),(-180393964466184913498)⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨15738555874556192577,15738555874556193234⟩,⟨(-195190204271537945118),(-195190204271537944460)⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨(-9956046983702312783),(-9956046983702312262)⟩,⟨(-139452972745469851572),(-139452972745469851050)⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨(-18474436065565740325),(-18474436065565740010)⟩,⟨(-70875998046653409911),(-70875998046653409597)⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨(-13207578290320114809),(-13207578290320114657)⟩,⟨(-26436939668078015614),(-26436939668078015462)⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨(-6084103335548195290),(-6084103335548195225)⟩,⟨(-7460562675742264172),(-7460562675742264108)⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨(-2080433746981580648),(-2080433746981580619)⟩,⟨(-1667433824224418628),(-1667433824224418594)⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨(-579068203199500033),(-579068203199500011)⟩,⟨(-318903480023409892),(-318903480023409869)⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨(-142145865856677952),(-142145865856677931)⟩,⟨(-59347670147329247),(-59347670147329226)⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨(-33018978224735412),(-33018978224735389)⟩,⟨(-12566929797521682),(-12566929797521661)⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨(-7698784112142086),(-7698784112142064)⟩,⟨(-3253394782911908),(-3253394782911886)⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨(-1898276867767155),(-1898276867767138)⟩,⟨(-984032705142410),(-984032705142390)⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨(-517410493504977),(-517410493504957)⟩,⟨(-329038011266352),(-329038011266331)⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨(-154665560121917),(-154665560121900)⟩,⟨(-114644954729214),(-114644954729196)⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨(-35758141957334),(-35758141957317)⟩,⟨(-28738519961448),(-28738519961432)⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨(-477341842518198269347397),(-477341842518195941263276)⟩,⟨255213546259776223319449,255213546259778551377587⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨(-1175563634939259222495854),(-1175563634939254654962198)⟩,⟨751846972562846233935802,751846972562850801397127⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨(-1287915403629603743251473),(-1287915403629599938175416)⟩,⟨1139437233652618339369198,1139437233652622144364134⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨(-890205933472472552825041),(-890205933472470709606719)⟩,⟨1257454727373558639512253,1257454727373560482676898⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨(-345742208506007096247177),(-345742208506006587192977)⟩,⟨1054562702262225222463446,1054562702262225731499910⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨24491415603009551230519,24491415603009631393237⟩,⟨675170833100512341140064,675170833100512421308235⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨146488520384367782551882,146488520384367790440902⟩,⟨327028406643724986920996,327028406643724994821660⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨123256710630596025333753,123256710630596026177252⟩,⟨115716835599032402230865,115716835599032403082173⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨67789561611312247119273,67789561611312247378868⟩,⟨25731988450929116948421,25731988450929117209953⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨29084787604907445600450,29084787604907445711499⟩,⟨(-318589427396204005408),(-318589427396203894262)⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨10594334266936153708024,10594334266936153756704⟩,⟨(-3927882133701608252516),(-3927882133701608204027)⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨3489076489349736861927,3489076489349736883191⟩,⟨(-2689128468550076597327),(-2689128468550076576203)⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨1095593398759669553771,1095593398759669563220⟩,⟨(-1392965703236720635496),(-1392965703236720626118)⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨341613210795002060062,341613210795002064349⟩,⟨(-656753992845291894838),(-656753992845291890579)⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨105913471156057704044,105913471156057705905⟩,⟨(-284952439141265423099),(-284952439141265421247)⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨24162934319129496846,24162934319129497378⟩,⟨(-79654696736642931440),(-79654696736642930908)⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨64066069572137660864766842,64066069572139855378898601⟩,⟨51374979236429402400843133,51374979236431596915665239⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨189218795345102896478846664,189218795345110545003760126⟩,⟨127206493722286698923386068,127206493722294347447879551⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨294463160154277905343728531,294463160154294146653434371⟩,⟨135097600784575505145996201,135097600784591746448752220⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨347097077855149044226945546,347097077855177816940114215⟩,⟨69698771999014781811231590,69698771999043554507202804⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨322614902875239221151860554,322614902875280164736948715⟩,⟨(-32385764512362906972717883),(-32385764512321963413358085)⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨232390255945723587969114921,232390255945783679968350583⟩,⟨(-115356183065683887631456849),(-115356183065623795652564152)⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨120691597450359354858332172,120691597450435722094688245⟩,⟨(-143523966538070097215884275),(-143523966537993729987333196)⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨32499735898236470053550060,32499735898300068055939984⟩,⟨(-121350263167997104437947923),(-121350263167933506434649111)⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨(-13807373186983748869612715),(-13807373186949171314999136)⟩,⟨(-78020790596666748687365765),(-78020790596632171128689140)⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨(-26322202884510619628688128),(-26322202884496741809111034)⟩,⟨(-39496991725684406104266899),(-39496991725670528281434427)⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨(-22273923052518834407829092),(-22273923052512821379325234)⟩,⟨(-15591607695278597257891500),(-15591607695272584228329732)⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨(-14385643165761233578513103),(-14385643165759245989169218)⟩,⟨(-4252323788017718707722135),(-4252323788015731118247063)⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨(-8033151745340587145234034),(-8033151745340026817662968)⟩,⟨(-125487761229991458448956),(-125487761229431131012954)⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨(-4084285936383943295769092),(-4084285936383791020525497)⟩,⟨835313985919677241641780,835313985919829516737915⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨(-1856537074928884980659427),(-1856537074928842372317938)⟩,⟨691393800742326492423285,691393800742369100671514⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨(-529000973958667377689157),(-529000973958658092604987)⟩,⟨247524135334299527379868,247524135334308812433586⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨52701758708274214236020009,52701758708274214911350794⟩,⟨(-36040918465630727027092319),(-36040918465630726410357993)⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨108316072506824878568969358,108316072506824880565784505⟩,⟨(-139310866791354167279516499),(-139310866791354165410300965)⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨(-20324433112656376251745668),(-20324433112656373109319759)⟩,⟨(-271448278452934885164734457),(-271448278452934882091509427)⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨(-480164784868499513830598240),(-480164784868499509775134257)⟩,⟨(-308192045627285994806216850),(-308192045627285990637584985)⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨(-1257361876383912357209505879),(-1257361876383912351980057906)⟩,⟨(-87588728049222834397572968),(-87588728049222828831575450)⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨(-2051787071176218418116839692),(-2051787071176218411674134064)⟩,⟨446058113924397624889120300,446058113924397631839302631⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨(-2444587155791724427508257109),(-2444587155791724419272430884)⟩,⟨1164593723531015831029579919,1164593723531015839734716330⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨(-2234765059500315894446500787),(-2234765059500315880481953111)⟩,⟨1796781851045265970251458597,1796781851045265984396646814⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨(-1572773968114536807488355750),(-1572773968114536767402162035)⟩,⟨2089233046417633616072965726,2089233046417633656155001990⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨(-795941513778915732193087268),(-795941513778915571133278982)⟩,⟨1972726962106253339269020772,1972726962106253500255376482⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨(-182521019375212017420552251),(-182521019375211495871520023)⟩,⟨1575095501941839349023493353,1575095501941839870495980811⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨165429868680278483105384965,165429868680279919863314144⟩,⟨1095306531129228460268190220,1095306531129229896980075036⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨285357906315753046463419448,285357906315756265109131374⟩,⟨679152631599213100232988878,679152631599216318866732670⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨263688893418086228753454768,263688893418090839362713301⟩,⟨379846069732316760614146434,379846069732321371222880450⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨174197692242091457864147492,174197692242095613664745533⟩,⟨184688921830304503745613764,184688921830308659547690806⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨59878831175708937544461978,59878831175710599895327485⟩,⟨54411795446081656959509774,54411795446083319311096092⟩⟩
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
noncomputable def ans : CBox := ⟨⟨(-1403779395047116952141350967),(-1403779395047055461788425864)⟩,⟨1739325854574024317489353925,1739325854574085808020993779⟩⟩
lemma checked : cachedMomentRuleBox density1 kernel7_0 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (tableMomentRule true 7 0) := by
  rw [← checked]
  simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Bool.false_eq_true,ite_false,ite_true] using @tableRule_contains_bridge true 7 false density1 kernel7_0
    density1_contains kernel7_0_contains
noncomputable def atomAnswer : CBox := ⟨⟨4738944808926609579855782876,4738944808926609584030349446⟩,⟨9065007400112829898284524614,9065007400112829902616551541⟩⟩
lemma atomChecked : tableAtomBox true atomKernel7_0 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (tableMomentAtom true 7 0) := by
  rw [← atomChecked]
  exact tableAtomBox_contains true atomKernel7_0_contains
noncomputable def realAnswer : RBox := ⟨3335165413879492627614431909,3335165413879554122341923582⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma KContains : realAnswer.Contains (tableMomentK true 7 0) := by
  rw [← realChecked]
  exact tableMomentK_contains atomContains contains (by norm_num) (by norm_num)
end tm1_7_0

namespace tm1_7_1
noncomputable def chunk (j : Fin 6) (i : Fin 16) : CBox := finSum (fun k => (density1 j i k).mul (kernel7_1 j i k))
noncomputable def s0_0 : CBox := ⟨⟨(-1602514),(-1602494)⟩,⟨(-1647866),(-1647849)⟩⟩
lemma c0_0 : chunk 0 0 = s0_0 := by decide +kernel
noncomputable def s0_1 : CBox := ⟨⟨(-2132978),(-2132957)⟩,⟨(-4360381),(-4360362)⟩⟩
lemma c0_1 : chunk 0 1 = s0_1 := by decide +kernel
noncomputable def s0_2 : CBox := ⟨⟨749916,749940⟩,⟨(-3990792),(-3990770)⟩⟩
lemma c0_2 : chunk 0 2 = s0_2 := by decide +kernel
noncomputable def s0_3 : CBox := ⟨⟨1923224,1923251⟩,⟨(-838507),(-838479)⟩⟩
lemma c0_3 : chunk 0 3 = s0_3 := by decide +kernel
noncomputable def s0_4 : CBox := ⟨⟨481531,481562⟩,⟨604764,604792⟩⟩
lemma c0_4 : chunk 0 4 = s0_4 := by decide +kernel
noncomputable def s0_5 : CBox := ⟨⟨(-188253),(-188227)⟩,⟨130448,130479⟩⟩
lemma c0_5 : chunk 0 5 = s0_5 := by decide +kernel
noncomputable def s0_6 : CBox := ⟨⟨(-14066),(-14036)⟩,⟨(-60465),(-60434)⟩⟩
lemma c0_6 : chunk 0 6 = s0_6 := by decide +kernel
noncomputable def s0_7 : CBox := ⟨⟨15842,15873⟩,⟨7288,7317⟩⟩
lemma c0_7 : chunk 0 7 = s0_7 := by decide +kernel
noncomputable def s0_8 : CBox := ⟨⟨(-5477),(-5449)⟩,⟨1417,1447⟩⟩
lemma c0_8 : chunk 0 8 = s0_8 := by decide +kernel
noncomputable def s0_9 : CBox := ⟨⟨1501,1531⟩,⟨(-1664),(-1635)⟩⟩
lemma c0_9 : chunk 0 9 = s0_9 := by decide +kernel
noncomputable def s0_10 : CBox := ⟨⟨(-175),(-144)⟩,⟨1090,1117⟩⟩
lemma c0_10 : chunk 0 10 = s0_10 := by decide +kernel
noncomputable def s0_11 : CBox := ⟨⟨(-419),(-393)⟩,⟨(-552),(-528)⟩⟩
lemma c0_11 : chunk 0 11 = s0_11 := by decide +kernel
noncomputable def s0_12 : CBox := ⟨⟨446,466⟩,⟨(-102),(-76)⟩⟩
lemma c0_12 : chunk 0 12 = s0_12 := by decide +kernel
noncomputable def s0_13 : CBox := ⟨⟨47,69⟩,⟨312,336⟩⟩
lemma c0_13 : chunk 0 13 = s0_13 := by decide +kernel
noncomputable def s0_14 : CBox := ⟨⟨(-169),(-151)⟩,⟨115,135⟩⟩
lemma c0_14 : chunk 0 14 = s0_14 := by decide +kernel
noncomputable def s0_15 : CBox := ⟨⟨(-78),(-62)⟩,⟨(-1),18⟩⟩
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
noncomputable def s1_0 : CBox := ⟨⟨24709644233849,24709644233866⟩,⟨271139596376791,271139596376807⟩⟩
lemma c1_0 : chunk 1 0 = s1_0 := by decide +kernel
noncomputable def s1_1 : CBox := ⟨⟨32401996370761,32401996370783⟩,⟨576759216641390,576759216641409⟩⟩
lemma c1_1 : chunk 1 1 = s1_1 := by decide +kernel
noncomputable def s1_2 : CBox := ⟨⟨(-9704366244513),(-9704366244491)⟩,⟨485187264361867,485187264361888⟩⟩
lemma c1_2 : chunk 1 2 = s1_2 := by decide +kernel
noncomputable def s1_3 : CBox := ⟨⟨(-37432996844826),(-37432996844801)⟩,⟨245754481166528,245754481166551⟩⟩
lemma c1_3 : chunk 1 3 = s1_3 := by decide +kernel
noncomputable def s1_4 : CBox := ⟨⟨(-30740186032015),(-30740186031992)⟩,⟨81833455505200,81833455505225⟩⟩
lemma c1_4 : chunk 1 4 = s1_4 := by decide +kernel
noncomputable def s1_5 : CBox := ⟨⟨(-14194221447510),(-14194221447484)⟩,⟨17738452599240,17738452599261⟩⟩
lemma c1_5 : chunk 1 5 = s1_5 := by decide +kernel
noncomputable def s1_6 : CBox := ⟨⟨(-4202720832921),(-4202720832894)⟩,⟨1983618496366,1983618496394⟩⟩
lemma c1_6 : chunk 1 6 = s1_6 := by decide +kernel
noncomputable def s1_7 : CBox := ⟨⟨(-785611896560),(-785611896534)⟩,⟨(-138916587530),(-138916587504)⟩⟩
lemma c1_7 : chunk 1 7 = s1_7 := by decide +kernel
noncomputable def s1_8 : CBox := ⟨⟨(-71442727289),(-71442727261)⟩,⟨(-101030382596),(-101030382566)⟩⟩
lemma c1_8 : chunk 1 8 = s1_8 := by decide +kernel
noncomputable def s1_9 : CBox := ⟨⟨5777742676,5777742707⟩,⟨(-17946074298),(-17946074269)⟩⟩
lemma c1_9 : chunk 1 9 = s1_9 := by decide +kernel
noncomputable def s1_10 : CBox := ⟨⟨2993508566,2993508595⟩,⟨(-686734967),(-686734936)⟩⟩
lemma c1_10 : chunk 1 10 = s1_10 := by decide +kernel
noncomputable def s1_11 : CBox := ⟨⟨378760600,378760630⟩,⟨432541559,432541588⟩⟩
lemma c1_11 : chunk 1 11 = s1_11 := by decide +kernel
noncomputable def s1_12 : CBox := ⟨⟨(-40147621),(-40147594)⟩,⟨123223221,123223244⟩⟩
lemma c1_12 : chunk 1 12 = s1_12 := by decide +kernel
noncomputable def s1_13 : CBox := ⟨⟨(-33192548),(-33192523)⟩,⟨12648916,12648938⟩⟩
lemma c1_13 : chunk 1 13 = s1_13 := by decide +kernel
noncomputable def s1_14 : CBox := ⟨⟨(-10661974),(-10661952)⟩,⟨(-3190072),(-3190052)⟩⟩
lemma c1_14 : chunk 1 14 = s1_14 := by decide +kernel
noncomputable def s1_15 : CBox := ⟨⟨(-2148632),(-2148613)⟩,⟨(-1589883),(-1589865)⟩⟩
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
noncomputable def s2_0 : CBox := ⟨⟨(-432575597595732175382),(-432575597595732173639)⟩,⟨113562548020812854168,113562548020812855915⟩⟩
lemma c2_0 : chunk 2 0 = s2_0 := by decide +kernel
noncomputable def s2_1 : CBox := ⟨⟨(-1023126030408995784269),(-1023126030408995779926)⟩,⟨338851225465843995473,338851225465843999821⟩⟩
lemma c2_1 : chunk 2 1 = s2_1 := by decide +kernel
noncomputable def s2_2 : CBox := ⟨⟨(-1047191311535638334697),(-1047191311535638329697)⟩,⟨491153994405633996267,491153994405634001273⟩⟩
lemma c2_2 : chunk 2 2 = s2_2 := by decide +kernel
noncomputable def s2_3 : CBox := ⟨⟨(-687520731225250232743),(-687520731225250228782)⟩,⟨472467140513690119970,472467140513690123940⟩⟩
lemma c2_3 : chunk 2 3 = s2_3 := by decide +kernel
noncomputable def s2_4 : CBox := ⟨⟨(-308127085091913725341),(-308127085091913722989)⟩,⟨317969733050053673235,317969733050053675594⟩⟩
lemma c2_4 : chunk 2 4 = s2_4 := by decide +kernel
noncomputable def s2_5 : CBox := ⟨⟨(-93729538930473378914),(-93729538930473377824)⟩,⟨155359053745476809524,155359053745476810618⟩⟩
lemma c2_5 : chunk 2 5 = s2_5 := by decide +kernel
noncomputable def s2_6 : CBox := ⟨⟨(-17823227334956735634),(-17823227334956735213)⟩,⟨57448166136063084265,57448166136063084688⟩⟩
lemma c2_6 : chunk 2 6 = s2_6 := by decide +kernel
noncomputable def s2_7 : CBox := ⟨⟨(-1127782841366761497),(-1127782841366761342)⟩,⟨16938696153060102659,16938696153060102816⟩⟩
lemma c2_7 : chunk 2 7 = s2_7 := by decide +kernel
noncomputable def s2_8 : CBox := ⟨⟨558345654252371117,558345654252371188⟩,⟨4255889023034377679,4255889023034377753⟩⟩
lemma c2_8 : chunk 2 8 = s2_8 := by decide +kernel
noncomputable def s2_9 : CBox := ⟨⟨265612333385412048,265612333385412103⟩,⟨984600495783953225,984600495783953283⟩⟩
lemma c2_9 : chunk 2 9 = s2_9 := by decide +kernel
noncomputable def s2_10 : CBox := ⟨⟨74948512666091279,74948512666091335⟩,⟨226166425542426879,226166425542426938⟩⟩
lemma c2_10 : chunk 2 10 = s2_10 := by decide +kernel
noncomputable def s2_11 : CBox := ⟨⟨17317339690979042,17317339690979101⟩,⟨54638479729960979,54638479729961038⟩⟩
lemma c2_11 : chunk 2 11 = s2_11 := by decide +kernel
noncomputable def s2_12 : CBox := ⟨⟨3663881488187095,3663881488187144⟩,⟨14415685182263105,14415685182263152⟩⟩
lemma c2_12 : chunk 2 12 = s2_12 := by decide +kernel
noncomputable def s2_13 : CBox := ⟨⟨760647903433719,760647903433755⟩,⟨4246130757727834,4246130757727872⟩⟩
lemma c2_13 : chunk 2 13 = s2_13 := by decide +kernel
noncomputable def s2_14 : CBox := ⟨⟨160005525601341,160005525601371⟩,⟨1355555910965700,1355555910965725⟩⟩
lemma c2_14 : chunk 2 14 = s2_14 := by decide +kernel
noncomputable def s2_15 : CBox := ⟨⟨27536810410424,27536810410444⟩,⟨325379261304319,325379261304337⟩⟩
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
noncomputable def s3_0 : CBox := ⟨⟨1905393724221466650759355,1905393724221479203255523⟩,⟨1818549586367480714283230,1818549586367493266884238⟩⟩
lemma c3_0 : chunk 3 0 = s3_0 := by decide +kernel
noncomputable def s3_1 : CBox := ⟨⟨5292538258737474582229423,5292538258737501658180148⟩,⟨4288224622097484612606554,4288224622097511688798439⟩⟩
lemma c3_1 : chunk 3 1 = s3_1 := by decide +kernel
noncomputable def s3_2 : CBox := ⟨⟨7332185067066551592290146,7332185067066574007529709⟩,⟨4193279955437849149414176,4193279955437871564870812⟩⟩
lemma c3_2 : chunk 3 2 = s3_2 := by decide +kernel
noncomputable def s3_3 : CBox := ⟨⟨7339457301168044699298726,7339457301168054843012485⟩,⟨2110572685325296229241664,2110572685325306373033266⟩⟩
lemma c3_3 : chunk 3 3 = s3_3 := by decide +kernel
noncomputable def s3_4 : CBox := ⟨⟨5563411058101093735812067,5563411058101096326182302⟩,⟨(-172022844464554430422946),(-172022844464551840112455)⟩⟩
lemma c3_4 : chunk 3 4 = s3_4 := by decide +kernel
noncomputable def s3_5 : CBox := ⟨⟨3167755357602504709819073,3167755357602505080822243⟩,⟨(-1331861129607617478721123),(-1331861129607617107835369)⟩⟩
lemma c3_5 : chunk 3 5 = s3_5 := by decide +kernel
noncomputable def s3_6 : CBox := ⟨⟨1291686555825169682175054,1291686555825169717392317⟩,⟨(-1326840420400163148157277),(-1326840420400163113027245)⟩⟩
lemma c3_6 : chunk 3 6 = s3_6 := by decide +kernel
noncomputable def s3_7 : CBox := ⟨⟨312100260889743427261082,312100260889743432826719⟩,⟨(-832165558389757988178036),(-832165558389757982634994)⟩⟩
lemma c3_7 : chunk 3 7 = s3_7 := by decide +kernel
noncomputable def s3_8 : CBox := ⟨⟨(-19580846778023185497634),(-19580846778023183743888)⟩,⟨(-387540452305225536335160),(-387540452305225534580991)⟩⟩
lemma c3_8 : chunk 3 8 = s3_8 := by decide +kernel
noncomputable def s3_9 : CBox := ⟨⟨(-67873806162744119565219),(-67873806162744118803554)⟩,⟨(-143185448548137243676879),(-143185448548137242911297)⟩⟩
lemma c3_9 : chunk 3 9 = s3_9 := by decide +kernel
noncomputable def s3_10 : CBox := ⟨⟨(-45122352678281521892717),(-45122352678281521551650)⟩,⟨(-43416843103228281660694),(-43416843103228281317066)⟩⟩
lemma c3_10 : chunk 3 10 = s3_10 := by decide +kernel
noncomputable def s3_11 : CBox := ⟨⟨(-22352495549108260474548),(-22352495549108260318653)⟩,⟨(-10740448076588299493005),(-10740448076588299336263)⟩⟩
lemma c3_11 : chunk 3 11 = s3_11 := by decide +kernel
noncomputable def s3_12 : CBox := ⟨⟨(-9939086339413250899088),(-9939086339413250827043)⟩,⟨(-1867324629338041186217),(-1867324629338041113972)⟩⟩
lemma c3_12 : chunk 3 12 = s3_12 := by decide +kernel
noncomputable def s3_13 : CBox := ⟨⟨(-4269922547626013613343),(-4269922547626013580204)⟩,⟨54634333625571934133,54634333625571967310⟩⟩
lemma c3_13 : chunk 3 13 = s3_13 := by decide +kernel
noncomputable def s3_14 : CBox := ⟨⟨(-1748318664024457197023),(-1748318664024457182581)⟩,⟨254875911286252101952,254875911286252116396⟩⟩
lemma c3_14 : chunk 3 14 = s3_14 := by decide +kernel
noncomputable def s3_15 : CBox := ⟨⟨(-474935185939888261584),(-474935185939888257512)⟩,⟨101391986346689378961,101391986346689383032⟩⟩
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
noncomputable def s4_0 : CBox := ⟨⟨164687874671331298455838944,164687874671340265077796469⟩,⟨(-298224743354907607320817433),(-298224743354898640693727025)⟩⟩
lemma c4_0 : chunk 4 0 = s4_0 := by decide +kernel
noncomputable def s4_1 : CBox := ⟨⟨385028572019983294382006101,385028572020014226204454005⟩,⟨(-866800257391232039383844636),(-866800257391201107537231001)⟩⟩
lemma c4_1 : chunk 4 1 = s4_1 := by decide +kernel
noncomputable def s4_2 : CBox := ⟨⟨337009854595972549164414708,337009854596036783625229549⟩,⟨(-1312452283357704264601050032),(-1312452283357640030079712590)⟩⟩
lemma c4_2 : chunk 4 2 = s4_2 := by decide +kernel
noncomputable def s4_3 : CBox := ⟨⟨18138302989579003927756040,18138302989688316103541020⟩,⟨(-1492399894402995168658318335),(-1492399894402885856377344520)⟩⟩
lemma c4_3 : chunk 4 3 = s4_3 := by decide +kernel
noncomputable def s4_4 : CBox := ⟨⟨(-401987228194544236526431938),(-401987228194371800422644473)⟩,⟨(-1321141117305907697330000540),(-1321141117305735261109804438)⟩⟩
lemma c4_4 : chunk 4 4 = s4_4 := by decide +kernel
noncomputable def s4_5 : CBox := ⟨⟨(-692136134446188653012072603),(-692136134445898839306505238)⟩,⟨(-878676282459429543394299851),(-878676282459139729625951189)⟩⟩
lemma c4_5 : chunk 4 5 = s4_5 := by decide +kernel
noncomputable def s4_6 : CBox := ⟨⟨(-726989733954481224305574407),(-726989733954135896257138464)⟩,⟨(-378637533547988311701325389),(-378637533547642983641842490)⟩⟩
lemma c4_6 : chunk 4 6 = s4_6 := by decide +kernel
noncomputable def s4_7 : CBox := ⟨⟨(-557143206281880861538746979),(-557143206281612558377819212)⟩,⟨(-16182716323688012715593616),(-16182716323419709574815605)⟩⟩
lemma c4_7 : chunk 4 7 = s4_7 := by decide +kernel
noncomputable def s4_8 : CBox := ⟨⟨(-325722681608606647593638427),(-325722681608469662596256872)⟩,⟨146224260506016991871778126,146224260506153976843400877⟩⟩
lemma c4_8 : chunk 4 8 = s4_8 := by decide +kernel
noncomputable def s4_9 : CBox := ⟨⟨(-143558752694538969878458261),(-143558752694465898489120450)⟩,⟨163032929469633730547421182,163032929469706801925915860⟩⟩
lemma c4_9 : chunk 4 9 = s4_9 := by decide +kernel
noncomputable def s4_10 : CBox := ⟨⟨(-41651762607252401410178175),(-41651762607222426022925733)⟩,⟨119236704012937768764333880,119236704012967744149915892⟩⟩
lemma c4_10 : chunk 4 10 = s4_10 := by decide +kernel
noncomputable def s4_11 : CBox := ⟨⟨(-12769107255857708200430),(-12769107246700861868765)⟩,⟨70642794722308655775598295,70642794722317812623188363⟩⟩
lemma c4_11 : chunk 4 11 = s4_11 := by decide +kernel
noncomputable def s4_12 : CBox := ⟨⟨10673182869266812607373826,10673182869269199711847110⟩,⟨36765449934381583890297873,36765449934383970996381034⟩⟩
lemma c4_12 : chunk 4 12 = s4_12 := by decide +kernel
noncomputable def s4_13 : CBox := ⟨⟨9765434250260500760670404,9765434250261104700208346⟩,⟨17514029715935301584945810,17514029715935905525633639⟩⟩
lemma c4_13 : chunk 4 13 = s4_13 := by decide +kernel
noncomputable def s4_14 : CBox := ⟨⟨5952829108652596672772999,5952829108652788945664970⟩,⟨7521326207099447727555531,7521326207099640000967956⟩⟩
lemma c4_14 : chunk 4 14 = s4_14 := by decide +kernel
noncomputable def s4_15 : CBox := ⟨⟨1941921579190953682397700,1941921579191000955627355⟩,⟨2068696663082741540345741,2068696663082788813713461⟩⟩
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
noncomputable def s5_0 : CBox := ⟨⟨(-140221209035459723370724822),(-140221209035459721082737722)⟩,⟨(-183573583916150822195914669),(-183573583916150819739842370)⟩⟩
lemma c5_0 : chunk 5 0 = s5_0 := by decide +kernel
noncomputable def s5_1 : CBox := ⟨⟨(-525884728592999543399139846),(-525884728592999536464825060)⟩,⟨(-364594525824317095958752235),(-364594525824317088694085844)⟩⟩
lemma c5_1 : chunk 5 1 = s5_1 := by decide +kernel
noncomputable def s5_2 : CBox := ⟨⟨(-982732299410880063401389036),(-982732299410880052009586093)⟩,⟨132368602256209001618975285,132368602256209013053308067⟩⟩
lemma c5_2 : chunk 5 2 = s5_2 := by decide +kernel
noncomputable def s5_3 : CBox := ⟨⟨(-1013304072310068741717343431),(-1013304072310068726267492990)⟩,⟨1832174939836449088121917648,1832174939836449102896863006⟩⟩
lemma c5_3 : chunk 5 3 = s5_3 := by decide +kernel
noncomputable def s5_4 : CBox := ⟨⟨15638326521013533078907283,15638326521013553870206322⟩,⟨4667220987048662927488067902,4667220987048662946769397145⟩⟩
lemma c5_4 : chunk 5 4 = s5_4 := by decide +kernel
noncomputable def s5_5 : CBox := ⟨⟨2291332180858142781584706652,2291332180858142807875298306⟩,⟨7515761747501254578607405877,7515761747501254602780873920⟩⟩
lemma c5_5 : chunk 5 5 = s5_5 := by decide +kernel
noncomputable def s5_6 : CBox := ⟨⟨5241605375306816149481567707,5241605375306816184779138957⟩,⟨8811800628666014521642667775,8811800628666014555363020484⟩⟩
lemma c5_6 : chunk 5 6 = s5_6 := by decide +kernel
noncomputable def s5_7 : CBox := ⟨⟨7735495537730886689180626760,7735495537730886746427185171⟩,⟨7815550382740434397943242043,7815550382740434454714018147⟩⟩
lemma c5_7 : chunk 5 7 = s5_7 := by decide +kernel
noncomputable def s5_8 : CBox := ⟨⟨8763622145490165989733614605,8763622145490166146892696867⟩,⟨5143476495293544996707038129,5143476495293545154045990312⟩⟩
lemma c5_8 : chunk 5 8 = s5_8 := by decide +kernel
noncomputable def s5_9 : CBox := ⟨⟨8099740764654855447927616106,8099740764654856052966078571⟩,⟨2132704581227067731860915114,2132704581227068337287474795⟩⟩
lemma c5_9 : chunk 5 9 = s5_9 := by decide +kernel
noncomputable def s5_10 : CBox := ⟨⟨6321411207941505284663813415,6321411207941507252364023962⟩,⟨(-137178116830869704943551005),(-137178116830867736906208601)⟩⟩
lemma c5_10 : chunk 5 10 = s5_10 := by decide +kernel
noncomputable def s5_11 : CBox := ⟨⟨4273083484638236123236168981,4273083484638242513461625546⟩,⟨(-1308103459468954041301598746),(-1308103459468947650943703811)⟩⟩
lemma c5_11 : chunk 5 11 = s5_11 := by decide +kernel
noncomputable def s5_12 : CBox := ⟨⟨2553444137075440997140774449,2553444137075454875567289519⟩,⟨(-1578416986062619529380777398),(-1578416986062605650938818255)⟩⟩
lemma c5_12 : chunk 5 12 = s5_12 := by decide +kernel
noncomputable def s5_13 : CBox := ⟨⟨1364105815055077005782136996,1364105815055096425095739918⟩,⟨(-1321787247026981262750357195),(-1321787247026961843453613904)⟩⟩
lemma c5_13 : chunk 5 13 = s5_13 := by decide +kernel
noncomputable def s5_14 : CBox := ⟨⟨632153824221426041226475001,632153824221443256642702324⟩,⟨(-836774478835469320351693974),(-836774478835452104951274209)⟩⟩
lemma c5_14 : chunk 5 14 = s5_14 := by decide +kernel
noncomputable def s5_15 : CBox := ⟨⟨180163072274898054078917130,180163072274904879208401047⟩,⟨(-282630613822208742256863179),(-282630613822201917133235974)⟩⟩
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
noncomputable def ans : CBox := ⟨⟨7147613136854623667973654536,7147613136854891743740636148⟩,⟨4340775680407569977352556569,4340775680407838052374919562⟩⟩
lemma checked : cachedMomentRuleBox density1 kernel7_1 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (tableMomentRule true 7 1) := by
  rw [← checked]
  simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Bool.false_eq_true,ite_false,ite_true] using @tableRule_contains_bridge true 7 true density1 kernel7_1
    density1_contains kernel7_1_contains
noncomputable def atomAnswer : CBox := ⟨⟨32212805902528216815616367009,32212805902528216832663432487⟩,⟨(-19040580849561774497104660124),(-19040580849561774480641562371)⟩⟩
lemma atomChecked : tableAtomBox true atomKernel7_1 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (tableMomentAtom true 7 1) := by
  rw [← atomChecked]
  exact tableAtomBox_contains true atomKernel7_1_contains
noncomputable def realAnswer : RBox := ⟨39360419039382840483490021545,39360419039383108576504068635⟩
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma KContains : realAnswer.Contains (tableMomentK true 7 1) := by
  rw [← realChecked]
  exact tableMomentK_contains atomContains contains (by norm_num) (by norm_num)
end tm1_7_1

end SharpPlanar.CachedData

end OAI
