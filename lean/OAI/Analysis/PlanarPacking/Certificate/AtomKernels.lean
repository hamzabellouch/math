import OAI.Analysis.PlanarPacking.MomentRecurrence
import OAI.Analysis.PlanarPacking.Grid

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid
noncomputable def atomPoint0 : PointBox := ⟨⟨0,0⟩,⟨⟨2886751345948128822491487805010,2886751345948128822591487805032⟩,⟨0,0⟩⟩,⟨⟨0,0⟩,⟨2933333333333333333333333333333,2933333333333333333333333333334⟩⟩,⟨⟨999999999999999999999999999989,1000000000000000000000000000015⟩,⟨(-15),15⟩⟩,⟨⟨99875126068614995128859923084,99875126068614995129850328303⟩,⟨(-2),2⟩⟩⟩
lemma atomPoint0_contains : atomPoint0.Contains (0/6:ℝ) := by
  have ht : atomPoint0.t.Contains (0/6:ℝ) := by
    convert RBox.contains_rat 0 6 (by norm_num) using 1 <;> norm_num [atomPoint0]
    decide +kernel
  have he : PointBox.calc atomPoint0.t = atomPoint0 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains ht (by decide +kernel)
noncomputable def atomPoint1 : PointBox := ⟨⟨166666666666666666666666666666,166666666666666666666666666667⟩,⟨⟨2459717123174736984844818011358,2459717123174736984930025111996⟩,⟨1024882134656140410352007504727,1024882134656140410387510463337⟩⟩,⟨⟨(-1183431952662721893491124260363),(-1183431952662721893491124260348)⟩,⟨2440236686390532544378698224848,2440236686390532544378698224864⟩⟩,⟨⟨866025403784438646763098939526,866025403784438646763954632529⟩,⟨(-500000000000000000001210408427),(-499999999999999999999469888220)⟩⟩,⟨⟨88011921021907828079523012267,88011921021907828081313061486⟩,⟨(-117881300351469008776578899699),(-117881300351469008774941580239)⟩⟩⟩
lemma atomPoint1_contains : atomPoint1.Contains (1/6:ℝ) := by
  have ht : atomPoint1.t.Contains (1/6:ℝ) := by
    convert RBox.contains_rat 1 6 (by norm_num) using 1 <;> norm_num [atomPoint1]
    decide +kernel
  have he : PointBox.calc atomPoint1.t = atomPoint1 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains ht (by decide +kernel)
noncomputable def atomPoint2 : PointBox := ⟨⟨333333333333333333333333333333,333333333333333333333333333334⟩,⟨⟨1703656532034961272290058376722,1703656532034961272349074770188⟩,⟨1419713776695801060241715313933,1419713776695801060290895641830⟩⟩,⟨⟨(-1639344262295081967213114754110),(-1639344262295081967213114754090)⟩,⟨1567213114754098360655737704910,1567213114754098360655737704927⟩⟩,⟨⟨499999999999999999997708137538,500000000000000000000931269165⟩,⟨(-866025403784438646766051325440),(-866025403784438646762180554973)⟩⟩,⟨⟨81619205305569481307151807559,81619205305569481310396378569⟩,⟨(-280396055793447804630865756591),(-280396055793447804627615754177)⟩⟩⟩
lemma atomPoint2_contains : atomPoint2.Contains (2/6:ℝ) := by
  have ht : atomPoint2.t.Contains (2/6:ℝ) := by
    convert RBox.contains_rat 2 6 (by norm_num) using 1
    norm_num [atomPoint2]
    decide +kernel
  have he : PointBox.calc atomPoint2.t = atomPoint2 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains ht (by decide +kernel)
noncomputable def atomPoint3 : PointBox := ⟨⟨500000000000000000000000000000,500000000000000000000000000000⟩,⟨⟨1126537110613903930728385484882,1126537110613903930767409875134⟩,⟨1408171388267379913410481856103,1408171388267379913459262343918⟩⟩,⟨⟨(-1626016260162601626016260162603),(-1626016260162601626016260162601)⟩,⟨900813008130081300813008130080,900813008130081300813008130083⟩⟩,⟨⟨(-4444983321),2088366603⟩,⟨(-1000000000000000000003266674962),(-999999999999999999996733325039)⟩⟩,⟨⟨142697957066396950735325887717,142697957066396950739297566444⟩,⟨(-471767338116830861279282785979),(-471767338116830861275221116079)⟩⟩⟩
lemma atomPoint3_contains : atomPoint3.Contains (3/6:ℝ) := by
  have ht : atomPoint3.t.Contains (3/6:ℝ) := by
    convert RBox.contains_rat 3 6 (by norm_num) using 1
    norm_num [atomPoint3]
    decide +kernel
  have he : PointBox.calc atomPoint3.t = atomPoint3 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains ht (by decide +kernel)
noncomputable def atomPoint4 : PointBox := ⟨⟨666666666666666666666666666666,666666666666666666666666666667⟩,⟨⟨764140062162739982424217360149,764140062162739982450687948391⟩,⟨1273566770271233304040362266913,1273566770271233304084479913987⟩⟩,⟨⟨(-1470588235294117647058823529418),(-1470588235294117647058823529408)⟩,⟨482352941176470588235294117645,482352941176470588235294117651⟩⟩,⟨⟨(-500000000000000000006328835244),(-499999999999999999996392351351)⟩,⟨(-866025403784438646767669145432),(-866025403784438646758206118258)⟩⟩,⟨⟨276546840654658619933702465609,276546840654658619937500463543⟩,⟨(-626318886933968865987490837754),(-626318886933968865983439240032)⟩⟩⟩
lemma atomPoint4_contains : atomPoint4.Contains (4/6:ℝ) := by
  have ht : atomPoint4.t.Contains (4/6:ℝ) := by
    convert RBox.contains_rat 4 6 (by norm_num) using 1
    norm_num [atomPoint4]
    decide +kernel
  have he : PointBox.calc atomPoint4.t = atomPoint4 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains ht (by decide +kernel)
noncomputable def atomPoint5 : PointBox := ⟨⟨833333333333333333333333333333,833333333333333333333333333334⟩,⟨⟨540562020567660013574478860754,540562020567660013593204478445⟩,⟨1126170876182625028280164293239,1126170876182625028319175996763⟩⟩,⟨⟨(-1300390117035110533159947984400),(-1300390117035110533159947984390)⟩,⟨224187256176853055916775032508,224187256176853055916775032512⟩⟩,⟨⟨(-866025403784438646770926677365),(-866025403784438646758483511404)⟩,⟨(-500000000000000000004285885012),(-499999999999999999992312631744)⟩⟩,⟨⟨437924188962394509423764780759,437924188962394509426958319345⟩,⟨(-715119061161322533370337011021),(-715119061161322533366664758504)⟩⟩⟩
lemma atomPoint5_contains : atomPoint5.Contains (5/6:ℝ) := by
  have ht : atomPoint5.t.Contains (5/6:ℝ) := by
    convert RBox.contains_rat 5 6 (by norm_num) using 1
    norm_num [atomPoint5]
    decide +kernel
  have he : PointBox.calc atomPoint5.t = atomPoint5 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains ht (by decide +kernel)
noncomputable def atomPoint6 : PointBox := ⟨⟨1000000000000000000000000000000,1000000000000000000000000000000⟩,⟨⟨398172599441121216895377628277,398172599441121216909170731728⟩,⟨995431498602803042238444070694,995431498602803042272926829319⟩⟩,⟨⟨(-1149425287356321839080459770116),(-1149425287356321839080459770114)⟩,⟨59770114942528735632183908045,59770114942528735632183908047⟩⟩,⟨⟨(-1000000000000000000006553197785),(-999999999999999999993446802219)⟩,⟨(-4196581061),8909814505⟩⟩,⟨⟨591041363234240777970266834369,591041363234240777972775244344⟩,⟨(-749036735415657815476580310485),(-749036735415657815473358766432)⟩⟩⟩
lemma atomPoint6_contains : atomPoint6.Contains (6/6:ℝ) := by
  have ht : atomPoint6.t.Contains (6/6:ℝ) := by
    convert RBox.contains_rat 6 6 (by norm_num) using 1
    norm_num [atomPoint6]
    decide +kernel
  have he : PointBox.calc atomPoint6.t = atomPoint6 := by decide +kernel
  rw [← he]
  exact PointBox.calc_contains ht (by decide +kernel)
noncomputable def atomPoints : Fin 7 → PointBox := ![atomPoint0,atomPoint1,atomPoint2,atomPoint3,atomPoint4,atomPoint5,atomPoint6]
lemma atomPoints_contains (j : Fin 7) : (atomPoints j).Contains ((j.val:ℝ)/6) := by
  fin_cases j
  · simpa [atomPoints] using atomPoint0_contains
  · simpa [atomPoints] using atomPoint1_contains
  · simpa [atomPoints] using atomPoint2_contains
  · simpa [atomPoints] using atomPoint3_contains
  · simpa [atomPoints] using atomPoint4_contains
  · simpa [atomPoints] using atomPoint5_contains
  · simpa [atomPoints] using atomPoint6_contains
noncomputable def atomKernel0_0 : Fin 7 → CBox := ![⟨⟨2886751345948128822491487805010,2886751345948128822591487805032⟩,⟨0,0⟩⟩,⟨⟨2459717123174736984844818011358,2459717123174736984930025111996⟩,⟨1024882134656140410352007504727,1024882134656140410387510463337⟩⟩,⟨⟨1703656532034961272290058376722,1703656532034961272349074770188⟩,⟨1419713776695801060241715313933,1419713776695801060290895641830⟩⟩,⟨⟨1126537110613903930728385484882,1126537110613903930767409875134⟩,⟨1408171388267379913410481856103,1408171388267379913459262343918⟩⟩,⟨⟨764140062162739982424217360149,764140062162739982450687948391⟩,⟨1273566770271233304040362266913,1273566770271233304084479913987⟩⟩,⟨⟨540562020567660013574478860754,540562020567660013593204478445⟩,⟨1126170876182625028280164293239,1126170876182625028319175996763⟩⟩,⟨⟨398172599441121216895377628277,398172599441121216909170731728⟩,⟨995431498602803042238444070694,995431498602803042272926829319⟩⟩]
lemma atomKernel0_0_eq (j : Fin 7) : atomKernel0_0 j = kernel0Box (atomPoints j) 0 := by
  fin_cases j <;> decide +kernel
lemma atomKernel0_0_contains (j : Fin 7) : (atomKernel0_0 j).Contains
    (complexTransformedFactor 0 1 0 ((j.val:ℝ)/6)) := by
  rw [atomKernel0_0_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=0) (by decide)
  have h0 := transformed_factor_zero_contains hh
  simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using h0
noncomputable def atomKernel0_1 : Fin 7 → CBox := ![⟨⟨(-26602390675435195142530321043993),(-26602390675435195141524109159245)⟩,⟨0,0⟩⟩,⟨⟨(-15046386883137311960977771542034),(-15046386883137311960120407568771)⟩,⟨(-17001868484744399809876351294364),(-17001868484744399809233270664782)⟩⟩,⟨⟨(-1076288362329791189253868592463),(-1076288362329791188660038627375)⟩,⟨(-15764114872167322034205686079730),(-15764114872167322033609422385277)⟩⟩,⟨⟨4005248804305423355782453862022,4005248804305423356175121914620⟩,⟨(-9739775289205357801899857956194),(-9739775289205357801531459575359)⟩⟩,⟨⟨4725920142797114330304028335327,4725920142797114330570378540195⟩,⟨(-5460226459805430899811586813878),(-5460226459805430899605058580158)⟩⟩,⟨⟨4220020865203592699679309874866,4220020865203592699867729265570⟩,⟨(-3001523701832900019824858424479),(-3001523701832900019711328446699)⟩⟩,⟨⟨3519762856635247957323462123219,3519762856635247957462249969389⟩,⟨(-1624727135620028673173671104732),(-1624727135620028673112217238669)⟩⟩]
lemma atomKernel0_1_eq (j : Fin 7) : atomKernel0_1 j = (kernel0Box (atomPoints j) 0).mul (piI.mul (atomPoints j).z) := by
  fin_cases j <;> decide +kernel
lemma atomKernel0_1_contains (j : Fin 7) : (atomKernel0_1 j).Contains
    (complexTransformedFactor 0 1 1 ((j.val:ℝ)/6)) := by
  rw [atomKernel0_1_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=0) (by decide)
  have h0 := transformed_factor_zero_contains hh
  rw [transformed_factor_step]
  have hzz : complexZ ((j.val:ℂ)/6) = z ((j.val:ℝ)/6) := by
    simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat] using
      complexZ_ofReal ((j.val:ℝ)/6)
  have hz := (atomPoints_contains j).2.2.1
  rw [pointZ_eq] at hz
  simpa only [Nat.zero_add,Nat.cast_one,div_one,hzz,complexZ_ofReal,Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using
    CBox.contains_mul h0 (CBox.contains_mul piI_contains hz)
noncomputable def atomKernel1_0 : Fin 7 → CBox := ![⟨⟨287235913262267589131245569,287235913262267589152589145⟩,⟨(-3),3⟩⟩,⟨⟨(-1227594407139841125053370123),(-1227594407139841124878361402)⟩,⟨225258927663398569617556379,225258927663398569785347626⟩⟩,⟨⟨(-4099475087999640329578559768),(-4099475087999640327343491894)⟩,⟨15600083655785914278280280272,15600083655785914280549783452⟩⟩,⟨⟨(-51036477369635067913459257139),(-51036477369635067901487188489)⟩,⟨93385323635182926762172010361,93385323635182926773837146635⟩⟩,⟨⟨(-294139142057855203281176399137),(-294139142057855203251857742481)⟩,⟨141367692329865808421293419379,141367692329865808447103276276⟩⟩,⟨⟨(-607731118347857408150380104706),(-607731118347857408104316711950)⟩,⟨(-110320451301813891842385438936),(-110320451301813891798653618696)⟩⟩,⟨⟨(-667529588463563842466349351680),(-667529588463563842419653782517)⟩,⟨(-586481159748591935787351906668),(-586481159748591935733302259315)⟩⟩]
lemma atomKernel1_0_eq (j : Fin 7) : atomKernel1_0 j = kernel0Box (atomPoints j) 1 := by
  fin_cases j <;> decide +kernel
lemma atomKernel1_0_contains (j : Fin 7) : (atomKernel1_0 j).Contains
    (complexTransformedFactor 1 1 0 ((j.val:ℝ)/6)) := by
  rw [atomKernel1_0_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=1) (by decide)
  have h0 := transformed_factor_zero_contains hh
  simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using h0
noncomputable def atomKernel1_1 : Fin 7 → CBox := ![⟨⟨(-2646976155858891764422936308),(-2646976155858891764217822444)⟩,⟨(-28),28⟩⟩,⟨⟨10248502049497462764170562060,10248502049497462766168665657⟩,⟨2837138858378663619951611366,2837138858378663621908620316⟩⟩,⟨⟨100526751266157010641267391192,100526751266157010664280121597⟩,⟨(-55694797749507294492877899648),(-55694797749507294469881268035)⟩⟩,⟨⟨621471044354675043360749079671,621471044354675043456196879347⟩,⟨(-3570646982377401830921203437),(-3570646982377401735081237023)⟩⟩,⟨⟨1098842859300173353297675724200,1098842859300173353464842925351⟩,⟨1144697213258281395037408564524,1144697213258281395216979041672⟩⟩,⟨⟨(-22663614851943702239959505301),(-22663614851943702026062341800)⟩,⟨2560460779786166905954461002828,2560460779786166906181594339863⟩⟩,⟨⟨(-1992454469280585019061246880751),(-1992454469280585018850163867175)⟩,⟨2520592259912149515844324457216,2520592259912149516031115751282⟩⟩]
lemma atomKernel1_1_eq (j : Fin 7) : atomKernel1_1 j = (kernel0Box (atomPoints j) 1).mul (piI.mul (atomPoints j).z) := by
  fin_cases j <;> decide +kernel
lemma atomKernel1_1_contains (j : Fin 7) : (atomKernel1_1 j).Contains
    (complexTransformedFactor 1 1 1 ((j.val:ℝ)/6)) := by
  rw [atomKernel1_1_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=1) (by decide)
  have h0 := transformed_factor_zero_contains hh
  rw [transformed_factor_step]
  have hzz : complexZ ((j.val:ℂ)/6) = z ((j.val:ℝ)/6) := by
    simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat] using
      complexZ_ofReal ((j.val:ℝ)/6)
  have hz := (atomPoints_contains j).2.2.1
  rw [pointZ_eq] at hz
  simpa only [Nat.zero_add,Nat.cast_one,div_one,hzz,complexZ_ofReal,Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using
    CBox.contains_mul h0 (CBox.contains_mul piI_contains hz)
noncomputable def atomKernel3_0 : Fin 7 → CBox := ![⟨⟨2843789610077025929,2843789610077025936⟩,⟨(-3),3⟩⟩,⟨⟨(-64228312723007910724),(-64228312723007910558)⟩,⟨266166603357464236131,266166603357464236302⟩⟩,⟨⟨(-494776904616736031147973),(-494776904616736030744849)⟩,⟨(-695181898442626142129027),(-695181898442626141728600)⟩⟩,⟨⟨(-106555917680778035558591732),(-106555917680778035421458844)⟩,⟨(-354976034124043666142003790),(-354976034124043666003755425)⟩⟩,⟨⟨15213751127784570539427089845,15213751127784570544253007311⟩,⟨(-4099688160756901354180537737),(-4099688160756901349483904669)⟩⟩,⟨⟨20629052952773211972690043554,20629052952773211997040008897⟩,⟨149592350264871972775750070482,149592350264871972801712808839⟩⟩,⟨⟨(-595922937275834702091915645087),(-595922937275834701979420127280)⟩,⟨132015435447815391188745737182,132015435447815391291484111950⟩⟩]
lemma atomKernel3_0_eq (j : Fin 7) : atomKernel3_0 j = kernel0Box (atomPoints j) 3 := by
  fin_cases j <;> decide +kernel
lemma atomKernel3_0_contains (j : Fin 7) : (atomKernel3_0 j).Contains
    (complexTransformedFactor 3 1 0 ((j.val:ℝ)/6)) := by
  rw [atomKernel3_0_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=3) (by decide)
  have h0 := transformed_factor_zero_contains hh
  simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using h0
noncomputable def atomKernel3_1 : Fin 7 → CBox := ![⟨⟨(-26206483738960704163),(-26206483738960704098)⟩,⟨(-28),28⟩⟩,⟨⟨1481959463502825266027,1481959463502825267941⟩,⟨(-1801702358473668140785),(-1801702358473668138848)⟩⟩,⟨⟨(-1144235911228454129864486),(-1144235911228454125798275)⟩,⟨5970935715710382851586040,5970935715710382855652717⟩⟩,⟨⟨(-1511765319270662542217988349),(-1511765319270662541116960688)⟩,⟨1548895291282867661132607122,1548895291282867662229291849⟩⟩,⟨⟨(-41994771009654300602998834631),(-41994771009654300573853781897)⟩,⟨(-64074876924145524496005170041),(-64074876924145524466348903640)⟩⟩,⟨⟨596599890019863798301114245875,596599890019863798426321053128⟩,⟨(-189634434098775036919004515716),(-189634434098775036800638386208)⟩⟩,⟨⟨588609623562744722558957134694,588609623562744722952945344464⟩,⟨2127104262412552993036337815244,2127104262412552993468782183206⟩⟩]
lemma atomKernel3_1_eq (j : Fin 7) : atomKernel3_1 j = (kernel0Box (atomPoints j) 3).mul (piI.mul (atomPoints j).z) := by
  fin_cases j <;> decide +kernel
lemma atomKernel3_1_contains (j : Fin 7) : (atomKernel3_1 j).Contains
    (complexTransformedFactor 3 1 1 ((j.val:ℝ)/6)) := by
  rw [atomKernel3_1_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=3) (by decide)
  have h0 := transformed_factor_zero_contains hh
  rw [transformed_factor_step]
  have hzz : complexZ ((j.val:ℂ)/6) = z ((j.val:ℝ)/6) := by
    simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat] using
      complexZ_ofReal ((j.val:ℝ)/6)
  have hz := (atomPoints_contains j).2.2.1
  rw [pointZ_eq] at hz
  simpa only [Nat.zero_add,Nat.cast_one,div_one,hzz,complexZ_ofReal,Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using
    CBox.contains_mul h0 (CBox.contains_mul piI_contains hz)
noncomputable def atomKernel4_0 : Fin 7 → CBox := ![⟨⟨282961158716610,282961158716614⟩,⟨(-3),3⟩⟩,⟨⟨(-42706143494991529),(-42706143494991525)⟩,⟨(-120926048035417579),(-120926048035417575)⟩⟩,⟨⟨3053947772385296866737,3053947772385296871889⟩,⟨(-5402739214956985245174),(-5402739214956985240000)⟩⟩,⟨⟨16903170382964137658517564,16903170382964137671935629⟩,⟨(-13880229317351426973322715),(-13880229317351426960021447)⟩⟩,⟨⟨588535793916102761833935025,588535793916102762958836647⟩,⟨3411772456086199165686422228,3411772456086199166834991902⟩⟩,⟨⟨(-65878528817845185855981007311),(-65878528817845185832427874592)⟩,⟨(-35143520097970271640063878406),(-35143520097970271616257367065)⟩⟩,⟨⟨390977274694468298190061327583,390977274694468298307974382443⟩,⟨(-321010859534684108975007802739),(-321010859534684108863412052127)⟩⟩]
lemma atomKernel4_0_eq (j : Fin 7) : atomKernel4_0 j = kernel0Box (atomPoints j) 4 := by
  fin_cases j <;> decide +kernel
lemma atomKernel4_0_contains (j : Fin 7) : (atomKernel4_0 j).Contains
    (complexTransformedFactor 4 1 0 ((j.val:ℝ)/6)) := by
  rw [atomKernel4_0_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=4) (by decide)
  have h0 := transformed_factor_zero_contains hh
  simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using h0
noncomputable def atomKernel4_1 : Fin 7 → CBox := ![⟨⟨(-2607582845927753),(-2607582845927715)⟩,⟨(-28),28⟩⟩,⟨⟨(-122191150045355554),(-122191150045355508)⟩,⟨1085822365390366632,1085822365390366679⟩⟩,⟨⟨(-42861177505166100888659),(-42861177505166100836508)⟩,⟨10872335876083759744346,10872335876083759796489⟩⟩,⟨⟨(-118739869432107462448785546),(-118739869432107462342488016)⟩,⟨(-47065263808519467727174204),(-47065263808519467620588654)⟩⟩,⟨⟨14870510372727659189857152835,14870510372727659196921171202⟩,⟨(-7889080428845410359742320073),(-7889080428845410352779682537)⟩⟩,⟨⟨(-97173103755644446269075637291),(-97173103755644446154625706676)⟩,⟨293885051024413729859965615305,293885051024413729973889646122⟩⟩,⟨⟨(-1232593686666143723165478075673),(-1232593686666143722736438517056)⟩,⟨(-1351551833658380839059320879344),(-1351551833658380838607893199339)⟩⟩]
lemma atomKernel4_1_eq (j : Fin 7) : atomKernel4_1 j = (kernel0Box (atomPoints j) 4).mul (piI.mul (atomPoints j).z) := by
  fin_cases j <;> decide +kernel
lemma atomKernel4_1_contains (j : Fin 7) : (atomKernel4_1 j).Contains
    (complexTransformedFactor 4 1 1 ((j.val:ℝ)/6)) := by
  rw [atomKernel4_1_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=4) (by decide)
  have h0 := transformed_factor_zero_contains hh
  rw [transformed_factor_step]
  have hzz : complexZ ((j.val:ℂ)/6) = z ((j.val:ℝ)/6) := by
    simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat] using
      complexZ_ofReal ((j.val:ℝ)/6)
  have hz := (atomPoints_contains j).2.2.1
  rw [pointZ_eq] at hz
  simpa only [Nat.zero_add,Nat.cast_one,div_one,hzz,complexZ_ofReal,Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using
    CBox.contains_mul h0 (CBox.contains_mul piI_contains hz)
noncomputable def atomKernel7_0 : Fin 7 → CBox := ![⟨⟨277,281⟩,⟨(-3),3⟩⟩,⟨⟨11580277,11580282⟩,⟨(-6288733),(-6288728)⟩⟩,⟨⟨(-1665710323167166),(-1665710323167162)⟩,⟨1710986465904294,1710986465904298⟩⟩,⟨⟨(-4288482058811659370282),(-4288482058811659363575)⟩,⟨1347241831520230599839,1347241831520230606532⟩⟩,⟨⟨36521831631557482951131335,36521831631557482985427878⟩,⟨3899877544961305718935797,3899877544961305753146455⟩⟩,⟨⟨(-6285013554969111273878743515),(-6285013554969111268462701209)⟩,⟨(-6478261771340776764017300108),(-6478261771340776758509615976)⟩⟩,⟨⟨144338024383918188411416917775,144338024383918188519066263138⟩,⟨249223963933666164018182252952,249223963933666164130533379093⟩⟩]
lemma atomKernel7_0_eq (j : Fin 7) : atomKernel7_0 j = kernel0Box (atomPoints j) 7 := by
  fin_cases j <;> decide +kernel
lemma atomKernel7_0_contains (j : Fin 7) : (atomKernel7_0 j).Contains
    (complexTransformedFactor 7 1 0 ((j.val:ℝ)/6)) := by
  rw [atomKernel7_0_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=7) (by decide)
  have h0 := transformed_factor_zero_contains hh
  simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using h0
noncomputable def atomKernel7_1 : Fin 7 → CBox := ![⟨⟨(-2590),(-2552)⟩,⟨(-28),28⟩⟩,⟨⟨(-112157738),(-112157680)⟩,⟨5156952,5157010⟩⟩,⟨⟨17013040262490527,17013040262490568⟩,⟨154541955914585,154541955914626⟩⟩,⟨⟨19018440239828876646774,19018440239828876700006⟩,⟨18094092713122343905337,18094092713122343958622⟩⟩,⟨⟨(-37326201238580442081012481),(-37326201238580441870754607)⟩,⟨(-174640172189637644844922541),(-174640172189637644634075644)⟩⟩,⟨⟨(-22039050446094185125438974516),(-22039050446094185099025575597)⟩,⟨30238813374675442746566322808,30238813374675442772667801795⟩⟩,⟨⟨872851388260399717489646974695,872851388260399717918514409563⟩,⟨(-568005984018613276009284490086),(-568005984018613275597655333954)⟩⟩]
lemma atomKernel7_1_eq (j : Fin 7) : atomKernel7_1 j = (kernel0Box (atomPoints j) 7).mul (piI.mul (atomPoints j).z) := by
  fin_cases j <;> decide +kernel
lemma atomKernel7_1_contains (j : Fin 7) : (atomKernel7_1 j).Contains
    (complexTransformedFactor 7 1 1 ((j.val:ℝ)/6)) := by
  rw [atomKernel7_1_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=7) (by decide)
  have h0 := transformed_factor_zero_contains hh
  rw [transformed_factor_step]
  have hzz : complexZ ((j.val:ℂ)/6) = z ((j.val:ℝ)/6) := by
    simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat] using
      complexZ_ofReal ((j.val:ℝ)/6)
  have hz := (atomPoints_contains j).2.2.1
  rw [pointZ_eq] at hz
  simpa only [Nat.zero_add,Nat.cast_one,div_one,hzz,complexZ_ofReal,Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using
    CBox.contains_mul h0 (CBox.contains_mul piI_contains hz)
noncomputable def atomKernel9_0 : Fin 7 → CBox := ![⟨⟨0,3⟩,⟨(-3),3⟩⟩,⟨⟨(-3),2⟩,⟨(-4),0⟩⟩,⟨⟨(-13055430470),(-13055430466)⟩,⟨(-125645570149),(-125645570145)⟩⟩,⟨⟨7154252614161620552,7154252614161620589⟩,⟨(-13924345974453591569),(-13924345974453591532)⟩⟩,⟨⟨(-1698695877854235861304740),(-1698695877854235858983332)⟩,⟨(-509093624274864032090577),(-509093624274864029767916)⟩⟩,⟨⟨(-1026692507277594175516071066),(-1026692507277594173128666505)⟩,⟨1953323598494588998753708432,1953323598494589001134169251⟩⟩,⟨⟨196702530130659703536642999895,196702530130659703684165160486⟩,⟨21124309294066164671702566946,21124309294066164817617441453⟩⟩]
lemma atomKernel9_0_eq (j : Fin 7) : atomKernel9_0 j = kernel0Box (atomPoints j) 9 := by
  fin_cases j <;> decide +kernel
lemma atomKernel9_0_contains (j : Fin 7) : (atomKernel9_0 j).Contains
    (complexTransformedFactor 9 1 0 ((j.val:ℝ)/6)) := by
  rw [atomKernel9_0_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=9) (by decide)
  have h0 := transformed_factor_zero_contains hh
  simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using h0
noncomputable def atomKernel9_1 : Fin 7 → CBox := ![⟨⟨(-28),0⟩,⟨(-28),28⟩⟩,⟨⟨(-31),23⟩,⟨(-8),42⟩⟩,⟨⟨(-582814768607),(-582814768566)⟩,⟨685859094687,685859094729⟩⟩,⟨⟨(-91375913998733273822),(-91375913998733273527)⟩,⟨2859794631161188478,2859794631161188773⟩⟩,⟨⟨222122721895776563286434,222122721895776577550545⟩,⟨8619414914226240484798227,8619414914226240499070203⟩⟩,⟨⟨8703009863156394059139731164,8703009863156394070573781917⟩,⟨2818607183340039793692065116,2818607183340039805139620169⟩⟩,⟨⟨39344937084074217692613206192,39344937084074218247576725826⟩,⟨(-714264540569317372231588285146),(-714264540569317371669209421945)⟩⟩]
lemma atomKernel9_1_eq (j : Fin 7) : atomKernel9_1 j = (kernel0Box (atomPoints j) 9).mul (piI.mul (atomPoints j).z) := by
  fin_cases j <;> decide +kernel
lemma atomKernel9_1_contains (j : Fin 7) : (atomKernel9_1 j).Contains
    (complexTransformedFactor 9 1 1 ((j.val:ℝ)/6)) := by
  rw [atomKernel9_1_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=9) (by decide)
  have h0 := transformed_factor_zero_contains hh
  rw [transformed_factor_step]
  have hzz : complexZ ((j.val:ℂ)/6) = z ((j.val:ℝ)/6) := by
    simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat] using
      complexZ_ofReal ((j.val:ℝ)/6)
  have hz := (atomPoints_contains j).2.2.1
  rw [pointZ_eq] at hz
  simpa only [Nat.zero_add,Nat.cast_one,div_one,hzz,complexZ_ofReal,Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using
    CBox.contains_mul h0 (CBox.contains_mul piI_contains hz)
noncomputable def atomKernel12_0 : Fin 7 → CBox := ![⟨⟨0,3⟩,⟨(-3),3⟩⟩,⟨⟨0,4⟩,⟨(-3),2⟩⟩,⟨⟨(-7456),(-7452)⟩,⟨48027,48031⟩⟩,⟨⟨(-2433521169088633),(-2433521169088629)⟩,⟨2104633841203363,2104633841203366⟩⟩,⟨⟨(-10126433418478817995544),(-10126433418478817959972)⟩,⟨15855193807734678938298,15855193807734678973769⟩⟩,⟨⟨(-190318804329798986529500314),(-190318804329798986262853704)⟩,⟨186919098208693442779401710,186919098208693443043376098⟩⟩,⟨⟨(-29985267079005839469470031008),(-29985267079005839367492391446)⟩,⟨108564951811294072989478110531,108564951811294073091885636862⟩⟩]
lemma atomKernel12_0_eq (j : Fin 7) : atomKernel12_0 j = kernel0Box (atomPoints j) 12 := by
  fin_cases j <;> decide +kernel
lemma atomKernel12_0_contains (j : Fin 7) : (atomKernel12_0 j).Contains
    (complexTransformedFactor 12 1 0 ((j.val:ℝ)/6)) := by
  rw [atomKernel12_0_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=12) (by decide)
  have h0 := transformed_factor_zero_contains hh
  simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using h0
noncomputable def atomKernel12_1 : Fin 7 → CBox := ![⟨⟨(-28),0⟩,⟨(-28),28⟩⟩,⟨⟨(-42),8⟩,⟨(-31),23⟩⟩,⟨⟨284036,284077⟩,⟨(-198104),(-198063)⟩⟩,⟨⟨17637895069707079,17637895069707107⟩,⟨6475021789587754,6475021789587784⟩⟩,⟨⟨88595980360819229063312,88595980360819229281375⟩,⟨22757742687381368101870,22757742687381368320190⟩⟩,⟨⟨897662343959606823409130490,897662343959606824678201911⟩,⟨645860594990278562951585548,645860594990278564229728316⟩⟩,⟨⟨397661302041150198906510073424,397661302041150199296720796209⟩,⟨87891975067646749052475051597,87891975067646749440357915747⟩⟩]
lemma atomKernel12_1_eq (j : Fin 7) : atomKernel12_1 j = (kernel0Box (atomPoints j) 12).mul (piI.mul (atomPoints j).z) := by
  fin_cases j <;> decide +kernel
lemma atomKernel12_1_contains (j : Fin 7) : (atomKernel12_1 j).Contains
    (complexTransformedFactor 12 1 1 ((j.val:ℝ)/6)) := by
  rw [atomKernel12_1_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=12) (by decide)
  have h0 := transformed_factor_zero_contains hh
  rw [transformed_factor_step]
  have hzz : complexZ ((j.val:ℂ)/6) = z ((j.val:ℝ)/6) := by
    simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat] using
      complexZ_ofReal ((j.val:ℝ)/6)
  have hz := (atomPoints_contains j).2.2.1
  rw [pointZ_eq] at hz
  simpa only [Nat.zero_add,Nat.cast_one,div_one,hzz,complexZ_ofReal,Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using
    CBox.contains_mul h0 (CBox.contains_mul piI_contains hz)
noncomputable def atomKernel13_0 : Fin 7 → CBox := ![⟨⟨0,3⟩,⟨(-3),3⟩⟩,⟨⟨(-4),0⟩,⟨(-2),3⟩⟩,⟨⟨(-341),(-337)⟩,⟨98,102⟩⟩,⟨⟨(-169976153021903),(-169976153021900)⟩,⟨(-84606803526621),(-84606803526617)⟩⟩,⟨⟨(-3263693326028840015143),(-3263693326028840004989)⟩,⟨(-2537037848528971869479),(-2537037848528971859297)⟩⟩,⟨⟨(-19618607417581830024810844),(-19618607417581829855857605)⟩,⟨(-130432011910631655003953346),(-130432011910631654833571214)⟩⟩,⟨⟨(-18541242464926204931798182214),(-18541242464926204806447611936)⟩,⟨(-91487929281433214680992385330),(-91487929281433214554185512444)⟩⟩]
lemma atomKernel13_0_eq (j : Fin 7) : atomKernel13_0 j = kernel0Box (atomPoints j) 13 := by
  fin_cases j <;> decide +kernel
lemma atomKernel13_0_contains (j : Fin 7) : (atomKernel13_0 j).Contains
    (complexTransformedFactor 13 1 0 ((j.val:ℝ)/6)) := by
  rw [atomKernel13_0_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=13) (by decide)
  have h0 := transformed_factor_zero_contains hh
  simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using h0
noncomputable def atomKernel13_1 : Fin 7 → CBox := ![⟨⟨(-28),0⟩,⟨(-28),28⟩⟩,⟨⟨(-8),42⟩,⟨(-23),31⟩⟩,⟨⟨2163,2205⟩,⟨1233,1274⟩⟩,⟨⟨48835088491071,48835088491101⟩,⟨1107722107138669,1107722107138696⟩⟩,⟨⟨(-6775428697773202029332),(-6775428697773201966850)⟩,⟨18922744590791917501633,18922744590791917564035⟩⟩,⟨⟨(-519035897525465939974967179),(-519035897525465939158171005)⟩,⟨172011742142599044405582776,172011742142599045216355299⟩⟩,⟨⟨(-326883743568561696968067370144),(-326883743568561696485564285752)⟩,⟨84131904661401513556648150900,84131904661401514033371076133⟩⟩]
lemma atomKernel13_1_eq (j : Fin 7) : atomKernel13_1 j = (kernel0Box (atomPoints j) 13).mul (piI.mul (atomPoints j).z) := by
  fin_cases j <;> decide +kernel
lemma atomKernel13_1_contains (j : Fin 7) : (atomKernel13_1 j).Contains
    (complexTransformedFactor 13 1 1 ((j.val:ℝ)/6)) := by
  rw [atomKernel13_1_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=13) (by decide)
  have h0 := transformed_factor_zero_contains hh
  rw [transformed_factor_step]
  have hzz : complexZ ((j.val:ℂ)/6) = z ((j.val:ℝ)/6) := by
    simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat] using
      complexZ_ofReal ((j.val:ℝ)/6)
  have hz := (atomPoints_contains j).2.2.1
  rw [pointZ_eq] at hz
  simpa only [Nat.zero_add,Nat.cast_one,div_one,hzz,complexZ_ofReal,Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using
    CBox.contains_mul h0 (CBox.contains_mul piI_contains hz)
noncomputable def atomKernel15_0 : Fin 7 → CBox := ![⟨⟨(-3),3⟩,⟨(-3),3⟩⟩,⟨⟨(-2),3⟩,⟨0,4⟩⟩,⟨⟨(-2),2⟩,⟨(-4),0⟩⟩,⟨⟨625573895434,625573895437⟩,⟨(-214227081645),(-214227081642)⟩⟩,⟨⟨132384326353275230385,132384326353275230804⟩,⟨149359938803361118801,149359938803361119222⟩⟩,⟨⟨(-28810067062832780021385073),(-28810067062832779936816669)⟩,⟨14486376964375100047519274,14486376964375100131573904⟩⟩,⟨⟨(-58231720871487424966415309699),(-58231720871487424854159620381)⟩,⟨(-26845578778470410410385226492),(-26845578778470410298096885403)⟩⟩]
lemma atomKernel15_0_eq (j : Fin 7) : atomKernel15_0 j = kernel0Box (atomPoints j) 15 := by
  fin_cases j <;> decide +kernel
lemma atomKernel15_0_contains (j : Fin 7) : (atomKernel15_0 j).Contains
    (complexTransformedFactor 15 1 0 ((j.val:ℝ)/6)) := by
  rw [atomKernel15_0_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=15) (by decide)
  have h0 := transformed_factor_zero_contains hh
  simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using h0
noncomputable def atomKernel15_1 : Fin 7 → CBox := ![⟨⟨(-28),28⟩,⟨(-28),28⟩⟩,⟨⟨(-23),31⟩,⟨(-42),8⟩⟩,⟨⟨(-31),10⟩,⟨(-11),30⟩⟩,⟨⟨(-2864698396932),(-2864698396907)⟩,⟨(-2589347110637),(-2589347110612)⟩⟩,⟨⟨489431859984239291916,489431859984239294500⟩,⟨(-837947705130953727508),(-837947705130953724930)⟩⟩,⟨⟨79472213774095043298203588,79472213774095043701406556⟩,⟨107494824575706493716140980,107494824575706494121235166⟩⟩,⟨⟨(-86005718452907319310299713598),(-86005718452907318883401587765)⟩,⟨215317144707460205231342483657,215317144707460205658470834949⟩⟩]
lemma atomKernel15_1_eq (j : Fin 7) : atomKernel15_1 j = (kernel0Box (atomPoints j) 15).mul (piI.mul (atomPoints j).z) := by
  fin_cases j <;> decide +kernel
lemma atomKernel15_1_contains (j : Fin 7) : (atomKernel15_1 j).Contains
    (complexTransformedFactor 15 1 1 ((j.val:ℝ)/6)) := by
  rw [atomKernel15_1_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=15) (by decide)
  have h0 := transformed_factor_zero_contains hh
  rw [transformed_factor_step]
  have hzz : complexZ ((j.val:ℂ)/6) = z ((j.val:ℝ)/6) := by
    simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat] using
      complexZ_ofReal ((j.val:ℝ)/6)
  have hz := (atomPoints_contains j).2.2.1
  rw [pointZ_eq] at hz
  simpa only [Nat.zero_add,Nat.cast_one,div_one,hzz,complexZ_ofReal,Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using
    CBox.contains_mul h0 (CBox.contains_mul piI_contains hz)
noncomputable def atomKernel16_0 : Fin 7 → CBox := ![⟨⟨(-3),3⟩,⟨(-3),3⟩⟩,⟨⟨(-3),2⟩,⟨(-4),0⟩⟩,⟨⟨0,4⟩,⟨(-2),2⟩⟩,⟨⟨25900948433,25900948436⟩,⟨29186647703,29186647707⟩⟩,⟨⟨(-35362811819921003609),(-35362811819921003509)⟩,⟨25936559903539299125,25936559903539299225⟩⟩,⟨⟨2558988247663461789901146,2558988247663461822219051⟩,⟨(-15737954547823165151092270),(-15737954547823165118709214)⟩⟩,⟨⟨53107114358929705735138510744,53107114358929705810825491739⟩,⟨(-1990265249209479056273496423),(-1990265249209478981209968663)⟩⟩]
lemma atomKernel16_0_eq (j : Fin 7) : atomKernel16_0 j = kernel0Box (atomPoints j) 16 := by
  fin_cases j <;> decide +kernel
lemma atomKernel16_0_contains (j : Fin 7) : (atomKernel16_0 j).Contains
    (complexTransformedFactor 16 1 0 ((j.val:ℝ)/6)) := by
  rw [atomKernel16_0_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=16) (by decide)
  have h0 := transformed_factor_zero_contains hh
  simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using h0
noncomputable def atomKernel16_1 : Fin 7 → CBox := ![⟨⟨(-28),28⟩,⟨(-28),28⟩⟩,⟨⟨(-31),23⟩,⟨(-8),42⟩⟩,⟨⟨(-30),11⟩,⟨(-31),10⟩⟩,⟨⟨75794229201,75794229231⟩,⟨(-214907164993),(-214907164965)⟩⟩,⟨⟨173413891756673643302,173413891756673643917⟩,⟨124072675056722227766,124072675056722228381⟩⟩,⟨⟨(-66096511680512424745057204),(-66096511680512424589790778)⟩,⟨630096109946563809592209,630096109946563964496528⟩⟩,⟨⟨(-17159000623478874601575700458),(-17159000623478874316252730094)⟩,⟨(-191397454004269867419843465767),(-191397454004269867131829260053)⟩⟩]
lemma atomKernel16_1_eq (j : Fin 7) : atomKernel16_1 j = (kernel0Box (atomPoints j) 16).mul (piI.mul (atomPoints j).z) := by
  fin_cases j <;> decide +kernel
lemma atomKernel16_1_contains (j : Fin 7) : (atomKernel16_1 j).Contains
    (complexTransformedFactor 16 1 1 ((j.val:ℝ)/6)) := by
  rw [atomKernel16_1_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=16) (by decide)
  have h0 := transformed_factor_zero_contains hh
  rw [transformed_factor_step]
  have hzz : complexZ ((j.val:ℂ)/6) = z ((j.val:ℝ)/6) := by
    simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat] using
      complexZ_ofReal ((j.val:ℝ)/6)
  have hz := (atomPoints_contains j).2.2.1
  rw [pointZ_eq] at hz
  simpa only [Nat.zero_add,Nat.cast_one,div_one,hzz,complexZ_ofReal,Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using
    CBox.contains_mul h0 (CBox.contains_mul piI_contains hz)
noncomputable def atomKernel19_0 : Fin 7 → CBox := ![⟨⟨(-3),3⟩,⟨(-3),3⟩⟩,⟨⟨(-3),4⟩,⟨(-4),2⟩⟩,⟨⟨(-4),0⟩,⟨(-2),2⟩⟩,⟨⟨(-2694941),(-2694938)⟩,⟨(-7553494),(-7553491)⟩⟩,⟨⟨161985630457654811,161985630457654815⟩,⟨436136473825194671,436136473825194675⟩⟩,⟨⟨875795745701851962050983,875795745701851969854345⟩,⟨(-1717008702880404811713990),(-1717008702880404803916317)⟩⟩,⟨⟨(-3773270257214874982714516262),(-3773270257214874921032772599)⟩,⟨30019734216488397017839289471,30019734216488397079757731725⟩⟩]
lemma atomKernel19_0_eq (j : Fin 7) : atomKernel19_0 j = kernel0Box (atomPoints j) 19 := by
  fin_cases j <;> decide +kernel
lemma atomKernel19_0_contains (j : Fin 7) : (atomKernel19_0 j).Contains
    (complexTransformedFactor 19 1 0 ((j.val:ℝ)/6)) := by
  rw [atomKernel19_0_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=19) (by decide)
  have h0 := transformed_factor_zero_contains hh
  simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using h0
noncomputable def atomKernel19_1 : Fin 7 → CBox := ![⟨⟨(-28),28⟩,⟨(-28),28⟩⟩,⟨⟨(-46),31⟩,⟨(-31),42⟩⟩,⟨⟨(-11),30⟩,⟨(-10),31⟩⟩,⟨⟨(-30958727),(-30958703)⟩,⟨35142785,35142810⟩⟩,⟨⟨1769479826288535701,1769479826288535726⟩,⟨(-1409274084194273722),(-1409274084194273697)⟩⟩,⟨⟨(-7631316207020498734798912),(-7631316207020498697422870)⟩,⟨(-2368587012362611643398018),(-2368587012362611606011795)⟩⟩,⟨⟨109110561539634485129127268825,109110561539634485364645873668⟩,⟨7988470969262919066081260666,7988470969262919300503590470⟩⟩]
lemma atomKernel19_1_eq (j : Fin 7) : atomKernel19_1 j = (kernel0Box (atomPoints j) 19).mul (piI.mul (atomPoints j).z) := by
  fin_cases j <;> decide +kernel
lemma atomKernel19_1_contains (j : Fin 7) : (atomKernel19_1 j).Contains
    (complexTransformedFactor 19 1 1 ((j.val:ℝ)/6)) := by
  rw [atomKernel19_1_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=19) (by decide)
  have h0 := transformed_factor_zero_contains hh
  rw [transformed_factor_step]
  have hzz : complexZ ((j.val:ℂ)/6) = z ((j.val:ℝ)/6) := by
    simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat] using
      complexZ_ofReal ((j.val:ℝ)/6)
  have hz := (atomPoints_contains j).2.2.1
  rw [pointZ_eq] at hz
  simpa only [Nat.zero_add,Nat.cast_one,div_one,hzz,complexZ_ofReal,Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using
    CBox.contains_mul h0 (CBox.contains_mul piI_contains hz)
noncomputable def atomKernel21_0 : Fin 7 → CBox := ![⟨⟨(-3),3⟩,⟨(-3),3⟩⟩,⟨⟨(-3),4⟩,⟨(-4),2⟩⟩,⟨⟨0,4⟩,⟨(-2),2⟩⟩,⟨⟨25312,25315⟩,⟨11801,11804⟩⟩,⟨⟨(-3818447111475508),(-3818447111475505)⟩,⟨(-22135735523014202),(-22135735523014199)⟩⟩,⟨⟨(-465579338219423601664417),(-465579338219423599382689)⟩,⟨(-72777510407062961050706),(-72777510407062958771017)⟩⟩,⟨⟨15107785144520704772910159032,15107785144520704814094127433⟩,⟨14272246381970123218210380229,14272246381970123259587922189⟩⟩]
lemma atomKernel21_0_eq (j : Fin 7) : atomKernel21_0 j = kernel0Box (atomPoints j) 21 := by
  fin_cases j <;> decide +kernel
lemma atomKernel21_0_contains (j : Fin 7) : (atomKernel21_0 j).Contains
    (complexTransformedFactor 21 1 0 ((j.val:ℝ)/6)) := by
  rw [atomKernel21_0_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=21) (by decide)
  have h0 := transformed_factor_zero_contains hh
  simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using h0
noncomputable def atomKernel21_1 : Fin 7 → CBox := ![⟨⟨(-28),28⟩,⟨(-28),28⟩⟩,⟨⟨(-46),31⟩,⟨(-31),42⟩⟩,⟨⟨(-30),11⟩,⟨(-31),10⟩⟩,⟨⟨(-11359),(-11334)⟩,⟨(-162722),(-162697)⟩⟩,⟨⟨(-96480550487984323),(-96480550487984304)⟩,⟨51184714145044773,51184714145044792⟩⟩,⟨⟨30592198090449795242469,30592198090449806164697⟩,⟨1953286993187611677087887,1953286993187611688021236⟩⟩,⟨⟨48700613826522762890528929747,48700613826522763047850641807⟩,⟨(-57234553114940164290854633226),(-57234553114940164134186467881)⟩⟩]
lemma atomKernel21_1_eq (j : Fin 7) : atomKernel21_1 j = (kernel0Box (atomPoints j) 21).mul (piI.mul (atomPoints j).z) := by
  fin_cases j <;> decide +kernel
lemma atomKernel21_1_contains (j : Fin 7) : (atomKernel21_1 j).Contains
    (complexTransformedFactor 21 1 1 ((j.val:ℝ)/6)) := by
  rw [atomKernel21_1_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=21) (by decide)
  have h0 := transformed_factor_zero_contains hh
  rw [transformed_factor_step]
  have hzz : complexZ ((j.val:ℂ)/6) = z ((j.val:ℝ)/6) := by
    simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat] using
      complexZ_ofReal ((j.val:ℝ)/6)
  have hz := (atomPoints_contains j).2.2.1
  rw [pointZ_eq] at hz
  simpa only [Nat.zero_add,Nat.cast_one,div_one,hzz,complexZ_ofReal,Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using
    CBox.contains_mul h0 (CBox.contains_mul piI_contains hz)
noncomputable def atomKernel24_0 : Fin 7 → CBox := ![⟨⟨(-3),3⟩,⟨(-3),3⟩⟩,⟨⟨(-3),4⟩,⟨(-4),2⟩⟩,⟨⟨(-4),0⟩,⟨(-2),2⟩⟩,⟨⟨(-6),(-3)⟩,⟨(-6),(-3)⟩⟩,⟨⟨(-236955311709037),(-236955311709034)⟩,⟨(-25302583633154),(-25302583633151)⟩⟩,⟨⟨(-50902692348634872196574),(-50902692348634872055211)⟩,⟨(-25572105302796923445599),(-25572105302796923304077)⟩⟩,⟨⟨(-9409877970793072962720468375),(-9409877970793072933272212257)⟩,⟨7173247941176577457230122546,7173247941176577486520048649⟩⟩]
lemma atomKernel24_0_eq (j : Fin 7) : atomKernel24_0 j = kernel0Box (atomPoints j) 24 := by
  fin_cases j <;> decide +kernel
lemma atomKernel24_0_contains (j : Fin 7) : (atomKernel24_0 j).Contains
    (complexTransformedFactor 24 1 0 ((j.val:ℝ)/6)) := by
  rw [atomKernel24_0_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=24) (by decide)
  have h0 := transformed_factor_zero_contains hh
  simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using h0
noncomputable def atomKernel24_1 : Fin 7 → CBox := ![⟨⟨(-28),28⟩,⟨(-28),28⟩⟩,⟨⟨(-46),31⟩,⟨(-31),42⟩⟩,⟨⟨(-11),30⟩,⟨(-10),31⟩⟩,⟨⟨(-23),2⟩,⟨23,48⟩⟩,⟨⟨242174098457843,242174098457862⟩,⟨1133073413611544,1133073413611563⟩⟩,⟨⟨(-68618597869347544447143),(-68618597869347543768973)⟩,⟨225963129972071328187395,225963129972071328865300⟩⟩,⟨⟨27669709444365382060075635835,27669709444365382171459994905⟩,⟨32632369547623298580507136818,32632369547623298692457871091⟩⟩]
lemma atomKernel24_1_eq (j : Fin 7) : atomKernel24_1 j = (kernel0Box (atomPoints j) 24).mul (piI.mul (atomPoints j).z) := by
  fin_cases j <;> decide +kernel
lemma atomKernel24_1_contains (j : Fin 7) : (atomKernel24_1 j).Contains
    (complexTransformedFactor 24 1 1 ((j.val:ℝ)/6)) := by
  rw [atomKernel24_1_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=24) (by decide)
  have h0 := transformed_factor_zero_contains hh
  rw [transformed_factor_step]
  have hzz : complexZ ((j.val:ℂ)/6) = z ((j.val:ℝ)/6) := by
    simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat] using
      complexZ_ofReal ((j.val:ℝ)/6)
  have hz := (atomPoints_contains j).2.2.1
  rw [pointZ_eq] at hz
  simpa only [Nat.zero_add,Nat.cast_one,div_one,hzz,complexZ_ofReal,Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using
    CBox.contains_mul h0 (CBox.contains_mul piI_contains hz)
noncomputable def atomKernel25_0 : Fin 7 → CBox := ![⟨⟨(-3),3⟩,⟨(-3),3⟩⟩,⟨⟨(-4),3⟩,⟨(-2),4⟩⟩,⟨⟨(-2),2⟩,⟨(-4),0⟩⟩,⟨⟨(-2),2⟩,⟨(-3),0⟩⟩,⟨⟨10340074628317,10340074628320⟩,⟨(-51331061870575),(-51331061870572)⟩⟩,⟨⟨25007424357324989033834,25007424357324989135643⟩,⟨(-12960697545205626522481),(-12960697545205626421114)⟩⟩,⟨⟨4265780981286296484845899622,4265780981286296520258313301⟩,⟨(-8830170284357607012539510376),(-8830170284357606977137540426)⟩⟩]
lemma atomKernel25_0_eq (j : Fin 7) : atomKernel25_0 j = kernel0Box (atomPoints j) 25 := by
  fin_cases j <;> decide +kernel
lemma atomKernel25_0_contains (j : Fin 7) : (atomKernel25_0 j).Contains
    (complexTransformedFactor 25 1 0 ((j.val:ℝ)/6)) := by
  rw [atomKernel25_0_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=25) (by decide)
  have h0 := transformed_factor_zero_contains hh
  simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using h0
noncomputable def atomKernel25_1 : Fin 7 → CBox := ![⟨⟨(-28),28⟩,⟨(-28),28⟩⟩,⟨⟨(-31),46⟩,⟨(-42),31⟩⟩,⟨⟨(-31),10⟩,⟨(-11),30⟩⟩,⟨⟨(-21),6⟩,⟨(-11),19⟩⟩,⟨⟨(-252817850132719),(-252817850132700)⟩,⟨30013822947977,30013822947997⟩⟩,⟨⟨(-70561141275445737041550),(-70561141275445736555506)⟩,⟨(-93034447094966848163873),(-93034447094966847676205)⟩⟩,⟨⟨(-32686974824484623380691466343),(-32686974824484623246100477472)⟩,⟨(-13745775507675035894603552736),(-13745775507675035760026548446)⟩⟩]
lemma atomKernel25_1_eq (j : Fin 7) : atomKernel25_1 j = (kernel0Box (atomPoints j) 25).mul (piI.mul (atomPoints j).z) := by
  fin_cases j <;> decide +kernel
lemma atomKernel25_1_contains (j : Fin 7) : (atomKernel25_1 j).Contains
    (complexTransformedFactor 25 1 1 ((j.val:ℝ)/6)) := by
  rw [atomKernel25_1_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=25) (by decide)
  have h0 := transformed_factor_zero_contains hh
  rw [transformed_factor_step]
  have hzz : complexZ ((j.val:ℂ)/6) = z ((j.val:ℝ)/6) := by
    simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat] using
      complexZ_ofReal ((j.val:ℝ)/6)
  have hz := (atomPoints_contains j).2.2.1
  rw [pointZ_eq] at hz
  simpa only [Nat.zero_add,Nat.cast_one,div_one,hzz,complexZ_ofReal,Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using
    CBox.contains_mul h0 (CBox.contains_mul piI_contains hz)
noncomputable def atomKernel27_0 : Fin 7 → CBox := ![⟨⟨(-3),3⟩,⟨(-3),3⟩⟩,⟨⟨(-4),3⟩,⟨(-2),4⟩⟩,⟨⟨0,4⟩,⟨(-2),2⟩⟩,⟨⟨(-2),2⟩,⟨0,3⟩⟩,⟨⟨(-946122032372),(-946122032369)⟩,⟨2344393842845,2344393842848⟩⟩,⟨⟨(-4914715484280113312030),(-4914715484280113277429)⟩,⟨(-4823446996496663396948),(-4823446996496663362281)⟩⟩,⟨⟨(-3163347492825092488356998232),(-3163347492825092453738357979)⟩,⟨(-5947311263201831421663297862),(-5947311263201831386929852948)⟩⟩]
lemma atomKernel27_0_eq (j : Fin 7) : atomKernel27_0 j = kernel0Box (atomPoints j) 27 := by
  fin_cases j <;> decide +kernel
lemma atomKernel27_0_contains (j : Fin 7) : (atomKernel27_0 j).Contains
    (complexTransformedFactor 27 1 0 ((j.val:ℝ)/6)) := by
  rw [atomKernel27_0_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=27) (by decide)
  have h0 := transformed_factor_zero_contains hh
  simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using h0
noncomputable def atomKernel27_1 : Fin 7 → CBox := ![⟨⟨(-28),28⟩,⟨(-28),28⟩⟩,⟨⟨(-31),46⟩,⟨(-42),31⟩⟩,⟨⟨(-30),11⟩,⟨(-31),10⟩⟩,⟨⟨(-6),21⟩,⟨(-19),11⟩⟩,⟨⟨12264786356508,12264786356528⟩,⟨818481221881,818481221900⟩⟩,⟨⟨(-16243750035431970811935),(-16243750035431970645865)⟩,⟨23475245713674834422464,23475245713674834588311⟩⟩,⟨⟨(-20881903462514637627417506508),(-20881903462514637495423423685)⟩,⟨12539676748978747560769434746,12539676748978747692340176601⟩⟩]
lemma atomKernel27_1_eq (j : Fin 7) : atomKernel27_1 j = (kernel0Box (atomPoints j) 27).mul (piI.mul (atomPoints j).z) := by
  fin_cases j <;> decide +kernel
lemma atomKernel27_1_contains (j : Fin 7) : (atomKernel27_1 j).Contains
    (complexTransformedFactor 27 1 1 ((j.val:ℝ)/6)) := by
  rw [atomKernel27_1_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=27) (by decide)
  have h0 := transformed_factor_zero_contains hh
  rw [transformed_factor_step]
  have hzz : complexZ ((j.val:ℂ)/6) = z ((j.val:ℝ)/6) := by
    simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat] using
      complexZ_ofReal ((j.val:ℝ)/6)
  have hz := (atomPoints_contains j).2.2.1
  rw [pointZ_eq] at hz
  simpa only [Nat.zero_add,Nat.cast_one,div_one,hzz,complexZ_ofReal,Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using
    CBox.contains_mul h0 (CBox.contains_mul piI_contains hz)
noncomputable def atomKernel28_0 : Fin 7 → CBox := ![⟨⟨(-3),3⟩,⟨(-3),3⟩⟩,⟨⟨(-4),3⟩,⟨(-2),4⟩⟩,⟨⟨(-2),2⟩,⟨0,4⟩⟩,⟨⟨(-2),2⟩,⟨0,3⟩⟩,⟨⟨(-493754047503),(-493754047500)⟩,⟨(-254534926262),(-254534926259)⟩⟩,⟨⟨3357153827198104502458,3357153827198104516477⟩,⟨(-568253757477525623876),(-568253757477525609895)⟩⟩,⟨⟨4568030054686774396541880045,4568030054686774407918970971⟩,⟨3209886730187197181988549093,3209886730187197193397127950⟩⟩]
lemma atomKernel28_0_eq (j : Fin 7) : atomKernel28_0 j = kernel0Box (atomPoints j) 28 := by
  fin_cases j <;> decide +kernel
lemma atomKernel28_0_contains (j : Fin 7) : (atomKernel28_0 j).Contains
    (complexTransformedFactor 28 1 0 ((j.val:ℝ)/6)) := by
  rw [atomKernel28_0_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=28) (by decide)
  have h0 := transformed_factor_zero_contains hh
  simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using h0
noncomputable def atomKernel28_1 : Fin 7 → CBox := ![⟨⟨(-28),28⟩,⟨(-28),28⟩⟩,⟨⟨(-31),46⟩,⟨(-42),31⟩⟩,⟨⟨(-10),31⟩,⟨(-30),11⟩⟩,⟨⟨(-6),21⟩,⟨(-19),11⟩⟩,⟨⟨(-427735225680),(-427735225661)⟩,⟨2666849509051,2666849509071⟩⟩,⟨⟨(-4685945174865765828890),(-4685945174865765761884)⟩,⟨(-13314743247109872706579),(-13314743247109872639414)⟩⟩,⟨⟨10733230239114978357051547456,10733230239114978400424162862⟩,⟨(-17098006669934193027518235080),(-17098006669934192984238611740)⟩⟩]
lemma atomKernel28_1_eq (j : Fin 7) : atomKernel28_1 j = (kernel0Box (atomPoints j) 28).mul (piI.mul (atomPoints j).z) := by
  fin_cases j <;> decide +kernel
lemma atomKernel28_1_contains (j : Fin 7) : (atomKernel28_1 j).Contains
    (complexTransformedFactor 28 1 1 ((j.val:ℝ)/6)) := by
  rw [atomKernel28_1_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=28) (by decide)
  have h0 := transformed_factor_zero_contains hh
  rw [transformed_factor_step]
  have hzz : complexZ ((j.val:ℂ)/6) = z ((j.val:ℝ)/6) := by
    simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat] using
      complexZ_ofReal ((j.val:ℝ)/6)
  have hz := (atomPoints_contains j).2.2.1
  rw [pointZ_eq] at hz
  simpa only [Nat.zero_add,Nat.cast_one,div_one,hzz,complexZ_ofReal,Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using
    CBox.contains_mul h0 (CBox.contains_mul piI_contains hz)
noncomputable def atomKernel31_0 : Fin 7 → CBox := ![⟨⟨(-3),3⟩,⟨(-3),3⟩⟩,⟨⟨(-3),4⟩,⟨(-4),2⟩⟩,⟨⟨(-2),4⟩,⟨(-4),2⟩⟩,⟨⟨0,3⟩,⟨(-2),2⟩⟩,⟨⟨(-4030720336),(-4030720333)⟩,⟨4299209323,4299209326⟩⟩,⟨⟨407412577843147764126,407412577843147767566⟩,⟨58579429178108479865,58579429178108483303⟩⟩,⟨⟨(-2224103963996790476325329693),(-2224103963996790455774833313)⟩,⟨2270745127693704504337839885,2270745127693704524857452908⟩⟩]
lemma atomKernel31_0_eq (j : Fin 7) : atomKernel31_0 j = kernel0Box (atomPoints j) 31 := by
  fin_cases j <;> decide +kernel
lemma atomKernel31_0_contains (j : Fin 7) : (atomKernel31_0 j).Contains
    (complexTransformedFactor 31 1 0 ((j.val:ℝ)/6)) := by
  rw [atomKernel31_0_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=31) (by decide)
  have h0 := transformed_factor_zero_contains hh
  simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using h0
noncomputable def atomKernel31_1 : Fin 7 → CBox := ![⟨⟨(-28),28⟩,⟨(-28),28⟩⟩,⟨⟨(-46),31⟩,⟨(-31),42⟩⟩,⟨⟨(-41),21⟩,⟨(-31),30⟩⟩,⟨⟨(-19),11⟩,⟨(-21),6⟩⟩,⟨⟨25970278706,25970278725⟩,⟨12107049782,12107049802⟩⟩,⟨⟨(-47628420768149630847),(-47628420768149614376)⟩,⟨(-1705658777325531325301),(-1705658777325531308820)⟩⟩,⟨⟨8617347244127811818499525611,8617347244127811896482648040⟩,⟨7604911897842197952003746458,7604911897842198030092082194⟩⟩]
lemma atomKernel31_1_eq (j : Fin 7) : atomKernel31_1 j = (kernel0Box (atomPoints j) 31).mul (piI.mul (atomPoints j).z) := by
  fin_cases j <;> decide +kernel
lemma atomKernel31_1_contains (j : Fin 7) : (atomKernel31_1 j).Contains
    (complexTransformedFactor 31 1 1 ((j.val:ℝ)/6)) := by
  rw [atomKernel31_1_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=31) (by decide)
  have h0 := transformed_factor_zero_contains hh
  rw [transformed_factor_step]
  have hzz : complexZ ((j.val:ℂ)/6) = z ((j.val:ℝ)/6) := by
    simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat] using
      complexZ_ofReal ((j.val:ℝ)/6)
  have hz := (atomPoints_contains j).2.2.1
  rw [pointZ_eq] at hz
  simpa only [Nat.zero_add,Nat.cast_one,div_one,hzz,complexZ_ofReal,Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using
    CBox.contains_mul h0 (CBox.contains_mul piI_contains hz)
noncomputable def atomKernel33_0 : Fin 7 → CBox := ![⟨⟨(-3),3⟩,⟨(-3),3⟩⟩,⟨⟨(-4),3⟩,⟨(-2),4⟩⟩,⟨⟨(-2),4⟩,⟨(-4),2⟩⟩,⟨⟨(-2),2⟩,⟨0,3⟩⟩,⟨⟨229435537,229435540⟩,⟨(-168277587),(-168277584)⟩⟩,⟨⟨(-17402041971918504781),(-17402041971918504071)⟩,⟨(-99113638007083976860),(-99113638007083976149)⟩⟩,⟨⟨356134034453168626612634853,356134034453168633806136668⟩,⟨2154120630586429646770321740,2154120630586429653996527604⟩⟩]
lemma atomKernel33_0_eq (j : Fin 7) : atomKernel33_0 j = kernel0Box (atomPoints j) 33 := by
  fin_cases j <;> decide +kernel
lemma atomKernel33_0_contains (j : Fin 7) : (atomKernel33_0 j).Contains
    (complexTransformedFactor 33 1 0 ((j.val:ℝ)/6)) := by
  rw [atomKernel33_0_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=33) (by decide)
  have h0 := transformed_factor_zero_contains hh
  simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using h0
noncomputable def atomKernel33_1 : Fin 7 → CBox := ![⟨⟨(-28),28⟩,⟨(-28),28⟩⟩,⟨⟨(-31),46⟩,⟨(-42),31⟩⟩,⟨⟨(-41),21⟩,⟨(-31),30⟩⟩,⟨⟨(-6),21⟩,⟨(-19),11⟩⟩,⟨⟨(-1125117261),(-1125117242)⟩,⟨(-804989193),(-804989174)⟩⟩,⟨⟨(-392652206894016658349),(-392652206894016654942)⟩,⟨140898727616430839872,140898727616430843274⟩⟩,⟨⟨7711713205226792022808918861,7711713205226792050278657229⟩,⟨(-1690495727387573553837620386),(-1690495727387573526499428095)⟩⟩]
lemma atomKernel33_1_eq (j : Fin 7) : atomKernel33_1 j = (kernel0Box (atomPoints j) 33).mul (piI.mul (atomPoints j).z) := by
  fin_cases j <;> decide +kernel
lemma atomKernel33_1_contains (j : Fin 7) : (atomKernel33_1 j).Contains
    (complexTransformedFactor 33 1 1 ((j.val:ℝ)/6)) := by
  rw [atomKernel33_1_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=33) (by decide)
  have h0 := transformed_factor_zero_contains hh
  rw [transformed_factor_step]
  have hzz : complexZ ((j.val:ℂ)/6) = z ((j.val:ℝ)/6) := by
    simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat] using
      complexZ_ofReal ((j.val:ℝ)/6)
  have hz := (atomPoints_contains j).2.2.1
  rw [pointZ_eq] at hz
  simpa only [Nat.zero_add,Nat.cast_one,div_one,hzz,complexZ_ofReal,Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using
    CBox.contains_mul h0 (CBox.contains_mul piI_contains hz)
noncomputable def atomKernel36_0 : Fin 7 → CBox := ![⟨⟨(-3),3⟩,⟨(-3),3⟩⟩,⟨⟨(-4),4⟩,⟨(-4),4⟩⟩,⟨⟨(-4),2⟩,⟨(-2),4⟩⟩,⟨⟨(-2),2⟩,⟨(-3),0⟩⟩,⟨⟨(-1050972),(-1050969)⟩,⟨(-2829675),(-2829672)⟩⟩,⟨⟨1657458069911691374,1657458069911691465⟩,⟨(-12051186734807603617),(-12051186734807603525)⟩⟩,⟨⟨(-1243020940282687197299659347),(-1243020940282687190617026701)⟩,⟨1676392578950671605784059,1676392578950678274948786⟩⟩]
lemma atomKernel36_0_eq (j : Fin 7) : atomKernel36_0 j = kernel0Box (atomPoints j) 36 := by
  fin_cases j <;> decide +kernel
lemma atomKernel36_0_contains (j : Fin 7) : (atomKernel36_0 j).Contains
    (complexTransformedFactor 36 1 0 ((j.val:ℝ)/6)) := by
  rw [atomKernel36_0_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=36) (by decide)
  have h0 := transformed_factor_zero_contains hh
  simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using h0
noncomputable def atomKernel36_1 : Fin 7 → CBox := ![⟨⟨(-28),28⟩,⟨(-28),28⟩⟩,⟨⟨(-46),46⟩,⟨(-46),46⟩⟩,⟨⟨(-21),41⟩,⟨(-30),31⟩⟩,⟨⟨(-21),6⟩,⟨(-11),19⟩⟩,⟨⟨(-11480476),(-11480456)⟩,⟨9143427,9143446⟩⟩,⟨⟨(-50400021493982320839),(-50400021493982320398)⟩,⟨1716504632604075338,1716504632604075776⟩⟩,⟨⟨239459708312164333399207818,239459708312164358737317874⟩,⟨4488266200039790625597273898,4488266200039790650995014418⟩⟩]
lemma atomKernel36_1_eq (j : Fin 7) : atomKernel36_1 j = (kernel0Box (atomPoints j) 36).mul (piI.mul (atomPoints j).z) := by
  fin_cases j <;> decide +kernel
lemma atomKernel36_1_contains (j : Fin 7) : (atomKernel36_1 j).Contains
    (complexTransformedFactor 36 1 1 ((j.val:ℝ)/6)) := by
  rw [atomKernel36_1_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=36) (by decide)
  have h0 := transformed_factor_zero_contains hh
  rw [transformed_factor_step]
  have hzz : complexZ ((j.val:ℂ)/6) = z ((j.val:ℝ)/6) := by
    simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat] using
      complexZ_ofReal ((j.val:ℝ)/6)
  have hz := (atomPoints_contains j).2.2.1
  rw [pointZ_eq] at hz
  simpa only [Nat.zero_add,Nat.cast_one,div_one,hzz,complexZ_ofReal,Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using
    CBox.contains_mul h0 (CBox.contains_mul piI_contains hz)
noncomputable def atomKernel37_0 : Fin 7 → CBox := ![⟨⟨(-3),3⟩,⟨(-3),3⟩⟩,⟨⟨(-4),4⟩,⟨(-4),4⟩⟩,⟨⟨(-2),4⟩,⟨(-4),2⟩⟩,⟨⟨0,3⟩,⟨(-2),2⟩⟩,⟨⟨640417,640420⟩,⟨(-172576),(-172573)⟩⟩,⟨⟨4344109497548861007,4344109497548861053⟩,⟨4160151813898398136,4160151813898398182⟩⟩,⟨⟨918146183807522803526732868,918146183807522811268423752⟩,⟨(-467290594442411598540061168),(-467290594442411590816352397)⟩⟩]
lemma atomKernel37_0_eq (j : Fin 7) : atomKernel37_0 j = kernel0Box (atomPoints j) 37 := by
  fin_cases j <;> decide +kernel
lemma atomKernel37_0_contains (j : Fin 7) : (atomKernel37_0 j).Contains
    (complexTransformedFactor 37 1 0 ((j.val:ℝ)/6)) := by
  rw [atomKernel37_0_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=37) (by decide)
  have h0 := transformed_factor_zero_contains hh
  simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using h0
noncomputable def atomKernel37_1 : Fin 7 → CBox := ![⟨⟨(-28),28⟩,⟨(-28),28⟩⟩,⟨⟨(-46),46⟩,⟨(-46),46⟩⟩,⟨⟨(-41),21⟩,⟨(-31),30⟩⟩,⟨⟨(-19),11⟩,⟨(-21),6⟩⟩,⟨⟨(-1767764),(-1767745)⟩,⟨(-2697224),(-2697205)⟩⟩,⟨⟨13935873524237933494,13935873524237933716⟩,⟨(-20676989198405546918),(-20676989198405546696)⟩⟩,⟨⟨(-1859801892531483976917095203),(-1859801892531483947566978519)⟩,⟨(-3227705054763723539994758263),(-3227705054763723510578171492)⟩⟩]
lemma atomKernel37_1_eq (j : Fin 7) : atomKernel37_1 j = (kernel0Box (atomPoints j) 37).mul (piI.mul (atomPoints j).z) := by
  fin_cases j <;> decide +kernel
lemma atomKernel37_1_contains (j : Fin 7) : (atomKernel37_1 j).Contains
    (complexTransformedFactor 37 1 1 ((j.val:ℝ)/6)) := by
  rw [atomKernel37_1_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=37) (by decide)
  have h0 := transformed_factor_zero_contains hh
  rw [transformed_factor_step]
  have hzz : complexZ ((j.val:ℂ)/6) = z ((j.val:ℝ)/6) := by
    simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat] using
      complexZ_ofReal ((j.val:ℝ)/6)
  have hz := (atomPoints_contains j).2.2.1
  rw [pointZ_eq] at hz
  simpa only [Nat.zero_add,Nat.cast_one,div_one,hzz,complexZ_ofReal,Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using
    CBox.contains_mul h0 (CBox.contains_mul piI_contains hz)
noncomputable def atomKernel39_0 : Fin 7 → CBox := ![⟨⟨(-3),3⟩,⟨(-3),3⟩⟩,⟨⟨(-4),4⟩,⟨(-4),4⟩⟩,⟨⟨(-4),2⟩,⟨(-2),4⟩⟩,⟨⟨(-3),0⟩,⟨(-2),2⟩⟩,⟨⟨(-31926),(-31923)⟩,⟨2507,2510⟩⟩,⟨⟨635863206902312638,635863206902312662⟩,⟨(-1325938779881954263),(-1325938779881954239)⟩⟩,⟨⟨113546669637062691669758862,113546669637062697375502405⟩,⟨(-698503320922647562276889979),(-698503320922647556566360541)⟩⟩]
lemma atomKernel39_0_eq (j : Fin 7) : atomKernel39_0 j = kernel0Box (atomPoints j) 39 := by
  fin_cases j <;> decide +kernel
lemma atomKernel39_0_contains (j : Fin 7) : (atomKernel39_0 j).Contains
    (complexTransformedFactor 39 1 0 ((j.val:ℝ)/6)) := by
  rw [atomKernel39_0_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=39) (by decide)
  have h0 := transformed_factor_zero_contains hh
  simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using h0
noncomputable def atomKernel39_1 : Fin 7 → CBox := ![⟨⟨(-28),28⟩,⟨(-28),28⟩⟩,⟨⟨(-46),46⟩,⟨(-46),46⟩⟩,⟨⟨(-21),41⟩,⟨(-30),31⟩⟩,⟨⟨(-11),19⟩,⟨(-6),21⟩⟩,⟨⟨59957,59976⟩,⟨143680,143699⟩⟩,⟨⟨(-5864694104202136490),(-5864694104202136374)⟩,⟨(-1663824078702990933),(-1663824078702990817)⟩⟩,⟨⟨(-2543634718900661190487942318),(-2543634718900661168787588579)⟩,⟨(-278859669301624039056922852),(-278859669301624017379326452)⟩⟩]
lemma atomKernel39_1_eq (j : Fin 7) : atomKernel39_1 j = (kernel0Box (atomPoints j) 39).mul (piI.mul (atomPoints j).z) := by
  fin_cases j <;> decide +kernel
lemma atomKernel39_1_contains (j : Fin 7) : (atomKernel39_1 j).Contains
    (complexTransformedFactor 39 1 1 ((j.val:ℝ)/6)) := by
  rw [atomKernel39_1_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=39) (by decide)
  have h0 := transformed_factor_zero_contains hh
  rw [transformed_factor_step]
  have hzz : complexZ ((j.val:ℂ)/6) = z ((j.val:ℝ)/6) := by
    simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat] using
      complexZ_ofReal ((j.val:ℝ)/6)
  have hz := (atomPoints_contains j).2.2.1
  rw [pointZ_eq] at hz
  simpa only [Nat.zero_add,Nat.cast_one,div_one,hzz,complexZ_ofReal,Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using
    CBox.contains_mul h0 (CBox.contains_mul piI_contains hz)
noncomputable def atomKernel40_0 : Fin 7 → CBox := ![⟨⟨(-3),3⟩,⟨(-3),3⟩⟩,⟨⟨(-4),4⟩,⟨(-4),4⟩⟩,⟨⟨(-4),2⟩,⟨(-2),4⟩⟩,⟨⟨(-3),0⟩,⟨(-2),2⟩⟩,⟨⟨97,100⟩,⟨(-7038),(-7035)⟩⟩,⟨⟨346384015365736346,346384015365736351⟩,⟨639293806035028343,639293806035028348⟩⟩,⟨⟨177965390395636590606821606,177965390395636592442449226⟩,⟨558868935012030951364803856,558868935012030953210918094⟩⟩]
lemma atomKernel40_0_eq (j : Fin 7) : atomKernel40_0 j = kernel0Box (atomPoints j) 40 := by
  fin_cases j <;> decide +kernel
lemma atomKernel40_0_contains (j : Fin 7) : (atomKernel40_0 j).Contains
    (complexTransformedFactor 40 1 0 ((j.val:ℝ)/6)) := by
  rw [atomKernel40_0_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=40) (by decide)
  have h0 := transformed_factor_zero_contains hh
  simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using h0
noncomputable def atomKernel40_1 : Fin 7 → CBox := ![⟨⟨(-28),28⟩,⟨(-28),28⟩⟩,⟨⟨(-46),46⟩,⟨(-46),46⟩⟩,⟨⟨(-21),41⟩,⟨(-30),31⟩⟩,⟨⟨(-11),19⟩,⟨(-6),21⟩⟩,⟨⟨(-32668),(-32648)⟩,⟨10198,10217⟩⟩,⟨⟨2367744446448568917,2367744446448568942⟩,⟨(-1865339093500727158),(-1865339093500727133)⟩⟩,⟨⟨1984673118246228857746059855,1984673118246228864763638546⟩,⟨(-747578353067753521244344664),(-747578353067753514266814852)⟩⟩]
lemma atomKernel40_1_eq (j : Fin 7) : atomKernel40_1 j = (kernel0Box (atomPoints j) 40).mul (piI.mul (atomPoints j).z) := by
  fin_cases j <;> decide +kernel
lemma atomKernel40_1_contains (j : Fin 7) : (atomKernel40_1 j).Contains
    (complexTransformedFactor 40 1 1 ((j.val:ℝ)/6)) := by
  rw [atomKernel40_1_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=40) (by decide)
  have h0 := transformed_factor_zero_contains hh
  rw [transformed_factor_step]
  have hzz : complexZ ((j.val:ℂ)/6) = z ((j.val:ℝ)/6) := by
    simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat] using
      complexZ_ofReal ((j.val:ℝ)/6)
  have hz := (atomPoints_contains j).2.2.1
  rw [pointZ_eq] at hz
  simpa only [Nat.zero_add,Nat.cast_one,div_one,hzz,complexZ_ofReal,Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using
    CBox.contains_mul h0 (CBox.contains_mul piI_contains hz)
noncomputable def atomKernel43_0 : Fin 7 → CBox := ![⟨⟨(-3),3⟩,⟨(-3),3⟩⟩,⟨⟨(-4),4⟩,⟨(-4),4⟩⟩,⟨⟨(-2),4⟩,⟨(-4),2⟩⟩,⟨⟨(-2),2⟩,⟨0,3⟩⟩,⟨⟨(-73),(-70)⟩,⟨(-24),(-21)⟩⟩,⟨⟨16259798808128842,16259798808128846⟩,⟨86378826263974455,86378826263974459⟩⟩,⟨⟨(-330372957935110601859926653),(-330372957935110598947142807)⟩,⟨48509138613335145931700031,48509138613335148839683869⟩⟩]
lemma atomKernel43_0_eq (j : Fin 7) : atomKernel43_0 j = kernel0Box (atomPoints j) 43 := by
  fin_cases j <;> decide +kernel
lemma atomKernel43_0_contains (j : Fin 7) : (atomKernel43_0 j).Contains
    (complexTransformedFactor 43 1 0 ((j.val:ℝ)/6)) := by
  rw [atomKernel43_0_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=43) (by decide)
  have h0 := transformed_factor_zero_contains hh
  simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using h0
noncomputable def atomKernel43_1 : Fin 7 → CBox := ![⟨⟨(-28),28⟩,⟨(-28),28⟩⟩,⟨⟨(-46),46⟩,⟨(-46),46⟩⟩,⟨⟨(-41),21⟩,⟨(-31),30⟩⟩,⟨⟨(-6),21⟩,⟨(-19),11⟩⟩,⟨⟨(-5),14⟩,⟨355,374⟩⟩,⟨⟨341431218542899030,341431218542899050⟩,⟨(-127263134088074692),(-127263134088074672)⟩⟩,⟨⟨237203001028153647116588586,237203001028153658165092179⟩,⟨1183876629898497547286430368,1183876629898497558354436945⟩⟩]
lemma atomKernel43_1_eq (j : Fin 7) : atomKernel43_1 j = (kernel0Box (atomPoints j) 43).mul (piI.mul (atomPoints j).z) := by
  fin_cases j <;> decide +kernel
lemma atomKernel43_1_contains (j : Fin 7) : (atomKernel43_1 j).Contains
    (complexTransformedFactor 43 1 1 ((j.val:ℝ)/6)) := by
  rw [atomKernel43_1_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=43) (by decide)
  have h0 := transformed_factor_zero_contains hh
  rw [transformed_factor_step]
  have hzz : complexZ ((j.val:ℂ)/6) = z ((j.val:ℝ)/6) := by
    simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat] using
      complexZ_ofReal ((j.val:ℝ)/6)
  have hz := (atomPoints_contains j).2.2.1
  rw [pointZ_eq] at hz
  simpa only [Nat.zero_add,Nat.cast_one,div_one,hzz,complexZ_ofReal,Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using
    CBox.contains_mul h0 (CBox.contains_mul piI_contains hz)
noncomputable def atomKernel45_0 : Fin 7 → CBox := ![⟨⟨(-3),3⟩,⟨(-3),3⟩⟩,⟨⟨(-4),4⟩,⟨(-4),4⟩⟩,⟨⟨(-4),2⟩,⟨(-2),4⟩⟩,⟨⟨(-3),0⟩,⟨(-2),2⟩⟩,⟨⟨2,5⟩,⟨1,4⟩⟩,⟨⟨18830809875395978,18830809875395981⟩,⟨(-10352733558348000),(-10352733558347997)⟩⟩,⟨⟨(-107165896840389841321838953),(-107165896840389839088330843)⟩,⟨202796730022409554673157723,202796730022409556906216278⟩⟩]
lemma atomKernel45_0_eq (j : Fin 7) : atomKernel45_0 j = kernel0Box (atomPoints j) 45 := by
  fin_cases j <;> decide +kernel
lemma atomKernel45_0_contains (j : Fin 7) : (atomKernel45_0 j).Contains
    (complexTransformedFactor 45 1 0 ((j.val:ℝ)/6)) := by
  rw [atomKernel45_0_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=45) (by decide)
  have h0 := transformed_factor_zero_contains hh
  simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using h0
noncomputable def atomKernel45_1 : Fin 7 → CBox := ![⟨⟨(-28),28⟩,⟨(-28),28⟩⟩,⟨⟨(-46),46⟩,⟨(-46),46⟩⟩,⟨⟨(-21),41⟩,⟨(-30),31⟩⟩,⟨⟨(-11),19⟩,⟨(-6),21⟩⟩,⟨⟨(-3),16⟩,⟨(-30),(-10)⟩⟩,⟨⟨(-55556615640004652),(-55556615640004636)⟩,⟨(-69637950593080931),(-69637950593080915)⟩⟩,⟨⟨752427172540631380285593794,752427172540631388771014742⟩,⟨348899021763434204543123126,348899021763434213029040968⟩⟩]
lemma atomKernel45_1_eq (j : Fin 7) : atomKernel45_1 j = (kernel0Box (atomPoints j) 45).mul (piI.mul (atomPoints j).z) := by
  fin_cases j <;> decide +kernel
lemma atomKernel45_1_contains (j : Fin 7) : (atomKernel45_1 j).Contains
    (complexTransformedFactor 45 1 1 ((j.val:ℝ)/6)) := by
  rw [atomKernel45_1_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=45) (by decide)
  have h0 := transformed_factor_zero_contains hh
  rw [transformed_factor_step]
  have hzz : complexZ ((j.val:ℂ)/6) = z ((j.val:ℝ)/6) := by
    simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat] using
      complexZ_ofReal ((j.val:ℝ)/6)
  have hz := (atomPoints_contains j).2.2.1
  rw [pointZ_eq] at hz
  simpa only [Nat.zero_add,Nat.cast_one,div_one,hzz,complexZ_ofReal,Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using
    CBox.contains_mul h0 (CBox.contains_mul piI_contains hz)
noncomputable def atomKernel48_0 : Fin 7 → CBox := ![⟨⟨(-3),3⟩,⟨(-3),3⟩⟩,⟨⟨(-4),4⟩,⟨(-4),4⟩⟩,⟨⟨(-2),4⟩,⟨(-4),2⟩⟩,⟨⟨0,3⟩,⟨(-2),2⟩⟩,⟨⟨(-1),2⟩,⟨(-3),0⟩⟩,⟨⟨2549875219752031,2549875219752034⟩,⟨(-496182088842491),(-496182088842488)⟩⟩,⟨⟨(-104063906274990395845241810),(-104063906274990395052490689)⟩,⟨(-78886104748897649066142166),(-78886104748897648272540146)⟩⟩]
lemma atomKernel48_0_eq (j : Fin 7) : atomKernel48_0 j = kernel0Box (atomPoints j) 48 := by
  fin_cases j <;> decide +kernel
lemma atomKernel48_0_contains (j : Fin 7) : (atomKernel48_0 j).Contains
    (complexTransformedFactor 48 1 0 ((j.val:ℝ)/6)) := by
  rw [atomKernel48_0_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=48) (by decide)
  have h0 := transformed_factor_zero_contains hh
  simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using h0
noncomputable def atomKernel48_1 : Fin 7 → CBox := ![⟨⟨(-28),28⟩,⟨(-28),28⟩⟩,⟨⟨(-46),46⟩,⟨(-46),46⟩⟩,⟨⟨(-41),21⟩,⟨(-31),30⟩⟩,⟨⟨(-19),11⟩,⟨(-21),6⟩⟩,⟨⟨(-17),2⟩,⟨(-10),10⟩⟩,⟨⟨(-3822940682990759),(-3822940682990743)⟩,⟨(-10067531589409261),(-10067531589409245)⟩⟩,⟨⟨(-265319349620308840886986549),(-265319349620308837871442516)⟩,⟨390590183711652991010880853,390590183711652994023786395⟩⟩]
lemma atomKernel48_1_eq (j : Fin 7) : atomKernel48_1 j = (kernel0Box (atomPoints j) 48).mul (piI.mul (atomPoints j).z) := by
  fin_cases j <;> decide +kernel
lemma atomKernel48_1_contains (j : Fin 7) : (atomKernel48_1 j).Contains
    (complexTransformedFactor 48 1 1 ((j.val:ℝ)/6)) := by
  rw [atomKernel48_1_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=48) (by decide)
  have h0 := transformed_factor_zero_contains hh
  rw [transformed_factor_step]
  have hzz : complexZ ((j.val:ℂ)/6) = z ((j.val:ℝ)/6) := by
    simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat] using
      complexZ_ofReal ((j.val:ℝ)/6)
  have hz := (atomPoints_contains j).2.2.1
  rw [pointZ_eq] at hz
  simpa only [Nat.zero_add,Nat.cast_one,div_one,hzz,complexZ_ofReal,Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using
    CBox.contains_mul h0 (CBox.contains_mul piI_contains hz)
noncomputable def atomKernel49_0 : Fin 7 → CBox := ![⟨⟨(-3),3⟩,⟨(-3),3⟩⟩,⟨⟨(-4),4⟩,⟨(-4),4⟩⟩,⟨⟨(-2),4⟩,⟨(-4),2⟩⟩,⟨⟨(-3),2⟩,⟨(-2),3⟩⟩,⟨⟨0,3⟩,⟨(-1),2⟩⟩,⟨⟨(-541164345766439),(-541164345766436)⟩,⟨1164871767201477,1164871767201480⟩⟩,⟨⟨106495610180144283951438661,106495610180144284840827478⟩,⟨19291243679728066472327862,19291243679728067361043383⟩⟩]
lemma atomKernel49_0_eq (j : Fin 7) : atomKernel49_0 j = kernel0Box (atomPoints j) 49 := by
  fin_cases j <;> decide +kernel
lemma atomKernel49_0_contains (j : Fin 7) : (atomKernel49_0 j).Contains
    (complexTransformedFactor 49 1 0 ((j.val:ℝ)/6)) := by
  rw [atomKernel49_0_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=49) (by decide)
  have h0 := transformed_factor_zero_contains hh
  simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using h0
noncomputable def atomKernel49_1 : Fin 7 → CBox := ![⟨⟨(-28),28⟩,⟨(-28),28⟩⟩,⟨⟨(-46),46⟩,⟨(-46),46⟩⟩,⟨⟨(-41),21⟩,⟨(-31),30⟩⟩,⟨⟨(-16),24⟩,⟨(-19),21⟩⟩,⟨⟨(-10),10⟩,⟨(-17),2⟩⟩,⟨⟨5139990790469704,5139990790469719⟩,⟨1390391504787011,1390391504787026⟩⟩,⟨⟨49664145334029922136449977,49664145334029925512913778⟩,⟨(-388180802886771933709335300),(-388180802886771930329616411)⟩⟩]
lemma atomKernel49_1_eq (j : Fin 7) : atomKernel49_1 j = (kernel0Box (atomPoints j) 49).mul (piI.mul (atomPoints j).z) := by
  fin_cases j <;> decide +kernel
lemma atomKernel49_1_contains (j : Fin 7) : (atomKernel49_1 j).Contains
    (complexTransformedFactor 49 1 1 ((j.val:ℝ)/6)) := by
  rw [atomKernel49_1_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=49) (by decide)
  have h0 := transformed_factor_zero_contains hh
  rw [transformed_factor_step]
  have hzz : complexZ ((j.val:ℂ)/6) = z ((j.val:ℝ)/6) := by
    simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat] using
      complexZ_ofReal ((j.val:ℝ)/6)
  have hz := (atomPoints_contains j).2.2.1
  rw [pointZ_eq] at hz
  simpa only [Nat.zero_add,Nat.cast_one,div_one,hzz,complexZ_ofReal,Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using
    CBox.contains_mul h0 (CBox.contains_mul piI_contains hz)
noncomputable def atomKernel51_0 : Fin 7 → CBox := ![⟨⟨(-3),3⟩,⟨(-3),3⟩⟩,⟨⟨(-4),4⟩,⟨(-4),4⟩⟩,⟨⟨(-4),2⟩,⟨(-2),4⟩⟩,⟨⟨(-2),3⟩,⟨(-3),2⟩⟩,⟨⟨(-3),2⟩,⟨(-3),1⟩⟩,⟨⟨311828906300556,311828906300558⟩,⟨37060368709048,37060368709051⟩⟩,⟨⟨53904277469795663176536190,53904277469795664246312225⟩,⟨(-51198948346911017898515124),(-51198948346911016829532955)⟩⟩]
lemma atomKernel51_0_eq (j : Fin 7) : atomKernel51_0 j = kernel0Box (atomPoints j) 51 := by
  fin_cases j <;> decide +kernel
lemma atomKernel51_0_contains (j : Fin 7) : (atomKernel51_0 j).Contains
    (complexTransformedFactor 51 1 0 ((j.val:ℝ)/6)) := by
  rw [atomKernel51_0_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=51) (by decide)
  have h0 := transformed_factor_zero_contains hh
  simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using h0
noncomputable def atomKernel51_1 : Fin 7 → CBox := ![⟨⟨(-28),28⟩,⟨(-28),28⟩⟩,⟨⟨(-46),46⟩,⟨(-46),46⟩⟩,⟨⟨(-21),41⟩,⟨(-30),31⟩⟩,⟨⟨(-24),16⟩,⟨(-21),19⟩⟩,⟨⟨(-17),10⟩,⟨(-11),19⟩⟩,⟨⟨(-68220091928561),(-68220091928546)⟩,⟨(-1300015199948792),(-1300015199948781)⟩⟩,⟨⟨(-195002522605954123780304968),(-195002522605954119718686374)⟩,⟨(-185035951283069611197523655),(-185035951283069607133157977)⟩⟩]
lemma atomKernel51_1_eq (j : Fin 7) : atomKernel51_1 j = (kernel0Box (atomPoints j) 51).mul (piI.mul (atomPoints j).z) := by
  fin_cases j <;> decide +kernel
lemma atomKernel51_1_contains (j : Fin 7) : (atomKernel51_1 j).Contains
    (complexTransformedFactor 51 1 1 ((j.val:ℝ)/6)) := by
  rw [atomKernel51_1_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=51) (by decide)
  have h0 := transformed_factor_zero_contains hh
  rw [transformed_factor_step]
  have hzz : complexZ ((j.val:ℂ)/6) = z ((j.val:ℝ)/6) := by
    simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat] using
      complexZ_ofReal ((j.val:ℝ)/6)
  have hz := (atomPoints_contains j).2.2.1
  rw [pointZ_eq] at hz
  simpa only [Nat.zero_add,Nat.cast_one,div_one,hzz,complexZ_ofReal,Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using
    CBox.contains_mul h0 (CBox.contains_mul piI_contains hz)
noncomputable def atomKernel52_0 : Fin 7 → CBox := ![⟨⟨(-3),3⟩,⟨(-3),3⟩⟩,⟨⟨(-4),4⟩,⟨(-4),4⟩⟩,⟨⟨(-4),2⟩,⟨(-2),4⟩⟩,⟨⟨(-2),3⟩,⟨(-3),2⟩⟩,⟨⟨0,3⟩,⟨(-1),2⟩⟩,⟨⟨(-105312484749326),(-105312484749324)⟩,⟨114096081268131,114096081268134⟩⟩,⟨⟨(-20646909703251340773450717),(-20646909703251340282135772)⟩,⟨58054105314515772666001100,58054105314515773157431688⟩⟩]
lemma atomKernel52_0_eq (j : Fin 7) : atomKernel52_0 j = kernel0Box (atomPoints j) 52 := by
  fin_cases j <;> decide +kernel
lemma atomKernel52_0_contains (j : Fin 7) : (atomKernel52_0 j).Contains
    (complexTransformedFactor 52 1 0 ((j.val:ℝ)/6)) := by
  rw [atomKernel52_0_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=52) (by decide)
  have h0 := transformed_factor_zero_contains hh
  simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using h0
noncomputable def atomKernel52_1 : Fin 7 → CBox := ![⟨⟨(-28),28⟩,⟨(-28),28⟩⟩,⟨⟨(-46),46⟩,⟨(-46),46⟩⟩,⟨⟨(-21),41⟩,⟨(-30),31⟩⟩,⟨⟨(-24),16⟩,⟨(-21),19⟩⟩,⟨⟨(-10),10⟩,⟨(-17),2⟩⟩,⟨⟨540288382282069,540288382282084⟩,⟨349874232005769,349874232005780⟩⟩,⟨⟨213511825423736055546754853,213511825423736057414258988⟩,⟨63655514486427655666285289,63655514486427657532985939⟩⟩]
lemma atomKernel52_1_eq (j : Fin 7) : atomKernel52_1 j = (kernel0Box (atomPoints j) 52).mul (piI.mul (atomPoints j).z) := by
  fin_cases j <;> decide +kernel
lemma atomKernel52_1_contains (j : Fin 7) : (atomKernel52_1 j).Contains
    (complexTransformedFactor 52 1 1 ((j.val:ℝ)/6)) := by
  rw [atomKernel52_1_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=52) (by decide)
  have h0 := transformed_factor_zero_contains hh
  rw [transformed_factor_step]
  have hzz : complexZ ((j.val:ℂ)/6) = z ((j.val:ℝ)/6) := by
    simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat] using
      complexZ_ofReal ((j.val:ℝ)/6)
  have hz := (atomPoints_contains j).2.2.1
  rw [pointZ_eq] at hz
  simpa only [Nat.zero_add,Nat.cast_one,div_one,hzz,complexZ_ofReal,Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using
    CBox.contains_mul h0 (CBox.contains_mul piI_contains hz)
noncomputable def atomKernel55_0 : Fin 7 → CBox := ![⟨⟨(-3),3⟩,⟨(-3),3⟩⟩,⟨⟨(-4),4⟩,⟨(-4),4⟩⟩,⟨⟨(-2),4⟩,⟨(-4),2⟩⟩,⟨⟨(-3),2⟩,⟨(-2),3⟩⟩,⟨⟨(-1),2⟩,⟨(-3),0⟩⟩,⟨⟨(-16335865291838),(-16335865291835)⟩,⟨9243578969829,9243578969832⟩⟩,⟨⟨(-30714034438307723652198978),(-30714034438307722796076532)⟩,⟨(-16946837666584302430922347),(-16946837666584301574712951)⟩⟩]
lemma atomKernel55_0_eq (j : Fin 7) : atomKernel55_0 j = kernel0Box (atomPoints j) 55 := by
  fin_cases j <;> decide +kernel
lemma atomKernel55_0_contains (j : Fin 7) : (atomKernel55_0 j).Contains
    (complexTransformedFactor 55 1 0 ((j.val:ℝ)/6)) := by
  rw [atomKernel55_0_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=55) (by decide)
  have h0 := transformed_factor_zero_contains hh
  simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using h0
noncomputable def atomKernel55_1 : Fin 7 → CBox := ![⟨⟨(-28),28⟩,⟨(-28),28⟩⟩,⟨⟨(-46),46⟩,⟨(-46),46⟩⟩,⟨⟨(-41),21⟩,⟨(-31),30⟩⟩,⟨⟨(-16),24⟩,⟨(-19),21⟩⟩,⟨⟨(-17),2⟩,⟨(-10),10⟩⟩,⟨⟨49268188756146,49268188756161⟩,⟨60226546533177,60226546533192⟩⟩,⟨⟨(-55428194824526991733240576),(-55428194824526988480476019)⟩,⟨114091342655939419980830988,114091342655939423233447907⟩⟩]
lemma atomKernel55_1_eq (j : Fin 7) : atomKernel55_1 j = (kernel0Box (atomPoints j) 55).mul (piI.mul (atomPoints j).z) := by
  fin_cases j <;> decide +kernel
lemma atomKernel55_1_contains (j : Fin 7) : (atomKernel55_1 j).Contains
    (complexTransformedFactor 55 1 1 ((j.val:ℝ)/6)) := by
  rw [atomKernel55_1_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=55) (by decide)
  have h0 := transformed_factor_zero_contains hh
  rw [transformed_factor_step]
  have hzz : complexZ ((j.val:ℂ)/6) = z ((j.val:ℝ)/6) := by
    simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat] using
      complexZ_ofReal ((j.val:ℝ)/6)
  have hz := (atomPoints_contains j).2.2.1
  rw [pointZ_eq] at hz
  simpa only [Nat.zero_add,Nat.cast_one,div_one,hzz,complexZ_ofReal,Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using
    CBox.contains_mul h0 (CBox.contains_mul piI_contains hz)
noncomputable def atomKernel57_0 : Fin 7 → CBox := ![⟨⟨(-3),3⟩,⟨(-3),3⟩⟩,⟨⟨(-4),4⟩,⟨(-4),4⟩⟩,⟨⟨(-4),4⟩,⟨(-4),4⟩⟩,⟨⟨(-2),3⟩,⟨(-3),2⟩⟩,⟨⟨(-2),1⟩,⟨0,3⟩⟩,⟨⟨3391042084770,3391042084773⟩,⟨3091717459698,3091717459701⟩⟩,⟨⟨(-21855590582580566140865624),(-21855590582580565938327545)⟩,⟨10147279730891965438020305,10147279730891965640119812⟩⟩]
lemma atomKernel57_0_eq (j : Fin 7) : atomKernel57_0 j = kernel0Box (atomPoints j) 57 := by
  fin_cases j <;> decide +kernel
lemma atomKernel57_0_contains (j : Fin 7) : (atomKernel57_0 j).Contains
    (complexTransformedFactor 57 1 0 ((j.val:ℝ)/6)) := by
  rw [atomKernel57_0_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=57) (by decide)
  have h0 := transformed_factor_zero_contains hh
  simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using h0
noncomputable def atomKernel57_1 : Fin 7 → CBox := ![⟨⟨(-28),28⟩,⟨(-28),28⟩⟩,⟨⟨(-46),46⟩,⟨(-46),46⟩⟩,⟨⟨(-41),41⟩,⟨(-41),41⟩⟩,⟨⟨(-24),16⟩,⟨(-21),19⟩⟩,⟨⟨(-2),17⟩,⟨(-10),10⟩⟩,⟨⟨10242253069099,10242253069114⟩,⟨(-16030922975189),(-16030922975174)⟩⟩,⟨⟨40745988876809292236146413,40745988876809293004093949⟩,⟨77015717933751555155819035,77015717933751555925395494⟩⟩]
lemma atomKernel57_1_eq (j : Fin 7) : atomKernel57_1 j = (kernel0Box (atomPoints j) 57).mul (piI.mul (atomPoints j).z) := by
  fin_cases j <;> decide +kernel
lemma atomKernel57_1_contains (j : Fin 7) : (atomKernel57_1 j).Contains
    (complexTransformedFactor 57 1 1 ((j.val:ℝ)/6)) := by
  rw [atomKernel57_1_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=57) (by decide)
  have h0 := transformed_factor_zero_contains hh
  rw [transformed_factor_step]
  have hzz : complexZ ((j.val:ℂ)/6) = z ((j.val:ℝ)/6) := by
    simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat] using
      complexZ_ofReal ((j.val:ℝ)/6)
  have hz := (atomPoints_contains j).2.2.1
  rw [pointZ_eq] at hz
  simpa only [Nat.zero_add,Nat.cast_one,div_one,hzz,complexZ_ofReal,Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using
    CBox.contains_mul h0 (CBox.contains_mul piI_contains hz)
noncomputable def atomKernel60_0 : Fin 7 → CBox := ![⟨⟨(-3),3⟩,⟨(-3),3⟩⟩,⟨⟨(-4),4⟩,⟨(-4),4⟩⟩,⟨⟨(-4),4⟩,⟨(-4),4⟩⟩,⟨⟨(-3),2⟩,⟨(-2),3⟩⟩,⟨⟨0,3⟩,⟨(-1),2⟩⟩,⟨⟨276141132453,276141132456⟩,⟨481112337745,481112337747⟩⟩,⟨⟨(-3687892951764255580220410),(-3687892951764255439615550)⟩,⟨(-13213433696955863833376530),(-13213433696955863692536649)⟩⟩]
lemma atomKernel60_0_eq (j : Fin 7) : atomKernel60_0 j = kernel0Box (atomPoints j) 60 := by
  fin_cases j <;> decide +kernel
lemma atomKernel60_0_contains (j : Fin 7) : (atomKernel60_0 j).Contains
    (complexTransformedFactor 60 1 0 ((j.val:ℝ)/6)) := by
  rw [atomKernel60_0_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=60) (by decide)
  have h0 := transformed_factor_zero_contains hh
  simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using h0
noncomputable def atomKernel60_1 : Fin 7 → CBox := ![⟨⟨(-28),28⟩,⟨(-28),28⟩⟩,⟨⟨(-46),46⟩,⟨(-46),46⟩⟩,⟨⟨(-41),41⟩,⟨(-41),41⟩⟩,⟨⟨(-16),24⟩,⟨(-19),21⟩⟩,⟨⟨(-10),10⟩,⟨(-17),2⟩⟩,⟨⟨1770998736931,1770998736943⟩,⟨(-1466968117338),(-1466968117323)⟩⟩,⟨⟨(-47021565110366643310598364),(-47021565110366642775465957)⟩,⟨15798208239658489099154911,15798208239658489633378987⟩⟩]
lemma atomKernel60_1_eq (j : Fin 7) : atomKernel60_1 j = (kernel0Box (atomPoints j) 60).mul (piI.mul (atomPoints j).z) := by
  fin_cases j <;> decide +kernel
lemma atomKernel60_1_contains (j : Fin 7) : (atomKernel60_1 j).Contains
    (complexTransformedFactor 60 1 1 ((j.val:ℝ)/6)) := by
  rw [atomKernel60_1_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=60) (by decide)
  have h0 := transformed_factor_zero_contains hh
  rw [transformed_factor_step]
  have hzz : complexZ ((j.val:ℂ)/6) = z ((j.val:ℝ)/6) := by
    simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat] using
      complexZ_ofReal ((j.val:ℝ)/6)
  have hz := (atomPoints_contains j).2.2.1
  rw [pointZ_eq] at hz
  simpa only [Nat.zero_add,Nat.cast_one,div_one,hzz,complexZ_ofReal,Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using
    CBox.contains_mul h0 (CBox.contains_mul piI_contains hz)
noncomputable def atomKernel61_0 : Fin 7 → CBox := ![⟨⟨(-3),3⟩,⟨(-3),3⟩⟩,⟨⟨(-4),4⟩,⟨(-4),4⟩⟩,⟨⟨(-4),4⟩,⟨(-4),4⟩⟩,⟨⟨(-3),2⟩,⟨(-2),3⟩⟩,⟨⟨(-2),1⟩,⟨0,3⟩⟩,⟨⟨(-272745757303),(-272745757300)⟩,⟨(-29030202555),(-29030202552)⟩⟩,⟨⟨7680066386702458508481384,7680066386702458647801409⟩,⟨8383946322022811120249854,8383946322022811259696890⟩⟩]
lemma atomKernel61_0_eq (j : Fin 7) : atomKernel61_0 j = kernel0Box (atomPoints j) 61 := by
  fin_cases j <;> decide +kernel
lemma atomKernel61_0_contains (j : Fin 7) : (atomKernel61_0 j).Contains
    (complexTransformedFactor 61 1 0 ((j.val:ℝ)/6)) := by
  rw [atomKernel61_0_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=61) (by decide)
  have h0 := transformed_factor_zero_contains hh
  simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using h0
noncomputable def atomKernel61_1 : Fin 7 → CBox := ![⟨⟨(-28),28⟩,⟨(-28),28⟩⟩,⟨⟨(-46),46⟩,⟨(-46),46⟩⟩,⟨⟨(-41),41⟩,⟨(-41),41⟩⟩,⟨⟨(-16),24⟩,⟨(-19),21⟩⟩,⟨⟨(-2),17⟩,⟨(-10),10⟩⟩,⟨⟨73499239201,73499239217⟩,⟨1134693279692,1134693279708⟩⟩,⟨⟨28832536650691517300184176,28832536650691517829992601⟩,⟨(-29307201421334448060540620),(-29307201421334447531174655)⟩⟩]
lemma atomKernel61_1_eq (j : Fin 7) : atomKernel61_1 j = (kernel0Box (atomPoints j) 61).mul (piI.mul (atomPoints j).z) := by
  fin_cases j <;> decide +kernel
lemma atomKernel61_1_contains (j : Fin 7) : (atomKernel61_1 j).Contains
    (complexTransformedFactor 61 1 1 ((j.val:ℝ)/6)) := by
  rw [atomKernel61_1_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=61) (by decide)
  have h0 := transformed_factor_zero_contains hh
  rw [transformed_factor_step]
  have hzz : complexZ ((j.val:ℂ)/6) = z ((j.val:ℝ)/6) := by
    simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat] using
      complexZ_ofReal ((j.val:ℝ)/6)
  have hz := (atomPoints_contains j).2.2.1
  rw [pointZ_eq] at hz
  simpa only [Nat.zero_add,Nat.cast_one,div_one,hzz,complexZ_ofReal,Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using
    CBox.contains_mul h0 (CBox.contains_mul piI_contains hz)
noncomputable def atomKernel63_0 : Fin 7 → CBox := ![⟨⟨(-3),3⟩,⟨(-3),3⟩⟩,⟨⟨(-4),4⟩,⟨(-4),4⟩⟩,⟨⟨(-4),4⟩,⟨(-4),4⟩⟩,⟨⟨(-2),3⟩,⟨(-3),2⟩⟩,⟨⟨(-1),2⟩,⟨(-3),0⟩⟩,⟨⟨14016533948,14016533950⟩,⟨65577083170,65577083173⟩⟩,⟨⟨7763190550023462404344915,7763190550023462585911865⟩,⟨(-854893022145203587180632),(-854893022145203405719207)⟩⟩]
lemma atomKernel63_0_eq (j : Fin 7) : atomKernel63_0 j = kernel0Box (atomPoints j) 63 := by
  fin_cases j <;> decide +kernel
lemma atomKernel63_0_contains (j : Fin 7) : (atomKernel63_0 j).Contains
    (complexTransformedFactor 63 1 0 ((j.val:ℝ)/6)) := by
  rw [atomKernel63_0_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=63) (by decide)
  have h0 := transformed_factor_zero_contains hh
  simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using h0
noncomputable def atomKernel63_1 : Fin 7 → CBox := ![⟨⟨(-28),28⟩,⟨(-28),28⟩⟩,⟨⟨(-46),46⟩,⟨(-46),46⟩⟩,⟨⟨(-41),41⟩,⟨(-41),41⟩⟩,⟨⟨(-24),16⟩,⟨(-21),19⟩⟩,⟨⟨(-17),2⟩,⟨(-10),10⟩⟩,⟨⟨258029882626,258029882641⟩,⟨(-103447960612),(-103447960601)⟩⟩,⟨⟨(-4544761290569955933404665),(-4544761290569955244034832)⟩,⟨(-27872557088731765363058055),(-27872557088731764673251706)⟩⟩]
lemma atomKernel63_1_eq (j : Fin 7) : atomKernel63_1 j = (kernel0Box (atomPoints j) 63).mul (piI.mul (atomPoints j).z) := by
  fin_cases j <;> decide +kernel
lemma atomKernel63_1_contains (j : Fin 7) : (atomKernel63_1 j).Contains
    (complexTransformedFactor 63 1 1 ((j.val:ℝ)/6)) := by
  rw [atomKernel63_1_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=63) (by decide)
  have h0 := transformed_factor_zero_contains hh
  rw [transformed_factor_step]
  have hzz : complexZ ((j.val:ℂ)/6) = z ((j.val:ℝ)/6) := by
    simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat] using
      complexZ_ofReal ((j.val:ℝ)/6)
  have hz := (atomPoints_contains j).2.2.1
  rw [pointZ_eq] at hz
  simpa only [Nat.zero_add,Nat.cast_one,div_one,hzz,complexZ_ofReal,Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using
    CBox.contains_mul h0 (CBox.contains_mul piI_contains hz)
noncomputable def atomKernel64_0 : Fin 7 → CBox := ![⟨⟨(-3),3⟩,⟨(-3),3⟩⟩,⟨⟨(-4),4⟩,⟨(-4),4⟩⟩,⟨⟨(-4),4⟩,⟨(-4),4⟩⟩,⟨⟨(-2),3⟩,⟨(-3),2⟩⟩,⟨⟨0,3⟩,⟨(-1),2⟩⟩,⟨⟨(-30322265718),(-30322265715)⟩,⟨(-13414726933),(-13414726930)⟩⟩,⟨⟨(-5417607093436297299550652),(-5417607093436297234620271)⟩,⟨3542579624932083293148638,3542579624932083357981311⟩⟩]
lemma atomKernel64_0_eq (j : Fin 7) : atomKernel64_0 j = kernel0Box (atomPoints j) 64 := by
  fin_cases j <;> decide +kernel
lemma atomKernel64_0_contains (j : Fin 7) : (atomKernel64_0 j).Contains
    (complexTransformedFactor 64 1 0 ((j.val:ℝ)/6)) := by
  rw [atomKernel64_0_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=64) (by decide)
  have h0 := transformed_factor_zero_contains hh
  simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using h0
noncomputable def atomKernel64_1 : Fin 7 → CBox := ![⟨⟨(-28),28⟩,⟨(-28),28⟩⟩,⟨⟨(-46),46⟩,⟨(-46),46⟩⟩,⟨⟨(-41),41⟩,⟨(-41),41⟩⟩,⟨⟨(-24),16⟩,⟨(-21),19⟩⟩,⟨⟨(-10),10⟩,⟨(-17),2⟩⟩,⟨⟨(-33447006320),(-33447006304)⟩,⟨133323491750,133323491765⟩⟩,⟨⟨13809629524105563278775466,13809629524105563525124090⟩,⟨18897918223338345978367614,18897918223338346225071149⟩⟩]
lemma atomKernel64_1_eq (j : Fin 7) : atomKernel64_1 j = (kernel0Box (atomPoints j) 64).mul (piI.mul (atomPoints j).z) := by
  fin_cases j <;> decide +kernel
lemma atomKernel64_1_contains (j : Fin 7) : (atomKernel64_1 j).Contains
    (complexTransformedFactor 64 1 1 ((j.val:ℝ)/6)) := by
  rw [atomKernel64_1_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=64) (by decide)
  have h0 := transformed_factor_zero_contains hh
  rw [transformed_factor_step]
  have hzz : complexZ ((j.val:ℂ)/6) = z ((j.val:ℝ)/6) := by
    simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat] using
      complexZ_ofReal ((j.val:ℝ)/6)
  have hz := (atomPoints_contains j).2.2.1
  rw [pointZ_eq] at hz
  simpa only [Nat.zero_add,Nat.cast_one,div_one,hzz,complexZ_ofReal,Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using
    CBox.contains_mul h0 (CBox.contains_mul piI_contains hz)
noncomputable def atomKernel67_0 : Fin 7 → CBox := ![⟨⟨(-3),3⟩,⟨(-3),3⟩⟩,⟨⟨(-4),4⟩,⟨(-4),4⟩⟩,⟨⟨(-4),4⟩,⟨(-4),4⟩⟩,⟨⟨(-2),3⟩,⟨(-3),2⟩⟩,⟨⟨(-1),2⟩,⟨(-3),0⟩⟩,⟨⟨(-2994806832),(-2994806830)⟩,⟨(-2663982706),(-2663982703)⟩⟩,⟨⟨(-1491288608414460994055002),(-1491288608414460949634509)⟩,⟨(-3369987193263265566741046),(-3369987193263265522252121)⟩⟩]
lemma atomKernel67_0_eq (j : Fin 7) : atomKernel67_0 j = kernel0Box (atomPoints j) 67 := by
  fin_cases j <;> decide +kernel
lemma atomKernel67_0_contains (j : Fin 7) : (atomKernel67_0 j).Contains
    (complexTransformedFactor 67 1 0 ((j.val:ℝ)/6)) := by
  rw [atomKernel67_0_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=67) (by decide)
  have h0 := transformed_factor_zero_contains hh
  simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using h0
noncomputable def atomKernel67_1 : Fin 7 → CBox := ![⟨⟨(-28),28⟩,⟨(-28),28⟩⟩,⟨⟨(-46),46⟩,⟨(-46),46⟩⟩,⟨⟨(-41),41⟩,⟨(-41),41⟩⟩,⟨⟨(-24),16⟩,⟨(-21),19⟩⟩,⟨⟨(-17),2⟩,⟨(-10),10⟩⟩,⟨⟨(-8773900461),(-8773900446)⟩,⟨14110928914,14110928926⟩⟩,⟨⟨(-11889087240856962074595714),(-11889087240856961905564435)⟩,⟨6017875794307459362748221,6017875794307459531524769⟩⟩]
lemma atomKernel67_1_eq (j : Fin 7) : atomKernel67_1 j = (kernel0Box (atomPoints j) 67).mul (piI.mul (atomPoints j).z) := by
  fin_cases j <;> decide +kernel
lemma atomKernel67_1_contains (j : Fin 7) : (atomKernel67_1 j).Contains
    (complexTransformedFactor 67 1 1 ((j.val:ℝ)/6)) := by
  rw [atomKernel67_1_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=67) (by decide)
  have h0 := transformed_factor_zero_contains hh
  rw [transformed_factor_step]
  have hzz : complexZ ((j.val:ℂ)/6) = z ((j.val:ℝ)/6) := by
    simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat] using
      complexZ_ofReal ((j.val:ℝ)/6)
  have hz := (atomPoints_contains j).2.2.1
  rw [pointZ_eq] at hz
  simpa only [Nat.zero_add,Nat.cast_one,div_one,hzz,complexZ_ofReal,Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using
    CBox.contains_mul h0 (CBox.contains_mul piI_contains hz)
noncomputable def atomKernel69_0 : Fin 7 → CBox := ![⟨⟨(-3),3⟩,⟨(-3),3⟩⟩,⟨⟨(-4),4⟩,⟨(-4),4⟩⟩,⟨⟨(-4),4⟩,⟨(-4),4⟩⟩,⟨⟨(-2),3⟩,⟨(-3),2⟩⟩,⟨⟨(-3),0⟩,⟨(-2),1⟩⟩,⟨⟨(-390964209),(-390964206)⟩,⟨898566756,898566758⟩⟩,⟨⟨(-2472967857929847675126881),(-2472967857929847620472772)⟩,⟨(-540845680360740571625389),(-540845680360740516984804)⟩⟩]
lemma atomKernel69_0_eq (j : Fin 7) : atomKernel69_0 j = kernel0Box (atomPoints j) 69 := by
  fin_cases j <;> decide +kernel
lemma atomKernel69_0_contains (j : Fin 7) : (atomKernel69_0 j).Contains
    (complexTransformedFactor 69 1 0 ((j.val:ℝ)/6)) := by
  rw [atomKernel69_0_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=69) (by decide)
  have h0 := transformed_factor_zero_contains hh
  simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using h0
noncomputable def atomKernel69_1 : Fin 7 → CBox := ![⟨⟨(-28),28⟩,⟨(-28),28⟩⟩,⟨⟨(-46),46⟩,⟨(-46),46⟩⟩,⟨⟨(-41),41⟩,⟨(-41),41⟩⟩,⟨⟨(-24),16⟩,⟨(-21),19⟩⟩,⟨⟨(-10),10⟩,⟨(-2),17⟩⟩,⟨⟨3946269268,3946269279⟩,⟨964339428,964339442⟩⟩,⟨⟨(-1488650365615171334974520),(-1488650365615171127395664)⟩,⟨9031507735029591659109512,9031507735029591866755718⟩⟩]
lemma atomKernel69_1_eq (j : Fin 7) : atomKernel69_1 j = (kernel0Box (atomPoints j) 69).mul (piI.mul (atomPoints j).z) := by
  fin_cases j <;> decide +kernel
lemma atomKernel69_1_contains (j : Fin 7) : (atomKernel69_1 j).Contains
    (complexTransformedFactor 69 1 1 ((j.val:ℝ)/6)) := by
  rw [atomKernel69_1_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=69) (by decide)
  have h0 := transformed_factor_zero_contains hh
  rw [transformed_factor_step]
  have hzz : complexZ ((j.val:ℂ)/6) = z ((j.val:ℝ)/6) := by
    simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat] using
      complexZ_ofReal ((j.val:ℝ)/6)
  have hz := (atomPoints_contains j).2.2.1
  rw [pointZ_eq] at hz
  simpa only [Nat.zero_add,Nat.cast_one,div_one,hzz,complexZ_ofReal,Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using
    CBox.contains_mul h0 (CBox.contains_mul piI_contains hz)
noncomputable def atomKernel72_0 : Fin 7 → CBox := ![⟨⟨(-3),3⟩,⟨(-3),3⟩⟩,⟨⟨(-4),4⟩,⟨(-4),4⟩⟩,⟨⟨(-4),4⟩,⟨(-4),4⟩⟩,⟨⟨(-3),2⟩,⟨(-2),3⟩⟩,⟨⟨(-2),1⟩,⟨0,3⟩⟩,⟨⟨(-78188356),(-78188354)⟩,⟨88990295,88990297⟩⟩,⟨⟨531628501514138473100772,531628501514138493147184⟩,⟨(-1339538026650656465365006),(-1339538026650656445317450)⟩⟩]
lemma atomKernel72_0_eq (j : Fin 7) : atomKernel72_0 j = kernel0Box (atomPoints j) 72 := by
  fin_cases j <;> decide +kernel
lemma atomKernel72_0_contains (j : Fin 7) : (atomKernel72_0 j).Contains
    (complexTransformedFactor 72 1 0 ((j.val:ℝ)/6)) := by
  rw [atomKernel72_0_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=72) (by decide)
  have h0 := transformed_factor_zero_contains hh
  simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using h0
noncomputable def atomKernel72_1 : Fin 7 → CBox := ![⟨⟨(-28),28⟩,⟨(-28),28⟩⟩,⟨⟨(-46),46⟩,⟨(-46),46⟩⟩,⟨⟨(-41),41⟩,⟨(-41),41⟩⟩,⟨⟨(-16),24⟩,⟨(-19),21⟩⟩,⟨⟨(-2),17⟩,⟨(-10),10⟩⟩,⟨⟨418620151,418620161⟩,⟨256746258,256746269⟩⟩,⟨⟨(-4936932360757759705282210),(-4936932360757759629110065)⟩,⟨(-1668194813749212036209059),(-1668194813749211960049634)⟩⟩]
lemma atomKernel72_1_eq (j : Fin 7) : atomKernel72_1 j = (kernel0Box (atomPoints j) 72).mul (piI.mul (atomPoints j).z) := by
  fin_cases j <;> decide +kernel
lemma atomKernel72_1_contains (j : Fin 7) : (atomKernel72_1 j).Contains
    (complexTransformedFactor 72 1 1 ((j.val:ℝ)/6)) := by
  rw [atomKernel72_1_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=72) (by decide)
  have h0 := transformed_factor_zero_contains hh
  rw [transformed_factor_step]
  have hzz : complexZ ((j.val:ℂ)/6) = z ((j.val:ℝ)/6) := by
    simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat] using
      complexZ_ofReal ((j.val:ℝ)/6)
  have hz := (atomPoints_contains j).2.2.1
  rw [pointZ_eq] at hz
  simpa only [Nat.zero_add,Nat.cast_one,div_one,hzz,complexZ_ofReal,Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using
    CBox.contains_mul h0 (CBox.contains_mul piI_contains hz)
noncomputable def atomKernel73_0 : Fin 7 → CBox := ![⟨⟨(-3),3⟩,⟨(-3),3⟩⟩,⟨⟨(-4),4⟩,⟨(-4),4⟩⟩,⟨⟨(-4),4⟩,⟨(-4),4⟩⟩,⟨⟨(-2),3⟩,⟨(-3),2⟩⟩,⟨⟨(-3),0⟩,⟨(-2),1⟩⟩,⟨⟨(-12943923),(-12943920)⟩,⟨(-57124493),(-57124490)⟩⟩,⟨⟨109287676979571211948290,109287676979571227649066⟩,⟨1189440891031047220487264,1189440891031047236203926⟩⟩]
lemma atomKernel73_0_eq (j : Fin 7) : atomKernel73_0 j = kernel0Box (atomPoints j) 73 := by
  fin_cases j <;> decide +kernel
lemma atomKernel73_0_contains (j : Fin 7) : (atomKernel73_0 j).Contains
    (complexTransformedFactor 73 1 0 ((j.val:ℝ)/6)) := by
  rw [atomKernel73_0_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=73) (by decide)
  have h0 := transformed_factor_zero_contains hh
  simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using h0
noncomputable def atomKernel73_1 : Fin 7 → CBox := ![⟨⟨(-28),28⟩,⟨(-28),28⟩⟩,⟨⟨(-46),46⟩,⟨(-46),46⟩⟩,⟨⟨(-41),41⟩,⟨(-41),41⟩⟩,⟨⟨(-24),16⟩,⟨(-21),19⟩⟩,⟨⟨(-10),10⟩,⟨(-2),17⟩⟩,⟨⟨(-224253997),(-224253982)⟩,⟨93112811,93112826⟩⟩,⟨⟨4274580715241190966150627,4274580715241191025865828⟩,⟨(-617985952775082751425094),(-617985952775082691776045)⟩⟩]
lemma atomKernel73_1_eq (j : Fin 7) : atomKernel73_1 j = (kernel0Box (atomPoints j) 73).mul (piI.mul (atomPoints j).z) := by
  fin_cases j <;> decide +kernel
lemma atomKernel73_1_contains (j : Fin 7) : (atomKernel73_1 j).Contains
    (complexTransformedFactor 73 1 1 ((j.val:ℝ)/6)) := by
  rw [atomKernel73_1_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=73) (by decide)
  have h0 := transformed_factor_zero_contains hh
  rw [transformed_factor_step]
  have hzz : complexZ ((j.val:ℂ)/6) = z ((j.val:ℝ)/6) := by
    simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat] using
      complexZ_ofReal ((j.val:ℝ)/6)
  have hz := (atomPoints_contains j).2.2.1
  rw [pointZ_eq] at hz
  simpa only [Nat.zero_add,Nat.cast_one,div_one,hzz,complexZ_ofReal,Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using
    CBox.contains_mul h0 (CBox.contains_mul piI_contains hz)
noncomputable def atomKernel75_0 : Fin 7 → CBox := ![⟨⟨(-3),3⟩,⟨(-3),3⟩⟩,⟨⟨(-4),4⟩,⟨(-4),4⟩⟩,⟨⟨(-4),4⟩,⟨(-4),4⟩⟩,⟨⟨(-3),2⟩,⟨(-2),3⟩⟩,⟨⟨0,3⟩,⟨(-1),2⟩⟩,⟨⟨(-12286520),(-12286517)⟩,⟨7355538,7355541⟩⟩,⟨⟨703608085078664601370298,703608085078664619181865⟩,⟨422055543839951182722930,422055543839951200537419⟩⟩]
lemma atomKernel75_0_eq (j : Fin 7) : atomKernel75_0 j = kernel0Box (atomPoints j) 75 := by
  fin_cases j <;> decide +kernel
lemma atomKernel75_0_contains (j : Fin 7) : (atomKernel75_0 j).Contains
    (complexTransformedFactor 75 1 0 ((j.val:ℝ)/6)) := by
  rw [atomKernel75_0_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=75) (by decide)
  have h0 := transformed_factor_zero_contains hh
  simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using h0
noncomputable def atomKernel75_1 : Fin 7 → CBox := ![⟨⟨(-28),28⟩,⟨(-28),28⟩⟩,⟨⟨(-46),46⟩,⟨(-46),46⟩⟩,⟨⟨(-41),41⟩,⟨(-41),41⟩⟩,⟨⟨(-16),24⟩,⟨(-19),21⟩⟩,⟨⟨(-10),10⟩,⟨(-17),2⟩⟩,⟨⟨38703006,38703021⟩,⟨45013514,45013530⟩⟩,⟨⟨1391934708503196287668457,1391934708503196355346851⟩,⟨(-2619997901239201881920850),(-2619997901239201814249391)⟩⟩]
lemma atomKernel75_1_eq (j : Fin 7) : atomKernel75_1 j = (kernel0Box (atomPoints j) 75).mul (piI.mul (atomPoints j).z) := by
  fin_cases j <;> decide +kernel
lemma atomKernel75_1_contains (j : Fin 7) : (atomKernel75_1 j).Contains
    (complexTransformedFactor 75 1 1 ((j.val:ℝ)/6)) := by
  rw [atomKernel75_1_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=75) (by decide)
  have h0 := transformed_factor_zero_contains hh
  rw [transformed_factor_step]
  have hzz : complexZ ((j.val:ℂ)/6) = z ((j.val:ℝ)/6) := by
    simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat] using
      complexZ_ofReal ((j.val:ℝ)/6)
  have hz := (atomPoints_contains j).2.2.1
  rw [pointZ_eq] at hz
  simpa only [Nat.zero_add,Nat.cast_one,div_one,hzz,complexZ_ofReal,Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using
    CBox.contains_mul h0 (CBox.contains_mul piI_contains hz)
noncomputable def atomKernel76_0 : Fin 7 → CBox := ![⟨⟨(-3),3⟩,⟨(-3),3⟩⟩,⟨⟨(-4),4⟩,⟨(-4),4⟩⟩,⟨⟨(-4),4⟩,⟨(-4),4⟩⟩,⟨⟨(-3),2⟩,⟨(-2),3⟩⟩,⟨⟨(-2),1⟩,⟨0,3⟩⟩,⟨⟨619843,619845⟩,⟨(-7053373),(-7053371)⟩⟩,⟨⟨(-678312739500487052041191),(-678312739500487041764779)⟩,⟨(-48153947454543726886191),(-48153947454543716615960)⟩⟩]
lemma atomKernel76_0_eq (j : Fin 7) : atomKernel76_0 j = kernel0Box (atomPoints j) 76 := by
  fin_cases j <;> decide +kernel
lemma atomKernel76_0_contains (j : Fin 7) : (atomKernel76_0 j).Contains
    (complexTransformedFactor 76 1 0 ((j.val:ℝ)/6)) := by
  rw [atomKernel76_0_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=76) (by decide)
  have h0 := transformed_factor_zero_contains hh
  simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using h0
noncomputable def atomKernel76_1 : Fin 7 → CBox := ![⟨⟨(-28),28⟩,⟨(-28),28⟩⟩,⟨⟨(-46),46⟩,⟨(-46),46⟩⟩,⟨⟨(-41),41⟩,⟨(-41),41⟩⟩,⟨⟨(-16),24⟩,⟨(-19),21⟩⟩,⟨⟨(-2),17⟩,⟨(-10),10⟩⟩,⟨⟨(-29251677),(-29251667)⟩,⟨2435474,2435484⟩⟩,⟨⟨(-46516099958030390332757),(-46516099958030351316090)⟩,⟨2458446992878682192858732,2458446992878682231903426⟩⟩]
lemma atomKernel76_1_eq (j : Fin 7) : atomKernel76_1 j = (kernel0Box (atomPoints j) 76).mul (piI.mul (atomPoints j).z) := by
  fin_cases j <;> decide +kernel
lemma atomKernel76_1_contains (j : Fin 7) : (atomKernel76_1 j).Contains
    (complexTransformedFactor 76 1 1 ((j.val:ℝ)/6)) := by
  rw [atomKernel76_1_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=76) (by decide)
  have h0 := transformed_factor_zero_contains hh
  rw [transformed_factor_step]
  have hzz : complexZ ((j.val:ℂ)/6) = z ((j.val:ℝ)/6) := by
    simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat] using
      complexZ_ofReal ((j.val:ℝ)/6)
  have hz := (atomPoints_contains j).2.2.1
  rw [pointZ_eq] at hz
  simpa only [Nat.zero_add,Nat.cast_one,div_one,hzz,complexZ_ofReal,Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using
    CBox.contains_mul h0 (CBox.contains_mul piI_contains hz)
noncomputable def atomKernel79_0 : Fin 7 → CBox := ![⟨⟨(-3),3⟩,⟨(-3),3⟩⟩,⟨⟨(-4),4⟩,⟨(-4),4⟩⟩,⟨⟨(-4),4⟩,⟨(-4),4⟩⟩,⟨⟨(-2),3⟩,⟨(-3),2⟩⟩,⟨⟨0,3⟩,⟨(-1),2⟩⟩,⟨⟨331845,331848⟩,⟨(-788988),(-788986)⟩⟩,⟨⟨89529674993727874189181,89529674993727886667074⟩,⟨(-376651654647634047610591),(-376651654647634035130828)⟩⟩]
lemma atomKernel79_0_eq (j : Fin 7) : atomKernel79_0 j = kernel0Box (atomPoints j) 79 := by
  fin_cases j <;> decide +kernel
lemma atomKernel79_0_contains (j : Fin 7) : (atomKernel79_0 j).Contains
    (complexTransformedFactor 79 1 0 ((j.val:ℝ)/6)) := by
  rw [atomKernel79_0_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=79) (by decide)
  have h0 := transformed_factor_zero_contains hh
  simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using h0
noncomputable def atomKernel79_1 : Fin 7 → CBox := ![⟨⟨(-28),28⟩,⟨(-28),28⟩⟩,⟨⟨(-46),46⟩,⟨(-46),46⟩⟩,⟨⟨(-41),41⟩,⟨(-41),41⟩⟩,⟨⟨(-24),16⟩,⟨(-21),19⟩⟩,⟨⟨(-10),10⟩,⟨(-17),2⟩⟩,⟨⟨(-3456972),(-3456961)⟩,⟨(-800011),(-799996)⟩⟩,⟨⟨(-1376910219774543734492856),(-1376910219774543687080707)⟩,⟨(-252568843144825406234940),(-252568843144825358832321)⟩⟩]
lemma atomKernel79_1_eq (j : Fin 7) : atomKernel79_1 j = (kernel0Box (atomPoints j) 79).mul (piI.mul (atomPoints j).z) := by
  fin_cases j <;> decide +kernel
lemma atomKernel79_1_contains (j : Fin 7) : (atomKernel79_1 j).Contains
    (complexTransformedFactor 79 1 1 ((j.val:ℝ)/6)) := by
  rw [atomKernel79_1_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=79) (by decide)
  have h0 := transformed_factor_zero_contains hh
  rw [transformed_factor_step]
  have hzz : complexZ ((j.val:ℂ)/6) = z ((j.val:ℝ)/6) := by
    simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat] using
      complexZ_ofReal ((j.val:ℝ)/6)
  have hz := (atomPoints_contains j).2.2.1
  rw [pointZ_eq] at hz
  simpa only [Nat.zero_add,Nat.cast_one,div_one,hzz,complexZ_ofReal,Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using
    CBox.contains_mul h0 (CBox.contains_mul piI_contains hz)
noncomputable def atomKernel81_0 : Fin 7 → CBox := ![⟨⟨(-3),3⟩,⟨(-3),3⟩⟩,⟨⟨(-4),4⟩,⟨(-4),4⟩⟩,⟨⟨(-4),4⟩,⟨(-4),4⟩⟩,⟨⟨(-3),2⟩,⟨(-2),3⟩⟩,⟨⟨(-3),0⟩,⟨(-2),1⟩⟩,⟨⟨(-208567),(-208565)⟩,⟨(-17042),(-17039)⟩⟩,⟨⟨(-172436430715579443954493),(-172436430715579440303708)⟩,⟨(-202453859519989861406243),(-202453859519989857752274)⟩⟩]
lemma atomKernel81_0_eq (j : Fin 7) : atomKernel81_0 j = kernel0Box (atomPoints j) 81 := by
  fin_cases j <;> decide +kernel
lemma atomKernel81_0_contains (j : Fin 7) : (atomKernel81_0 j).Contains
    (complexTransformedFactor 81 1 0 ((j.val:ℝ)/6)) := by
  rw [atomKernel81_0_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=81) (by decide)
  have h0 := transformed_factor_zero_contains hh
  simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using h0
noncomputable def atomKernel81_1 : Fin 7 → CBox := ![⟨⟨(-28),28⟩,⟨(-28),28⟩⟩,⟨⟨(-46),46⟩,⟨(-46),46⟩⟩,⟨⟨(-41),41⟩,⟨(-41),41⟩⟩,⟨⟨(-16),24⟩,⟨(-19),21⟩⟩,⟨⟨(-10),10⟩,⟨(-2),17⟩⟩,⟨⟨77271,77286⟩,⟨864050,864061⟩⟩,⟨⟨(-698687191394988581642740),(-698687191394988567760212)⟩,⟨660687881552612128250917,660687881552612142122219⟩⟩]
lemma atomKernel81_1_eq (j : Fin 7) : atomKernel81_1 j = (kernel0Box (atomPoints j) 81).mul (piI.mul (atomPoints j).z) := by
  fin_cases j <;> decide +kernel
lemma atomKernel81_1_contains (j : Fin 7) : (atomKernel81_1 j).Contains
    (complexTransformedFactor 81 1 1 ((j.val:ℝ)/6)) := by
  rw [atomKernel81_1_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=81) (by decide)
  have h0 := transformed_factor_zero_contains hh
  rw [transformed_factor_step]
  have hzz : complexZ ((j.val:ℂ)/6) = z ((j.val:ℝ)/6) := by
    simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat] using
      complexZ_ofReal ((j.val:ℝ)/6)
  have hz := (atomPoints_contains j).2.2.1
  rw [pointZ_eq] at hz
  simpa only [Nat.zero_add,Nat.cast_one,div_one,hzz,complexZ_ofReal,Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using
    CBox.contains_mul h0 (CBox.contains_mul piI_contains hz)
noncomputable def atomKernel84_0 : Fin 7 → CBox := ![⟨⟨(-3),3⟩,⟨(-3),3⟩⟩,⟨⟨(-4),4⟩,⟨(-4),4⟩⟩,⟨⟨(-4),4⟩,⟨(-4),4⟩⟩,⟨⟨(-2),3⟩,⟨(-3),2⟩⟩,⟨⟨(-2),1⟩,⟨0,3⟩⟩,⟨⟨(-23379),(-23376)⟩,⟨(-9665),(-9663)⟩⟩,⟨⟨129624059787215343467447,129624059787215345689455⟩,⟨(-78230506048611033060433),(-78230506048611030840833)⟩⟩]
lemma atomKernel84_0_eq (j : Fin 7) : atomKernel84_0 j = kernel0Box (atomPoints j) 84 := by
  fin_cases j <;> decide +kernel
lemma atomKernel84_0_contains (j : Fin 7) : (atomKernel84_0 j).Contains
    (complexTransformedFactor 84 1 0 ((j.val:ℝ)/6)) := by
  rw [atomKernel84_0_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=84) (by decide)
  have h0 := transformed_factor_zero_contains hh
  simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using h0
noncomputable def atomKernel84_1 : Fin 7 → CBox := ![⟨⟨(-28),28⟩,⟨(-28),28⟩⟩,⟨⟨(-46),46⟩,⟨(-46),46⟩⟩,⟨⟨(-41),41⟩,⟨(-41),41⟩⟩,⟨⟨(-24),16⟩,⟨(-21),19⟩⟩,⟨⟨(-2),17⟩,⟨(-10),10⟩⟩,⟨⟨(-23021),(-23010)⟩,⟨102303,102318⟩⟩,⟨⟨(-306832338821425630953193),(-306832338821425622519948)⟩,⟨(-453386250615374248059790),(-453386250615374239617742)⟩⟩]
lemma atomKernel84_1_eq (j : Fin 7) : atomKernel84_1 j = (kernel0Box (atomPoints j) 84).mul (piI.mul (atomPoints j).z) := by
  fin_cases j <;> decide +kernel
lemma atomKernel84_1_contains (j : Fin 7) : (atomKernel84_1 j).Contains
    (complexTransformedFactor 84 1 1 ((j.val:ℝ)/6)) := by
  rw [atomKernel84_1_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=84) (by decide)
  have h0 := transformed_factor_zero_contains hh
  rw [transformed_factor_step]
  have hzz : complexZ ((j.val:ℂ)/6) = z ((j.val:ℝ)/6) := by
    simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat] using
      complexZ_ofReal ((j.val:ℝ)/6)
  have hz := (atomPoints_contains j).2.2.1
  rw [pointZ_eq] at hz
  simpa only [Nat.zero_add,Nat.cast_one,div_one,hzz,complexZ_ofReal,Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using
    CBox.contains_mul h0 (CBox.contains_mul piI_contains hz)
noncomputable def atomKernel85_0 : Fin 7 → CBox := ![⟨⟨(-3),3⟩,⟨(-3),3⟩⟩,⟨⟨(-4),4⟩,⟨(-4),4⟩⟩,⟨⟨(-4),4⟩,⟨(-4),4⟩⟩,⟨⟨(-2),3⟩,⟨(-3),2⟩⟩,⟨⟨(-3),2⟩,⟨(-3),1⟩⟩,⟨⟨10651,10653⟩,⟨(-6557),(-6555)⟩⟩,⟨⟨(-66479865675897499458536),(-66479865675897497215962)⟩,⟨106424352074323537274067,106424352074323539516148⟩⟩]
lemma atomKernel85_0_eq (j : Fin 7) : atomKernel85_0 j = kernel0Box (atomPoints j) 85 := by
  fin_cases j <;> decide +kernel
lemma atomKernel85_0_contains (j : Fin 7) : (atomKernel85_0 j).Contains
    (complexTransformedFactor 85 1 0 ((j.val:ℝ)/6)) := by
  rw [atomKernel85_0_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=85) (by decide)
  have h0 := transformed_factor_zero_contains hh
  simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using h0
noncomputable def atomKernel85_1 : Fin 7 → CBox := ![⟨⟨(-28),28⟩,⟨(-28),28⟩⟩,⟨⟨(-46),46⟩,⟨(-46),46⟩⟩,⟨⟨(-41),41⟩,⟨(-41),41⟩⟩,⟨⟨(-24),16⟩,⟨(-21),19⟩⟩,⟨⟨(-17),10⟩,⟨(-11),19⟩⟩,⟨⟨(-34291),(-34280)⟩,⟨(-38904),(-38894)⟩⟩,⟨⟨396784253834411909373238,396784253834411917891811⟩,⟨220076868461803344191588,220076868461803352711413⟩⟩]
lemma atomKernel85_1_eq (j : Fin 7) : atomKernel85_1 j = (kernel0Box (atomPoints j) 85).mul (piI.mul (atomPoints j).z) := by
  fin_cases j <;> decide +kernel
lemma atomKernel85_1_contains (j : Fin 7) : (atomKernel85_1 j).Contains
    (complexTransformedFactor 85 1 1 ((j.val:ℝ)/6)) := by
  rw [atomKernel85_1_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=85) (by decide)
  have h0 := transformed_factor_zero_contains hh
  rw [transformed_factor_step]
  have hzz : complexZ ((j.val:ℂ)/6) = z ((j.val:ℝ)/6) := by
    simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat] using
      complexZ_ofReal ((j.val:ℝ)/6)
  have hz := (atomPoints_contains j).2.2.1
  rw [pointZ_eq] at hz
  simpa only [Nat.zero_add,Nat.cast_one,div_one,hzz,complexZ_ofReal,Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using
    CBox.contains_mul h0 (CBox.contains_mul piI_contains hz)
noncomputable def atomKernel87_0 : Fin 7 → CBox := ![⟨⟨(-3),3⟩,⟨(-3),3⟩⟩,⟨⟨(-4),4⟩,⟨(-4),4⟩⟩,⟨⟨(-4),4⟩,⟨(-4),4⟩⟩,⟨⟨(-3),2⟩,⟨(-2),3⟩⟩,⟨⟨(-2),1⟩,⟨0,3⟩⟩,⟨⟨(-2335),(-2332)⟩,⟨(-1977),(-1975)⟩⟩,⟨⟨32012112202517490930319,32012112202517492431184⟩,⟨80030280506293728395916,80030280506293729898451⟩⟩]
lemma atomKernel87_0_eq (j : Fin 7) : atomKernel87_0 j = kernel0Box (atomPoints j) 87 := by
  fin_cases j <;> decide +kernel
lemma atomKernel87_0_contains (j : Fin 7) : (atomKernel87_0 j).Contains
    (complexTransformedFactor 87 1 0 ((j.val:ℝ)/6)) := by
  rw [atomKernel87_0_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=87) (by decide)
  have h0 := transformed_factor_zero_contains hh
  simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using h0
noncomputable def atomKernel87_1 : Fin 7 → CBox := ![⟨⟨(-28),28⟩,⟨(-28),28⟩⟩,⟨⟨(-46),46⟩,⟨(-46),46⟩⟩,⟨⟨(-41),41⟩,⟨(-41),41⟩⟩,⟨⟨(-16),24⟩,⟨(-19),21⟩⟩,⟨⟨(-2),17⟩,⟨(-10),10⟩⟩,⟨⟨(-6435),(-6423)⟩,⟨10917,10932⟩⟩,⟨⟨282980405108269099955578,282980405108269105664034⟩,⟨(-130624124907003306108101),(-130624124907003300405886)⟩⟩]
lemma atomKernel87_1_eq (j : Fin 7) : atomKernel87_1 j = (kernel0Box (atomPoints j) 87).mul (piI.mul (atomPoints j).z) := by
  fin_cases j <;> decide +kernel
lemma atomKernel87_1_contains (j : Fin 7) : (atomKernel87_1 j).Contains
    (complexTransformedFactor 87 1 1 ((j.val:ℝ)/6)) := by
  rw [atomKernel87_1_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=87) (by decide)
  have h0 := transformed_factor_zero_contains hh
  rw [transformed_factor_step]
  have hzz : complexZ ((j.val:ℂ)/6) = z ((j.val:ℝ)/6) := by
    simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat] using
      complexZ_ofReal ((j.val:ℝ)/6)
  have hz := (atomPoints_contains j).2.2.1
  rw [pointZ_eq] at hz
  simpa only [Nat.zero_add,Nat.cast_one,div_one,hzz,complexZ_ofReal,Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using
    CBox.contains_mul h0 (CBox.contains_mul piI_contains hz)
noncomputable def atomKernel88_0 : Fin 7 → CBox := ![⟨⟨(-3),3⟩,⟨(-3),3⟩⟩,⟨⟨(-4),4⟩,⟨(-4),4⟩⟩,⟨⟨(-4),4⟩,⟨(-4),4⟩⟩,⟨⟨(-3),2⟩,⟨(-2),3⟩⟩,⟨⟨(-3),0⟩,⟨(-2),1⟩⟩,⟨⟨1466,1469⟩,⟨(-363),(-360)⟩⟩,⟨⟨(-53667761454177673217850),(-53667761454177671809334)⟩,⟨(-47151664169976977915978),(-47151664169976976506861)⟩⟩]
lemma atomKernel88_0_eq (j : Fin 7) : atomKernel88_0 j = kernel0Box (atomPoints j) 88 := by
  fin_cases j <;> decide +kernel
lemma atomKernel88_0_contains (j : Fin 7) : (atomKernel88_0 j).Contains
    (complexTransformedFactor 88 1 0 ((j.val:ℝ)/6)) := by
  rw [atomKernel88_0_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=88) (by decide)
  have h0 := transformed_factor_zero_contains hh
  simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using h0
noncomputable def atomKernel88_1 : Fin 7 → CBox := ![⟨⟨(-28),28⟩,⟨(-28),28⟩⟩,⟨⟨(-46),46⟩,⟨(-46),46⟩⟩,⟨⟨(-41),41⟩,⟨(-41),41⟩⟩,⟨⟨(-16),24⟩,⟨(-19),21⟩⟩,⟨⟨(-10),10⟩,⟨(-2),17⟩⟩,⟨⟨(-2518),(-2503)⟩,⟨(-5748),(-5733)⟩⟩,⟨⟨(-160188511511197630997088),(-160188511511197625643673)⟩,⟨202649510173129374133916,202649510173129379485345⟩⟩]
lemma atomKernel88_1_eq (j : Fin 7) : atomKernel88_1 j = (kernel0Box (atomPoints j) 88).mul (piI.mul (atomPoints j).z) := by
  fin_cases j <;> decide +kernel
lemma atomKernel88_1_contains (j : Fin 7) : (atomKernel88_1 j).Contains
    (complexTransformedFactor 88 1 1 ((j.val:ℝ)/6)) := by
  rw [atomKernel88_1_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=88) (by decide)
  have h0 := transformed_factor_zero_contains hh
  rw [transformed_factor_step]
  have hzz : complexZ ((j.val:ℂ)/6) = z ((j.val:ℝ)/6) := by
    simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat] using
      complexZ_ofReal ((j.val:ℝ)/6)
  have hz := (atomPoints_contains j).2.2.1
  rw [pointZ_eq] at hz
  simpa only [Nat.zero_add,Nat.cast_one,div_one,hzz,complexZ_ofReal,Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using
    CBox.contains_mul h0 (CBox.contains_mul piI_contains hz)
noncomputable def atomKernel91_0 : Fin 7 → CBox := ![⟨⟨(-3),3⟩,⟨(-3),3⟩⟩,⟨⟨(-4),4⟩,⟨(-4),4⟩⟩,⟨⟨(-4),4⟩,⟨(-4),4⟩⟩,⟨⟨(-3),2⟩,⟨(-2),3⟩⟩,⟨⟨(-2),1⟩,⟨0,3⟩⟩,⟨⟨181,184⟩,⟨11,14⟩⟩,⟨⟨31433625527526022583414,31433625527526024155485⟩,⟨(-25808495280877464698778),(-25808495280877463127214)⟩⟩]
lemma atomKernel91_0_eq (j : Fin 7) : atomKernel91_0 j = kernel0Box (atomPoints j) 91 := by
  fin_cases j <;> decide +kernel
lemma atomKernel91_0_contains (j : Fin 7) : (atomKernel91_0 j).Contains
    (complexTransformedFactor 91 1 0 ((j.val:ℝ)/6)) := by
  rw [atomKernel91_0_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=91) (by decide)
  have h0 := transformed_factor_zero_contains hh
  simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using h0
noncomputable def atomKernel91_1 : Fin 7 → CBox := ![⟨⟨(-28),28⟩,⟨(-28),28⟩⟩,⟨⟨(-46),46⟩,⟨(-46),46⟩⟩,⟨⟨(-41),41⟩,⟨(-41),41⟩⟩,⟨⟨(-16),24⟩,⟨(-19),21⟩⟩,⟨⟨(-2),17⟩,⟨(-10),10⟩⟩,⟨⟨(-85),(-70)⟩,⟨(-762),(-747)⟩⟩,⟨⟨(-99097545770489476463551),(-99097545770489470493083)⟩,⟨(-108661492546998332529326),(-108661492546998326557061)⟩⟩]
lemma atomKernel91_1_eq (j : Fin 7) : atomKernel91_1 j = (kernel0Box (atomPoints j) 91).mul (piI.mul (atomPoints j).z) := by
  fin_cases j <;> decide +kernel
lemma atomKernel91_1_contains (j : Fin 7) : (atomKernel91_1 j).Contains
    (complexTransformedFactor 91 1 1 ((j.val:ℝ)/6)) := by
  rw [atomKernel91_1_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=91) (by decide)
  have h0 := transformed_factor_zero_contains hh
  rw [transformed_factor_step]
  have hzz : complexZ ((j.val:ℂ)/6) = z ((j.val:ℝ)/6) := by
    simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat] using
      complexZ_ofReal ((j.val:ℝ)/6)
  have hz := (atomPoints_contains j).2.2.1
  rw [pointZ_eq] at hz
  simpa only [Nat.zero_add,Nat.cast_one,div_one,hzz,complexZ_ofReal,Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using
    CBox.contains_mul h0 (CBox.contains_mul piI_contains hz)
noncomputable def atomKernel93_0 : Fin 7 → CBox := ![⟨⟨(-3),3⟩,⟨(-3),3⟩⟩,⟨⟨(-4),4⟩,⟨(-4),4⟩⟩,⟨⟨(-4),4⟩,⟨(-4),4⟩⟩,⟨⟨(-3),2⟩,⟨(-2),3⟩⟩,⟨⟨(-1),3⟩,⟨(-3),2⟩⟩,⟨⟨(-12),(-9)⟩,⟨(-45),(-43)⟩⟩,⟨⟨(-1550134697257742362828),(-1550134697257741337808)⟩,⟨(-27894603629501960600858),(-27894603629501959575495)⟩⟩]
lemma atomKernel93_0_eq (j : Fin 7) : atomKernel93_0 j = kernel0Box (atomPoints j) 93 := by
  fin_cases j <;> decide +kernel
lemma atomKernel93_0_contains (j : Fin 7) : (atomKernel93_0 j).Contains
    (complexTransformedFactor 93 1 0 ((j.val:ℝ)/6)) := by
  rw [atomKernel93_0_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=93) (by decide)
  have h0 := transformed_factor_zero_contains hh
  simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using h0
noncomputable def atomKernel93_1 : Fin 7 → CBox := ![⟨⟨(-28),28⟩,⟨(-28),28⟩⟩,⟨⟨(-46),46⟩,⟨(-46),46⟩⟩,⟨⟨(-41),41⟩,⟨(-41),41⟩⟩,⟨⟨(-16),24⟩,⟨(-19),21⟩⟩,⟨⟨(-19),11⟩,⟨(-17),10⟩⟩,⟨⟨(-178),(-167)⟩,⟨67,81⟩⟩,⟨⟨(-100437066051539775915596),(-100437066051539772020190)⟩,⟨10835440037374908526648,10835440037374912420593⟩⟩]
lemma atomKernel93_1_eq (j : Fin 7) : atomKernel93_1 j = (kernel0Box (atomPoints j) 93).mul (piI.mul (atomPoints j).z) := by
  fin_cases j <;> decide +kernel
lemma atomKernel93_1_contains (j : Fin 7) : (atomKernel93_1 j).Contains
    (complexTransformedFactor 93 1 1 ((j.val:ℝ)/6)) := by
  rw [atomKernel93_1_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=93) (by decide)
  have h0 := transformed_factor_zero_contains hh
  rw [transformed_factor_step]
  have hzz : complexZ ((j.val:ℂ)/6) = z ((j.val:ℝ)/6) := by
    simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat] using
      complexZ_ofReal ((j.val:ℝ)/6)
  have hz := (atomPoints_contains j).2.2.1
  rw [pointZ_eq] at hz
  simpa only [Nat.zero_add,Nat.cast_one,div_one,hzz,complexZ_ofReal,Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using
    CBox.contains_mul h0 (CBox.contains_mul piI_contains hz)
noncomputable def atomKernel96_0 : Fin 7 → CBox := ![⟨⟨(-3),3⟩,⟨(-3),3⟩⟩,⟨⟨(-4),4⟩,⟨(-4),4⟩⟩,⟨⟨(-4),4⟩,⟨(-4),4⟩⟩,⟨⟨(-2),3⟩,⟨(-3),2⟩⟩,⟨⟨(-3),1⟩,⟨(-2),3⟩⟩,⟨⟨0,2⟩,⟨(-7),(-4)⟩⟩,⟨⟨15814406802226201521746,15814406802226201786124⟩,⟨1698343281962387932152,1698343281962388196402⟩⟩]
lemma atomKernel96_0_eq (j : Fin 7) : atomKernel96_0 j = kernel0Box (atomPoints j) 96 := by
  fin_cases j <;> decide +kernel
lemma atomKernel96_0_contains (j : Fin 7) : (atomKernel96_0 j).Contains
    (complexTransformedFactor 96 1 0 ((j.val:ℝ)/6)) := by
  rw [atomKernel96_0_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=96) (by decide)
  have h0 := transformed_factor_zero_contains hh
  simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using h0
noncomputable def atomKernel96_1 : Fin 7 → CBox := ![⟨⟨(-28),28⟩,⟨(-28),28⟩⟩,⟨⟨(-46),46⟩,⟨(-46),46⟩⟩,⟨⟨(-41),41⟩,⟨(-41),41⟩⟩,⟨⟨(-24),16⟩,⟨(-21),19⟩⟩,⟨⟨(-11),19⟩,⟨(-10),17⟩⟩,⟨⟨(-31),(-16)⟩,⟨(-6),5⟩⟩,⟨⟨3163237606767119156122,3163237606767120160009⟩,⟨(-57425138362303901024255),(-57425138362303900019776)⟩⟩]
lemma atomKernel96_1_eq (j : Fin 7) : atomKernel96_1 j = (kernel0Box (atomPoints j) 96).mul (piI.mul (atomPoints j).z) := by
  fin_cases j <;> decide +kernel
lemma atomKernel96_1_contains (j : Fin 7) : (atomKernel96_1 j).Contains
    (complexTransformedFactor 96 1 1 ((j.val:ℝ)/6)) := by
  rw [atomKernel96_1_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=96) (by decide)
  have h0 := transformed_factor_zero_contains hh
  rw [transformed_factor_step]
  have hzz : complexZ ((j.val:ℂ)/6) = z ((j.val:ℝ)/6) := by
    simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat] using
      complexZ_ofReal ((j.val:ℝ)/6)
  have hz := (atomPoints_contains j).2.2.1
  rw [pointZ_eq] at hz
  simpa only [Nat.zero_add,Nat.cast_one,div_one,hzz,complexZ_ofReal,Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using
    CBox.contains_mul h0 (CBox.contains_mul piI_contains hz)
noncomputable def atomKernel97_0 : Fin 7 → CBox := ![⟨⟨(-3),3⟩,⟨(-3),3⟩⟩,⟨⟨(-4),4⟩,⟨(-4),4⟩⟩,⟨⟨(-4),4⟩,⟨(-4),4⟩⟩,⟨⟨(-3),3⟩,⟨(-3),3⟩⟩,⟨⟨(-1),3⟩,⟨(-3),2⟩⟩,⟨⟨0,3⟩,⟨0,3⟩⟩,⟨⟨(-12325932838736401844278),(-12325932838736401506904)⟩,⟨4674042778858330868088,4674042778858331205212⟩⟩]
lemma atomKernel97_0_eq (j : Fin 7) : atomKernel97_0 j = kernel0Box (atomPoints j) 97 := by
  fin_cases j <;> decide +kernel
lemma atomKernel97_0_contains (j : Fin 7) : (atomKernel97_0 j).Contains
    (complexTransformedFactor 97 1 0 ((j.val:ℝ)/6)) := by
  rw [atomKernel97_0_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=97) (by decide)
  have h0 := transformed_factor_zero_contains hh
  simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using h0
noncomputable def atomKernel97_1 : Fin 7 → CBox := ![⟨⟨(-28),28⟩,⟨(-28),28⟩⟩,⟨⟨(-46),46⟩,⟨(-46),46⟩⟩,⟨⟨(-41),41⟩,⟨(-41),41⟩⟩,⟨⟨(-24),24⟩,⟨(-24),24⟩⟩,⟨⟨(-19),11⟩,⟨(-17),10⟩⟩,⟨⟨(-3),13⟩,⟨(-15),0⟩⟩,⟨⟨19192571930432366632996,19192571930432367913771⟩,⟨43631603741460833699467,43631603741460834981181⟩⟩]
lemma atomKernel97_1_eq (j : Fin 7) : atomKernel97_1 j = (kernel0Box (atomPoints j) 97).mul (piI.mul (atomPoints j).z) := by
  fin_cases j <;> decide +kernel
lemma atomKernel97_1_contains (j : Fin 7) : (atomKernel97_1 j).Contains
    (complexTransformedFactor 97 1 1 ((j.val:ℝ)/6)) := by
  rw [atomKernel97_1_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=97) (by decide)
  have h0 := transformed_factor_zero_contains hh
  rw [transformed_factor_step]
  have hzz : complexZ ((j.val:ℂ)/6) = z ((j.val:ℝ)/6) := by
    simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat] using
      complexZ_ofReal ((j.val:ℝ)/6)
  have hz := (atomPoints_contains j).2.2.1
  rw [pointZ_eq] at hz
  simpa only [Nat.zero_add,Nat.cast_one,div_one,hzz,complexZ_ofReal,Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using
    CBox.contains_mul h0 (CBox.contains_mul piI_contains hz)
noncomputable def atomKernel99_0 : Fin 7 → CBox := ![⟨⟨(-3),3⟩,⟨(-3),3⟩⟩,⟨⟨(-4),4⟩,⟨(-4),4⟩⟩,⟨⟨(-4),4⟩,⟨(-4),4⟩⟩,⟨⟨(-3),3⟩,⟨(-3),3⟩⟩,⟨⟨(-3),1⟩,⟨(-2),3⟩⟩,⟨⟨(-1),2⟩,⟨(-2),0⟩⟩,⟨⟨(-2410742817318172851508),(-2410742817318172628096)⟩,⟨8728359067203883702675,8728359067203883926122⟩⟩]
lemma atomKernel99_0_eq (j : Fin 7) : atomKernel99_0 j = kernel0Box (atomPoints j) 99 := by
  fin_cases j <;> decide +kernel
lemma atomKernel99_0_contains (j : Fin 7) : (atomKernel99_0 j).Contains
    (complexTransformedFactor 99 1 0 ((j.val:ℝ)/6)) := by
  rw [atomKernel99_0_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=99) (by decide)
  have h0 := transformed_factor_zero_contains hh
  simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using h0
noncomputable def atomKernel99_1 : Fin 7 → CBox := ![⟨⟨(-28),28⟩,⟨(-28),28⟩⟩,⟨⟨(-46),46⟩,⟨(-46),46⟩⟩,⟨⟨(-41),41⟩,⟨(-41),41⟩⟩,⟨⟨(-24),24⟩,⟨(-24),24⟩⟩,⟨⟨(-11),19⟩,⟨(-10),17⟩⟩,⟨⟨(-10),1⟩,⟨(-9),6⟩⟩,⟨⟨31971005130459540601775,31971005130459541450702⟩,⟨7066301828693344635646,7066301828693345484384⟩⟩]
lemma atomKernel99_1_eq (j : Fin 7) : atomKernel99_1 j = (kernel0Box (atomPoints j) 99).mul (piI.mul (atomPoints j).z) := by
  fin_cases j <;> decide +kernel
lemma atomKernel99_1_contains (j : Fin 7) : (atomKernel99_1 j).Contains
    (complexTransformedFactor 99 1 1 ((j.val:ℝ)/6)) := by
  rw [atomKernel99_1_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=99) (by decide)
  have h0 := transformed_factor_zero_contains hh
  rw [transformed_factor_step]
  have hzz : complexZ ((j.val:ℂ)/6) = z ((j.val:ℝ)/6) := by
    simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat] using
      complexZ_ofReal ((j.val:ℝ)/6)
  have hz := (atomPoints_contains j).2.2.1
  rw [pointZ_eq] at hz
  simpa only [Nat.zero_add,Nat.cast_one,div_one,hzz,complexZ_ofReal,Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using
    CBox.contains_mul h0 (CBox.contains_mul piI_contains hz)
noncomputable def atomKernel100_0 : Fin 7 → CBox := ![⟨⟨(-3),3⟩,⟨(-3),3⟩⟩,⟨⟨(-4),4⟩,⟨(-4),4⟩⟩,⟨⟨(-4),4⟩,⟨(-4),4⟩⟩,⟨⟨(-3),3⟩,⟨(-3),3⟩⟩,⟨⟨(-3),1⟩,⟨(-2),3⟩⟩,⟨⟨0,2⟩,⟨(-1),2⟩⟩,⟨⟨(-1490670967802415506034),(-1490670967802415341050)⟩,⟨(-7355407834301021603761),(-7355407834301021438660)⟩⟩]
lemma atomKernel100_0_eq (j : Fin 7) : atomKernel100_0 j = kernel0Box (atomPoints j) 100 := by
  fin_cases j <;> decide +kernel
lemma atomKernel100_0_contains (j : Fin 7) : (atomKernel100_0 j).Contains
    (complexTransformedFactor 100 1 0 ((j.val:ℝ)/6)) := by
  rw [atomKernel100_0_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=100) (by decide)
  have h0 := transformed_factor_zero_contains hh
  simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using h0
noncomputable def atomKernel100_1 : Fin 7 → CBox := ![⟨⟨(-28),28⟩,⟨(-28),28⟩⟩,⟨⟨(-46),46⟩,⟨(-46),46⟩⟩,⟨⟨(-41),41⟩,⟨(-41),41⟩⟩,⟨⟨(-24),24⟩,⟨(-24),24⟩⟩,⟨⟨(-11),19⟩,⟨(-10),17⟩⟩,⟨⟨(-6),9⟩,⟨(-10),1⟩⟩,⟨⟨(-26280660926903198384712),(-26280660926903197757462)⟩,⟨6764001278873901214272,6764001278873901841058⟩⟩]
lemma atomKernel100_1_eq (j : Fin 7) : atomKernel100_1 j = (kernel0Box (atomPoints j) 100).mul (piI.mul (atomPoints j).z) := by
  fin_cases j <;> decide +kernel
lemma atomKernel100_1_contains (j : Fin 7) : (atomKernel100_1 j).Contains
    (complexTransformedFactor 100 1 1 ((j.val:ℝ)/6)) := by
  rw [atomKernel100_1_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=100) (by decide)
  have h0 := transformed_factor_zero_contains hh
  rw [transformed_factor_step]
  have hzz : complexZ ((j.val:ℂ)/6) = z ((j.val:ℝ)/6) := by
    simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat] using
      complexZ_ofReal ((j.val:ℝ)/6)
  have hz := (atomPoints_contains j).2.2.1
  rw [pointZ_eq] at hz
  simpa only [Nat.zero_add,Nat.cast_one,div_one,hzz,complexZ_ofReal,Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using
    CBox.contains_mul h0 (CBox.contains_mul piI_contains hz)
end SharpPlanar.CachedData

end OAI
