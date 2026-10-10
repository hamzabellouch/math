import OAI.Analysis.PlanarPacking.Certificate.Powers10
import OAI.Analysis.PlanarPacking.Certificate.KernelValues10
import OAI.Analysis.PlanarPacking.HighRuleBridge
import OAI.Analysis.PlanarPacking.Certificate.MomentPowers30

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid Numerical
noncomputable def hk4_0_0 (j : Fin 6) (i k : Fin 16) : CBox := (power4 j i k).conj.mul (mpower0_0 j i k)
lemma hk4_0_0_contains (j : Fin 6) (i k : Fin 16) :
    (hk4_0_0 j i k).Contains (fullFactor false 4 0 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk4_0_0,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power4 j i k) (mpower0_0 j i k) (quadraturePoint j.val (16*i.val+k.val)) 4 0 (power4_contains j i k) (mpower0_0_contains j i k)
noncomputable def ha4_0_0 : Fin 7 → CBox := ![⟨⟨999999999999999999999999999953,1000000000000000000000000000063⟩,⟨(-63),63⟩⟩,⟨⟨(-500000000000000000006323737467),(-499999999999999999996397449121)⟩,⟨866025403784438646758211576414,866025403784438646767663687290⟩⟩,⟨⟨(-500000000000000000010429447776),(-499999999999999999984128179037)⟩,⟨(-866025403784438646778618417240),(-866025403784438646751970079893)⟩⟩,⟨⟨999999999999999999986933300153,1000000000000000000013066699851⟩,⟨(-8353466415),17779933287⟩⟩,⟨⟨(-500000000000000000041705784837),(-499999999999999999969178961544)⟩,⟨866025403784438646724444465820,866025403784438646796717564422⟩⟩,⟨⟨(-500000000000000000038695735702),(-499999999999999999947698331324)⟩,⟨(-866025403784438646813275480195),(-866025403784438646722026250364)⟩⟩,⟨⟨999999999999999999973787208873,1000000000000000000026212791143⟩,⟨(-16786324247),35639258023⟩⟩]
lemma ha4_0_0_eq (j : Fin 7) : ha4_0_0 j = ((atomPoints j).direct.powBin 7 4).conj := by fin_cases j <;> decide +kernel
lemma ha4_0_0_contains (j : Fin 7) : (ha4_0_0 j).Contains (fullFactor false 4 0 ((j.val:ℝ)/6)) := by
  rw [ha4_0_0_eq]
  simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @direct_factor_zero_full ((atomPoints j).direct.powBin 7 4) ((j.val:ℝ)/6) 4 (@direct_power_bin_contains (atomPoints j) ((j.val:ℝ)/6) (atomPoints_contains j) 4 (by norm_num))
noncomputable def hk4_0_1 (j : Fin 6) (i k : Fin 16) : CBox := (power4 j i k).conj.mul (mpower0_1 j i k)
lemma hk4_0_1_contains (j : Fin 6) (i k : Fin 16) :
    (hk4_0_1 j i k).Contains (fullFactor false 4 1 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk4_0_1,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power4 j i k) (mpower0_1 j i k) (quadraturePoint j.val (16*i.val+k.val)) 4 1 (power4_contains j i k) (mpower0_1_contains j i k)
noncomputable def ha4_0_1 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-453449841058554462651644650207),(-453449841058554462645252160848)⟩,⟨(-261799387799149436542477767863),(-261799387799149436536447042102)⟩⟩,⟨⟨906899682117108925283968241828,906899682117108925314761066791⟩,⟨(-523598775598298873089255025506),(-523598775598298873060045734620)⟩⟩,⟨⟨(-27928653898),13121594361⟩,⟨1570796326794896619209474875877,1570796326794896619255525124130⟩⟩,⟨⟨(-1813799364234217850667428898795),(-1813799364234217850510286972351)⟩,⟨(-1047197551196597746244015058172),(-1047197551196597746088781901339)⟩⟩,⟨⟨2267249205292772313131527842182,2267249205292772313377634645620⟩,⟨(-1308996938995747182797138532507),(-1308996938995747182554741218263)⟩⟩,⟨⟨(-111964031185),52735792936⟩,⟨3141592653589793238377650087965,3141592653589793238552349912085⟩⟩]
lemma ha4_0_1_eq (j : Fin 7) : ha4_0_1 j = ((ha4_0_0 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 1 := by fin_cases j <;> decide +kernel
lemma ha4_0_1_contains (j : Fin 7) : (ha4_0_1 j).Contains (fullFactor false 4 1 ((j.val:ℝ)/6)) := by
  rw [ha4_0_1_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha4_0_0 j) false 4 0 j (ha4_0_0_contains j)
noncomputable def hk4_0_2 (j : Fin 6) (i k : Fin 16) : CBox := (power4 j i k).conj.mul (mpower0_2 j i k)
lemma hk4_0_2_contains (j : Fin 6) (i k : Fin 16) :
    (hk4_0_2 j i k).Contains (fullFactor false 4 2 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk4_0_2,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power4 j i k) (mpower0_2 j i k) (quadraturePoint j.val (16*i.val+k.val)) 4 2 (power4_contains j i k) (mpower0_2_contains j i k)
noncomputable def ha4_0_2 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨68538919452009434852408129366,68538919452009434854205135836⟩,⟨(-118712890786751174409033445074),(-118712890786751174406982020404)⟩⟩,⟨⟨274155677808037739402905137355,274155677808037739419071750927⟩,⟨474851563147004697624505798204,474851563147004697642140383124⟩⟩,⟨⟨(-1233700550136169827376209643041),(-1233700550136169827336114871821)⟩,⟨(-21935113478),10305676112⟩⟩,⟨⟨1096622711232150957578833246587,1096622711232150957744883686794⟩,⟨(-1899406252588018790608257404198),(-1899406252588018790437652765749)⟩⟩,⟨⟨1713472986300235871143313988573,1713472986300235871466065484855⟩,⟨2967822269668779360050545352772,2967822269668779360382145276832⟩⟩,⟨⟨(-4934802200544679309569711932398),(-4934802200544679309279586127110)⟩,⟨(-175872688919),82837189835⟩⟩]
lemma ha4_0_2_eq (j : Fin 7) : ha4_0_2 j = ((ha4_0_1 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 2 := by fin_cases j <;> decide +kernel
lemma ha4_0_2_contains (j : Fin 7) : (ha4_0_2 j).Contains (fullFactor false 4 2 ((j.val:ℝ)/6)) := by
  rw [ha4_0_2_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha4_0_1 j) false 4 1 j (ha4_0_1_contains j)
noncomputable def hk4_0_3 (j : Fin 6) (i k : Fin 16) : CBox := (power4 j i k).conj.mul (mpower0_3 j i k)
lemma hk4_0_3_contains (j : Fin 6) (i k : Fin 16) :
    (hk4_0_3 j i k).Contains (fullFactor false 4 3 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk4_0_3,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power4 j i k) (mpower0_3 j i k) (quadraturePoint j.val (16*i.val+k.val)) 4 3 (power4_contains j i k) (mpower0_3_contains j i k)
noncomputable def ha4_0_3 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨20719308087892496642231256645,20719308087892496642655249401⟩,⟨11962298101967523215730958428,11962298101967523216082672402⟩⟩,⟨⟨(-165754464703139973143338695125),(-165754464703139973136655450894)⟩,⟨95698384815740185723499368767,95698384815740185729447198903⟩⟩,⟨⟨(-5396039394),11485198560⟩,⟨(-645964097506246253668735113923),(-645964097506246253645685373220)⟩⟩,⟨⟨1326035717625119785051097098231,1326035717625119785174422507423⟩,⟨765587078525921485765105094650,765587078525921485883467110251⟩⟩,⟨⟨(-2589913510986562080468311640916),(-2589913510986562080170692166451)⟩,⟨1495287262745940401820731462464,1495287262745940402107144923445⟩⟩,⟨⟨(-86746902344),184173449159⟩,⟨(-5167712780049970029417816135356),(-5167712780049970029097547761850)⟩⟩]
lemma ha4_0_3_eq (j : Fin 7) : ha4_0_3 j = ((ha4_0_2 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 3 := by fin_cases j <;> decide +kernel
lemma ha4_0_3_contains (j : Fin 7) : (ha4_0_3 j).Contains (fullFactor false 4 3 ((j.val:ℝ)/6)) := by
  rw [ha4_0_3_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha4_0_2 j) false 4 2 j (ha4_0_2_contains j)
noncomputable def hk4_0_4 (j : Fin 6) (i k : Fin 16) : CBox := (power4 j i k).conj.mul (mpower0_4 j i k)
lemma hk4_0_4_contains (j : Fin 6) (i k : Fin 16) :
    (hk4_0_4 j i k).Contains (fullFactor false 4 4 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk4_0_4,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power4 j i k) (mpower0_4 j i k) (quadraturePoint j.val (16*i.val+k.val)) 4 4 (power4_contains j i k) (mpower0_4_contains j i k)
noncomputable def ha4_0_4 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1565861159883012429889800619),(-1565861159883012429838777076)⟩,⟨2712151086516110563369561304,2712151086516110563433694872⟩⟩,⟨⟨(-25053778558128198878442537017),(-25053778558128198876805650073)⟩,⟨(-43394417384257769015488032703),(-43394417384257769013600234733)⟩⟩,⟨⟨253669507901048013632394977709,253669507901048013642254044839⟩,⟨(-2119019715),4510226928⟩⟩,⟨⟨(-400860456930051182080155485789),(-400860456930051182016905300877)⟩,⟨694310678148124304195535895276,694310678148124304262318988061⟩⟩,⟨⟨(-978663224926882768744487955190),(-978663224926882768553915601535)⟩,⟨(-1695094429072569102235336463441),(-1695094429072569102035149319760)⟩⟩,⟨⟨4058712126416768218064963443257,4058712126416768218329420917555⟩,⟨(-68130857782),144649488717⟩⟩]
lemma ha4_0_4_eq (j : Fin 7) : ha4_0_4 j = ((ha4_0_3 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 4 := by fin_cases j <;> decide +kernel
lemma ha4_0_4_contains (j : Fin 7) : (ha4_0_4 j).Contains (fullFactor false 4 4 ((j.val:ℝ)/6)) := by
  rw [ha4_0_4_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha4_0_3 j) false 4 3 j (ha4_0_3_contains j)
noncomputable def hk4_0_5 (j : Fin 6) (i k : Fin 16) : CBox := (power4 j i k).conj.mul (mpower0_5 j i k)
lemma hk4_0_5_contains (j : Fin 6) (i k : Fin 16) :
    (hk4_0_5 j i k).Contains (fullFactor false 4 5 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk4_0_5,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power4 j i k) (mpower0_5 j i k) (quadraturePoint j.val (16*i.val+k.val)) 4 5 (power4_contains j i k) (mpower0_5_contains j i k)
noncomputable def ha4_0_5 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-284015797627486289491841743),(-284015797627486289484221640)⟩,⟨(-163976597214335483791042253),(-163976597214335483785177125)⟩⟩,⟨⟨9088505524079561263429591088,9088505524079561263853900183⟩,⟨(-5247251110858735481356439463),(-5247251110858735480996908143)⟩⟩,⟨⟨(-1416929579),665709677⟩,⟨79692626246167045119128956995,79692626246167045122479943790⟩⟩,⟨⟨(-290832176770545960449402935121),(-290832176770545960420503151058)⟩,⟨(-167912035547479535413909409627),(-167912035547479535386880753515)⟩⟩,⟨⟨887549367585894654601107959292,887549367585894654708750859998⟩,⟨(-512426866294798386880183601903),(-512426866294798386778769045490)⟩⟩,⟨⟨(-90885954220),42807880459⟩,⟨2550164039877345443778601934605,2550164039877345443952882890548⟩⟩]
lemma ha4_0_5_eq (j : Fin 7) : ha4_0_5 j = ((ha4_0_4 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 5 := by fin_cases j <;> decide +kernel
lemma ha4_0_5_contains (j : Fin 7) : (ha4_0_5 j).Contains (fullFactor false 4 5 ((j.val:ℝ)/6)) := by
  rw [ha4_0_5_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha4_0_4 j) false 4 4 j (ha4_0_4_contains j)
noncomputable def hk4_0_6 (j : Fin 6) (i k : Fin 16) : CBox := (power4 j i k).conj.mul (mpower0_6 j i k)
lemma hk4_0_6_contains (j : Fin 6) (i k : Fin 16) :
    (hk4_0_6 j i k).Contains (fullFactor false 4 6 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk4_0_6,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power4 j i k) (mpower0_6 j i k) (quadraturePoint j.val (16*i.val+k.val)) 4 6 (power4_contains j i k) (mpower0_6_contains j i k)
noncomputable def ha4_0_6 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨14309657588033580845539084,14309657588033580846096463⟩,⟨(-24785053981387676527365456),(-24785053981387676526621582)⟩⟩,⟨⟨915818085634149174092028544,915818085634149174157693738⟩,⟨1586243454808811297692349160,1586243454808811297771454239⟩⟩,⟨⟨(-20863480763352960873617388127),(-20863480763352960872673691313)⟩,⟨(-370951297),174282386⟩⟩,⟨⟨58612357480585547140137409121,58612357480585547149758758882⟩,⟨(-101519581107763923059494738593),(-101519581107763923049083664029)⟩⟩,⟨⟨223588399813024700689771073789,223588399813024700734733225743⟩,⟨387266468459182445712280995989,387266468459182445760481779288⟩⟩,⟨⟨(-1335262768854589495929066326349),(-1335262768854589495833562757806)⟩,⟨(-47587774349),22414153795⟩⟩]
lemma ha4_0_6_eq (j : Fin 7) : ha4_0_6 j = ((ha4_0_5 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 6 := by fin_cases j <;> decide +kernel
lemma ha4_0_6_contains (j : Fin 7) : (ha4_0_6 j).Contains (fullFactor false 4 6 ((j.val:ℝ)/6)) := by
  rw [ha4_0_6_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha4_0_5 j) false 4 5 j (ha4_0_5_contains j)
noncomputable def hk4_0_7 (j : Fin 6) (i k : Fin 16) : CBox := (power4 j i k).conj.mul (mpower0_7 j i k)
lemma hk4_0_7_contains (j : Fin 6) (i k : Fin 16) :
    (hk4_0_7 j i k).Contains (fullFactor false 4 7 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk4_0_7,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power4 j i k) (mpower0_7 j i k) (quadraturePoint j.val (16*i.val+k.val)) 4 7 (power4_contains j i k) (mpower0_7_contains j i k)
noncomputable def ha4_0_7 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1853917702541761442234844,1853917702541761442296388⟩,⟨1070359884617898514088741,1070359884617898514133841⟩⟩,⟨⟨(-237301465925345464616939325),(-237301465925345464604349878)⟩,⟨137006065231091009799997012,137006065231091009810256607⟩⟩,⟨⟨(-39108876),83241277⟩,⟨(-4681754135318688100823381326),(-4681754135318688100596713769)⟩⟩,⟨⟨30374587638444219468391363401,30374587638444219471603034943⟩,⟨17536776349579649253875295459,17536776349579649256809817870⟩⟩,⟨⟨(-144837320511075112687033557292),(-144837320511075112668545474982)⟩,⟨83621865985773321405038325520,83621865985773321422120307696⟩⟩,⟨⟨(-10059448700),21357343186⟩,⟨(-599264529320792076913270795905),(-599264529320792076868501376331)⟩⟩]
lemma ha4_0_7_eq (j : Fin 7) : ha4_0_7 j = ((ha4_0_6 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 7 := by fin_cases j <;> decide +kernel
lemma ha4_0_7_contains (j : Fin 7) : (ha4_0_7 j).Contains (fullFactor false 4 7 ((j.val:ℝ)/6)) := by
  rw [ha4_0_7_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha4_0_6 j) false 4 6 j (ha4_0_6_contains j)
noncomputable def hk4_0_8 (j : Fin 6) (i k : Fin 16) : CBox := (power4 j i k).conj.mul (mpower0_8 j i k)
lemma hk4_0_8_contains (j : Fin 6) (i k : Fin 16) :
    (hk4_0_8 j i k).Contains (fullFactor false 4 8 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk4_0_8,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power4 j i k) (mpower0_8 j i k) (quadraturePoint j.val (16*i.val+k.val)) 4 8 (power4_contains j i k) (mpower0_8_contains j i k)
noncomputable def ha4_0_8 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-70054890629433514728743),(-70054890629433514725568)⟩,⟨121338629888859693713002,121338629888859693717417⟩⟩,⟨⟨(-17934052001134979770705430),(-17934052001134979769305366)⟩,⟨(-31062689251548081592051496),(-31062689251548081590304665)⟩⟩,⟨⟨919260274839426580223516688,919260274839426580270948856⟩,⟨(-7679010),16344387⟩⟩,⟨⟨(-4591117312290554821587776684),(-4591117312290554820804906532)⟩,⟨7952048448396308886865247732,7952048448396308887731373533⟩⟩,⟨⟨(-27365191652122466692686901722),(-27365191652122466687009730016)⟩,⟨(-47397902300335817860862089393),(-47397902300335817854661006395)⟩⟩,⟨⟨235330630358893204534126594278,235330630358893204552456584896⟩,⟨(-3950336267),8387009057⟩⟩]
lemma ha4_0_8_eq (j : Fin 7) : ha4_0_8 j = ((ha4_0_7 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 8 := by fin_cases j <;> decide +kernel
lemma ha4_0_8_contains (j : Fin 7) : (ha4_0_8 j).Contains (fullFactor false 4 8 ((j.val:ℝ)/6)) := by
  rw [ha4_0_8_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha4_0_7 j) false 4 7 j (ha4_0_7_contains j)
noncomputable def hk4_0_9 (j : Fin 6) (i k : Fin 16) : CBox := (power4 j i k).conj.mul (mpower0_9 j i k)
lemma hk4_0_9_contains (j : Fin 6) (i k : Fin 16) :
    (hk4_0_9 j i k).Contains (fullFactor false 4 9 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk4_0_9,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power4 j i k) (mpower0_9 j i k) (quadraturePoint j.val (16*i.val+k.val)) 4 9 (power4_contains j i k) (mpower0_9_contains j i k)
noncomputable def ha4_0_9 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-7059195338064676366744),(-7059195338064676366463)⟩,⟨(-4075628328693792152571),(-4075628328693792152372)⟩⟩,⟨⟨3614308013089114299603439,3614308013089114299818198⟩,⟨(-2086721704291221582132985),(-2086721704291221581963437)⟩⟩,⟨⟨(-2852634),1340241⟩,⟨160441184787359821869349454,160441184787359821878138630⟩⟩,⟨⟨(-1850525702701626521545591306),(-1850525702701626521338144273)⟩,⟨(-1068401512597105450118919533),(-1068401512597105449933336547)⟩⟩,⟨⟨13787490894657571027673609727,13787490894657571029521318599⟩,⟨(-7960211579480062798503694312),(-7960211579480062796826933862)⟩⟩,⟨⟨(-2927618449),1378927489⟩,⟨82145886611128228796027023502,82145886611128228802686875744⟩⟩]
lemma ha4_0_9_eq (j : Fin 7) : ha4_0_9 j = ((ha4_0_8 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 9 := by fin_cases j <;> decide +kernel
lemma ha4_0_9_contains (j : Fin 7) : (ha4_0_9 j).Contains (fullFactor false 4 9 ((j.val:ℝ)/6)) := by
  rw [ha4_0_9_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha4_0_8 j) false 4 8 j (ha4_0_8_contains j)
noncomputable def hk4_0_10 (j : Fin 6) (i k : Fin 16) : CBox := (power4 j i k).conj.mul (mpower0_10 j i k)
lemma hk4_0_10_contains (j : Fin 6) (i k : Fin 16) :
    (hk4_0_10 j i k).Contains (fullFactor false 4 10 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk4_0_10,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power4 j i k) (mpower0_10 j i k) (quadraturePoint j.val (16*i.val+k.val)) 4 10 (power4_contains j i k) (mpower0_10_contains j i k)
noncomputable def ha4_0_10 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨213399400269781075722,213399400269781075734⟩,⟨(-369618603571988403201),(-369618603571988403184)⟩⟩,⟨⟨218520985876255821534335,218520985876255821552786⟩,⟨378489450057716124858105,378489450057716124881800⟩⟩,⟨⟨(-25202042373060605481972482),(-25202042373060605480511660)⟩,⟨(-448091),210525⟩⟩,⟨⟨223765489537285961244469249,223765489537285961284049927⟩,⟨(-387573196859101311887062706),(-387573196859101311842381416)⟩⟩,⟨⟨2083978518259580817398205421,2083978518259580817843813791⟩,⟨3609556675507699249696910294,3609556675507699250192128922⟩⟩,⟨⟨(-25806891390014060013879080711),(-25806891390014060011704680535)⟩,⟨(-919738462),433202847⟩⟩]
lemma ha4_0_10_eq (j : Fin 7) : ha4_0_10 j = ((ha4_0_9 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 10 := by fin_cases j <;> decide +kernel
lemma ha4_0_10_contains (j : Fin 7) : (ha4_0_10 j).Contains (fullFactor false 4 10 ((j.val:ℝ)/6)) := by
  rw [ha4_0_10_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha4_0_9 j) false 4 9 j (ha4_0_9_contains j)
noncomputable def hk4_0_11 (j : Fin 6) (i k : Fin 16) : CBox := (power4 j i k).conj.mul (mpower0_11 j i k)
lemma hk4_0_11_contains (j : Fin 6) (i k : Fin 16) :
    (hk4_0_11 j i k).Contains (fullFactor false 4 11 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk4_0_11,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power4 j i k) (mpower0_11 j i k) (quadraturePoint j.val (16*i.val+k.val)) 4 11 (power4_contains j i k) (mpower0_11_contains j i k)
noncomputable def ha4_0_11 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨17593804388058740564,17593804388058740566⟩,⟨10157787699515332860,10157787699515332861⟩⟩,⟨⟨(-36032111386744300677715),(-36032111386744300675343)⟩,⟨20803149208607401697338,20803149208607401699162⟩⟩,⟨⟨(-30063),63988⟩,⟨(-3598843235212085340598266),(-3598843235212085340378205)⟩⟩,⟨⟨73793764120052327780758291,73793764120052327789500483⟩,⟨42604849579227958674875785,42604849579227958682547545⟩⟩,⟨⟨(-859072479885680691698931359),(-859072479885680691578335087)⟩,⟨495985727515397112269949025,495985727515397112377582342⟩⟩,⟨⟨(-123722444),262676691⟩,⟨(-7370430945714350777642140934),(-7370430945714350776997672884)⟩⟩]
lemma ha4_0_11_eq (j : Fin 7) : ha4_0_11 j = ((ha4_0_10 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 11 := by fin_cases j <;> decide +kernel
lemma ha4_0_11_contains (j : Fin 7) : (ha4_0_11 j).Contains (fullFactor false 4 11 ((j.val:ℝ)/6)) := by
  rw [ha4_0_11_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha4_0_10 j) false 4 10 j (ha4_0_10_contains j)
noncomputable def hk4_0_12 (j : Fin 6) (i k : Fin 16) : CBox := (power4 j i k).conj.mul (mpower0_12 j i k)
lemma hk4_0_12_contains (j : Fin 6) (i k : Fin 16) :
    (hk4_0_12 j i k).Contains (fullFactor false 4 12 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk4_0_12,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power4 j i k) (mpower0_12 j i k) (quadraturePoint j.val (16*i.val+k.val)) 4 12 (power4_contains j i k) (mpower0_12_contains j i k)
noncomputable def ha4_0_12 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-443217100187807443),(-443217100187807442)⟩,⟨767674536308627877,767674536308627878⟩⟩,⟨⟨(-1815417242369259285601),(-1815417242369259285435)⟩,⟨(-3144394900720139785068),(-3144394900720139784850)⟩⟩,⟨⟨471087477881817150356115,471087477881817150386421⟩,⟨(-3936),8377⟩⟩,⟨⟨(-7435949024744486034285501),(-7435949024744486032922855)⟩,⟨12879441513349692558338725,12879441513349692559905523⟩⟩,⟨⟨(-108207299850538926464516188),(-108207299850538926440689805)⟩,⟨(-187420541090973602842885445),(-187420541090973602815978840)⟩⟩,⟨⟨1929574309403923047833283161,1929574309403923048008146528⟩,⟨(-32390461),68768597⟩⟩]
lemma ha4_0_12_eq (j : Fin 7) : ha4_0_12 j = ((ha4_0_11 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 12 := by fin_cases j <;> decide +kernel
lemma ha4_0_12_contains (j : Fin 7) : (ha4_0_12 j).Contains (fullFactor false 4 12 ((j.val:ℝ)/6)) := by
  rw [ha4_0_12_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha4_0_11 j) false 4 11 j (ha4_0_11_contains j)
noncomputable def hk4_0_13 (j : Fin 6) (i k : Fin 16) : CBox := (power4 j i k).conj.mul (mpower0_13 j i k)
lemma hk4_0_13_contains (j : Fin 6) (i k : Fin 16) :
    (hk4_0_13 j i k).Contains (fullFactor false 4 13 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk4_0_13,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power4 j i k) (mpower0_13 j i k) (quadraturePoint j.val (16*i.val+k.val)) 4 13 (power4_contains j i k) (mpower0_13_contains j i k)
noncomputable def ha4_0_13 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-30919495943783800),(-30919495943783799)⟩,⟨(-17851379306351119),(-17851379306351118)⟩⟩,⟨⟨253292510771476882274,253292510771476882293⟩,⟨(-146238499277628361520),(-146238499277628361505)⟩⟩,⟨⟨(-1013),476⟩,⟨56921729219679268116386,56921729219679268120230⟩⟩,⟨⟨(-2074972248239938619787253),(-2074972248239938619528225)⟩,⟨(-1197985786082331537639709),(-1197985786082331537416363)⟩⟩,⟨⟨37743525322001707891512183,37743525322001707897050889⟩,⟨(-21791234504823142517716348),(-21791234504823142512848728)⟩⟩,⟨⟨(-16618687),7827511⟩,⟨466302805767612564403305211,466302805767612564447047152⟩⟩]
lemma ha4_0_13_eq (j : Fin 7) : ha4_0_13 j = ((ha4_0_12 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 13 := by fin_cases j <;> decide +kernel
lemma ha4_0_13_contains (j : Fin 7) : (ha4_0_13 j).Contains (fullFactor false 4 13 ((j.val:ℝ)/6)) := by
  rw [ha4_0_13_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha4_0_12 j) false 4 12 j (ha4_0_12_contains j)
noncomputable def hk4_0_14 (j : Fin 6) (i k : Fin 16) : CBox := (power4 j i k).conj.mul (mpower0_14 j i k)
lemma hk4_0_14_contains (j : Fin 6) (i k : Fin 16) :
    (hk4_0_14 j i k).Contains (fullFactor false 4 14 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk4_0_14,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power4 j i k) (mpower0_14 j i k) (quadraturePoint j.val (16*i.val+k.val)) 4 14 (power4_contains j i k) (mpower0_14_contains j i k)
noncomputable def ha4_0_14 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨667640024824732,667640024824733⟩,⟨(-1156386444162984),(-1156386444162983)⟩⟩,⟨⟨10938614166728417758,10938614166728417760⟩,⟨18946235501166317750,18946235501166317752⟩⟩,⟨⟨(-6386603083791852241383),(-6386603083791852240931)⟩,⟨(-114),54⟩⟩,⟨⟨179218254507678396545713,179218254507678396579697⟩,⟨(-310415122451108950053305),(-310415122451108950013566)⟩⟩,⟨⟨4074951323393142878058241,4074951323393142878981456⟩,⟨7058022730486958380713523,7058022730486958381771726⟩⟩,⟨⟨(-104638104924845707124189997),(-104638104924845707114041254)⟩,⟨(-3729225),1756490⟩⟩]
lemma ha4_0_14_eq (j : Fin 7) : ha4_0_14 j = ((ha4_0_13 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 14 := by fin_cases j <;> decide +kernel
lemma ha4_0_14_contains (j : Fin 7) : (ha4_0_14 j).Contains (fullFactor false 4 14 ((j.val:ℝ)/6)) := by
  rw [ha4_0_14_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha4_0_13 j) false 4 13 j (ha4_0_13_contains j)
noncomputable def hk4_0_15 (j : Fin 6) (i k : Fin 16) : CBox := (power4 j i k).conj.mul (mpower0_15 j i k)
lemma hk4_0_15_contains (j : Fin 6) (i k : Fin 16) :
    (hk4_0_15 j i k).Contains (fullFactor false 4 15 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk4_0_15,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power4 j i k) (mpower0_15 j i k) (quadraturePoint j.val (16*i.val+k.val)) 4 15 (power4_contains j i k) (mpower0_15_contains j i k)
noncomputable def ha4_0_15 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨40365501752147,40365501752148⟩,⟨23305033302576,23305033302577⟩⟩,⟨⟨(-1322696761414360853),(-1322696761414360852)⟩,⟨763659331258827443,763659331258827444⟩⟩,⟨⟨(-6),12⟩,⟨(-668803510981146723281),(-668803510981146723230)⟩⟩,⟨⟨43342127478025776417891,43342127478025776423579⟩,⟨25023588966689257661869,25023588966689257666695⟩⟩,⟨⟨(-1231857353275977869327756),(-1231857353275977869139143)⟩,⟨711213174517105746326552,711213174517105746489949⟩⟩,⟨⟨(-367879),781048⟩,⟨(-21915353447830215828728898),(-21915353447830215826533590)⟩⟩]
lemma ha4_0_15_eq (j : Fin 7) : ha4_0_15 j = ((ha4_0_14 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 15 := by fin_cases j <;> decide +kernel
lemma ha4_0_15_contains (j : Fin 7) : (ha4_0_15 j).Contains (fullFactor false 4 15 ((j.val:ℝ)/6)) := by
  rw [ha4_0_15_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha4_0_14 j) false 4 14 j (ha4_0_14_contains j)
noncomputable def hk4_0_16 (j : Fin 6) (i k : Fin 16) : CBox := (power4 j i k).conj.mul (mpower0_16 j i k)
lemma hk4_0_16_contains (j : Fin 6) (i k : Fin 16) :
    (hk4_0_16 j i k).Contains (fullFactor false 4 16 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk4_0_16,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power4 j i k) (mpower0_16 j i k) (quadraturePoint j.val (16*i.val+k.val)) 4 16 (power4_contains j i k) (mpower0_16_contains j i k)
noncomputable def ha4_0_16 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-762655431407),(-762655431406)⟩,⟨1320957955864,1320957955865⟩⟩,⟨⟨(-49981386352667222),(-49981386352667221)⟩,⟨(-86570300595549324),(-86570300595549323)⟩⟩,⟨⟨65659631149794723620,65659631149794723626⟩,⟨(-1),2⟩⟩,⟨⟨(-3275580136008399049772),(-3275580136008399049129)⟩,⟨5673471219829920494419,5673471219829920495183⟩⟩,⟨⟨(-116371983552042445699890),(-116371983552042445672783)⟩,⟨(-201562188089707223614188),(-201562188089707223582683)⟩⟩,⟨⟨4303069587032947007127097,4303069587032947007571843⟩,⟨(-72233),153359⟩⟩]
lemma ha4_0_16_eq (j : Fin 7) : ha4_0_16 j = ((ha4_0_15 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 16 := by fin_cases j <;> decide +kernel
lemma ha4_0_16_contains (j : Fin 7) : (ha4_0_16 j).Contains (fullFactor false 4 16 ((j.val:ℝ)/6)) := by
  rw [ha4_0_16_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha4_0_15 j) false 4 15 j (ha4_0_15_contains j)
noncomputable def hk4_0_17 (j : Fin 6) (i k : Fin 16) : CBox := (power4 j i k).conj.mul (mpower0_17 j i k)
lemma hk4_0_17_contains (j : Fin 6) (i k : Fin 16) :
    (hk4_0_17 j i k).Contains (fullFactor false 4 17 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk4_0_17,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power4 j i k) (mpower0_17 j i k) (quadraturePoint j.val (16*i.val+k.val)) 4 17 (power4_contains j i k) (mpower0_17_contains j i k)
noncomputable def ha4_0_17 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-40685409901),(-40685409900)⟩,⟨(-23489732359),(-23489732358)⟩⟩,⟨⟨5332718046471330,5332718046471331⟩,⟨(-3078846199642598),(-3078846199642597)⟩⟩,⟨⟨(-1),1⟩,⟨6066935731106195666,6066935731106195668⟩⟩,⟨⟨(-698970019787090239269),(-698970019787090239172)⟩,⟨(-403550529079554596759),(-403550529079554596677)⟩⟩,⟨⟨31040504379613153636906,31040504379613153641858⟩,⟨(-17921243559351411745160),(-17921243559351411740928)⟩⟩,⟨⟨(-28341),13349⟩,⟨795205400147551278446101,795205400147551278530822⟩⟩]
lemma ha4_0_17_eq (j : Fin 7) : ha4_0_17 j = ((ha4_0_16 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 17 := by fin_cases j <;> decide +kernel
lemma ha4_0_17_contains (j : Fin 7) : (ha4_0_17 j).Contains (fullFactor false 4 17 ((j.val:ℝ)/6)) := by
  rw [ha4_0_17_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha4_0_16 j) false 4 16 j (ha4_0_16_contains j)
noncomputable def hk4_0_18 (j : Fin 6) (i k : Fin 16) : CBox := (power4 j i k).conj.mul (mpower0_18 j i k)
lemma hk4_0_18_contains (j : Fin 6) (i k : Fin 16) :
    (hk4_0_18 j i k).Contains (fullFactor false 4 18 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk4_0_18,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power4 j i k) (mpower0_18 j i k) (quadraturePoint j.val (16*i.val+k.val)) 4 18 (power4_contains j i k) (mpower0_18_contains j i k)
noncomputable def ha4_0_18 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨683288616,683288617⟩,⟨(-1183490601),(-1183490600)⟩⟩,⟨⟨179120011154259,179120011154260⟩,⟨310244959971482,310244959971483⟩⟩,⟨⟨(-529440020073462377),(-529440020073462376)⟩,⟨(-1),1⟩⟩,⟨⟨46955236204022331365,46955236204022331375⟩,⟨(-81328854786764263389),(-81328854786764263377)⟩⟩,⟨⟨2606539218020916335489,2606539218020916336114⟩,⟨4514658357533078057840,4514658357533078058575⟩⟩,⟨⟨(-138789524622137721154170),(-138789524622137721138940)⟩,⟨(-4947),2330⟩⟩]
lemma ha4_0_18_eq (j : Fin 7) : ha4_0_18 j = ((ha4_0_17 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 18 := by fin_cases j <;> decide +kernel
lemma ha4_0_18_contains (j : Fin 7) : (ha4_0_18 j).Contains (fullFactor false 4 18 ((j.val:ℝ)/6)) := by
  rw [ha4_0_18_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha4_0_17 j) false 4 17 j (ha4_0_17_contains j)
noncomputable def hk4_0_19 (j : Fin 6) (i k : Fin 16) : CBox := (power4 j i k).conj.mul (mpower0_19 j i k)
lemma hk4_0_19_contains (j : Fin 6) (i k : Fin 16) :
    (hk4_0_19 j i k).Contains (fullFactor false 4 19 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk4_0_19,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power4 j i k) (mpower0_19 j i k) (quadraturePoint j.val (16*i.val+k.val)) 4 19 (power4_contains j i k) (mpower0_19_contains j i k)
noncomputable def ha4_0_19 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨32614433,32614434⟩,⟨18829951,18829952⟩⟩,⟨⟨(-17099355913328),(-17099355913327)⟩,⟨9872317739528,9872317739529⟩⟩,⟨⟨(-1),1⟩,⟨(-43770654673137423),(-43770654673137422)⟩⟩,⟨⟨8964987113086656144,8964987113086656146⟩,⟨5175937723022106880,5175937723022106882⟩⟩,⟨⟨(-622070944276038605552),(-622070944276038605448)⟩,⟨359152827132815577476,359152827132815577564⟩⟩,⟨⟨(-386),818⟩,⟨(-22948428997269873111827),(-22948428997269873109235)⟩⟩]
lemma ha4_0_19_eq (j : Fin 7) : ha4_0_19 j = ((ha4_0_18 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 19 := by fin_cases j <;> decide +kernel
lemma ha4_0_19_contains (j : Fin 7) : (ha4_0_19 j).Contains (fullFactor false 4 19 ((j.val:ℝ)/6)) := by
  rw [ha4_0_19_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha4_0_18 j) false 4 18 j (ha4_0_18_contains j)
noncomputable def hk4_0_20 (j : Fin 6) (i k : Fin 16) : CBox := (power4 j i k).conj.mul (mpower0_20 j i k)
lemma hk4_0_20_contains (j : Fin 6) (i k : Fin 16) :
    (hk4_0_20 j i k).Contains (fullFactor false 4 20 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk4_0_20,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power4 j i k) (mpower0_20 j i k) (quadraturePoint j.val (16*i.val+k.val)) 4 20 (power4_contains j i k) (mpower0_20_contains j i k)
noncomputable def ha4_0_20 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-492967),(-492966)⟩,⟨853843,853844⟩⟩,⟨⟨(-516913348074),(-516913348073)⟩,⟨(-895320181974),(-895320181973)⟩⟩,⟨⟨3437739179098606,3437739179098608⟩,⟨(-1),1⟩⟩,⟨⟨(-542022930869484434),(-542022930869484433)⟩,⟨938811255133340262,938811255133340263⟩⟩,⟨⟨(-47012995134852432613),(-47012995134852432600)⟩,⟨(-81428896189552855164),(-81428896189552855149)⟩⟩,⟨⟨3604730797462500933704,3604730797462500934123⟩,⟨(-61),129⟩⟩]
lemma ha4_0_20_eq (j : Fin 7) : ha4_0_20 j = ((ha4_0_19 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 20 := by fin_cases j <;> decide +kernel
lemma ha4_0_20_contains (j : Fin 7) : (ha4_0_20 j).Contains (fullFactor false 4 20 ((j.val:ℝ)/6)) := by
  rw [ha4_0_20_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha4_0_19 j) false 4 19 j (ha4_0_19_contains j)
noncomputable def hk4_0_21 (j : Fin 6) (i k : Fin 16) : CBox := (power4 j i k).conj.mul (mpower0_21 j i k)
lemma hk4_0_21_contains (j : Fin 6) (i k : Fin 16) :
    (hk4_0_21 j i k).Contains (fullFactor false 4 21 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk4_0_21,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power4 j i k) (mpower0_21 j i k) (quadraturePoint j.val (16*i.val+k.val)) 4 21 (power4_contains j i k) (mpower0_21_contains j i k)
noncomputable def ha4_0_21 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-21290),(-21289)⟩,⟨(-12292),(-12291)⟩⟩,⟨⟨44646528671,44646528672⟩,⟨(-25776685347),(-25776685346)⟩⟩,⟨⟨(-1),1⟩,⟨257142289286047,257142289286048⟩⟩,⟨⟨(-93630556896327456),(-93630556896327455)⟩,⟨(-54057627228469228),(-54057627228469227)⟩⟩,⟨⟨10151445319802585614,10151445319802585617⟩,⟨(-5860939688051789413),(-5860939688051789410)⟩⟩,⟨⟨(-20),10⟩,⟨539266466260812848911,539266466260812848976⟩⟩]
lemma ha4_0_21_eq (j : Fin 7) : ha4_0_21 j = ((ha4_0_20 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 21 := by fin_cases j <;> decide +kernel
lemma ha4_0_21_contains (j : Fin 7) : (ha4_0_21 j).Contains (fullFactor false 4 21 ((j.val:ℝ)/6)) := by
  rw [ha4_0_21_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha4_0_20 j) false 4 20 j (ha4_0_20_contains j)
noncomputable def hk4_0_22 (j : Fin 6) (i k : Fin 16) : CBox := (power4 j i k).conj.mul (mpower0_22 j i k)
lemma hk4_0_22_contains (j : Fin 6) (i k : Fin 16) :
    (hk4_0_22 j i k).Contains (fullFactor false 4 22 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk4_0_22,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power4 j i k) (mpower0_22 j i k) (quadraturePoint j.val (16*i.val+k.val)) 4 22 (power4_contains j i k) (mpower0_22_contains j i k)
noncomputable def ha4_0_22 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨292,293⟩,⟨(-507),(-506)⟩⟩,⟨⟨1226967353,1226967354⟩,⟨2125169795,2125169796⟩⟩,⟨⟨(-18359916521553),(-18359916521552)⟩,⟨(-1),1⟩⟩,⟨⟨5146274077922863,5146274077922864⟩,⟨(-8913608172637076),(-8913608172637075)⟩⟩,⟨⟨697450191936225609,697450191936225610⟩,⟨1208019168182208037,1208019168182208038⟩⟩,⟨⟨(-77007071306013533804),(-77007071306013533794)⟩,⟨(-3),2⟩⟩]
lemma ha4_0_22_eq (j : Fin 7) : ha4_0_22 j = ((ha4_0_21 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 22 := by fin_cases j <;> decide +kernel
lemma ha4_0_22_contains (j : Fin 7) : (ha4_0_22 j).Contains (fullFactor false 4 22 ((j.val:ℝ)/6)) := by
  rw [ha4_0_22_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha4_0_21 j) false 4 21 j (ha4_0_21_contains j)
noncomputable def hk4_0_23 (j : Fin 6) (i k : Fin 16) : CBox := (power4 j i k).conj.mul (mpower0_23 j i k)
lemma hk4_0_23_contains (j : Fin 6) (i k : Fin 16) :
    (hk4_0_23 j i k).Contains (fullFactor false 4 23 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk4_0_23,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power4 j i k) (mpower0_23 j i k) (quadraturePoint j.val (16*i.val+k.val)) 4 23 (power4_contains j i k) (mpower0_23_contains j i k)
noncomputable def ha4_0_23 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨11,12⟩,⟨6,7⟩⟩,⟨⟨(-96759679),(-96759678)⟩,⟨55864226,55864227⟩⟩,⟨⟨(-1),1⟩,⟨(-1253899540536),(-1253899540535)⟩⟩,⟨⟨811679013105350,811679013105351⟩,⟨468623096711943,468623096711944⟩⟩,⟨⟨(-137503773339017308),(-137503773339017306)⟩,⟨79387840551870928,79387840551870929⟩⟩,⟨⟨(-1),1⟩,⟨(-10518471716932064456),(-10518471716932064454)⟩⟩]
lemma ha4_0_23_eq (j : Fin 7) : ha4_0_23 j = ((ha4_0_22 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 23 := by fin_cases j <;> decide +kernel
lemma ha4_0_23_contains (j : Fin 7) : (ha4_0_23 j).Contains (fullFactor false 4 23 ((j.val:ℝ)/6)) := by
  rw [ha4_0_23_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha4_0_22 j) false 4 22 j (ha4_0_22_contains j)
noncomputable def hk4_0_24 (j : Fin 6) (i k : Fin 16) : CBox := (power4 j i k).conj.mul (mpower0_24 j i k)
lemma hk4_0_24_contains (j : Fin 6) (i k : Fin 16) :
    (hk4_0_24 j i k).Contains (fullFactor false 4 24 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk4_0_24,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power4 j i k) (mpower0_24 j i k) (quadraturePoint j.val (16*i.val+k.val)) 4 24 (power4_contains j i k) (mpower0_24_contains j i k)
noncomputable def ha4_0_24 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),0⟩,⟨0,1⟩⟩,⟨⟨(-2437537),(-2437536)⟩,⟨(-4221938),(-4221937)⟩⟩,⟨⟨82067533018,82067533019⟩,⟨(-1),1⟩⟩,⟨⟨(-40895079942577),(-40895079942576)⟩,⟨70832356240132,70832356240133⟩⟩,⟨⟨(-8659870022990125),(-8659870022990124)⟩,⟨(-14999334866761558),(-14999334866761557)⟩⟩,⟨⟨1376864728037741370,1376864728037741371⟩,⟨(-1),1⟩⟩]
lemma ha4_0_24_eq (j : Fin 7) : ha4_0_24 j = ((ha4_0_23 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 24 := by fin_cases j <;> decide +kernel
lemma ha4_0_24_contains (j : Fin 7) : (ha4_0_24 j).Contains (fullFactor false 4 24 ((j.val:ℝ)/6)) := by
  rw [ha4_0_24_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha4_0_23 j) false 4 23 j (ha4_0_23_contains j)
noncomputable def hk4_0_25 (j : Fin 6) (i k : Fin 16) : CBox := (power4 j i k).conj.mul (mpower0_25 j i k)
lemma hk4_0_25_contains (j : Fin 6) (i k : Fin 16) :
    (hk4_0_25 j i k).Contains (fullFactor false 4 25 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk4_0_25,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power4 j i k) (mpower0_25 j i k) (quadraturePoint j.val (16*i.val+k.val)) 4 25 (power4_contains j i k) (mpower0_25_contains j i k)
noncomputable def ha4_0_25 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),0⟩,⟨(-1),0⟩⟩,⟨⟨176848,176849⟩,⟨(-102104),(-102103)⟩⟩,⟨⟨(-1),1⟩,⟨5156455176,5156455177⟩⟩,⟨⟨(-5934037600013),(-5934037600012)⟩,⟨(-3426018205749),(-3426018205748)⟩⟩,⟨⟨1570726674205044,1570726674205046⟩,⟨(-906859468175609),(-906859468175608)⟩⟩,⟨⟨(-1),1⟩,⟨173021924583611076,173021924583611077⟩⟩]
lemma ha4_0_25_eq (j : Fin 7) : ha4_0_25 j = ((ha4_0_24 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 25 := by fin_cases j <;> decide +kernel
lemma ha4_0_25_contains (j : Fin 7) : (ha4_0_25 j).Contains (fullFactor false 4 25 ((j.val:ℝ)/6)) := by
  rw [ha4_0_25_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha4_0_24 j) false 4 24 j (ha4_0_24_contains j)
noncomputable def hk4_0_26 (j : Fin 6) (i k : Fin 16) : CBox := (power4 j i k).conj.mul (mpower0_26 j i k)
lemma hk4_0_26_contains (j : Fin 6) (i k : Fin 16) :
    (hk4_0_26 j i k).Contains (fullFactor false 4 26 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk4_0_26,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power4 j i k) (mpower0_26 j i k) (quadraturePoint j.val (16*i.val+k.val)) 4 26 (power4_contains j i k) (mpower0_26_contains j i k)
noncomputable def ha4_0_26 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨0,1⟩,⟨(-1),0⟩⟩,⟨⟨4112,4113⟩,⟨7122,7123⟩⟩,⟨⟨(-311528495),(-311528494)⟩,⟨(-1),1⟩⟩,⟨⟨275978298108,275978298109⟩,⟨(-478008434111),(-478008434110)⟩⟩,⟨⟨91313559072398,91313559072399⟩,⟨158159723733336,158159723733337⟩⟩,⟨⟨(-20906323353147685),(-20906323353147684)⟩,⟨(-1),1⟩⟩]
lemma ha4_0_26_eq (j : Fin 7) : ha4_0_26 j = ((ha4_0_25 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 26 := by fin_cases j <;> decide +kernel
lemma ha4_0_26_contains (j : Fin 7) : (ha4_0_26 j).Contains (fullFactor false 4 26 ((j.val:ℝ)/6)) := by
  rw [ha4_0_26_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha4_0_25 j) false 4 25 j (ha4_0_25_contains j)
noncomputable def hk4_0_27 (j : Fin 6) (i k : Fin 16) : CBox := (power4 j i k).conj.mul (mpower0_27 j i k)
lemma hk4_0_27_contains (j : Fin 6) (i k : Fin 16) :
    (hk4_0_27 j i k).Contains (fullFactor false 4 27 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk4_0_27,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power4 j i k) (mpower0_27 j i k) (quadraturePoint j.val (16*i.val+k.val)) 4 27 (power4_contains j i k) (mpower0_27_contains j i k)
noncomputable def ha4_0_27 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨0,1⟩,⟨0,1⟩⟩,⟨⟨(-277),(-276)⟩,⟨159,160⟩⟩,⟨⟨(-1),1⟩,⟨(-18123994),(-18123993)⟩⟩,⟨⟨37079204566,37079204567⟩,⟨21407688737,21407688739⟩⟩,⟨⟨(-15335599573286),(-15335599573285)⟩,⟨8854012541820,8854012541821⟩⟩,⟨⟨(-1),1⟩,⟨(-2432561179993389),(-2432561179993388)⟩⟩]
lemma ha4_0_27_eq (j : Fin 7) : ha4_0_27 j = ((ha4_0_26 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 27 := by fin_cases j <;> decide +kernel
lemma ha4_0_27_contains (j : Fin 7) : (ha4_0_27 j).Contains (fullFactor false 4 27 ((j.val:ℝ)/6)) := by
  rw [ha4_0_27_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha4_0_26 j) false 4 26 j (ha4_0_26_contains j)
noncomputable def hk4_0_28 (j : Fin 6) (i k : Fin 16) : CBox := (power4 j i k).conj.mul (mpower0_28 j i k)
lemma hk4_0_28_contains (j : Fin 6) (i k : Fin 16) :
    (hk4_0_28 j i k).Contains (fullFactor false 4 28 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk4_0_28,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power4 j i k) (mpower0_28 j i k) (quadraturePoint j.val (16*i.val+k.val)) 4 28 (power4_contains j i k) (mpower0_28_contains j i k)
noncomputable def ha4_0_28 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),0⟩,⟨0,1⟩⟩,⟨⟨(-6),(-5)⟩,⟨(-11),(-10)⟩⟩,⟨⟨1016753,1016754⟩,⟨(-1),1⟩⟩,⟨⟨(-1601291374),(-1601291373)⟩,⟨2773518015,2773518016⟩⟩,⟨⟨(-827848236791),(-827848236790)⟩,⟨(-1433875207079),(-1433875207078)⟩⟩,⟨⟨272932726159819,272932726159820⟩,⟨(-1),1⟩⟩]
lemma ha4_0_28_eq (j : Fin 7) : ha4_0_28 j = ((ha4_0_27 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 28 := by fin_cases j <;> decide +kernel
lemma ha4_0_28_contains (j : Fin 7) : (ha4_0_28 j).Contains (fullFactor false 4 28 ((j.val:ℝ)/6)) := by
  rw [ha4_0_28_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha4_0_27 j) false 4 27 j (ha4_0_27_contains j)
noncomputable def hk4_0_29 (j : Fin 6) (i k : Fin 16) : CBox := (power4 j i k).conj.mul (mpower0_29 j i k)
lemma hk4_0_29_contains (j : Fin 6) (i k : Fin 16) :
    (hk4_0_29 j i k).Contains (fullFactor false 4 29 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk4_0_29,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power4 j i k) (mpower0_29 j i k) (quadraturePoint j.val (16*i.val+k.val)) 4 29 (power4_contains j i k) (mpower0_29_contains j i k)
noncomputable def ha4_0_29 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),0⟩,⟨(-1),0⟩⟩,⟨⟨0,1⟩,⟨(-1),0⟩⟩,⟨⟨(-1),1⟩,⟨55072,55073⟩⟩,⟨⟨(-200304916),(-200304915)⟩,⟨(-115646097),(-115646096)⟩⟩,⟨⟨129444017721,129444017722⟩,⟨(-74734538477),(-74734538476)⟩⟩,⟨⟨(-1),1⟩,⟨29567015428549,29567015428550⟩⟩]
lemma ha4_0_29_eq (j : Fin 7) : ha4_0_29 j = ((ha4_0_28 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 29 := by fin_cases j <;> decide +kernel
lemma ha4_0_29_contains (j : Fin 7) : (ha4_0_29 j).Contains (fullFactor false 4 29 ((j.val:ℝ)/6)) := by
  rw [ha4_0_29_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha4_0_28 j) false 4 28 j (ha4_0_28_contains j)
noncomputable def hk4_0_30 (j : Fin 6) (i k : Fin 16) : CBox := (power4 j i k).conj.mul (mpower0_30 j i k)
lemma hk4_0_30_contains (j : Fin 6) (i k : Fin 16) :
    (hk4_0_30 j i k).Contains (fullFactor false 4 30 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk4_0_30,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power4 j i k) (mpower0_30 j i k) (quadraturePoint j.val (16*i.val+k.val)) 4 30 (power4_contains j i k) (mpower0_30_contains j i k)
noncomputable def ha4_0_30 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨0,1⟩,⟨(-1),0⟩⟩,⟨⟨0,1⟩,⟨0,1⟩⟩,⟨⟨(-2884),(-2883)⟩,⟨(-1),1⟩⟩,⟨⟨8073620,8073621⟩,⟨(-13983922),(-13983921)⟩⟩,⟨⟨6521818806,6521818807⟩,⟨11296121531,11296121532⟩⟩,⟨⟨(-3096250615297),(-3096250615296)⟩,⟨(-1),1⟩⟩]
lemma ha4_0_30_eq (j : Fin 7) : ha4_0_30 j = ((ha4_0_29 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 30 := by fin_cases j <;> decide +kernel
lemma ha4_0_30_contains (j : Fin 7) : (ha4_0_30 j).Contains (fullFactor false 4 30 ((j.val:ℝ)/6)) := by
  rw [ha4_0_30_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha4_0_29 j) false 4 29 j (ha4_0_29_contains j)
noncomputable def hk4_1_0 (j : Fin 6) (i k : Fin 16) : CBox := (kernel4_0 j i k).mul (mpower1_0 j i k)
lemma hk4_1_0_contains (j : Fin 6) (i k : Fin 16) :
    (hk4_1_0 j i k).Contains (fullFactor true 4 0 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk4_1_0,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel4_0 j i k) (mpower1_0 j i k) (quadraturePoint j.val (16*i.val+k.val)) 4 0 (kernel4_0_contains j i k) (mpower1_0_contains j i k)
noncomputable def ha4_1_0 : Fin 7 → CBox := ![⟨⟨282961158716610,282961158716614⟩,⟨(-3),3⟩⟩,⟨⟨(-42706143494991529),(-42706143494991525)⟩,⟨(-120926048035417579),(-120926048035417575)⟩⟩,⟨⟨3053947772385296866737,3053947772385296871889⟩,⟨(-5402739214956985245174),(-5402739214956985240000)⟩⟩,⟨⟨16903170382964137658517564,16903170382964137671935629⟩,⟨(-13880229317351426973322715),(-13880229317351426960021447)⟩⟩,⟨⟨588535793916102761833935025,588535793916102762958836647⟩,⟨3411772456086199165686422228,3411772456086199166834991902⟩⟩,⟨⟨(-65878528817845185855981007311),(-65878528817845185832427874592)⟩,⟨(-35143520097970271640063878406),(-35143520097970271616257367065)⟩⟩,⟨⟨390977274694468298190061327583,390977274694468298307974382443⟩,⟨(-321010859534684108975007802739),(-321010859534684108863412052127)⟩⟩]
lemma ha4_1_0_eq (j : Fin 7) : ha4_1_0 j = atomKernel4_0 j := by fin_cases j <;> decide +kernel
lemma ha4_1_0_contains (j : Fin 7) : (ha4_1_0 j).Contains (fullFactor true 4 0 ((j.val:ℝ)/6)) := by
  rw [ha4_1_0_eq]
  simpa only [fullFactor,ite_true] using atomKernel4_0_contains j
noncomputable def hk4_1_1 (j : Fin 6) (i k : Fin 16) : CBox := (kernel4_0 j i k).mul (mpower1_1 j i k)
lemma hk4_1_1_contains (j : Fin 6) (i k : Fin 16) :
    (hk4_1_1 j i k).Contains (fullFactor true 4 1 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk4_1_1,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel4_0 j i k) (mpower1_1 j i k) (quadraturePoint j.val (16*i.val+k.val)) 4 1 (kernel4_0_contains j i k) (mpower1_1_contains j i k)
noncomputable def ha4_1_1 : Fin 7 → CBox := ![⟨⟨(-2607582845927753),(-2607582845927715)⟩,⟨(-28),28⟩⟩,⟨⟨(-122191150045355554),(-122191150045355508)⟩,⟨1085822365390366632,1085822365390366679⟩⟩,⟨⟨(-42861177505166100888659),(-42861177505166100836508)⟩,⟨10872335876083759744346,10872335876083759796489⟩⟩,⟨⟨(-118739869432107462448785546),(-118739869432107462342488016)⟩,⟨(-47065263808519467727174204),(-47065263808519467620588654)⟩⟩,⟨⟨14870510372727659189857152835,14870510372727659196921171202⟩,⟨(-7889080428845410359742320073),(-7889080428845410352779682537)⟩⟩,⟨⟨(-97173103755644446269075637291),(-97173103755644446154625706676)⟩,⟨293885051024413729859965615305,293885051024413729973889646122⟩⟩,⟨⟨(-1232593686666143723165478075673),(-1232593686666143722736438517056)⟩,⟨(-1351551833658380839059320879344),(-1351551833658380838607893199339)⟩⟩]
lemma ha4_1_1_eq (j : Fin 7) : ha4_1_1 j = ((ha4_1_0 j).mul (piI.mul (atomPoints j).z)).scale 1 1 := by fin_cases j <;> decide +kernel
lemma ha4_1_1_contains (j : Fin 7) : (ha4_1_1 j).Contains (fullFactor true 4 1 ((j.val:ℝ)/6)) := by
  rw [ha4_1_1_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha4_1_0 j) true 4 0 j (ha4_1_0_contains j)
noncomputable def hk4_1_2 (j : Fin 6) (i k : Fin 16) : CBox := (kernel4_0 j i k).mul (mpower1_2 j i k)
lemma hk4_1_2_contains (j : Fin 6) (i k : Fin 16) :
    (hk4_1_2 j i k).Contains (fullFactor true 4 2 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk4_1_2,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel4_0 j i k) (mpower1_2 j i k) (quadraturePoint j.val (16*i.val+k.val)) 4 2 (kernel4_0_contains j i k) (mpower1_2_contains j i k)
noncomputable def ha4_1_2 : Fin 7 → CBox := ![⟨⟨12014879231510136,12014879231510312⟩,⟨(-130),130⟩⟩,⟨⟨2486841090913505882,2486841090913506146⟩,⟨(-3934936940956697680),(-3934936940956697414)⟩⟩,⟨⟨133511563142318150939238,133511563142318151202320⟩,⟨83605568591362063713747,83605568591362063976841⟩⟩,⟨⟨47804884559951365221832273,47804884559951365645394529⟩,⟨369875348703464375946013737,369875348703464376369507789⟩⟩,⟨⟨(-29490795127533781843000266021),(-29490795127533781821470485885)⟩,⟨(-28373414152288670562781444012),(-28373414152288670541059792276)⟩⟩,⟨⟨634523470578658676307603943434,634523470578658676582634221580⟩,⟨94998087037092720567628901702,94998087037092720842489701286⟩⟩,⟨⟨(-2324520306598060129494091392307),(-2324520306598060128630615839706)⟩,⟨2352356659248850429136836689285,2352356659248850429961344026763⟩⟩]
lemma ha4_1_2_eq (j : Fin 7) : ha4_1_2 j = ((ha4_1_1 j).mul (piI.mul (atomPoints j).z)).scale 1 2 := by fin_cases j <;> decide +kernel
lemma ha4_1_2_contains (j : Fin 7) : (ha4_1_2 j).Contains (fullFactor true 4 2 ((j.val:ℝ)/6)) := by
  rw [ha4_1_2_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha4_1_1 j) true 4 1 j (ha4_1_1_contains j)
noncomputable def hk4_1_3 (j : Fin 6) (i k : Fin 16) : CBox := (kernel4_0 j i k).mul (mpower1_3 j i k)
lemma hk4_1_3_contains (j : Fin 6) (i k : Fin 16) :
    (hk4_1_3 j i k).Contains (fullFactor true 4 3 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk4_1_3,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel4_0 j i k) (mpower1_3 j i k) (quadraturePoint j.val (16*i.val+k.val)) 4 3 (kernel4_0_contains j i k) (mpower1_3_contains j i k)
noncomputable def ha4_1_3 : Fin 7 → CBox := ![⟨⟨(-36907059520204013),(-36907059520203472)⟩,⟨(-400),400⟩⟩,⟨⟨(-11231414664805568267),(-11231414664805567262)⟩,⟨6973466803697525733,6973466803697526741⟩⟩,⟨⟨(-75589613240513251416411),(-75589613240513250531833)⟩,⟨(-366413541999585259943478),(-366413541999585259058888)⟩⟩,⟨⟨584713297321204061332221952,584713297321204062455037712⟩,⟨(-430314464975119848289644011),(-430314464975119847167555010)⟩⟩,⟨⟨(-28798600016050553172797180124),(-28798600016050553128284315625)⟩,⟨59747663736978219251757518487,59747663736978219296075500153⟩⟩,⟨⟨(-19600922602991995227272665644),(-19600922602991994787522394838)⟩,⟨(-886374617295088768059581451890),(-886374617295088767617704716712)⟩⟩,⟨⟨2976968041023874541031972729021,2976968041023874542087933767707⟩,⟨2650731151557149500556206935305,2650731151557149501656532882917⟩⟩]
lemma ha4_1_3_eq (j : Fin 7) : ha4_1_3 j = ((ha4_1_2 j).mul (piI.mul (atomPoints j).z)).scale 1 3 := by fin_cases j <;> decide +kernel
lemma ha4_1_3_contains (j : Fin 7) : (ha4_1_3 j).Contains (fullFactor true 4 3 ((j.val:ℝ)/6)) := by
  rw [ha4_1_3_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha4_1_2 j) true 4 2 j (ha4_1_2_contains j)
noncomputable def hk4_1_4 (j : Fin 6) (i k : Fin 16) : CBox := (kernel4_0 j i k).mul (mpower1_4 j i k)
lemma hk4_1_4_contains (j : Fin 6) (i k : Fin 16) :
    (hk4_1_4 j i k).Contains (fullFactor true 4 4 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk4_1_4,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel4_0 j i k) (mpower1_4 j i k) (quadraturePoint j.val (16*i.val+k.val)) 4 4 (kernel4_0_contains j i k) (mpower1_4_contains j i k)
noncomputable def ha4_1_4 : Fin 7 → CBox := ![⟨⟨85027761173133142,85027761173134389⟩,⟨(-922),922⟩⟩,⟨⟨28007246310331154485,28007246310331157350⟩,⟨(-2925839488081969562),(-2925839488081966695)⟩⟩,⟨⟨(-378729129556541797995253),(-378729129556541795765696)⟩,⟨548337907102478304874139,548337907102478307103643⟩⟩,⟨⟨(-963224607936117361382280585),(-963224607936117359151839488)⟩,⟨(-442273776109093407109570037),(-442273776109093404878435071)⟩⟩,⟨⟨79918426362245342226220254877,79918426362245342294525006410⟩,⟨10627553236579141772659348121,10627553236579141841038897168⟩⟩,⟨⟨(-901824421030882223725182978333),(-901824421030882223193561509030)⟩,⟨176088419780057836982612322956,176088419780057837510104342203⟩⟩,⟨⟨2253215983947022747624847398950,2253215983947022748675806025234⟩,⟨(-2811911447786099791049895883254),(-2811911447786099790036016616080)⟩⟩]
lemma ha4_1_4_eq (j : Fin 7) : ha4_1_4 j = ((ha4_1_3 j).mul (piI.mul (atomPoints j).z)).scale 1 4 := by fin_cases j <;> decide +kernel
lemma ha4_1_4_contains (j : Fin 7) : (ha4_1_4 j).Contains (fullFactor true 4 4 ((j.val:ℝ)/6)) := by
  rw [ha4_1_4_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha4_1_3 j) true 4 3 j (ha4_1_3_contains j)
noncomputable def hk4_1_5 (j : Fin 6) (i k : Fin 16) : CBox := (kernel4_0 j i k).mul (mpower1_5 j i k)
lemma hk4_1_5_contains (j : Fin 6) (i k : Fin 16) :
    (hk4_1_5 j i k).Contains (fullFactor true 4 5 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk4_1_5,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel4_0 j i k) (mpower1_5 j i k) (quadraturePoint j.val (16*i.val+k.val)) 4 5 (kernel4_0_contains j i k) (mpower1_5_contains j i k)
noncomputable def ha4_1_5 : Fin 7 → CBox := ![⟨⟨(-156711919380254455),(-156711919380252155)⟩,⟨(-1700),1700⟩⟩,⟨⟨(-45117569379132367963),(-45117569379132361438)⟩,⟨(-16339378989578838897),(-16339378989578832370)⟩⟩,⟨⟨937742700034152255703841,937742700034152260198748⟩,⟨(-149850786404783572613355),(-149850786404783568118469)⟩⟩,⟨⟨93331003296068141784047768,93331003296068145329098279⟩,⟨1234410196252837007027900162,1234410196252837010573390097⟩⟩,⟨⟨(-14401144447719123242314468059),(-14401144447719123158322347952)⟩,⟨(-77065359560897373805053062246),(-77065359560897373720970434529)⟩⟩,⟨⟨270906561200275866269322119105,270906561200275866776061388513⟩,⟨712039954725207094952867269487,712039954725207095463960943915⟩⟩,⟨⟨(-2115395875765526876901022454895),(-2115395875765526876122591648692)⟩,⟨(-1521683908983851018554166802495),(-1521683908983851017751567163973)⟩⟩]
lemma ha4_1_5_eq (j : Fin 7) : ha4_1_5 j = ((ha4_1_4 j).mul (piI.mul (atomPoints j).z)).scale 1 5 := by fin_cases j <;> decide +kernel
lemma ha4_1_5_contains (j : Fin 7) : (ha4_1_5 j).Contains (fullFactor true 4 5 ((j.val:ℝ)/6)) := by
  rw [ha4_1_5_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha4_1_4 j) true 4 4 j (ha4_1_4_contains j)
noncomputable def hk4_1_6 (j : Fin 6) (i k : Fin 16) : CBox := (kernel4_0 j i k).mul (mpower1_6 j i k)
lemma hk4_1_6_contains (j : Fin 6) (i k : Fin 16) :
    (hk4_1_6 j i k).Contains (fullFactor true 4 6 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk4_1_6,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel4_0 j i k) (mpower1_6 j i k) (quadraturePoint j.val (16*i.val+k.val)) 4 6 (kernel4_0_contains j i k) (mpower1_6_contains j i k)
noncomputable def ha4_1_6 : Fin 7 → CBox := ![⟨⟨240692229386867433,240692229386870966⟩,⟨(-2612),2612⟩⟩,⟨⟨47522350994145363755,47522350994145376138⟩,⟨48833714838449540435,48833714838449552819⟩⟩,⟨⟨(-898128814667689135160379),(-898128814667689127610815)⟩,⟨(-681953369778087734850317),(-681953369778087727300658)⟩⟩,⟨⟨1006931375397864074242747258,1006931375397864078936867112⟩,⟨(-661687737820782025218663830),(-661687737820782020526090022)⟩⟩,⟨⟨(-55703043562228543359822715543),(-55703043562228543273665780273)⟩,⟨30552436990556070099101274918,30552436990556070185108166391⟩⟩,⟨⟨453015525109719719168171480263,453015525109719719577293916689⟩,⟨(-268037804658572995451047844263),(-268037804658572995045170356903)⟩⟩,⟨⟨(-849604206537745474207117197996),(-849604206537745473696595239522)⟩,⟨1320746880114118466942723094543,1320746880114118467440533951857⟩⟩]
lemma ha4_1_6_eq (j : Fin 7) : ha4_1_6 j = ((ha4_1_5 j).mul (piI.mul (atomPoints j).z)).scale 1 6 := by fin_cases j <;> decide +kernel
lemma ha4_1_6_contains (j : Fin 7) : (ha4_1_6 j).Contains (fullFactor true 4 6 ((j.val:ℝ)/6)) := by
  rw [ha4_1_6_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha4_1_5 j) true 4 5 j (ha4_1_5_contains j)
noncomputable def hk4_1_7 (j : Fin 6) (i k : Fin 16) : CBox := (kernel4_0 j i k).mul (mpower1_7 j i k)
lemma hk4_1_7_contains (j : Fin 6) (i k : Fin 16) :
    (hk4_1_7 j i k).Contains (fullFactor true 4 7 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk4_1_7,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel4_0 j i k) (mpower1_7 j i k) (quadraturePoint j.val (16*i.val+k.val)) 4 7 (kernel4_0_contains j i k) (mpower1_7_contains j i k)
noncomputable def ha4_1_7 : Fin 7 → CBox := ![⟨⟨(-316865765173233329),(-316865765173228677)⟩,⟨(-3439),3439⟩⟩,⟨⟨(-26108612275312577803),(-26108612275312557663)⟩,⟨(-78721710566199994627),(-78721710566199974486)⟩⟩,⟨⟨129973483503895742112276,129973483503895752980529⟩,⟨1140446865590912620867492,1140446865590912631735764⟩⟩,⟨⟨(-889955708558685670528337767),(-889955708558685665203321372)⟩,⟨(-467302871873413077374509263),(-467302871873413072048632002)⟩⟩,⟨⟨32223127932428178606954408683,32223127932428178682472603451⟩,⟨30149946687664775190203232695,30149946687664775265823481471⟩⟩,⟨⟨(-202010699674757644655085161409),(-202010699674757644376402615098)⟩,⟨(-237417450594773946771809038900),(-237417450594773946491274795573)⟩⟩,⟨⟨704112057992034190187424051998,704112057992034190460161080078⟩,⟨402848834406473326418740928286,402848834406473326696960739316⟩⟩]
lemma ha4_1_7_eq (j : Fin 7) : ha4_1_7 j = ((ha4_1_6 j).mul (piI.mul (atomPoints j).z)).scale 1 7 := by fin_cases j <;> decide +kernel
lemma ha4_1_7_contains (j : Fin 7) : (ha4_1_7 j).Contains (fullFactor true 4 7 ((j.val:ℝ)/6)) := by
  rw [ha4_1_7_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha4_1_6 j) true 4 6 j (ha4_1_6_contains j)
noncomputable def hk4_1_8 (j : Fin 6) (i k : Fin 16) : CBox := (kernel4_0 j i k).mul (mpower1_8 j i k)
lemma hk4_1_8_contains (j : Fin 6) (i k : Fin 16) :
    (hk4_1_8 j i k).Contains (fullFactor true 4 8 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk4_1_8,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel4_0 j i k) (mpower1_8 j i k) (quadraturePoint j.val (16*i.val+k.val)) 4 8 (kernel4_0_contains j i k) (mpower1_8_contains j i k)
noncomputable def ha4_1_8 : Fin 7 → CBox := ![⟨⟨365003158682185382,365003158682190741⟩,⟨(-3962),3962⟩⟩,⟨⟨(-11565221277143725581),(-11565221277143696920)⟩,⟨87570863262705806927,87570863262705835589⟩⟩,⟨⟨654193032461853717743986,654193032461853731432027⟩,⟨(-785553110229146349336997),(-785553110229146335649048)⟩⟩,⟨⟨16431162154620406567612414,16431162154620411854040099⟩,⟨733575612847315341933857479,733575612847315347220423137⟩⟩,⟨⟨11307862876463573025707578769,11307862876463573083757644666⟩,⟨(-24319802412277659428432972345),(-24319802412277659370419950486)⟩⟩,⟨⟨(-103455427133102106890136036073),(-103455427133102106721900637404)⟩,⟨124060977180637501742225554227,124060977180637501909630750468⟩⟩,⟨⟨165310518492329878248483281534,165310518492329878381098659482⟩,⟨(-327276406537794775653843130974),(-327276406537794775523163530670)⟩⟩]
lemma ha4_1_8_eq (j : Fin 7) : ha4_1_8 j = ((ha4_1_7 j).mul (piI.mul (atomPoints j).z)).scale 1 8 := by fin_cases j <;> decide +kernel
lemma ha4_1_8_contains (j : Fin 7) : (ha4_1_8 j).Contains (fullFactor true 4 8 ((j.val:ℝ)/6)) := by
  rw [ha4_1_8_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha4_1_7 j) true 4 7 j (ha4_1_7_contains j)
noncomputable def hk4_1_9 (j : Fin 6) (i k : Fin 16) : CBox := (kernel4_0 j i k).mul (mpower1_9 j i k)
lemma hk4_1_9_contains (j : Fin 6) (i k : Fin 16) :
    (hk4_1_9 j i k).Contains (fullFactor true 4 9 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk4_1_9,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel4_0 j i k) (mpower1_9 j i k) (quadraturePoint j.val (16*i.val+k.val)) 4 9 (kernel4_0_contains j i k) (mpower1_9_contains j i k)
noncomputable def ha4_1_9 : Fin 7 → CBox := ![⟨⟨(-373736404752101923),(-373736404752096435)⟩,⟨(-4057),4057⟩⟩,⟨⟨46026438971459646812,46026438971459683067⟩,⟨(-69815606836412645563),(-69815606836412609308)⟩⟩,⟨⟨(-807407422918136490944112),(-807407422918136475620573)⟩,⟨55390307570908635797442,55390307570908651120972⟩⟩,⟨⟨411201132073586750592642394,411201132073586755256849285⟩,⟨(-239993869419179599326551127),(-239993869419179594662957025)⟩⟩,⟨⟨(-14388074158112811012320385145),(-14388074158112810972720577993)⟩,⟨(-1709892746615031001852185635),(-1709892746615030962253887421)⟩⟩,⟨⟨64409999671568227960920542608,64409999671568228050279879752⟩,⟨37252141722033286571057820694,37252141722033286660704396663⟩⟩,⟨⟨(-134760504037822101221170491461),(-134760504037822101165542749483)⟩,⟨(-59498533132063636178054899765),(-59498533132063636121886959305)⟩⟩]
lemma ha4_1_9_eq (j : Fin 7) : ha4_1_9 j = ((ha4_1_8 j).mul (piI.mul (atomPoints j).z)).scale 1 9 := by fin_cases j <;> decide +kernel
lemma ha4_1_9_contains (j : Fin 7) : (ha4_1_9 j).Contains (fullFactor true 4 9 ((j.val:ℝ)/6)) := by
  rw [ha4_1_9_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha4_1_8 j) true 4 8 j (ha4_1_8_contains j)
noncomputable def hk4_1_10 (j : Fin 6) (i k : Fin 16) : CBox := (kernel4_0 j i k).mul (mpower1_10 j i k)
lemma hk4_1_10_contains (j : Fin 6) (i k : Fin 16) :
    (hk4_1_10 j i k).Contains (fullFactor true 4 10 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk4_1_10,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel4_0 j i k) (mpower1_10 j i k) (quadraturePoint j.val (16*i.val+k.val)) 4 10 (kernel4_0_contains j i k) (mpower1_10_contains j i k)
noncomputable def ha4_1_10 : Fin 7 → CBox := ![⟨⟨344410746107485977,344410746107491036⟩,⟨(-3739),3739⟩⟩,⟨⟨(-61241398180848069516),(-61241398180848028242)⟩,⟨36410256661587610071,36410256661587651345⟩⟩,⟨⟨426057544523511009005628,426057544523511024443450⟩,⟨388555418264887262139144,388555418264887277577020⟩⟩,⟨⟨(-238965013579701798855809224),(-238965013579701795152789048)⟩,⟨(-142135116483130960597255694),(-142135116483130956893971748)⟩⟩,⟨⟨1390337505473758473816047355,1390337505473758498120655373⟩,⟨6906384418168149384297776169,6906384418168149408615381683⟩⟩,⟨⟨10682173979783230084786718401,10682173979783230127766503913⟩,⟨(-28937078755176425808484739001),(-28937078755176425765572841313)⟩⟩,⟨⟨(-18954632056797412926593369349),(-18954632056797412905189995256)⟩,⟨49779592818138701473805312280,49779592818138701495105772379⟩⟩]
lemma ha4_1_10_eq (j : Fin 7) : ha4_1_10 j = ((ha4_1_9 j).mul (piI.mul (atomPoints j).z)).scale 1 10 := by fin_cases j <;> decide +kernel
lemma ha4_1_10_contains (j : Fin 7) : (ha4_1_10 j).Contains (fullFactor true 4 10 ((j.val:ℝ)/6)) := by
  rw [ha4_1_10_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha4_1_9 j) true 4 9 j (ha4_1_9_contains j)
noncomputable def hk4_1_11 (j : Fin 6) (i k : Fin 16) : CBox := (kernel4_0 j i k).mul (mpower1_11 j i k)
lemma hk4_1_11_contains (j : Fin 6) (i k : Fin 16) :
    (hk4_1_11 j i k).Contains (fullFactor true 4 11 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk4_1_11,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel4_0 j i k) (mpower1_11 j i k) (quadraturePoint j.val (16*i.val+k.val)) 4 11 (kernel4_0_contains j i k) (mpower1_11_contains j i k)
noncomputable def ha4_1_11 : Fin 7 → CBox := ![⟨⟨(-288532871943646218),(-288532871943641979)⟩,⟨(-3133),3133⟩⟩,⟨⟨54987172752541545098,54987172752541587814⟩,⟨(-4676579574663171544),(-4676579574663128828)⟩⟩,⟨⟨(-8781287222846539040959),(-8781287222846524901933)⟩,⟨(-373393748751650466502921),(-373393748751650452363895)⟩⟩,⟨⟨(-4527097223383423975371289),(-4527097223383421302518676)⟩,⟨147540089349048341846152415,147540089349048344519014234⟩⟩,⟨⟨2709142225723565901311545603,2709142225723565914882953808⟩,⟨(-1535361679402339012069200583),(-1535361679402338998506416375)⟩⟩,⟨⟨(-11430912922189751433404198707),(-11430912922189751414678841612)⟩,⟨(-2114482974330347687133479671),(-2114482974330347668405116365)⟩⟩,⟨⟨16664961881176035410467977874,16664961881176035417878796768⟩,⟨5372580800431791485102728033,5372580800431791492515039184⟩⟩]
lemma ha4_1_11_eq (j : Fin 7) : ha4_1_11 j = ((ha4_1_10 j).mul (piI.mul (atomPoints j).z)).scale 1 11 := by fin_cases j <;> decide +kernel
lemma ha4_1_11_contains (j : Fin 7) : (ha4_1_11 j).Contains (fullFactor true 4 11 ((j.val:ℝ)/6)) := by
  rw [ha4_1_11_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha4_1_10 j) true 4 10 j (ha4_1_10_contains j)
noncomputable def hk4_1_12 (j : Fin 6) (i k : Fin 16) : CBox := (kernel4_0 j i k).mul (mpower1_12 j i k)
lemma hk4_1_12_contains (j : Fin 6) (i k : Fin 16) :
    (hk4_1_12 j i k).Contains (fullFactor true 4 12 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk4_1_12,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel4_0 j i k) (mpower1_12 j i k) (quadraturePoint j.val (16*i.val+k.val)) 4 12 (kernel4_0_contains j i k) (mpower1_12_contains j i k)
noncomputable def ha4_1_12 : Fin 7 → CBox := ![⟨⟨221577339088675828,221577339088679084⟩,⟨(-2406),2406⟩⟩,⟨⟨(-36577597281202215869),(-36577597281202175344)⟩,⟨(-14048578263458107062),(-14048578263458066538)⟩⟩,⟨⟨(-156649954720359189061737),(-156649954720359177191859)⟩,⟨156970497110931007550277,156970497110931019420133⟩⟩,⟨⟨63873985426687764490455294,63873985426687766258814288⟩,⟨(-32867577440256272188100181),(-32867577440256270419829363)⟩⟩,⟨⟨(-933222544554014460066491758),(-933222544554014453128068087)⟩,⟨(-849132298387962067200019948),(-849132298387962060258398439)⟩⟩,⟨⟨(-48953280789182958523140572),(-48953280789182951043774327)⟩,⟨4015658690562889804409288571,4015658690562889811896163125⟩⟩,⟨⟨1355941114837619286755074774,1355941114837619289107517888⟩,⟨(-5098869900160554237572824837),(-5098869900160554235210553419)⟩⟩]
lemma ha4_1_12_eq (j : Fin 7) : ha4_1_12 j = ((ha4_1_11 j).mul (piI.mul (atomPoints j).z)).scale 1 12 := by fin_cases j <;> decide +kernel
lemma ha4_1_12_contains (j : Fin 7) : (ha4_1_12 j).Contains (fullFactor true 4 12 ((j.val:ℝ)/6)) := by
  rw [ha4_1_12_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha4_1_11 j) true 4 11 j (ha4_1_11_contains j)
noncomputable def hk4_1_13 (j : Fin 6) (i k : Fin 16) : CBox := (kernel4_0 j i k).mul (mpower1_13 j i k)
lemma hk4_1_13_contains (j : Fin 6) (i k : Fin 16) :
    (hk4_1_13 j i k).Contains (fullFactor true 4 13 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk4_1_13,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel4_0 j i k) (mpower1_13 j i k) (quadraturePoint j.val (16*i.val+k.val)) 4 13 (kernel4_0_contains j i k) (mpower1_13_contains j i k)
noncomputable def ha4_1_13 : Fin 7 → CBox := ![⟨⟨(-157070013282310896),(-157070013282308587)⟩,⟨(-1706),1706⟩⟩,⟨⟨17552430588930803793,17552430588930839282⟩,⟨18745388791333306437,18745388791333341925⟩⟩,⟨⟨121515002802467601445596,121515002802467610643941⟩,⟨2609209362546418089024,2609209362546427287370⟩⟩,⟨⟨(-26819953452868261665428530),(-26819953452868260585554108)⟩,⟨(-17943955010317935478491415),(-17943955010317934398584243)⟩⟩,⟨⟨(-192985941286998963688248889),(-192985941286998960411218876)⟩,⟨430632014189237208820928326,430632014189237212097258561⟩⟩,⟨⟨1264587121744351847794697697,1264587121744351850556711794⟩,⟨(-202173846053296087347084457),(-202173846053296084590306923)⟩⟩,⟨⟨(-1435904737533013182087880812),(-1435904737533013181393160205)⟩,⟨(-302992828438247915450070469),(-302992828438247914761075230)⟩⟩]
lemma ha4_1_13_eq (j : Fin 7) : ha4_1_13 j = ((ha4_1_12 j).mul (piI.mul (atomPoints j).z)).scale 1 13 := by fin_cases j <;> decide +kernel
lemma ha4_1_13_contains (j : Fin 7) : (ha4_1_13 j).Contains (fullFactor true 4 13 ((j.val:ℝ)/6)) := by
  rw [ha4_1_13_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha4_1_12 j) true 4 12 j (ha4_1_12_contains j)
noncomputable def hk4_1_14 (j : Fin 6) (i k : Fin 16) : CBox := (kernel4_0 j i k).mul (mpower1_14 j i k)
lemma hk4_1_14_contains (j : Fin 6) (i k : Fin 16) :
    (hk4_1_14 j i k).Contains (fullFactor true 4 14 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk4_1_14,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel4_0 j i k) (mpower1_14 j i k) (quadraturePoint j.val (16*i.val+k.val)) 4 14 (kernel4_0_contains j i k) (mpower1_14_contains j i k)
noncomputable def ha4_1_14 : Fin 7 → CBox := ![⟨⟨103389523773266113,103389523773267634⟩,⟨(-1123),1123⟩⟩,⟨⟨(-4633443673673209603),(-4633443673673180744)⟩,⟨(-14925996763843429024),(-14925996763843400166)⟩⟩,⟨⟨(-41774770371837720324116),(-41774770371837713705308)⟩,⟨(-45619091552665876988714),(-45619091552665870369900)⟩⟩,⟨⟨(-1125901853237962722994658),(-1125901853237962110635120)⟩,⟨13413215749862543630209335,13413215749862544242568141⟩⟩,⟨⟨162996981809506414549212219,162996981809506415985622404⟩,⟨17073711483102164194986172,17073711483102165631383790⟩⟩,⟨⟨(-122613935141277530749972356),(-122613935141277529806185436)⟩,⟨(-358844335760074371899781242),(-358844335760074370953913000)⟩⟩,⟨⟨(-58892167457158499583102199),(-58892167457158499395761435)⟩,⟨374427383987842205015766639,374427383987842205205389133⟩⟩]
lemma ha4_1_14_eq (j : Fin 7) : ha4_1_14 j = ((ha4_1_13 j).mul (piI.mul (atomPoints j).z)).scale 1 14 := by fin_cases j <;> decide +kernel
lemma ha4_1_14_contains (j : Fin 7) : (ha4_1_14 j).Contains (fullFactor true 4 14 ((j.val:ℝ)/6)) := by
  rw [ha4_1_14_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha4_1_13 j) true 4 13 j (ha4_1_13_contains j)
noncomputable def hk4_1_15 (j : Fin 6) (i k : Fin 16) : CBox := (kernel4_0 j i k).mul (mpower1_15 j i k)
lemma hk4_1_15_contains (j : Fin 6) (i k : Fin 16) :
    (hk4_1_15 j i k).Contains (fullFactor true 4 15 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk4_1_15,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel4_0 j i k) (mpower1_15 j i k) (quadraturePoint j.val (16*i.val+k.val)) 4 15 (kernel4_0_contains j i k) (mpower1_15_contains j i k)
noncomputable def ha4_1_15 : Fin 7 → CBox := ![⟨⟨(-63517963587318999),(-63517963587318064)⟩,⟨(-690),690⟩⟩,⟨⟨(-1331449327586107711),(-1331449327586085808)⟩,⟨8776841268483944298,8776841268483966201⟩⟩,⟨⟨(-1951018677024513354744),(-1951018677024508909589)⟩,⟨29316938149061007253744,29316938149061011698898⟩⟩,⟨⟨4780317323109354176191061,4780317323109354500277648⟩,⟨(-2147187369417703010993958),(-2147187369417702686913200)⟩⟩,⟨⟨(-11207877744634551981961976),(-11207877744634551394371826)⟩,⟨(-51927803596403653882774188),(-51927803596403653295085299)⟩⟩,⟨⟨(-91975182078698675059755517),(-91975182078698674757501721)⟩,⟨50243339778780636999260026,50243339778780637300875205⟩⟩,⟨⟨90875027530436312785404506,90875027530436312833687729⟩,⟨9490244295613674650501421,9490244295613674698034699⟩⟩]
lemma ha4_1_15_eq (j : Fin 7) : ha4_1_15 j = ((ha4_1_14 j).mul (piI.mul (atomPoints j).z)).scale 1 15 := by fin_cases j <;> decide +kernel
lemma ha4_1_15_contains (j : Fin 7) : (ha4_1_15 j).Contains (fullFactor true 4 15 ((j.val:ℝ)/6)) := by
  rw [ha4_1_15_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha4_1_14 j) true 4 14 j (ha4_1_14_contains j)
noncomputable def hk4_1_16 (j : Fin 6) (i k : Fin 16) : CBox := (kernel4_0 j i k).mul (mpower1_16 j i k)
lemma hk4_1_16_contains (j : Fin 6) (i k : Fin 16) :
    (hk4_1_16 j i k).Contains (fullFactor true 4 16 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk4_1_16,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel4_0 j i k) (mpower1_16 j i k) (quadraturePoint j.val (16*i.val+k.val)) 4 16 (kernel4_0_contains j i k) (mpower1_16_contains j i k)
noncomputable def ha4_1_16 : Fin 7 → CBox := ![⟨⟨36583720759098776,36583720759099316⟩,⟨(-398),398⟩⟩,⟨⟨2677392080736579140,2677392080736594725⟩,⟨(-3895946064982510822),(-3895946064982495237)⟩⟩,⟨⟨10037038319273749196460,10037038319273751995190⟩,⟨(-8393451737851121688081),(-8393451737851118889353)⟩⟩,⟨⟨(-1531042142890191918961909),(-1531042142890191758166003)⟩,⟨(-1146418088998160947433510),(-1146418088998160786635582)⟩⟩,⟨⟨(-13932622606734916266739991),(-13932622606734916041343581)⟩,⟨8154337908989474819208504,8154337908989475044560605⟩⟩,⟨⟨16877343811142840107776326,16877343811142840198146684⟩,⟨21272450606302319761884223,21272450606302319852417599⟩⟩,⟨⟨1075350659330757033750342,1075350659330757045054943⟩,⟨(-20620881604590682034097105),(-20620881604590682022576625)⟩⟩]
lemma ha4_1_16_eq (j : Fin 7) : ha4_1_16 j = ((ha4_1_15 j).mul (piI.mul (atomPoints j).z)).scale 1 16 := by fin_cases j <;> decide +kernel
lemma ha4_1_16_contains (j : Fin 7) : (ha4_1_16 j).Contains (fullFactor true 4 16 ((j.val:ℝ)/6)) := by
  rw [ha4_1_16_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha4_1_15 j) true 4 15 j (ha4_1_15_contains j)
noncomputable def hk4_1_17 (j : Fin 6) (i k : Fin 16) : CBox := (kernel4_0 j i k).mul (mpower1_17 j i k)
lemma hk4_1_17_contains (j : Fin 6) (i k : Fin 16) :
    (hk4_1_17 j i k).Contains (fullFactor true 4 17 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk4_1_17,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel4_0 j i k) (mpower1_17 j i k) (quadraturePoint j.val (16*i.val+k.val)) 4 17 (kernel4_0_contains j i k) (mpower1_17_contains j i k)
noncomputable def ha4_1_17 : Fin 7 → CBox := ![⟨⟨(-19831256974987217),(-19831256974986924)⟩,⟨(-216),216⟩⟩,⟨⟨(-2059416998806460849),(-2059416998806450412)⟩,⟨1171355604922066850,1171355604922077288⟩⟩,⟨⟨(-5449727250552316936235),(-5449727250552315277773)⟩,⟨(-609807811738035030507),(-609807811738033372044)⟩⟩,⟨⟨(-89611486533065604243206),(-89611486533065529155923)⟩,⟨650902469489435354949834,650902469489435430037010⟩⟩,⟨⟨3457990745058905354513310,3457990745058905435858446⟩,⟨3059519842532257558258589,3059519842532257639615177⟩⟩,⟨⟨4412791760747938877470250,4412791760747938902988981⟩,⟨(-4937131760221530261847230),(-4937131760221530236363703)⟩⟩,⟨⟨(-4392027212546253517558359),(-4392027212546253514972409)⟩,⟨(-651007646453216783336),(-651007646453214253386)⟩⟩]
lemma ha4_1_17_eq (j : Fin 7) : ha4_1_17 j = ((ha4_1_16 j).mul (piI.mul (atomPoints j).z)).scale 1 17 := by fin_cases j <;> decide +kernel
lemma ha4_1_17_contains (j : Fin 7) : (ha4_1_17 j).Contains (fullFactor true 4 17 ((j.val:ℝ)/6)) := by
  rw [ha4_1_17_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha4_1_16 j) true 4 16 j (ha4_1_16_contains j)
noncomputable def hk4_1_18 (j : Fin 6) (i k : Fin 16) : CBox := (kernel4_0 j i k).mul (mpower1_18 j i k)
lemma hk4_1_18_contains (j : Fin 6) (i k : Fin 16) :
    (hk4_1_18 j i k).Contains (fullFactor true 4 18 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk4_1_18,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel4_0 j i k) (mpower1_18 j i k) (quadraturePoint j.val (16*i.val+k.val)) 4 18 (kernel4_0_contains j i k) (mpower1_18_contains j i k)
noncomputable def ha4_1_18 : Fin 7 → CBox := ![⟨⟨10152874717996636,10152874717996787⟩,⟨(-111),111⟩⟩,⟨⟨1119050062386385031,1119050062386391633⟩,⟨(-73514147686835132),(-73514147686828529)⟩⟩,⟨⟨1316187535226924803759,1316187535226925731923⟩,⟨1726074413045262573102,1726074413045263501266⟩⟩,⟨⟨198810663123377547543181,198810663123377580658395⟩,⟨(-76904735581677704486588),(-76904735581677671371586)⟩⟩,⟨⟨494158889834145099319115,494158889834145127052178⟩,⟨(-1145119057255289100082241),(-1145119057255289072350935)⟩⟩,⟨⟨(-1293199793664092864640983),(-1293199793664092857854603)⟩,⟨(-808350773977237131983964),(-808350773977237125191285)⟩⟩,⟨⟨45686381946115178703335,45686381946115179237998⟩,⟨881102603815161103752823,881102603815161104300795⟩⟩]
lemma ha4_1_18_eq (j : Fin 7) : ha4_1_18 j = ((ha4_1_17 j).mul (piI.mul (atomPoints j).z)).scale 1 18 := by fin_cases j <;> decide +kernel
lemma ha4_1_18_contains (j : Fin 7) : (ha4_1_18 j).Contains (fullFactor true 4 18 ((j.val:ℝ)/6)) := by
  rw [ha4_1_18_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha4_1_17 j) true 4 17 j (ha4_1_17_contains j)
noncomputable def hk4_1_19 (j : Fin 6) (i k : Fin 16) : CBox := (kernel4_0 j i k).mul (mpower1_19 j i k)
lemma hk4_1_19_contains (j : Fin 6) (i k : Fin 16) :
    (hk4_1_19 j i k).Contains (fullFactor true 4 19 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk4_1_19,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel4_0 j i k) (mpower1_19 j i k) (quadraturePoint j.val (16*i.val+k.val)) 4 19 (kernel4_0_contains j i k) (mpower1_19_contains j i k)
noncomputable def ha4_1_19 : Fin 7 → CBox := ![⟨⟨(-4924325093272123),(-4924325093272049)⟩,⟨(-54),54⟩⟩,⟨⟨(-465905797726687868),(-465905797726683911)⟩,⟨(-189310336280628435),(-189310336280624478)⟩⟩,⟨⟨126801924778189848949,126801924778190341061⟩,⟨(-804051112026100038102),(-804051112026099545991)⟩⟩,⟨⟨(-50288561925768433668250),(-50288561925768419832490)⟩,⟨(-41996907277114615954997),(-41996907277114602119166)⟩⟩,⟨⟨(-317856028283734568040137),(-317856028283734559084187)⟩,⟨(-28828693450783567548442),(-28828693450783558592543)⟩⟩,⟨⟨(-125870794003239511753570),(-125870794003239510040769)⟩,⟨308022606095740110862217,308022606095740112574171⟩⟩,⟨⟨167005566310115885399711,167005566310115885509675⟩,⟨(-17390647682132445089246),(-17390647682132444982160)⟩⟩]
lemma ha4_1_19_eq (j : Fin 7) : ha4_1_19 j = ((ha4_1_18 j).mul (piI.mul (atomPoints j).z)).scale 1 19 := by fin_cases j <;> decide +kernel
lemma ha4_1_19_contains (j : Fin 7) : (ha4_1_19 j).Contains (fullFactor true 4 19 ((j.val:ℝ)/6)) := by
  rw [ha4_1_19_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha4_1_18 j) true 4 18 j (ha4_1_18_contains j)
noncomputable def hk4_1_20 (j : Fin 6) (i k : Fin 16) : CBox := (kernel4_0 j i k).mul (mpower1_20 j i k)
lemma hk4_1_20_contains (j : Fin 6) (i k : Fin 16) :
    (hk4_1_20 j i k).Contains (fullFactor true 4 20 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk4_1_20,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel4_0 j i k) (mpower1_20 j i k) (quadraturePoint j.val (16*i.val+k.val)) 4 20 (kernel4_0_contains j i k) (mpower1_20_contains j i k)
noncomputable def ha4_1_20 : Fin 7 → CBox := ![⟨⟨2268966118746996,2268966118747031⟩,⟨(-25),25⟩⟩,⟨⟨143395564937588033,143395564937590286⟩,⟨159173478369501403,159173478369503657⟩⟩,⟨⟨(-238265018213193681465),(-238265018213193433594)⟩,⟨165286641342213632702,165286641342213880573⟩⟩,⟨⟨(-3610799469949467280787),(-3610799469949461789112)⟩,⟨18786940801909900920126,18786940801909906411796⟩⟩,⟨⟨17423846619338282891150,17423846619338285638629⟩,⟨75608858172521635091822,75608858172521637839452⟩⟩,⟨⟨67350748333829412390720,67350748333829412800944⟩,⟨14863879155404315747231,14863879155404316157500⟩⟩,⟨⟨(-4707863846622743593336),(-4707863846622743572953)⟩,⟨(-29989797414741186507773),(-29989797414741186486816)⟩⟩]
lemma ha4_1_20_eq (j : Fin 7) : ha4_1_20 j = ((ha4_1_19 j).mul (piI.mul (atomPoints j).z)).scale 1 20 := by fin_cases j <;> decide +kernel
lemma ha4_1_20_contains (j : Fin 7) : (ha4_1_20 j).Contains (fullFactor true 4 20 ((j.val:ℝ)/6)) := by
  rw [ha4_1_20_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha4_1_19 j) true 4 19 j (ha4_1_19_contains j)
noncomputable def hk4_1_21 (j : Fin 6) (i k : Fin 16) : CBox := (kernel4_0 j i k).mul (mpower1_21 j i k)
lemma hk4_1_21_contains (j : Fin 6) (i k : Fin 16) :
    (hk4_1_21 j i k).Contains (fullFactor true 4 21 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk4_1_21,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel4_0 j i k) (mpower1_21 j i k) (quadraturePoint j.val (16*i.val+k.val)) 4 21 (kernel4_0_contains j i k) (mpower1_21_contains j i k)
noncomputable def ha4_1_21 : Fin 7 → CBox := ![⟨⟨(-995680510335213),(-995680510335197)⟩,⟨(-11),11⟩⟩,⟨⟨(-24167544916724271),(-24167544916723049)⟩,⟨(-83494535036761162),(-83494535036759939)⟩⟩,⟨⟨96398090339335817951,96398090339335936856⟩,⟨19681180153674845558,19681180153674964463⟩⟩,⟨⟨5056546918286374916924,5056546918286376992863⟩,⟨(-1653420513831688192605),(-1653420513831686116670)⟩⟩,⟨⟨15376608068704869496132,15376608068704870298925⟩,⟨(-9289159739887357853110),(-9289159739887357050367)⟩⟩,⟨⟨632755968118618195706,632755968118618289295⟩,⟨(-13600783348369112516012),(-13600783348369112422404)⟩⟩,⟨⟨(-5114758474883154535204),(-5114758474883154531400)⟩,⟨1077690656331277764701,1077690656331277768398⟩⟩]
lemma ha4_1_21_eq (j : Fin 7) : ha4_1_21 j = ((ha4_1_20 j).mul (piI.mul (atomPoints j).z)).scale 1 21 := by fin_cases j <;> decide +kernel
lemma ha4_1_21_contains (j : Fin 7) : (ha4_1_21 j).Contains (fullFactor true 4 21 ((j.val:ℝ)/6)) := by
  rw [ha4_1_21_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha4_1_20 j) true 4 20 j (ha4_1_20_contains j)
noncomputable def hk4_1_22 (j : Fin 6) (i k : Fin 16) : CBox := (kernel4_0 j i k).mul (mpower1_22 j i k)
lemma hk4_1_22_contains (j : Fin 6) (i k : Fin 16) :
    (hk4_1_22 j i k).Contains (fullFactor true 4 22 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk4_1_22,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel4_0 j i k) (mpower1_22 j i k) (quadraturePoint j.val (16*i.val+k.val)) 4 22 (kernel4_0_contains j i k) (mpower1_22_contains j i k)
noncomputable def ha4_1_22 : Fin 7 → CBox := ![⟨⟨417069676878878,417069676878886⟩,⟨(-5),5⟩⟩,⟨⟨(-5688506223666242),(-5688506223665609)⟩,⟨33179084348972314,33179084348972948⟩⟩,⟨⟨(-16966331297947434677),(-16966331297947380230)⟩,⟨(-26971181249744854994),(-26971181249744800547)⟩⟩,⟨⟨(-1034368221745284543763),(-1034368221745283794697)⟩,⟨(-961413717613513667859),(-961413717613512918792)⟩⟩,⟨⟨(-3009857270793159298842),(-3009857270793159074960)⟩,⟨(-2589244316765056088331),(-2589244316765055864438)⟩⟩,⟨⟨(-2545858161311484954193),(-2545858161311484933806)⟩,⟨317913853180970144320,317913853180970164698⟩⟩,⟨⟨220544744333898411295,220544744333898411936⟩,⟨830325656585312049258,830325656585312049918⟩⟩]
lemma ha4_1_22_eq (j : Fin 7) : ha4_1_22 j = ((ha4_1_21 j).mul (piI.mul (atomPoints j).z)).scale 1 22 := by fin_cases j <;> decide +kernel
lemma ha4_1_22_contains (j : Fin 7) : (ha4_1_22 j).Contains (fullFactor true 4 22 ((j.val:ℝ)/6)) := by
  rw [ha4_1_22_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha4_1_21 j) true 4 21 j (ha4_1_21_contains j)
noncomputable def hk4_1_23 (j : Fin 6) (i k : Fin 16) : CBox := (kernel4_0 j i k).mul (mpower1_23 j i k)
lemma hk4_1_23_contains (j : Fin 6) (i k : Fin 16) :
    (hk4_1_23 j i k).Contains (fullFactor true 4 23 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk4_1_23,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel4_0 j i k) (mpower1_23 j i k) (quadraturePoint j.val (16*i.val+k.val)) 4 23 (kernel4_0_contains j i k) (mpower1_23_contains j i k)
noncomputable def ha4_1_23 : Fin 7 → CBox := ![⟨⟨(-167106009995311),(-167106009995307)⟩,⟨(-3),3⟩⟩,⟨⟨7259331436498960,7259331436499274⟩,⟨(-10139539301202605),(-10139539301202290)⟩⟩,⟨⟨(-2407442650495455086),(-2407442650495431238)⟩,⟨9572739713644638996,9572739713644662844⟩⟩,⟨⟨(-86257478564224296273),(-86257478564224037737)⟩,⟨348027482319142265882,348027482319142524418⟩⟩,⟨⟨(-321794527051609111071),(-321794527051609051344)⟩,⟨775179833332239811424,775179833332239871150⟩⟩,⟨⟨134427518763586881360,134427518763586885605⟩,⟨442464170991098208850,442464170991098213097⟩⟩,⟨⟨128561527830534868032,128561527830534868143⟩,⟨(-41404602083639300230),(-41404602083639300122)⟩⟩]
lemma ha4_1_23_eq (j : Fin 7) : ha4_1_23 j = ((ha4_1_22 j).mul (piI.mul (atomPoints j).z)).scale 1 23 := by fin_cases j <;> decide +kernel
lemma ha4_1_23_contains (j : Fin 7) : (ha4_1_23 j).Contains (fullFactor true 4 23 ((j.val:ℝ)/6)) := by
  rw [ha4_1_23_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha4_1_22 j) true 4 22 j (ha4_1_22_contains j)
noncomputable def hk4_1_24 (j : Fin 6) (i k : Fin 16) : CBox := (kernel4_0 j i k).mul (mpower1_24 j i k)
lemma hk4_1_24_contains (j : Fin 6) (i k : Fin 16) :
    (hk4_1_24 j i k).Contains (fullFactor true 4 24 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk4_1_24,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel4_0 j i k) (mpower1_24 j i k) (quadraturePoint j.val (16*i.val+k.val)) 4 24 (kernel4_0_contains j i k) (mpower1_24_contains j i k)
noncomputable def ha4_1_24 : Fin 7 → CBox := ![⟨⟨64164101634350,64164101634353⟩,⟨(-2),2⟩⟩,⟨⟨(-3889545871029426),(-3889545871029276)⟩,⟨2114285442955130,2114285442955280⟩⟩,⟨⟨2548092344363394647,2548092344363404658⟩,⟨(-1447213392689696731),(-1447213392689686720)⟩⟩,⟨⟨84247069693839234255,84247069693839319770⟩,⟨(-22678584098096393804),(-22678584098096308289)⟩⟩,⟨⟨169539827896627858735,169539827896627874005⟩,⟨13000561379869408527,13000561379869423797⟩⟩,⟨⟨71371631097390712785,71371631097390713634⟩,⟨(-35866914758470672164),(-35866914758470671315)⟩⟩,⟨⟨(-7235563563306400966),(-7235563563306400948)⟩,⟨(-19019347648117244127),(-19019347648117244108)⟩⟩]
lemma ha4_1_24_eq (j : Fin 7) : ha4_1_24 j = ((ha4_1_23 j).mul (piI.mul (atomPoints j).z)).scale 1 24 := by fin_cases j <;> decide +kernel
lemma ha4_1_24_contains (j : Fin 7) : (ha4_1_24 j).Contains (fullFactor true 4 24 ((j.val:ℝ)/6)) := by
  rw [ha4_1_24_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha4_1_23 j) true 4 23 j (ha4_1_23_contains j)
noncomputable def hk4_1_25 (j : Fin 6) (i k : Fin 16) : CBox := (kernel4_0 j i k).mul (mpower1_25 j i k)
lemma hk4_1_25_contains (j : Fin 6) (i k : Fin 16) :
    (hk4_1_25 j i k).Contains (fullFactor true 4 25 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk4_1_25,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel4_0 j i k) (mpower1_25 j i k) (quadraturePoint j.val (16*i.val+k.val)) 4 25 (kernel4_0_contains j i k) (mpower1_25_contains j i k)
noncomputable def ha4_1_25 : Fin 7 → CBox := ![⟨⟨(-23651756517391),(-23651756517389)⟩,⟨(-1),1⟩⟩,⟨⟨1507150861309058,1507150861309128⟩,⟨(-69912253740847),(-69912253740778)⟩⟩,⟨⟨(-799960665706457510),(-799960665706453475)⟩,⟨(-239905681667305917),(-239905681667301882)⟩⟩,⟨⟨(-14170669234308460126),(-14170669234308432971)⟩,⟨(-14647102925907551858),(-14647102925907524703)⟩⟩,⟨⟨(-7874032788143656372),(-7874032788143652624)⟩,⟨(-32118906315026203165),(-32118906315026199417)⟩⟩,⟨⟨(-7871774562336731974),(-7871774562336731811)⟩,⟨(-10652519722186220085),(-10652519722186219921)⟩⟩,⟨⟨(-2692828542251588346),(-2692828542251588342)⟩,⟨1187965405201376517,1187965405201376521⟩⟩]
lemma ha4_1_25_eq (j : Fin 7) : ha4_1_25 j = ((ha4_1_24 j).mul (piI.mul (atomPoints j).z)).scale 1 25 := by fin_cases j <;> decide +kernel
lemma ha4_1_25_contains (j : Fin 7) : (ha4_1_25 j).Contains (fullFactor true 4 25 ((j.val:ℝ)/6)) := by
  rw [ha4_1_25_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha4_1_24 j) true 4 24 j (ha4_1_24_contains j)
noncomputable def hk4_1_26 (j : Fin 6) (i k : Fin 16) : CBox := (kernel4_0 j i k).mul (mpower1_26 j i k)
lemma hk4_1_26_contains (j : Fin 6) (i k : Fin 16) :
    (hk4_1_26 j i k).Contains (fullFactor true 4 26 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk4_1_26,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel4_0 j i k) (mpower1_26 j i k) (quadraturePoint j.val (16*i.val+k.val)) 4 26 (kernel4_0_contains j i k) (mpower1_26_contains j i k)
noncomputable def ha4_1_26 : Fin 7 → CBox := ![⟨⟨8383036202202,8383036202204⟩,⟨(-1),1⟩⟩,⟨⟨(-454388025616779),(-454388025616747)⟩,⟨(-194900546528633),(-194900546528601)⟩⟩,⟨⟨103965069308940120,103965069308941684⟩,⟨203888669409401143,203888669409402708⟩⟩,⟨⟨(-1335334482009259728),(-1335334482009251436)⟩,⟨4378418280698589550,4378418280698597842⟩⟩,⟨⟨(-5248347452064477218),(-5248347452064476333)⟩,⟨3271136095074790554,3271136095074791440⟩⟩,⟨⟨(-1460560236392765555),(-1460560236392765524)⟩,⟨1525428951259400239,1525428951259400270⟩⟩,⟨⟨184439056088267927,184439056088267929⟩,⟨365415605192313431,365415605192313433⟩⟩]
lemma ha4_1_26_eq (j : Fin 7) : ha4_1_26 j = ((ha4_1_25 j).mul (piI.mul (atomPoints j).z)).scale 1 26 := by fin_cases j <;> decide +kernel
lemma ha4_1_26_contains (j : Fin 7) : (ha4_1_26 j).Contains (fullFactor true 4 26 ((j.val:ℝ)/6)) := by
  rw [ha4_1_26_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha4_1_25 j) true 4 25 j (ha4_1_25_contains j)
noncomputable def hk4_1_27 (j : Fin 6) (i k : Fin 16) : CBox := (kernel4_0 j i k).mul (mpower1_27 j i k)
lemma hk4_1_27_contains (j : Fin 6) (i k : Fin 16) :
    (hk4_1_27 j i k).Contains (fullFactor true 4 27 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk4_1_27,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel4_0 j i k) (mpower1_27 j i k) (quadraturePoint j.val (16*i.val+k.val)) 4 27 (kernel4_0_contains j i k) (mpower1_27_contains j i k)
noncomputable def ha4_1_27 : Fin 7 → CBox := ![⟨⟨(-2861204290606),(-2861204290605)⟩,⟨(-1),1⟩⟩,⟨⟨102178881013114,102178881013129⟩,⟨117907552804125,117907552804139⟩⟩,⟨⟨19932625835250058,19932625835250642⟩,⟨(-57010777019742819),(-57010777019742234)⟩⟩,⟨⟨968339618325924218,968339618325926657⟩,⟨(-206281693212696787),(-206281693212694348)⟩⟩,⟨⟨854286319129416942,854286319129417144⟩,⟨714458197267627210,714458197267627413⟩⟩,⟨⟨268907732701577294,268907732701577300⟩,⟨181201987173529506,181201987173529512⟩⟩,⟨⟨47588612040436755,47588612040436756⟩,⟨(-27208501772773898),(-27208501772773896)⟩⟩]
lemma ha4_1_27_eq (j : Fin 7) : ha4_1_27 j = ((ha4_1_26 j).mul (piI.mul (atomPoints j).z)).scale 1 27 := by fin_cases j <;> decide +kernel
lemma ha4_1_27_contains (j : Fin 7) : (ha4_1_27 j).Contains (fullFactor true 4 27 ((j.val:ℝ)/6)) := by
  rw [ha4_1_27_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha4_1_26 j) true 4 26 j (ha4_1_26_contains j)
noncomputable def hk4_1_28 (j : Fin 6) (i k : Fin 16) : CBox := (kernel4_0 j i k).mul (mpower1_28 j i k)
lemma hk4_1_28_contains (j : Fin 6) (i k : Fin 16) :
    (hk4_1_28 j i k).Contains (fullFactor true 4 28 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk4_1_28,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel4_0 j i k) (mpower1_28 j i k) (quadraturePoint j.val (16*i.val+k.val)) 4 28 (kernel4_0_contains j i k) (mpower1_28_contains j i k)
noncomputable def ha4_1_28 : Fin 7 → CBox := ![⟨⟨941677354072,941677354073⟩,⟨(-1),1⟩⟩,⟨⟨(-12320102128234),(-12320102128227)⟩,⟨(-45849759527991),(-45849759527984)⟩⟩,⟨⟨(-13991190910553465),(-13991190910553253)⟩,⟨6358538834099595,6358538834099806⟩⟩,⟨⟨(-135504780116346921),(-135504780116346228)⟩,⟨(-155813428590181302),(-155813428590180609)⟩⟩,⟨⟨71651459405594189,71651459405594235⟩,⟨(-179623300255066272),(-179623300255066227)⟩⟩,⟨⟨19673953204478241,19673953204478243⟩,⟨(-43792470264598324),(-43792470264598321)⟩⟩,⟨⟨(-3828088631015248),(-3828088631015247)⟩,⟨(-5954810199424272),(-5954810199424271)⟩⟩]
lemma ha4_1_28_eq (j : Fin 7) : ha4_1_28 j = ((ha4_1_27 j).mul (piI.mul (atomPoints j).z)).scale 1 28 := by fin_cases j <;> decide +kernel
lemma ha4_1_28_contains (j : Fin 7) : (ha4_1_28 j).Contains (fullFactor true 4 28 ((j.val:ℝ)/6)) := by
  rw [ha4_1_28_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha4_1_27 j) true 4 27 j (ha4_1_27_contains j)
noncomputable def hk4_1_29 (j : Fin 6) (i k : Fin 16) : CBox := (kernel4_0 j i k).mul (mpower1_29 j i k)
lemma hk4_1_29_contains (j : Fin 6) (i k : Fin 16) :
    (hk4_1_29 j i k).Contains (fullFactor true 4 29 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk4_1_29,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel4_0 j i k) (mpower1_29 j i k) (quadraturePoint j.val (16*i.val+k.val)) 4 29 (kernel4_0_contains j i k) (mpower1_29_contains j i k)
noncomputable def ha4_1_29 : Fin 7 → CBox := ![⟨⟨(-299237087207),(-299237087205)⟩,⟨(-1),1⟩⟩,⟨⟨(-2621182983148),(-2621182983145)⟩,⟨13699972917322,13699972917326⟩⟩,⟨⟨3504610405587233,3504610405587308⟩,⟨1405179480039517,1405179480039591⟩⟩,⟨⟨(-14222824073209684),(-14222824073209493)⟩,⟨39074017855588667,39074017855588858⟩⟩,⟨⟨(-32359834766673598),(-32359834766673587)⟩,⟨(-2028815192965765),(-2028815192965755)⟩⟩,⟨⟨(-6646954125083435),(-6646954125083434)⟩,⟨(-1707953989515821),(-1707953989515819)⟩⟩,⟨⟨(-716695229083135),(-716695229083134)⟩,⟨515223531321514,515223531321515⟩⟩]
lemma ha4_1_29_eq (j : Fin 7) : ha4_1_29 j = ((ha4_1_28 j).mul (piI.mul (atomPoints j).z)).scale 1 29 := by fin_cases j <;> decide +kernel
lemma ha4_1_29_contains (j : Fin 7) : (ha4_1_29 j).Contains (fullFactor true 4 29 ((j.val:ℝ)/6)) := by
  rw [ha4_1_29_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha4_1_28 j) true 4 28 j (ha4_1_28_contains j)
noncomputable def hk4_1_30 (j : Fin 6) (i k : Fin 16) : CBox := (kernel4_0 j i k).mul (mpower1_30 j i k)
lemma hk4_1_30_contains (j : Fin 6) (i k : Fin 16) :
    (hk4_1_30 j i k).Contains (fullFactor true 4 30 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk4_1_30,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel4_0 j i k) (mpower1_30 j i k) (quadraturePoint j.val (16*i.val+k.val)) 4 30 (kernel4_0_contains j i k) (mpower1_30_contains j i k)
noncomputable def ha4_1_30 : Fin 7 → CBox := ![⟨⟨91919034518,91919034519⟩,⟨(-1),1⟩⟩,⟨⟨2367639582216,2367639582218⟩,⟨(-3176064807266),(-3176064807263)⟩⟩,⟨⟨(-333940667051865),(-333940667051839)⟩,⟨(-832258020107671),(-832258020107645)⟩⟩,⟨⟨7995048916627251,7995048916627303⟩,⟨(-1264160165897850),(-1264160165897798)⟩⟩,⟨⟨1322119342327348,1322119342327351⟩,⟨5085882174089953,5085882174089956⟩⟩,⟨⟨(-76533813201476),(-76533813201474)⟩,⟨945256531766263,945256531766264⟩⟩,⟨⟨66502061809075,66502061809077⟩,⟨83041996114203,83041996114204⟩⟩]
lemma ha4_1_30_eq (j : Fin 7) : ha4_1_30 j = ((ha4_1_29 j).mul (piI.mul (atomPoints j).z)).scale 1 30 := by fin_cases j <;> decide +kernel
lemma ha4_1_30_contains (j : Fin 7) : (ha4_1_30 j).Contains (fullFactor true 4 30 ((j.val:ℝ)/6)) := by
  rw [ha4_1_30_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha4_1_29 j) true 4 29 j (ha4_1_29_contains j)
end SharpPlanar.CachedData

end OAI
