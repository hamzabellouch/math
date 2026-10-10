import OAI.Analysis.PlanarPacking.Certificate.Powers30
import OAI.Analysis.PlanarPacking.Certificate.KernelValues30
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
noncomputable def hk28_0_0 (j : Fin 6) (i k : Fin 16) : CBox := (power28 j i k).conj.mul (mpower0_0 j i k)
lemma hk28_0_0_contains (j : Fin 6) (i k : Fin 16) :
    (hk28_0_0 j i k).Contains (fullFactor false 28 0 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk28_0_0,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power28 j i k) (mpower0_0 j i k) (quadraturePoint j.val (16*i.val+k.val)) 28 0 (power28_contains j i k) (mpower0_0_contains j i k)
noncomputable def ha28_0_0 : Fin 7 → CBox := ![⟨⟨999999999999999999999999999665,1000000000000000000000000000447⟩,⟨(-447),447⟩⟩,⟨⟨(-500000000000000000081972379005),(-499999999999999999937075927107)⟩,⟨866025403784438646686030283432,866025403784438646830418513450⟩⟩,⟨⟨(-500000000000000000178469317254),(-499999999999999999783434070433)⟩,⟨(-866025403784438646972424332367),(-866025403784438646577017098533)⟩⟩,⟨⟨999999999999999999908533101065,1000000000000000000091466898963⟩,⟨(-58474264911),124459533015⟩⟩,⟨⟨(-500000000000000000578565263118),(-499999999999999999497627961551)⟩,⟨866025403784438646201395401196,866025403784438647282060761459⟩⟩,⟨⟨(-500000000000000000632465456545),(-499999999999999999272293012623)⟩,⟨(-866025403784438647471438207249),(-866025403784438646110995857621)⟩⟩,⟨⟨999999999999999999816510462105,1000000000000000000183489538007⟩,⟨(-117504269735),249474806167⟩⟩]
lemma ha28_0_0_eq (j : Fin 7) : ha28_0_0 j = ((atomPoints j).direct.powBin 7 28).conj := by fin_cases j <;> decide +kernel
lemma ha28_0_0_contains (j : Fin 7) : (ha28_0_0 j).Contains (fullFactor false 28 0 ((j.val:ℝ)/6)) := by
  rw [ha28_0_0_eq]
  simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @direct_factor_zero_full ((atomPoints j).direct.powBin 7 28) ((j.val:ℝ)/6) 28 (@direct_power_bin_contains (atomPoints j) ((j.val:ℝ)/6) (atomPoints_contains j) 28 (by norm_num))
noncomputable def hk28_0_1 (j : Fin 6) (i k : Fin 16) : CBox := (power28 j i k).conj.mul (mpower0_1 j i k)
lemma hk28_0_1_contains (j : Fin 6) (i k : Fin 16) :
    (hk28_0_1 j i k).Contains (fullFactor false 28 1 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk28_0_1,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power28 j i k) (mpower0_1 j i k) (quadraturePoint j.val (16*i.val+k.val)) 28 1 (power28_contains j i k) (mpower0_1_contains j i k)
noncomputable def ha28_0_1 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-453449841058554462684503000348),(-453449841058554462607458124222)⟩,⟨(-261799387799149436582087303948),(-261799387799149436505386365809)⟩⟩,⟨⟨906899682117108925100757908173,906899682117108925517714146520⟩,⟨(-523598775598298873265225965327),(-523598775598298872849879355550)⟩⟩,⟨⟨(-195500577295),91851160535⟩,⟨1570796326794896619086324131129,1570796326794896619378675868915⟩⟩,⟨⟨(-1813799364234217851683929313649),(-1813799364234217849414815573092)⟩,⟨(-1047197551196597747368410920157),(-1047197551196597745101167796425)⟩⟩,⟨⟨2267249205292772311531854014714,2267249205292772315100700635769⟩,⟨(-1308996938995747184351624026611),(-1308996938995747180786534228741)⟩⟩,⟨⟨(-783748218310),369150550565⟩,⟨3141592653589793237883550615738,3141592653589793239046449384614⟩⟩]
lemma ha28_0_1_eq (j : Fin 7) : ha28_0_1 j = ((ha28_0_0 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 1 := by fin_cases j <;> decide +kernel
lemma ha28_0_1_contains (j : Fin 7) : (ha28_0_1 j).Contains (fullFactor false 28 1 ((j.val:ℝ)/6)) := by
  rw [ha28_0_1_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha28_0_0 j) false 28 0 j (ha28_0_0_contains j)
noncomputable def hk28_0_2 (j : Fin 6) (i k : Fin 16) : CBox := (power28 j i k).conj.mul (mpower0_2 j i k)
lemma hk28_0_2_contains (j : Fin 6) (i k : Fin 16) :
    (hk28_0_2 j i k).Contains (fullFactor false 28 2 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk28_0_2,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power28 j i k) (mpower0_2 j i k) (quadraturePoint j.val (16*i.val+k.val)) 28 2 (power28_contains j i k) (mpower0_2_contains j i k)
noncomputable def ha28_0_2 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨68538919452009434844276463328,68538919452009434864574888134⟩,⟨(-118712890786751174417635741025),(-118712890786751174397087564753)⟩⟩,⟨⟨274155677808037739292862278602,274155677808037739511209919558⟩,⟨474851563147004697528577091825,474851563147004697748406367174⟩⟩,⟨⟨(-1233700550136169827472932011816),(-1233700550136169827239392503075)⟩,⟨(-153545794351),72139732791⟩⟩,⟨⟨1096622711232150956544606174393,1096622711232150958922348280040⟩,⟨(-1899406252588018791672734149423),(-1899406252588018789290477799040)⟩⟩,⟨⟨1713472986300235868828736451777,1713472986300235873500882238350⟩,⟨2967822269668779357956577209225,2967822269668779362637633383625⟩⟩,⟨⟨(-4934802200544679310345841568918),(-4934802200544679308503456491064)⟩,⟨(-1231108822454),579860328862⟩⟩]
lemma ha28_0_2_eq (j : Fin 7) : ha28_0_2 j = ((ha28_0_1 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 2 := by fin_cases j <;> decide +kernel
lemma ha28_0_2_contains (j : Fin 7) : (ha28_0_2 j).Contains (fullFactor false 28 2 ((j.val:ℝ)/6)) := by
  rw [ha28_0_2_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha28_0_1 j) false 28 1 j (ha28_0_1_contains j)
noncomputable def hk28_0_3 (j : Fin 6) (i k : Fin 16) : CBox := (power28 j i k).conj.mul (mpower0_3 j i k)
lemma hk28_0_3_contains (j : Fin 6) (i k : Fin 16) :
    (hk28_0_3 j i k).Contains (fullFactor false 28 3 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk28_0_3,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power28 j i k) (mpower0_3 j i k) (quadraturePoint j.val (16*i.val+k.val)) 28 3 (power28_contains j i k) (mpower0_3_contains j i k)
noncomputable def ha28_0_3 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨20719308087892496640504348357,20719308087892496644156633276⟩,⟨11962298101967523214311714967,11962298101967523217892535604⟩⟩,⟨⟨(-165754464703139973180432521216),(-165754464703139973103170015424)⟩,⟨95698384815740185685087164696,95698384815740185761609487090⟩⟩,⟨⟨(-37772275762),80396389921⟩,⟨(-645964097506246253719378827787),(-645964097506246253595041659371)⟩⟩,⟨⟨1326035717625119784250217887610,1326035717625119785917567468026⟩,⟨765587078525921485043078389728,765587078525921486705492469363⟩⟩,⟨⟨(-2589913510986562082436596326071),(-2589913510986562078343360239613)⟩,⟨1495287262745940399800881521975,1495287262745940403882857524606⟩⟩,⟨⟨(-607228316421),1289214144131⟩,⟨(-5167712780049970030230577190131),(-5167712780049970028284786707572)⟩⟩]
lemma ha28_0_3_eq (j : Fin 7) : ha28_0_3 j = ((ha28_0_2 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 3 := by fin_cases j <;> decide +kernel
lemma ha28_0_3_contains (j : Fin 7) : (ha28_0_3 j).Contains (fullFactor false 28 3 ((j.val:ℝ)/6)) := by
  rw [ha28_0_3_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha28_0_2 j) false 28 2 j (ha28_0_2_contains j)
noncomputable def hk28_0_4 (j : Fin 6) (i k : Fin 16) : CBox := (power28 j i k).conj.mul (mpower0_4 j i k)
lemma hk28_0_4_contains (j : Fin 6) (i k : Fin 16) :
    (hk28_0_4 j i k).Contains (fullFactor false 28 4 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk28_0_4,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power28 j i k) (mpower0_4 j i k) (quadraturePoint j.val (16*i.val+k.val)) 28 4 (power28_contains j i k) (mpower0_4_contains j i k)
noncomputable def ha28_0_4 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1565861159883012430126711159),(-1565861159883012429652998541)⟩,⟨2712151086516110563143509538,2712151086516110563630225562⟩⟩,⟨⟨(-25053778558128198886862604375),(-25053778558128198866749358564)⟩,⟨(-43394417384257769025199173665),(-43394417384257769004833768227)⟩⟩,⟨⟨253669507901048013612507237786,253669507901048013662141784767⟩,⟨(-14833138006),31571588494⟩⟩,⟨⟨(-400860456930051182510566957331),(-400860456930051181638853002231)⟩,⟨694310678148124303776196521192,694310678148124304651428779524⟩⟩,⟨⟨(-978663224926882769906689134918),(-978663224926882767231926906869)⟩,⟨(-1695094429072569103523575777411),(-1695094429072569100839163370380)⟩⟩,⟨⟨4058712126416768217426622403947,4058712126416768218967761957256⟩,⟨(-476916004480),1012546421027⟩⟩]
lemma ha28_0_4_eq (j : Fin 7) : ha28_0_4 j = ((ha28_0_3 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 4 := by fin_cases j <;> decide +kernel
lemma ha28_0_4_contains (j : Fin 7) : (ha28_0_4 j).Contains (fullFactor false 28 4 ((j.val:ℝ)/6)) := by
  rw [ha28_0_4_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha28_0_3 j) false 28 3 j (ha28_0_3_contains j)
noncomputable def hk28_0_5 (j : Fin 6) (i k : Fin 16) : CBox := (power28 j i k).conj.mul (mpower0_5 j i k)
lemma hk28_0_5_contains (j : Fin 6) (i k : Fin 16) :
    (hk28_0_5 j i k).Contains (fullFactor false 28 5 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk28_0_5,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power28 j i k) (mpower0_5 j i k) (quadraturePoint j.val (16*i.val+k.val)) 28 5 (power28_contains j i k) (mpower0_5_contains j i k)
noncomputable def ha28_0_5 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-284015797627486289512422388),(-284015797627486289460549554)⟩,⟨(-163976597214335483815851467),(-163976597214335483765722443)⟩⟩,⟨⟨9088505524079561261593546636,9088505524079561265887796790⟩,⟨(-5247251110858735483119934246),(-5247251110858735478890723374)⟩⟩,⟨⟨(-9918507048),4659967739⟩,⟨79692626246167045112881039231,79692626246167045128727861556⟩⟩,⟨⟨(-290832176770545960612392863428),(-290832176770545960244850684794)⟩,⟨(-167912035547479535594199745229),(-167912035547479535228522576968)⟩⟩,⟨⟨887549367585894653974891180564,887549367585894655383271387470⟩,⟨(-512426866294798387488710716607),(-512426866294798386086577383608)⟩⟩,⟨⟨(-636201679544),299655163211⟩,⟨2550164039877345443377520430689,2550164039877345444353964394709⟩⟩]
lemma ha28_0_5_eq (j : Fin 7) : ha28_0_5 j = ((ha28_0_4 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 5 := by fin_cases j <;> decide +kernel
lemma ha28_0_5_contains (j : Fin 7) : (ha28_0_5 j).Contains (fullFactor false 28 5 ((j.val:ℝ)/6)) := by
  rw [ha28_0_5_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha28_0_4 j) false 28 4 j (ha28_0_4_contains j)
noncomputable def hk28_0_6 (j : Fin 6) (i k : Fin 16) : CBox := (power28 j i k).conj.mul (mpower0_6 j i k)
lemma hk28_0_6_contains (j : Fin 6) (i k : Fin 16) :
    (hk28_0_6 j i k).Contains (fullFactor false 28 6 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk28_0_6,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power28 j i k) (mpower0_6 j i k) (quadraturePoint j.val (16*i.val+k.val)) 28 6 (power28_contains j i k) (mpower0_6_contains j i k)
noncomputable def ha28_0_6 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨14309657588033580843841342,14309657588033580848261475⟩,⟨(-24785053981387676529161456),(-24785053981387676524555803)⟩⟩,⟨⟨915818085634149173724429956,915818085634149174465481641⟩,⟨1586243454808811297371898951,1586243454808811298126436163⟩⟩,⟨⟨(-20863480763352960875253089173),(-20863480763352960871037990267)⟩,⟨(-2596659074),1219976702⟩⟩,⟨⟨58612357480585547084859977557,58612357480585547212691958197⟩,⟨(-101519581107763923116388956524),(-101519581107763922987769386518)⟩⟩,⟨⟨223588399813024700387745484922,223588399813024701000253269224⟩,⟨387266468459182445439042380488,387266468459182446054796881205⟩⟩,⟨⟨(-1335262768854589496139072110843),(-1335262768854589495623556973441)⟩,⟨(-333114420443),156899076559⟩⟩]
lemma ha28_0_6_eq (j : Fin 7) : ha28_0_6 j = ((ha28_0_5 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 6 := by fin_cases j <;> decide +kernel
lemma ha28_0_6_contains (j : Fin 7) : (ha28_0_6 j).Contains (fullFactor false 28 6 ((j.val:ℝ)/6)) := by
  rw [ha28_0_6_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha28_0_5 j) false 28 5 j (ha28_0_5_contains j)
noncomputable def hk28_0_7 (j : Fin 6) (i k : Fin 16) : CBox := (power28 j i k).conj.mul (mpower0_7 j i k)
lemma hk28_0_7_contains (j : Fin 6) (i k : Fin 16) :
    (hk28_0_7 j i k).Contains (fullFactor false 28 7 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk28_0_7,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power28 j i k) (mpower0_7 j i k) (quadraturePoint j.val (16*i.val+k.val)) 28 7 (power28_contains j i k) (mpower0_7_contains j i k)
noncomputable def ha28_0_7 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1853917702541761442080324,1853917702541761442430728⟩,⟨1070359884617898513961750,1070359884617898514295784⟩⟩,⟨⟨(-237301465925345464670044497),(-237301465925345464556410639)⟩,⟨137006065231091009745004392,137006065231091009856301570⟩⟩,⟨⟨(-273762132),582688934⟩,⟨(-4681754135318688101190431783),(-4681754135318688100229663313)⟩⟩,⟨⟨30374587638444219450046174469,30374587638444219488625745142⟩,⟨17536776349579649237336326611,17536776349579649275639387073⟩⟩,⟨⟨(-144837320511075112797107148009),(-144837320511075112566354471751)⟩,⟨83621865985773321292081019427,83621865985773321521424571741⟩⟩,⟨⟨(-70416140897),149501402296⟩,⟨(-599264529320792077007521171588),(-599264529320792076774251000706)⟩⟩]
lemma ha28_0_7_eq (j : Fin 7) : ha28_0_7 j = ((ha28_0_6 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 7 := by fin_cases j <;> decide +kernel
lemma ha28_0_7_contains (j : Fin 7) : (ha28_0_7 j).Contains (fullFactor false 28 7 ((j.val:ℝ)/6)) := by
  rw [ha28_0_7_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha28_0_6 j) false 28 6 j (ha28_0_6_contains j)
noncomputable def hk28_0_8 (j : Fin 6) (i k : Fin 16) : CBox := (power28 j i k).conj.mul (mpower0_8 j i k)
lemma hk28_0_8_contains (j : Fin 6) (i k : Fin 16) :
    (hk28_0_8 j i k).Contains (fullFactor false 28 8 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk28_0_8,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power28 j i k) (mpower0_8 j i k) (quadraturePoint j.val (16*i.val+k.val)) 28 8 (power28_contains j i k) (mpower0_8_contains j i k)
noncomputable def ha28_0_8 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-70054890629433514739343),(-70054890629433514717256)⟩,⟨121338629888859693702888,121338629888859693726209⟩⟩,⟨⟨(-17934052001134979776732702),(-17934052001134979762106849)⟩,⟨(-31062689251548081599002947),(-31062689251548081584029433)⟩⟩,⟨⟨919260274839426580151446499,919260274839426580343019045⟩,⟨(-53753069),114410705⟩⟩,⟨⟨(-4591117312290554826517346373),(-4591117312290554816475014612)⟩,⟨7952048448396308882062488500,7952048448396308892187908641⟩⟩,⟨⟨(-27365191652122466725184146138),(-27365191652122466650044538038)⟩,⟨(-47397902300335817896883587721),(-47397902300335817821219078789)⟩⟩,⟨⟨235330630358893204497114558321,235330630358893204589468620876⟩,⟨(-27652353868),58709063395⟩⟩]
lemma ha28_0_8_eq (j : Fin 7) : ha28_0_8 j = ((ha28_0_7 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 8 := by fin_cases j <;> decide +kernel
lemma ha28_0_8_contains (j : Fin 7) : (ha28_0_8 j).Contains (fullFactor false 28 8 ((j.val:ℝ)/6)) := by
  rw [ha28_0_8_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha28_0_7 j) false 28 7 j (ha28_0_7_contains j)
noncomputable def hk28_0_9 (j : Fin 6) (i k : Fin 16) : CBox := (power28 j i k).conj.mul (mpower0_9 j i k)
lemma hk28_0_9_contains (j : Fin 6) (i k : Fin 16) :
    (hk28_0_9 j i k).Contains (fullFactor false 28 9 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk28_0_9,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power28 j i k) (mpower0_9 j i k) (quadraturePoint j.val (16*i.val+k.val)) 28 9 (power28_contains j i k) (mpower0_9_contains j i k)
noncomputable def ha28_0_9 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-7059195338064676367255),(-7059195338064676365875)⟩,⟨(-4075628328693792153187),(-4075628328693792151888)⟩⟩,⟨⟨3614308013089114298873283,3614308013089114300627036⟩,⟨(-2086721704291221582834290),(-2086721704291221581125852)⟩⟩,⟨⟨(-19968436),9381681⟩,⟨160441184787359821856770833,160441184787359821890717251⟩⟩,⟨⟨(-1850525702701626522582674118),(-1850525702701626520220491449)⟩,⟨(-1068401512597105451266082490),(-1068401512597105448925724944)⟩⟩,⟨⟨13787490894657571017945747311,13787490894657571039999547721⟩,⟨(-7960211579480062807956759526),(-7960211579480062786074195385)⟩⟩,⟨⟨(-20493329141),9652492419⟩,⟨82145886611128228783107385695,82145886611128228815606513558⟩⟩]
lemma ha28_0_9_eq (j : Fin 7) : ha28_0_9 j = ((ha28_0_8 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 9 := by fin_cases j <;> decide +kernel
lemma ha28_0_9_contains (j : Fin 7) : (ha28_0_9 j).Contains (fullFactor false 28 9 ((j.val:ℝ)/6)) := by
  rw [ha28_0_9_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha28_0_8 j) false 28 8 j (ha28_0_8_contains j)
noncomputable def hk28_0_10 (j : Fin 6) (i k : Fin 16) : CBox := (power28 j i k).conj.mul (mpower0_10 j i k)
lemma hk28_0_10_contains (j : Fin 6) (i k : Fin 16) :
    (hk28_0_10 j i k).Contains (fullFactor false 28 10 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk28_0_10,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power28 j i k) (mpower0_10 j i k) (quadraturePoint j.val (16*i.val+k.val)) 28 10 (power28_contains j i k) (mpower0_10_contains j i k)
noncomputable def ha28_0_10 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨213399400269781075697,213399400269781075766⟩,⟨(-369618603571988403228),(-369618603571988403153)⟩⟩,⟨⟨218520985876255821446623,218520985876255821626227⟩,⟨378489450057716124781643,378489450057716124966501⟩⟩,⟨⟨(-25202042373060605483948327),(-25202042373060605478535815)⟩,⟨(-3136635),1473672⟩⟩,⟨⟨223765489537285961033435568,223765489537285961524311175⟩,⟨(-387573196859101312104268822),(-387573196859101311608300756)⟩⟩,⟨⟨2083978518259580814583145070,2083978518259580820318620476⟩,⟨3609556675507699247150161869,3609556675507699252935322891⟩⟩,⟨⟨(-25806891390014060017937904635),(-25806891390014060007645856613)⟩,⟨(-6438169228),3032419928⟩⟩]
lemma ha28_0_10_eq (j : Fin 7) : ha28_0_10 j = ((ha28_0_9 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 10 := by fin_cases j <;> decide +kernel
lemma ha28_0_10_contains (j : Fin 7) : (ha28_0_10 j).Contains (fullFactor false 28 10 ((j.val:ℝ)/6)) := by
  rw [ha28_0_10_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha28_0_9 j) false 28 9 j (ha28_0_9_contains j)
noncomputable def hk28_0_11 (j : Fin 6) (i k : Fin 16) : CBox := (power28 j i k).conj.mul (mpower0_11 j i k)
lemma hk28_0_11_contains (j : Fin 6) (i k : Fin 16) :
    (hk28_0_11 j i k).Contains (fullFactor false 28 11 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk28_0_11,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power28 j i k) (mpower0_11 j i k) (quadraturePoint j.val (16*i.val+k.val)) 28 11 (power28_contains j i k) (mpower0_11_contains j i k)
noncomputable def ha28_0_11 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨17593804388058740562,17593804388058740567⟩,⟨10157787699515332859,10157787699515332863⟩⟩,⟨⟨(-36032111386744300685778),(-36032111386744300668064)⟩,⟨20803149208607401688988,20803149208607401706153⟩⟩,⟨⟨(-210440),447911⟩,⟨(-3598843235212085340880416),(-3598843235212085340096055)⟩⟩,⟨⟨73793764120052327736189438,73793764120052327830856431⟩,⟨42604849579227958634695066,42604849579227958728293180⟩⟩,⟨⟨(-859072479885680692351809997),(-859072479885680690972210380)⟩,⟨495985727515397111599966228,495985727515397112966584956⟩⟩,⟨⟨(-866057107),1838736832⟩,⟨(-7370430945714350778801338336),(-7370430945714350775838475483)⟩⟩]
lemma ha28_0_11_eq (j : Fin 7) : ha28_0_11 j = ((ha28_0_10 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 11 := by fin_cases j <;> decide +kernel
lemma ha28_0_11_contains (j : Fin 7) : (ha28_0_11 j).Contains (fullFactor false 28 11 ((j.val:ℝ)/6)) := by
  rw [ha28_0_11_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha28_0_10 j) false 28 10 j (ha28_0_10_contains j)
noncomputable def hk28_0_12 (j : Fin 6) (i k : Fin 16) : CBox := (power28 j i k).conj.mul (mpower0_12 j i k)
lemma hk28_0_12_contains (j : Fin 6) (i k : Fin 16) :
    (hk28_0_12 j i k).Contains (fullFactor false 28 12 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk28_0_12,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power28 j i k) (mpower0_12 j i k) (quadraturePoint j.val (16*i.val+k.val)) 28 12 (power28_contains j i k) (mpower0_12_contains j i k)
noncomputable def ha28_0_12 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-443217100187807443),(-443217100187807442)⟩,⟨767674536308627877,767674536308627878⟩⟩,⟨⟨(-1815417242369259286211),(-1815417242369259284707)⟩,⟨(-3144394900720139785772),(-3144394900720139784215)⟩⟩,⟨⟨471087477881817150319182,471087477881817150423355⟩,⟨(-27547),58632⟩⟩,⟨⟨(-7435949024744486042269620),(-7435949024744486025909997)⟩,⟨12879441513349692550559993,12879441513349692567123497⟩⟩,⟨⟨(-108207299850538926593016624),(-108207299850538926294522233)⟩,⟨(-187420541090973602985321468),(-187420541090973602683742943)⟩⟩,⟨⟨1929574309403923047529805991,1929574309403923048311623699⟩,⟨(-226733221),481380177⟩⟩]
lemma ha28_0_12_eq (j : Fin 7) : ha28_0_12 j = ((ha28_0_11 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 12 := by fin_cases j <;> decide +kernel
lemma ha28_0_12_contains (j : Fin 7) : (ha28_0_12 j).Contains (fullFactor false 28 12 ((j.val:ℝ)/6)) := by
  rw [ha28_0_12_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha28_0_11 j) false 28 11 j (ha28_0_11_contains j)
noncomputable def hk28_0_13 (j : Fin 6) (i k : Fin 16) : CBox := (power28 j i k).conj.mul (mpower0_13 j i k)
lemma hk28_0_13_contains (j : Fin 6) (i k : Fin 16) :
    (hk28_0_13 j i k).Contains (fullFactor false 28 13 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk28_0_13,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power28 j i k) (mpower0_13 j i k) (quadraturePoint j.val (16*i.val+k.val)) 28 13 (power28_contains j i k) (mpower0_13_contains j i k)
noncomputable def ha28_0_13 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-30919495943783800),(-30919495943783799)⟩,⟨(-17851379306351119),(-17851379306351118)⟩⟩,⟨⟨253292510771476882223,253292510771476882350⟩,⟨(-146238499277628361569),(-146238499277628361446)⟩⟩,⟨⟨(-7085),3329⟩,⟨56921729219679268111923,56921729219679268124692⟩⟩,⟨⟨(-2074972248239938620950122),(-2074972248239938618275014)⟩,⟨(-1197985786082331538926009),(-1197985786082331536286540)⟩⟩,⟨⟨37743525322001707864881970,37743525322001707925735245⟩,⟨(-21791234504823142543594298),(-21791234504823142483412896)⟩⟩,⟨⟨(-116330803),54792571⟩,⟨466302805767612564329966623,466302805767612564520385740⟩⟩]
lemma ha28_0_13_eq (j : Fin 7) : ha28_0_13 j = ((ha28_0_12 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 13 := by fin_cases j <;> decide +kernel
lemma ha28_0_13_contains (j : Fin 7) : (ha28_0_13 j).Contains (fullFactor false 28 13 ((j.val:ℝ)/6)) := by
  rw [ha28_0_13_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha28_0_12 j) false 28 12 j (ha28_0_12_contains j)
noncomputable def hk28_0_14 (j : Fin 6) (i k : Fin 16) : CBox := (power28 j i k).conj.mul (mpower0_14 j i k)
lemma hk28_0_14_contains (j : Fin 6) (i k : Fin 16) :
    (hk28_0_14 j i k).Contains (fullFactor false 28 14 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk28_0_14,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power28 j i k) (mpower0_14 j i k) (quadraturePoint j.val (16*i.val+k.val)) 28 14 (power28_contains j i k) (mpower0_14_contains j i k)
noncomputable def ha28_0_14 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨667640024824732,667640024824733⟩,⟨(-1156386444162984),(-1156386444162983)⟩⟩,⟨⟨10938614166728417753,10938614166728417764⟩,⟨18946235501166317746,18946235501166317757⟩⟩,⟨⟨(-6386603083791852241884),(-6386603083791852240430)⟩,⟨(-795),374⟩⟩,⟨⟨179218254507678396376692,179218254507678396772127⟩,⟨(-310415122451108950227270),(-310415122451108949826086)⟩⟩,⟨⟨4074951323393142872553753,4074951323393142883820621⟩,⟨7058022730486958375733685,7058022730486958387135688⟩⟩,⟨⟨(-104638104924845707140647138),(-104638104924845707097584113)⟩,⟨(-26104572),12295425⟩⟩]
lemma ha28_0_14_eq (j : Fin 7) : ha28_0_14 j = ((ha28_0_13 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 14 := by fin_cases j <;> decide +kernel
lemma ha28_0_14_contains (j : Fin 7) : (ha28_0_14 j).Contains (fullFactor false 28 14 ((j.val:ℝ)/6)) := by
  rw [ha28_0_14_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha28_0_13 j) false 28 13 j (ha28_0_13_contains j)
noncomputable def hk28_0_15 (j : Fin 6) (i k : Fin 16) : CBox := (power28 j i k).conj.mul (mpower0_15 j i k)
lemma hk28_0_15_contains (j : Fin 6) (i k : Fin 16) :
    (hk28_0_15 j i k).Contains (fullFactor false 28 15 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk28_0_15,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power28 j i k) (mpower0_15 j i k) (quadraturePoint j.val (16*i.val+k.val)) 28 15 (power28_contains j i k) (mpower0_15_contains j i k)
noncomputable def ha28_0_15 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨40365501752147,40365501752148⟩,⟨23305033302576,23305033302577⟩⟩,⟨⟨(-1322696761414360854),(-1322696761414360852)⟩,⟨763659331258827442,763659331258827444⟩⟩,⟨⟨(-40),84⟩,⟨(-668803510981146723333),(-668803510981146723178)⟩⟩,⟨⟨43342127478025776391714,43342127478025776447869⟩,⟨25023588966689257638269,25023588966689257693563⟩⟩,⟨⟨(-1231857353275977870263944),(-1231857353275977868269997)⟩,⟨711213174517105745365838,711213174517105747334542⟩⟩,⟨⟨(-2575148),5467329⟩,⟨(-21915353447830215832175673),(-21915353447830215823086815)⟩⟩]
lemma ha28_0_15_eq (j : Fin 7) : ha28_0_15 j = ((ha28_0_14 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 15 := by fin_cases j <;> decide +kernel
lemma ha28_0_15_contains (j : Fin 7) : (ha28_0_15 j).Contains (fullFactor false 28 15 ((j.val:ℝ)/6)) := by
  rw [ha28_0_15_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha28_0_14 j) false 28 14 j (ha28_0_14_contains j)
noncomputable def hk28_0_16 (j : Fin 6) (i k : Fin 16) : CBox := (power28 j i k).conj.mul (mpower0_16 j i k)
lemma hk28_0_16_contains (j : Fin 6) (i k : Fin 16) :
    (hk28_0_16 j i k).Contains (fullFactor false 28 16 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk28_0_16,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power28 j i k) (mpower0_16 j i k) (quadraturePoint j.val (16*i.val+k.val)) 28 16 (power28_contains j i k) (mpower0_16_contains j i k)
noncomputable def ha28_0_16 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-762655431407),(-762655431406)⟩,⟨1320957955864,1320957955865⟩⟩,⟨⟨(-49981386352667222),(-49981386352667221)⟩,⟨(-86570300595549325),(-86570300595549323)⟩⟩,⟨⟨65659631149794723615,65659631149794723631⟩,⟨(-4),9⟩⟩,⟨⟨(-3275580136008399053289),(-3275580136008399046040)⟩,⟨5673471219829920490993,5673471219829920498363⟩⟩,⟨⟨(-116371983552042445838086),(-116371983552042445515586)⟩,⟨(-201562188089707223767371),(-201562188089707223440470)⟩⟩,⟨⟨4303069587032947006450324,4303069587032947008248615⟩,⟨(-505630),1073508⟩⟩]
lemma ha28_0_16_eq (j : Fin 7) : ha28_0_16 j = ((ha28_0_15 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 16 := by fin_cases j <;> decide +kernel
lemma ha28_0_16_contains (j : Fin 7) : (ha28_0_16 j).Contains (fullFactor false 28 16 ((j.val:ℝ)/6)) := by
  rw [ha28_0_16_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha28_0_15 j) false 28 15 j (ha28_0_15_contains j)
noncomputable def hk28_0_17 (j : Fin 6) (i k : Fin 16) : CBox := (power28 j i k).conj.mul (mpower0_17 j i k)
lemma hk28_0_17_contains (j : Fin 6) (i k : Fin 16) :
    (hk28_0_17 j i k).Contains (fullFactor false 28 17 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk28_0_17,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power28 j i k) (mpower0_17 j i k) (quadraturePoint j.val (16*i.val+k.val)) 28 17 (power28_contains j i k) (mpower0_17_contains j i k)
noncomputable def ha28_0_17 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-40685409901),(-40685409900)⟩,⟨(-23489732359),(-23489732358)⟩⟩,⟨⟨5332718046471330,5332718046471331⟩,⟨(-3078846199642598),(-3078846199642597)⟩⟩,⟨⟨(-1),1⟩,⟨6066935731106195666,6066935731106195668⟩⟩,⟨⟨(-698970019787090239661),(-698970019787090238750)⟩,⟨(-403550529079554597192),(-403550529079554596297)⟩⟩,⟨⟨31040504379613153615005,31040504379613153665448⟩,⟨(-17921243559351411766443),(-17921243559351411716720)⟩⟩,⟨⟨(-198384),93441⟩,⟨795205400147551278321034,795205400147551278655889⟩⟩]
lemma ha28_0_17_eq (j : Fin 7) : ha28_0_17 j = ((ha28_0_16 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 17 := by fin_cases j <;> decide +kernel
lemma ha28_0_17_contains (j : Fin 7) : (ha28_0_17 j).Contains (fullFactor false 28 17 ((j.val:ℝ)/6)) := by
  rw [ha28_0_17_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha28_0_16 j) false 28 16 j (ha28_0_16_contains j)
noncomputable def hk28_0_18 (j : Fin 6) (i k : Fin 16) : CBox := (power28 j i k).conj.mul (mpower0_18 j i k)
lemma hk28_0_18_contains (j : Fin 6) (i k : Fin 16) :
    (hk28_0_18 j i k).Contains (fullFactor false 28 18 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk28_0_18,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power28 j i k) (mpower0_18 j i k) (quadraturePoint j.val (16*i.val+k.val)) 28 18 (power28_contains j i k) (mpower0_18_contains j i k)
noncomputable def ha28_0_18 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨683288616,683288617⟩,⟨(-1183490601),(-1183490600)⟩⟩,⟨⟨179120011154259,179120011154260⟩,⟨310244959971482,310244959971483⟩⟩,⟨⟨(-529440020073462377),(-529440020073462376)⟩,⟨(-1),1⟩⟩,⟨⟨46955236204022331321,46955236204022331426⟩,⟨(-81328854786764263435),(-81328854786764263328)⟩⟩,⟨⟨2606539218020916331968,2606539218020916339210⟩,⟨4514658357533078054654,4514658357533078062006⟩⟩,⟨⟨(-138789524622137721175998),(-138789524622137721117112)⟩,⟨(-34625),16309⟩⟩]
lemma ha28_0_18_eq (j : Fin 7) : ha28_0_18 j = ((ha28_0_17 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 18 := by fin_cases j <;> decide +kernel
lemma ha28_0_18_contains (j : Fin 7) : (ha28_0_18 j).Contains (fullFactor false 28 18 ((j.val:ℝ)/6)) := by
  rw [ha28_0_18_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha28_0_17 j) false 28 17 j (ha28_0_17_contains j)
noncomputable def hk28_0_19 (j : Fin 6) (i k : Fin 16) : CBox := (power28 j i k).conj.mul (mpower0_19 j i k)
lemma hk28_0_19_contains (j : Fin 6) (i k : Fin 16) :
    (hk28_0_19 j i k).Contains (fullFactor false 28 19 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk28_0_19,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power28 j i k) (mpower0_19 j i k) (quadraturePoint j.val (16*i.val+k.val)) 28 19 (power28_contains j i k) (mpower0_19_contains j i k)
noncomputable def ha28_0_19 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨32614433,32614434⟩,⟨18829951,18829952⟩⟩,⟨⟨(-17099355913328),(-17099355913327)⟩,⟨9872317739528,9872317739529⟩⟩,⟨⟨(-1),1⟩,⟨(-43770654673137423),(-43770654673137422)⟩⟩,⟨⟨8964987113086656138,8964987113086656151⟩,⟨5175937723022106875,5175937723022106888⟩⟩,⟨⟨(-622070944276038606025),(-622070944276038605009)⟩,⟨359152827132815576991,359152827132815577991⟩⟩,⟨⟨(-2697),5726⟩,⟨(-22948428997269873115436),(-22948428997269873105626)⟩⟩]
lemma ha28_0_19_eq (j : Fin 7) : ha28_0_19 j = ((ha28_0_18 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 19 := by fin_cases j <;> decide +kernel
lemma ha28_0_19_contains (j : Fin 7) : (ha28_0_19 j).Contains (fullFactor false 28 19 ((j.val:ℝ)/6)) := by
  rw [ha28_0_19_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha28_0_18 j) false 28 18 j (ha28_0_18_contains j)
noncomputable def hk28_0_20 (j : Fin 6) (i k : Fin 16) : CBox := (power28 j i k).conj.mul (mpower0_20 j i k)
lemma hk28_0_20_contains (j : Fin 6) (i k : Fin 16) :
    (hk28_0_20 j i k).Contains (fullFactor false 28 20 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk28_0_20,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power28 j i k) (mpower0_20 j i k) (quadraturePoint j.val (16*i.val+k.val)) 28 20 (power28_contains j i k) (mpower0_20_contains j i k)
noncomputable def ha28_0_20 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-492967),(-492966)⟩,⟨853843,853844⟩⟩,⟨⟨(-516913348074),(-516913348073)⟩,⟨(-895320181974),(-895320181973)⟩⟩,⟨⟨3437739179098606,3437739179098608⟩,⟨(-1),1⟩⟩,⟨⟨(-542022930869484435),(-542022930869484432)⟩,⟨938811255133340261,938811255133340264⟩⟩,⟨⟨(-47012995134852432669),(-47012995134852432537)⟩,⟨(-81428896189552855226),(-81428896189552855092)⟩⟩,⟨⟨3604730797462500933137,3604730797462500934690⟩,⟨(-424),900⟩⟩]
lemma ha28_0_20_eq (j : Fin 7) : ha28_0_20 j = ((ha28_0_19 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 20 := by fin_cases j <;> decide +kernel
lemma ha28_0_20_contains (j : Fin 7) : (ha28_0_20 j).Contains (fullFactor false 28 20 ((j.val:ℝ)/6)) := by
  rw [ha28_0_20_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha28_0_19 j) false 28 19 j (ha28_0_19_contains j)
noncomputable def hk28_0_21 (j : Fin 6) (i k : Fin 16) : CBox := (power28 j i k).conj.mul (mpower0_21 j i k)
lemma hk28_0_21_contains (j : Fin 6) (i k : Fin 16) :
    (hk28_0_21 j i k).Contains (fullFactor false 28 21 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk28_0_21,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power28 j i k) (mpower0_21 j i k) (quadraturePoint j.val (16*i.val+k.val)) 28 21 (power28_contains j i k) (mpower0_21_contains j i k)
noncomputable def ha28_0_21 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-21290),(-21289)⟩,⟨(-12292),(-12291)⟩⟩,⟨⟨44646528671,44646528672⟩,⟨(-25776685347),(-25776685346)⟩⟩,⟨⟨(-1),1⟩,⟨257142289286047,257142289286048⟩⟩,⟨⟨(-93630556896327456),(-93630556896327454)⟩,⟨(-54057627228469228),(-54057627228469227)⟩⟩,⟨⟨10151445319802585607,10151445319802585624⟩,⟨(-5860939688051789420),(-5860939688051789402)⟩⟩,⟨⟨(-135),64⟩,⟨539266466260812848826,539266466260812849061⟩⟩]
lemma ha28_0_21_eq (j : Fin 7) : ha28_0_21 j = ((ha28_0_20 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 21 := by fin_cases j <;> decide +kernel
lemma ha28_0_21_contains (j : Fin 7) : (ha28_0_21 j).Contains (fullFactor false 28 21 ((j.val:ℝ)/6)) := by
  rw [ha28_0_21_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha28_0_20 j) false 28 20 j (ha28_0_20_contains j)
noncomputable def hk28_0_22 (j : Fin 6) (i k : Fin 16) : CBox := (power28 j i k).conj.mul (mpower0_22 j i k)
lemma hk28_0_22_contains (j : Fin 6) (i k : Fin 16) :
    (hk28_0_22 j i k).Contains (fullFactor false 28 22 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk28_0_22,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power28 j i k) (mpower0_22 j i k) (quadraturePoint j.val (16*i.val+k.val)) 28 22 (power28_contains j i k) (mpower0_22_contains j i k)
noncomputable def ha28_0_22 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨292,293⟩,⟨(-507),(-506)⟩⟩,⟨⟨1226967353,1226967354⟩,⟨2125169795,2125169796⟩⟩,⟨⟨(-18359916521553),(-18359916521552)⟩,⟨(-1),1⟩⟩,⟨⟨5146274077922863,5146274077922864⟩,⟨(-8913608172637076),(-8913608172637075)⟩⟩,⟨⟨697450191936225608,697450191936225611⟩,⟨1208019168182208036,1208019168182208039⟩⟩,⟨⟨(-77007071306013533817),(-77007071306013533782)⟩,⟨(-20),10⟩⟩]
lemma ha28_0_22_eq (j : Fin 7) : ha28_0_22 j = ((ha28_0_21 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 22 := by fin_cases j <;> decide +kernel
lemma ha28_0_22_contains (j : Fin 7) : (ha28_0_22 j).Contains (fullFactor false 28 22 ((j.val:ℝ)/6)) := by
  rw [ha28_0_22_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha28_0_21 j) false 28 21 j (ha28_0_21_contains j)
noncomputable def hk28_0_23 (j : Fin 6) (i k : Fin 16) : CBox := (power28 j i k).conj.mul (mpower0_23 j i k)
lemma hk28_0_23_contains (j : Fin 6) (i k : Fin 16) :
    (hk28_0_23 j i k).Contains (fullFactor false 28 23 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk28_0_23,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power28 j i k) (mpower0_23 j i k) (quadraturePoint j.val (16*i.val+k.val)) 28 23 (power28_contains j i k) (mpower0_23_contains j i k)
noncomputable def ha28_0_23 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨11,12⟩,⟨6,7⟩⟩,⟨⟨(-96759679),(-96759678)⟩,⟨55864226,55864227⟩⟩,⟨⟨(-1),1⟩,⟨(-1253899540536),(-1253899540535)⟩⟩,⟨⟨811679013105350,811679013105351⟩,⟨468623096711943,468623096711944⟩⟩,⟨⟨(-137503773339017308),(-137503773339017306)⟩,⟨79387840551870928,79387840551870929⟩⟩,⟨⟨(-2),3⟩,⟨(-10518471716932064458),(-10518471716932064452)⟩⟩]
lemma ha28_0_23_eq (j : Fin 7) : ha28_0_23 j = ((ha28_0_22 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 23 := by fin_cases j <;> decide +kernel
lemma ha28_0_23_contains (j : Fin 7) : (ha28_0_23 j).Contains (fullFactor false 28 23 ((j.val:ℝ)/6)) := by
  rw [ha28_0_23_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha28_0_22 j) false 28 22 j (ha28_0_22_contains j)
noncomputable def hk28_0_24 (j : Fin 6) (i k : Fin 16) : CBox := (power28 j i k).conj.mul (mpower0_24 j i k)
lemma hk28_0_24_contains (j : Fin 6) (i k : Fin 16) :
    (hk28_0_24 j i k).Contains (fullFactor false 28 24 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk28_0_24,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power28 j i k) (mpower0_24 j i k) (quadraturePoint j.val (16*i.val+k.val)) 28 24 (power28_contains j i k) (mpower0_24_contains j i k)
noncomputable def ha28_0_24 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),0⟩,⟨0,1⟩⟩,⟨⟨(-2437537),(-2437536)⟩,⟨(-4221938),(-4221937)⟩⟩,⟨⟨82067533018,82067533019⟩,⟨(-1),1⟩⟩,⟨⟨(-40895079942577),(-40895079942576)⟩,⟨70832356240132,70832356240133⟩⟩,⟨⟨(-8659870022990125),(-8659870022990124)⟩,⟨(-14999334866761558),(-14999334866761557)⟩⟩,⟨⟨1376864728037741370,1376864728037741371⟩,⟨(-1),1⟩⟩]
lemma ha28_0_24_eq (j : Fin 7) : ha28_0_24 j = ((ha28_0_23 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 24 := by fin_cases j <;> decide +kernel
lemma ha28_0_24_contains (j : Fin 7) : (ha28_0_24 j).Contains (fullFactor false 28 24 ((j.val:ℝ)/6)) := by
  rw [ha28_0_24_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha28_0_23 j) false 28 23 j (ha28_0_23_contains j)
noncomputable def hk28_0_25 (j : Fin 6) (i k : Fin 16) : CBox := (power28 j i k).conj.mul (mpower0_25 j i k)
lemma hk28_0_25_contains (j : Fin 6) (i k : Fin 16) :
    (hk28_0_25 j i k).Contains (fullFactor false 28 25 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk28_0_25,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power28 j i k) (mpower0_25 j i k) (quadraturePoint j.val (16*i.val+k.val)) 28 25 (power28_contains j i k) (mpower0_25_contains j i k)
noncomputable def ha28_0_25 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),0⟩,⟨(-1),0⟩⟩,⟨⟨176848,176849⟩,⟨(-102104),(-102103)⟩⟩,⟨⟨(-1),1⟩,⟨5156455176,5156455177⟩⟩,⟨⟨(-5934037600013),(-5934037600012)⟩,⟨(-3426018205749),(-3426018205748)⟩⟩,⟨⟨1570726674205044,1570726674205046⟩,⟨(-906859468175609),(-906859468175608)⟩⟩,⟨⟨(-1),1⟩,⟨173021924583611076,173021924583611077⟩⟩]
lemma ha28_0_25_eq (j : Fin 7) : ha28_0_25 j = ((ha28_0_24 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 25 := by fin_cases j <;> decide +kernel
lemma ha28_0_25_contains (j : Fin 7) : (ha28_0_25 j).Contains (fullFactor false 28 25 ((j.val:ℝ)/6)) := by
  rw [ha28_0_25_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha28_0_24 j) false 28 24 j (ha28_0_24_contains j)
noncomputable def hk28_0_26 (j : Fin 6) (i k : Fin 16) : CBox := (power28 j i k).conj.mul (mpower0_26 j i k)
lemma hk28_0_26_contains (j : Fin 6) (i k : Fin 16) :
    (hk28_0_26 j i k).Contains (fullFactor false 28 26 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk28_0_26,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power28 j i k) (mpower0_26 j i k) (quadraturePoint j.val (16*i.val+k.val)) 28 26 (power28_contains j i k) (mpower0_26_contains j i k)
noncomputable def ha28_0_26 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨0,1⟩,⟨(-1),0⟩⟩,⟨⟨4112,4113⟩,⟨7122,7123⟩⟩,⟨⟨(-311528495),(-311528494)⟩,⟨(-1),1⟩⟩,⟨⟨275978298108,275978298109⟩,⟨(-478008434111),(-478008434110)⟩⟩,⟨⟨91313559072398,91313559072399⟩,⟨158159723733336,158159723733337⟩⟩,⟨⟨(-20906323353147685),(-20906323353147684)⟩,⟨(-1),1⟩⟩]
lemma ha28_0_26_eq (j : Fin 7) : ha28_0_26 j = ((ha28_0_25 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 26 := by fin_cases j <;> decide +kernel
lemma ha28_0_26_contains (j : Fin 7) : (ha28_0_26 j).Contains (fullFactor false 28 26 ((j.val:ℝ)/6)) := by
  rw [ha28_0_26_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha28_0_25 j) false 28 25 j (ha28_0_25_contains j)
noncomputable def hk28_0_27 (j : Fin 6) (i k : Fin 16) : CBox := (power28 j i k).conj.mul (mpower0_27 j i k)
lemma hk28_0_27_contains (j : Fin 6) (i k : Fin 16) :
    (hk28_0_27 j i k).Contains (fullFactor false 28 27 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk28_0_27,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power28 j i k) (mpower0_27 j i k) (quadraturePoint j.val (16*i.val+k.val)) 28 27 (power28_contains j i k) (mpower0_27_contains j i k)
noncomputable def ha28_0_27 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨0,1⟩,⟨0,1⟩⟩,⟨⟨(-277),(-276)⟩,⟨159,160⟩⟩,⟨⟨(-1),1⟩,⟨(-18123994),(-18123993)⟩⟩,⟨⟨37079204566,37079204567⟩,⟨21407688737,21407688739⟩⟩,⟨⟨(-15335599573286),(-15335599573285)⟩,⟨8854012541820,8854012541821⟩⟩,⟨⟨(-1),1⟩,⟨(-2432561179993389),(-2432561179993388)⟩⟩]
lemma ha28_0_27_eq (j : Fin 7) : ha28_0_27 j = ((ha28_0_26 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 27 := by fin_cases j <;> decide +kernel
lemma ha28_0_27_contains (j : Fin 7) : (ha28_0_27 j).Contains (fullFactor false 28 27 ((j.val:ℝ)/6)) := by
  rw [ha28_0_27_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha28_0_26 j) false 28 26 j (ha28_0_26_contains j)
noncomputable def hk28_0_28 (j : Fin 6) (i k : Fin 16) : CBox := (power28 j i k).conj.mul (mpower0_28 j i k)
lemma hk28_0_28_contains (j : Fin 6) (i k : Fin 16) :
    (hk28_0_28 j i k).Contains (fullFactor false 28 28 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk28_0_28,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power28 j i k) (mpower0_28 j i k) (quadraturePoint j.val (16*i.val+k.val)) 28 28 (power28_contains j i k) (mpower0_28_contains j i k)
noncomputable def ha28_0_28 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),0⟩,⟨0,1⟩⟩,⟨⟨(-6),(-5)⟩,⟨(-11),(-10)⟩⟩,⟨⟨1016753,1016754⟩,⟨(-1),1⟩⟩,⟨⟨(-1601291374),(-1601291373)⟩,⟨2773518015,2773518016⟩⟩,⟨⟨(-827848236791),(-827848236790)⟩,⟨(-1433875207079),(-1433875207078)⟩⟩,⟨⟨272932726159819,272932726159820⟩,⟨(-1),1⟩⟩]
lemma ha28_0_28_eq (j : Fin 7) : ha28_0_28 j = ((ha28_0_27 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 28 := by fin_cases j <;> decide +kernel
lemma ha28_0_28_contains (j : Fin 7) : (ha28_0_28 j).Contains (fullFactor false 28 28 ((j.val:ℝ)/6)) := by
  rw [ha28_0_28_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha28_0_27 j) false 28 27 j (ha28_0_27_contains j)
noncomputable def hk28_0_29 (j : Fin 6) (i k : Fin 16) : CBox := (power28 j i k).conj.mul (mpower0_29 j i k)
lemma hk28_0_29_contains (j : Fin 6) (i k : Fin 16) :
    (hk28_0_29 j i k).Contains (fullFactor false 28 29 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk28_0_29,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power28 j i k) (mpower0_29 j i k) (quadraturePoint j.val (16*i.val+k.val)) 28 29 (power28_contains j i k) (mpower0_29_contains j i k)
noncomputable def ha28_0_29 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),0⟩,⟨(-1),0⟩⟩,⟨⟨0,1⟩,⟨(-1),0⟩⟩,⟨⟨(-1),1⟩,⟨55072,55073⟩⟩,⟨⟨(-200304916),(-200304915)⟩,⟨(-115646097),(-115646096)⟩⟩,⟨⟨129444017721,129444017722⟩,⟨(-74734538477),(-74734538476)⟩⟩,⟨⟨(-1),1⟩,⟨29567015428549,29567015428550⟩⟩]
lemma ha28_0_29_eq (j : Fin 7) : ha28_0_29 j = ((ha28_0_28 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 29 := by fin_cases j <;> decide +kernel
lemma ha28_0_29_contains (j : Fin 7) : (ha28_0_29 j).Contains (fullFactor false 28 29 ((j.val:ℝ)/6)) := by
  rw [ha28_0_29_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha28_0_28 j) false 28 28 j (ha28_0_28_contains j)
noncomputable def hk28_0_30 (j : Fin 6) (i k : Fin 16) : CBox := (power28 j i k).conj.mul (mpower0_30 j i k)
lemma hk28_0_30_contains (j : Fin 6) (i k : Fin 16) :
    (hk28_0_30 j i k).Contains (fullFactor false 28 30 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk28_0_30,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power28 j i k) (mpower0_30 j i k) (quadraturePoint j.val (16*i.val+k.val)) 28 30 (power28_contains j i k) (mpower0_30_contains j i k)
noncomputable def ha28_0_30 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨0,1⟩,⟨(-1),0⟩⟩,⟨⟨0,1⟩,⟨0,1⟩⟩,⟨⟨(-2884),(-2883)⟩,⟨(-1),1⟩⟩,⟨⟨8073620,8073621⟩,⟨(-13983922),(-13983921)⟩⟩,⟨⟨6521818806,6521818807⟩,⟨11296121531,11296121532⟩⟩,⟨⟨(-3096250615297),(-3096250615296)⟩,⟨(-1),1⟩⟩]
lemma ha28_0_30_eq (j : Fin 7) : ha28_0_30 j = ((ha28_0_29 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 30 := by fin_cases j <;> decide +kernel
lemma ha28_0_30_contains (j : Fin 7) : (ha28_0_30 j).Contains (fullFactor false 28 30 ((j.val:ℝ)/6)) := by
  rw [ha28_0_30_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha28_0_29 j) false 28 29 j (ha28_0_29_contains j)
noncomputable def hk28_1_0 (j : Fin 6) (i k : Fin 16) : CBox := (kernel28_0 j i k).mul (mpower1_0 j i k)
lemma hk28_1_0_contains (j : Fin 6) (i k : Fin 16) :
    (hk28_1_0 j i k).Contains (fullFactor true 28 0 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk28_1_0,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel28_0 j i k) (mpower1_0 j i k) (quadraturePoint j.val (16*i.val+k.val)) 28 0 (kernel28_0_contains j i k) (mpower1_0_contains j i k)
noncomputable def ha28_1_0 : Fin 7 → CBox := ![⟨⟨(-3),3⟩,⟨(-3),3⟩⟩,⟨⟨(-4),3⟩,⟨(-2),4⟩⟩,⟨⟨(-2),2⟩,⟨0,4⟩⟩,⟨⟨(-2),2⟩,⟨0,3⟩⟩,⟨⟨(-493754047503),(-493754047500)⟩,⟨(-254534926262),(-254534926259)⟩⟩,⟨⟨3357153827198104502458,3357153827198104516477⟩,⟨(-568253757477525623876),(-568253757477525609895)⟩⟩,⟨⟨4568030054686774396541880045,4568030054686774407918970971⟩,⟨3209886730187197181988549093,3209886730187197193397127950⟩⟩]
lemma ha28_1_0_eq (j : Fin 7) : ha28_1_0 j = atomKernel28_0 j := by fin_cases j <;> decide +kernel
lemma ha28_1_0_contains (j : Fin 7) : (ha28_1_0 j).Contains (fullFactor true 28 0 ((j.val:ℝ)/6)) := by
  rw [ha28_1_0_eq]
  simpa only [fullFactor,ite_true] using atomKernel28_0_contains j
noncomputable def hk28_1_1 (j : Fin 6) (i k : Fin 16) : CBox := (kernel28_0 j i k).mul (mpower1_1 j i k)
lemma hk28_1_1_contains (j : Fin 6) (i k : Fin 16) :
    (hk28_1_1 j i k).Contains (fullFactor true 28 1 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk28_1_1,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel28_0 j i k) (mpower1_1 j i k) (quadraturePoint j.val (16*i.val+k.val)) 28 1 (kernel28_0_contains j i k) (mpower1_1_contains j i k)
noncomputable def ha28_1_1 : Fin 7 → CBox := ![⟨⟨(-28),28⟩,⟨(-28),28⟩⟩,⟨⟨(-31),46⟩,⟨(-42),31⟩⟩,⟨⟨(-10),31⟩,⟨(-30),11⟩⟩,⟨⟨(-6),21⟩,⟨(-19),11⟩⟩,⟨⟨(-427735225680),(-427735225661)⟩,⟨2666849509051,2666849509071⟩⟩,⟨⟨(-4685945174865765828890),(-4685945174865765761884)⟩,⟨(-13314743247109872706579),(-13314743247109872639414)⟩⟩,⟨⟨10733230239114978357051547456,10733230239114978400424162862⟩,⟨(-17098006669934193027518235080),(-17098006669934192984238611740)⟩⟩]
lemma ha28_1_1_eq (j : Fin 7) : ha28_1_1 j = ((ha28_1_0 j).mul (piI.mul (atomPoints j).z)).scale 1 1 := by fin_cases j <;> decide +kernel
lemma ha28_1_1_contains (j : Fin 7) : (ha28_1_1 j).Contains (fullFactor true 28 1 ((j.val:ℝ)/6)) := by
  rw [ha28_1_1_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha28_1_0 j) true 28 0 j (ha28_1_0_contains j)
noncomputable def hk28_1_2 (j : Fin 6) (i k : Fin 16) : CBox := (kernel28_0 j i k).mul (mpower1_2 j i k)
lemma hk28_1_2_contains (j : Fin 6) (i k : Fin 16) :
    (hk28_1_2 j i k).Contains (fullFactor true 28 2 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk28_1_2,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel28_0 j i k) (mpower1_2 j i k) (quadraturePoint j.val (16*i.val+k.val)) 28 2 (kernel28_0_contains j i k) (mpower1_2_contains j i k)
noncomputable def ha28_1_2 : Fin 7 → CBox := ![⟨⟨(-130),130⟩,⟨(-130),130⟩⟩,⟨⟨(-255),177⟩,⟨(-205),219⟩⟩,⟨⟨(-154),53⟩,⟨(-107),100⟩⟩,⟨⟨(-79),37⟩,⟨(-70),43⟩⟩,⟨⟨6484493628119,6484493628181⟩,⟨(-1032547750211),(-1032547750151)⟩⟩,⟨⟨(-25547166525425907308106),(-25547166525425907147222)⟩,⟨14260556997577409906764,14260556997577410067332⟩⟩,⟨⟨(-31878380967388563336379975931),(-31878380967388563254064469747)⟩,⟨(-17773711906285126222017443831),(-17773711906285126139577447036)⟩⟩]
lemma ha28_1_2_eq (j : Fin 7) : ha28_1_2 j = ((ha28_1_1 j).mul (piI.mul (atomPoints j).z)).scale 1 2 := by fin_cases j <;> decide +kernel
lemma ha28_1_2_contains (j : Fin 7) : (ha28_1_2 j).Contains (fullFactor true 28 2 ((j.val:ℝ)/6)) := by
  rw [ha28_1_2_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha28_1_1 j) true 28 1 j (ha28_1_1_contains j)
noncomputable def hk28_1_3 (j : Fin 6) (i k : Fin 16) : CBox := (kernel28_0 j i k).mul (mpower1_3 j i k)
lemma hk28_1_3_contains (j : Fin 6) (i k : Fin 16) :
    (hk28_1_3 j i k).Contains (fullFactor true 28 3 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk28_1_3,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel28_0 j i k) (mpower1_3 j i k) (quadraturePoint j.val (16*i.val+k.val)) 28 3 (kernel28_0_contains j i k) (mpower1_3_contains j i k)
noncomputable def ha28_1_3 : Fin 7 → CBox := ![⟨⟨(-400),400⟩,⟨(-400),400⟩⟩,⟨⟨(-707),924⟩,⟨(-779),840⟩⟩,⟨⟨(-271),425⟩,⟨(-256),440⟩⟩,⟨⟨(-155),148⟩,⟨(-104),201⟩⟩,⟨⟨(-4865559578997),(-4865559578873)⟩,⟨(-9464537535637),(-9464537535510)⟩⟩,⟨⟨25417198358163888449103,25417198358163888705611⟩,⟨31441318692122649502369,31441318692122649759274⟩⟩,⟨⟨(-19398475327249652548291993600),(-19398475327249652443834332594)⟩,⟨39483697746581819786216551954,39483697746581819890583389440⟩⟩]
lemma ha28_1_3_eq (j : Fin 7) : ha28_1_3 j = ((ha28_1_2 j).mul (piI.mul (atomPoints j).z)).scale 1 3 := by fin_cases j <;> decide +kernel
lemma ha28_1_3_contains (j : Fin 7) : (ha28_1_3 j).Contains (fullFactor true 28 3 ((j.val:ℝ)/6)) := by
  rw [ha28_1_3_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha28_1_2 j) true 28 2 j (ha28_1_2_contains j)
noncomputable def hk28_1_4 (j : Fin 6) (i k : Fin 16) : CBox := (kernel28_0 j i k).mul (mpower1_4 j i k)
lemma hk28_1_4_contains (j : Fin 6) (i k : Fin 16) :
    (hk28_1_4 j i k).Contains (fullFactor true 28 4 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk28_1_4,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel28_0 j i k) (mpower1_4 j i k) (quadraturePoint j.val (16*i.val+k.val)) 28 4 (kernel28_0_contains j i k) (mpower1_4_contains j i k)
noncomputable def ha28_1_4 : Fin 7 → CBox := ![⟨⟨(-922),922⟩,⟨(-922),922⟩⟩,⟨⟨(-2495),2136⟩,⟨(-2469),2151⟩⟩,⟨⟨(-853),901⟩,⟨(-1089),665⟩⟩,⟨⟨(-238),367⟩,⟨(-332),272⟩⟩,⟨⟨(-9088251010517),(-9088251010322)⟩,⟨9205245187683,9205245187875⟩⟩,⟨⟨27636408466630806852822,27636408466630807160487⟩,⟨(-31495264721916455077269),(-31495264721916454769955)⟩⟩,⟨⟨36554794359576350005982116024,36554794359576350105219906821⟩,⟨15658603290377833276090819030,15658603290377833375351622876⟩⟩]
lemma ha28_1_4_eq (j : Fin 7) : ha28_1_4 j = ((ha28_1_3 j).mul (piI.mul (atomPoints j).z)).scale 1 4 := by fin_cases j <;> decide +kernel
lemma ha28_1_4_contains (j : Fin 7) : (ha28_1_4 j).Contains (fullFactor true 28 4 ((j.val:ℝ)/6)) := by
  rw [ha28_1_4_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha28_1_3 j) true 28 3 j (ha28_1_3_contains j)
noncomputable def hk28_1_5 (j : Fin 6) (i k : Fin 16) : CBox := (kernel28_0 j i k).mul (mpower1_5 j i k)
lemma hk28_1_5_contains (j : Fin 6) (i k : Fin 16) :
    (hk28_1_5 j i k).Contains (fullFactor true 28 5 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk28_1_5,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel28_0 j i k) (mpower1_5 j i k) (quadraturePoint j.val (16*i.val+k.val)) 28 5 (kernel28_0_contains j i k) (mpower1_5_contains j i k)
noncomputable def ha28_1_5 : Fin 7 → CBox := ![⟨⟨(-1700),1700⟩,⟨(-1700),1700⟩⟩,⟨⟨(-5111),5425⟩,⟨(-4887),5641⟩⟩,⟨⟨(-2009),1525⟩,⟨(-1583),1951⟩⟩,⟨⟨(-547),413⟩,⟨(-529),432⟩⟩,⟨⟨11260014632807,11260014633044⟩,⟨5607678750765,5607678751005⟩⟩,⟨⟨(-29626388377567493745494),(-29626388377567493450967)⟩,⟨(-18144127288028032778373),(-18144127288028032483617)⟩⟩,⟨⟨9935921573568820690265604707,9935921573568820765719483290⟩,⟨(-26988116545467155499799051604),(-26988116545467155424315389632)⟩⟩]
lemma ha28_1_5_eq (j : Fin 7) : ha28_1_5 j = ((ha28_1_4 j).mul (piI.mul (atomPoints j).z)).scale 1 5 := by fin_cases j <;> decide +kernel
lemma ha28_1_5_contains (j : Fin 7) : (ha28_1_5 j).Contains (fullFactor true 28 5 ((j.val:ℝ)/6)) := by
  rw [ha28_1_5_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha28_1_4 j) true 28 4 j (ha28_1_4_contains j)
noncomputable def hk28_1_6 (j : Fin 6) (i k : Fin 16) : CBox := (kernel28_0 j i k).mul (mpower1_6 j i k)
lemma hk28_1_6_contains (j : Fin 6) (i k : Fin 16) :
    (hk28_1_6 j i k).Contains (fullFactor true 28 6 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk28_1_6,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel28_0 j i k) (mpower1_6 j i k) (quadraturePoint j.val (16*i.val+k.val)) 28 6 (kernel28_0_contains j i k) (mpower1_6_contains j i k)
noncomputable def ha28_1_6 : Fin 7 → CBox := ![⟨⟨(-2612),2612⟩,⟨(-2612),2612⟩⟩,⟨⟨(-9960),10026⟩,⟨(-10570),9412⟩⟩,⟨⟨(-2611),3324⟩,⟨(-2910),3024⟩⟩,⟨⟨(-646),626⟩,⟨(-556),716⟩⟩,⟨⟨1474079895327,1474079895573⟩,⟨(-10086463026260),(-10086463026016)⟩⟩,⟨⟨(-8876352794665062936640),(-8876352794665062701322)⟩,⟨22301927885805534417018,22301927885805534652228⟩⟩,⟨⟨(-16553415482953545671139655835),(-16553415482953545623296681888)⟩,⟨(-5135203726273558986739222252),(-5135203726273558938944209337)⟩⟩]
lemma ha28_1_6_eq (j : Fin 7) : ha28_1_6 j = ((ha28_1_5 j).mul (piI.mul (atomPoints j).z)).scale 1 6 := by fin_cases j <;> decide +kernel
lemma ha28_1_6_contains (j : Fin 7) : (ha28_1_6 j).Contains (fullFactor true 28 6 ((j.val:ℝ)/6)) := by
  rw [ha28_1_6_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha28_1_5 j) true 28 5 j (ha28_1_5_contains j)
noncomputable def hk28_1_7 (j : Fin 6) (i k : Fin 16) : CBox := (kernel28_0 j i k).mul (mpower1_7 j i k)
lemma hk28_1_7_contains (j : Fin 6) (i k : Fin 16) :
    (hk28_1_7 j i k).Contains (fullFactor true 28 7 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk28_1_7,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel28_0 j i k) (mpower1_7 j i k) (quadraturePoint j.val (16*i.val+k.val)) 28 7 (kernel28_0_contains j i k) (mpower1_7_contains j i k)
noncomputable def ha28_1_7 : Fin 7 → CBox := ![⟨⟨(-3439),3439⟩,⟨(-3439),3439⟩⟩,⟨⟨(-16595),15907⟩,⟨(-15633),16866⟩⟩,⟨⟨(-4479),4062⟩,⟨(-4573),3968⟩⟩,⟨⟨(-659),784⟩,⟨(-747),697⟩⟩,⟨⟨(-6976158099833),(-6976158099618)⟩,⟨1210621953833,1210621954049⟩⟩,⟨⟨13908805375154267714462,13908805375154267875455⟩,⟨2936452680378083247514,2936452680378083408539⟩⟩,⟨⟨(-2205009146231279427035635215),(-2205009146231279401086836476)⟩,⟨8677009823436139786137684074,8677009823436139812127711651⟩⟩]
lemma ha28_1_7_eq (j : Fin 7) : ha28_1_7 j = ((ha28_1_6 j).mul (piI.mul (atomPoints j).z)).scale 1 7 := by fin_cases j <;> decide +kernel
lemma ha28_1_7_contains (j : Fin 7) : (ha28_1_7 j).Contains (fullFactor true 28 7 ((j.val:ℝ)/6)) := by
  rw [ha28_1_7_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha28_1_6 j) true 28 6 j (ha28_1_6_contains j)
noncomputable def hk28_1_8 (j : Fin 6) (i k : Fin 16) : CBox := (kernel28_0 j i k).mul (mpower1_8 j i k)
lemma hk28_1_8_contains (j : Fin 6) (i k : Fin 16) :
    (hk28_1_8 j i k).Contains (fullFactor true 28 8 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk28_1_8,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel28_0 j i k) (mpower1_8 j i k) (quadraturePoint j.val (16*i.val+k.val)) 28 8 (kernel28_0_contains j i k) (mpower1_8_contains j i k)
noncomputable def ha28_1_8 : Fin 7 → CBox := ![⟨⟨(-3962),3962⟩,⟨(-3962),3962⟩⟩,⟨⟨(-22509),23741⟩,⟨(-23555),22694⟩⟩,⟨⟨(-5444),5312⟩,⟨(-5058),5698⟩⟩,⟨⟨(-755),679⟩,⟨(-748),686⟩⟩,⟨⟨2020553320635,2020553320802⟩,⟨3799406407328,3799406407494⟩⟩,⟨⟨275029602185696829490,275029602185696925902⟩,⟨(-7361218239110540503272),(-7361218239110540406858)⟩⟩,⟨⟨3968368796587380336814275492,3968368796587380349167302116⟩,⟨791629275638498607796883228,791629275638498620123452449⟩⟩]
lemma ha28_1_8_eq (j : Fin 7) : ha28_1_8 j = ((ha28_1_7 j).mul (piI.mul (atomPoints j).z)).scale 1 8 := by fin_cases j <;> decide +kernel
lemma ha28_1_8_contains (j : Fin 7) : (ha28_1_8 j).Contains (fullFactor true 28 8 ((j.val:ℝ)/6)) := by
  rw [ha28_1_8_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha28_1_7 j) true 28 7 j (ha28_1_7_contains j)
noncomputable def hk28_1_9 (j : Fin 6) (i k : Fin 16) : CBox := (kernel28_0 j i k).mul (mpower1_9 j i k)
lemma hk28_1_9_contains (j : Fin 6) (i k : Fin 16) :
    (hk28_1_9 j i k).Contains (fullFactor true 28 9 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk28_1_9,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel28_0 j i k) (mpower1_9 j i k) (quadraturePoint j.val (16*i.val+k.val)) 28 9 (kernel28_0_contains j i k) (mpower1_9_contains j i k)
noncomputable def ha28_1_9 : Fin 7 → CBox := ![⟨⟨(-4057),4057⟩,⟨(-4057),4057⟩⟩,⟨⟨(-29954),28549⟩,⟨(-29139),29363⟩⟩,⟨⟨(-5801),6239⟩,⟨(-6157),5883⟩⟩,⟨⟨(-639),627⟩,⟨(-602),664⟩⟩,⟨⟨1610150892727,1610150892841⟩,⟨(-1676932171466),(-1676932171352)⟩⟩,⟨⟨(-3362940049418340078320),(-3362940049418340026999)⟩,⟨451218415581786561877,451218415581786613189⟩⟩,⟨⟨234826667597909936902803030,234826667597909942107536670⟩,⟨(-1608725548833069416613427969),(-1608725548833069411394784787)⟩⟩]
lemma ha28_1_9_eq (j : Fin 7) : ha28_1_9 j = ((ha28_1_8 j).mul (piI.mul (atomPoints j).z)).scale 1 9 := by fin_cases j <;> decide +kernel
lemma ha28_1_9_contains (j : Fin 7) : (ha28_1_9 j).Contains (fullFactor true 28 9 ((j.val:ℝ)/6)) := by
  rw [ha28_1_9_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha28_1_8 j) true 28 8 j (ha28_1_8_contains j)
noncomputable def hk28_1_10 (j : Fin 6) (i k : Fin 16) : CBox := (kernel28_0 j i k).mul (mpower1_10 j i k)
lemma hk28_1_10_contains (j : Fin 6) (i k : Fin 16) :
    (hk28_1_10 j i k).Contains (fullFactor true 28 10 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk28_1_10,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel28_0 j i k) (mpower1_10 j i k) (quadraturePoint j.val (16*i.val+k.val)) 28 10 (kernel28_0_contains j i k) (mpower1_10_contains j i k)
noncomputable def ha28_1_10 : Fin 7 → CBox := ![⟨⟨(-3739),3739⟩,⟨(-3739),3739⟩⟩,⟨⟨(-32720),33881⟩,⟨(-33125),33476⟩⟩,⟨⟨(-6243),5886⟩,⟨(-6110),6020⟩⟩,⟨⟨(-485),521⟩,⟨(-509),497⟩⟩,⟨⟨(-1018736106667),(-1018736106596)⟩,⟨(-489772973673),(-489772973602)⟩⟩,⟨⟨421189642171226051379,421189642171226075958⟩,⟨1342081025863208068154,1342081025863208092740⟩⟩,⟨⟨(-585324403679700287012141317),(-585324403679700285028081500)⟩,⟨(-54588941927361483113968359),(-54588941927361481136167206)⟩⟩]
lemma ha28_1_10_eq (j : Fin 7) : ha28_1_10 j = ((ha28_1_9 j).mul (piI.mul (atomPoints j).z)).scale 1 10 := by fin_cases j <;> decide +kernel
lemma ha28_1_10_contains (j : Fin 7) : (ha28_1_10 j).Contains (fullFactor true 28 10 ((j.val:ℝ)/6)) := by
  rw [ha28_1_10_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha28_1_9 j) true 28 9 j (ha28_1_9_contains j)
noncomputable def hk28_1_11 (j : Fin 6) (i k : Fin 16) : CBox := (kernel28_0 j i k).mul (mpower1_11 j i k)
lemma hk28_1_11_contains (j : Fin 6) (i k : Fin 16) :
    (hk28_1_11 j i k).Contains (fullFactor true 28 11 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk28_1_11,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel28_0 j i k) (mpower1_11 j i k) (quadraturePoint j.val (16*i.val+k.val)) 28 11 (kernel28_0_contains j i k) (mpower1_11_contains j i k)
noncomputable def ha28_1_11 : Fin 7 → CBox := ![⟨⟨(-3133),3133⟩,⟨(-3133),3133⟩⟩,⟨⟨(-34809),34119⟩,⟨(-34782),34145⟩⟩,⟨⟨(-5496),5613⟩,⟨(-5451),5658⟩⟩,⟨⟨(-371),356⟩,⟨(-370),357⟩⟩,⟨⟨(-65363410050),(-65363410010)⟩,⟨495339131295,495339131335⟩⟩,⟨⟨471468391977111431641,471468391977111442348⟩,⟨(-242356254839358529757),(-242356254839358519052)⟩⟩,⟨⟨(-7928524023485484863463353),(-7928524023485484180243140)⟩,⟨193079273767098993471291408,193079273767098994156985092⟩⟩]
lemma ha28_1_11_eq (j : Fin 7) : ha28_1_11 j = ((ha28_1_10 j).mul (piI.mul (atomPoints j).z)).scale 1 11 := by fin_cases j <;> decide +kernel
lemma ha28_1_11_contains (j : Fin 7) : (ha28_1_11 j).Contains (fullFactor true 28 11 ((j.val:ℝ)/6)) := by
  rw [ha28_1_11_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha28_1_10 j) true 28 10 j (ha28_1_10_contains j)
noncomputable def hk28_1_12 (j : Fin 6) (i k : Fin 16) : CBox := (kernel28_0 j i k).mul (mpower1_12 j i k)
lemma hk28_1_12_contains (j : Fin 6) (i k : Fin 16) :
    (hk28_1_12 j i k).Contains (fullFactor true 28 12 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk28_1_12,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel28_0 j i k) (mpower1_12 j i k) (quadraturePoint j.val (16*i.val+k.val)) 28 12 (kernel28_0_contains j i k) (mpower1_12_contains j i k)
noncomputable def ha28_1_12 : Fin 7 → CBox := ![⟨⟨(-2406),2406⟩,⟨(-2406),2406⟩⟩,⟨⟨(-32574),32817⟩,⟨(-32385),33006⟩⟩,⟨⟨(-4643),4684⟩,⟨(-4731),4596⟩⟩,⟨⟨(-242),240⟩,⟨(-236),246⟩⟩,⟨⟨198959191711,198959191732⟩,⟨(-37386425226),(-37386425204)⟩⟩,⟨⟨(-110179550922274969061),(-110179550922274964787)⟩,⟨(-146282935247653628256),(-146282935247653623981)⟩⟩,⟨⟨58225254219743512917736865,58225254219743513134951228⟩,⟨(-635419677339146467434770),(-635419677339146251094142)⟩⟩]
lemma ha28_1_12_eq (j : Fin 7) : ha28_1_12 j = ((ha28_1_11 j).mul (piI.mul (atomPoints j).z)).scale 1 12 := by fin_cases j <;> decide +kernel
lemma ha28_1_12_contains (j : Fin 7) : (ha28_1_12 j).Contains (fullFactor true 28 12 ((j.val:ℝ)/6)) := by
  rw [ha28_1_12_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha28_1_11 j) true 28 11 j (ha28_1_11_contains j)
noncomputable def hk28_1_13 (j : Fin 6) (i k : Fin 16) : CBox := (kernel28_0 j i k).mul (mpower1_13 j i k)
lemma hk28_1_13_contains (j : Fin 6) (i k : Fin 16) :
    (hk28_1_13 j i k).Contains (fullFactor true 28 13 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk28_1_13,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel28_0 j i k) (mpower1_13 j i k) (quadraturePoint j.val (16*i.val+k.val)) 28 13 (kernel28_0_contains j i k) (mpower1_13_contains j i k)
noncomputable def ha28_1_13 : Fin 7 → CBox := ![⟨⟨(-1706),1706⟩,⟨(-1706),1706⟩⟩,⟨⟨(-28615),28649⟩,⟨(-28850),28414⟩⟩,⟨⟨(-3649),3580⟩,⟨(-3597),3632⟩⟩,⟨⟨(-145),150⟩,⟨(-148),147⟩⟩,⟨⟨(-36478382800),(-36478382789)⟩,⟨(-66348888887),(-66348888876)⟩⟩,⟨⟨(-40000698705503772693),(-40000698705503771117)⟩,⟨42549530079313509815,42549530079313511391⟩⟩,⟨⟨(-1017512944085107383093759),(-1017512944085107319859849)⟩,⟨(-16164122631392575296618999),(-16164122631392575233106739)⟩⟩]
lemma ha28_1_13_eq (j : Fin 7) : ha28_1_13 j = ((ha28_1_12 j).mul (piI.mul (atomPoints j).z)).scale 1 13 := by fin_cases j <;> decide +kernel
lemma ha28_1_13_contains (j : Fin 7) : (ha28_1_13 j).Contains (fullFactor true 28 13 ((j.val:ℝ)/6)) := by
  rw [ha28_1_13_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha28_1_12 j) true 28 12 j (ha28_1_12_contains j)
noncomputable def hk28_1_14 (j : Fin 6) (i k : Fin 16) : CBox := (kernel28_0 j i k).mul (mpower1_14 j i k)
lemma hk28_1_14_contains (j : Fin 6) (i k : Fin 16) :
    (hk28_1_14 j i k).Contains (fullFactor true 28 14 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk28_1_14,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel28_0 j i k) (mpower1_14 j i k) (quadraturePoint j.val (16*i.val+k.val)) 28 14 (kernel28_0_contains j i k) (mpower1_14_contains j i k)
noncomputable def ha28_1_14 : Fin 7 → CBox := ![⟨⟨(-1123),1123⟩,⟨(-1123),1123⟩⟩,⟨⟨(-23350),23215⟩,⟨(-23168),23397⟩⟩,⟨⟨(-2583),2620⟩,⟨(-2595),2608⟩⟩,⟨⟨(-85),83⟩,⟨(-85),83⟩⟩,⟨⟨(-17946671213),(-17946671207)⟩,⟨19219425108,19219425114⟩⟩,⟨⟨14428580018234540159,14428580018234540699⟩,⟨9531917685691578974,9531917685691579515⟩⟩,⟨⟨(-4155571849640704153785347),(-4155571849640704136542170)⟩,⟨479246946914341680458139,479246946914341697621466⟩⟩]
lemma ha28_1_14_eq (j : Fin 7) : ha28_1_14 j = ((ha28_1_13 j).mul (piI.mul (atomPoints j).z)).scale 1 14 := by fin_cases j <;> decide +kernel
lemma ha28_1_14_contains (j : Fin 7) : (ha28_1_14 j).Contains (fullFactor true 28 14 ((j.val:ℝ)/6)) := by
  rw [ha28_1_14_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha28_1_13 j) true 28 13 j (ha28_1_13_contains j)
noncomputable def hk28_1_15 (j : Fin 6) (i k : Fin 16) : CBox := (kernel28_0 j i k).mul (mpower1_15 j i k)
lemma hk28_1_15_contains (j : Fin 6) (i k : Fin 16) :
    (hk28_1_15 j i k).Contains (fullFactor true 28 15 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk28_1_15,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel28_0 j i k) (mpower1_15 j i k) (quadraturePoint j.val (16*i.val+k.val)) 28 15 (kernel28_0_contains j i k) (mpower1_15_contains j i k)
noncomputable def ha28_1_15 : Fin 7 → CBox := ![⟨⟨(-690),690⟩,⟨(-690),690⟩⟩,⟨⟨(-17608),17733⟩,⟨(-17712),17629⟩⟩,⟨⟨(-1751),1744⟩,⟨(-1756),1739⟩⟩,⟨⟨(-45),45⟩,⟨(-44),45⟩⟩,⟨⟨7732609363,7732609366⟩,⟨3585943143,3585943146⟩⟩,⟨⟨1918572265091405702,1918572265091405876⟩,⟨(-4377226561865541087),(-4377226561865540913)⟩⟩,⟨⟨167391924550560480587554,167391924550560484935756⟩,⟨994392556516195436139939,994392556516195440509035⟩⟩]
lemma ha28_1_15_eq (j : Fin 7) : ha28_1_15 j = ((ha28_1_14 j).mul (piI.mul (atomPoints j).z)).scale 1 15 := by fin_cases j <;> decide +kernel
lemma ha28_1_15_contains (j : Fin 7) : (ha28_1_15 j).Contains (fullFactor true 28 15 ((j.val:ℝ)/6)) := by
  rw [ha28_1_15_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha28_1_14 j) true 28 14 j (ha28_1_14_contains j)
noncomputable def hk28_1_16 (j : Fin 6) (i k : Fin 16) : CBox := (kernel28_0 j i k).mul (mpower1_16 j i k)
lemma hk28_1_16_contains (j : Fin 6) (i k : Fin 16) :
    (hk28_1_16 j i k).Contains (fullFactor true 28 16 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk28_1_16,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel28_0 j i k) (mpower1_16 j i k) (quadraturePoint j.val (16*i.val+k.val)) 28 16 (kernel28_0_contains j i k) (mpower1_16_contains j i k)
noncomputable def ha28_1_16 : Fin 7 → CBox := ![⟨⟨(-398),398⟩,⟨(-398),398⟩⟩,⟨⟨(-12613),12534⟩,⟨(-12568),12579⟩⟩,⟨⟨(-1102),1099⟩,⟨(-1097),1104⟩⟩,⟨⟨(-23),23⟩,⟨(-23),23⟩⟩,⟨⟨303084940,303084942⟩,⟨(-2572409615),(-2572409613)⟩⟩,⟨⟨(-1202095402683007419),(-1202095402683007366)⟩,⟨(-297189559897050281),(-297189559897050228)⟩⟩,⟨⟨222459104442015903718748,222459104442015904756556⟩,⟨(-49448563983890209871957),(-49448563983890208839181)⟩⟩]
lemma ha28_1_16_eq (j : Fin 7) : ha28_1_16 j = ((ha28_1_15 j).mul (piI.mul (atomPoints j).z)).scale 1 16 := by fin_cases j <;> decide +kernel
lemma ha28_1_16_contains (j : Fin 7) : (ha28_1_16 j).Contains (fullFactor true 28 16 ((j.val:ℝ)/6)) := by
  rw [ha28_1_16_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha28_1_15 j) true 28 15 j (ha28_1_15_contains j)
noncomputable def hk28_1_17 (j : Fin 6) (i k : Fin 16) : CBox := (kernel28_0 j i k).mul (mpower1_17 j i k)
lemma hk28_1_17_contains (j : Fin 6) (i k : Fin 16) :
    (hk28_1_17 j i k).Contains (fullFactor true 28 17 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk28_1_17,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel28_0 j i k) (mpower1_17 j i k) (quadraturePoint j.val (16*i.val+k.val)) 28 17 (kernel28_0_contains j i k) (mpower1_17_contains j i k)
noncomputable def ha28_1_17 : Fin 7 → CBox := ![⟨⟨(-216),216⟩,⟨(-216),216⟩⟩,⟨⟨(-8401),8439⟩,⟨(-8414),8427⟩⟩,⟨⟨(-651),654⟩,⟨(-653),652⟩⟩,⟨⟨(-11),11⟩,⟨(-11),11⟩⟩,⟨⟨(-726105080),(-726105078)⟩,⟨146933432,146933434⟩⟩,⟨⟨(-21615616742345886),(-21615616742345870)⟩,⟨301189864143714343,301189864143714358⟩⟩,⟨⟨(-12960702605192211705314),(-12960702605192211474434)⟩,⟨(-46707087997390079914349),(-46707087997390079682344)⟩⟩]
lemma ha28_1_17_eq (j : Fin 7) : ha28_1_17 j = ((ha28_1_16 j).mul (piI.mul (atomPoints j).z)).scale 1 17 := by fin_cases j <;> decide +kernel
lemma ha28_1_17_contains (j : Fin 7) : (ha28_1_17 j).Contains (fullFactor true 28 17 ((j.val:ℝ)/6)) := by
  rw [ha28_1_17_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha28_1_16 j) true 28 16 j (ha28_1_16_contains j)
noncomputable def hk28_1_18 (j : Fin 6) (i k : Fin 16) : CBox := (kernel28_0 j i k).mul (mpower1_18 j i k)
lemma hk28_1_18_contains (j : Fin 6) (i k : Fin 16) :
    (hk28_1_18 j i k).Contains (fullFactor true 28 18 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk28_1_18,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel28_0 j i k) (mpower1_18 j i k) (quadraturePoint j.val (16*i.val+k.val)) 28 18 (kernel28_0_contains j i k) (mpower1_18_contains j i k)
noncomputable def ha28_1_18 : Fin 7 → CBox := ![⟨⟨(-111),111⟩,⟨(-111),111⟩⟩,⟨⟨(-5333),5319⟩,⟨(-5333),5319⟩⟩,⟨⟨(-366),365⟩,⟨(-366),365⟩⟩,⟨⟨(-5),5⟩,⟨(-5),5⟩⟩,⟨⟨98841049,98841050⟩,⟨173996727,173996728⟩⟩,⟨⟨69204097031463841,69204097031463846⟩,⟨(-6879074720729438),(-6879074720729433)⟩⟩,⟨⟨(-9234824241539036892233),(-9234824241539036843250)⟩,⟨3087321175289841983220,3087321175289842031969⟩⟩]
lemma ha28_1_18_eq (j : Fin 7) : ha28_1_18 j = ((ha28_1_17 j).mul (piI.mul (atomPoints j).z)).scale 1 18 := by fin_cases j <;> decide +kernel
lemma ha28_1_18_contains (j : Fin 7) : (ha28_1_18 j).Contains (fullFactor true 28 18 ((j.val:ℝ)/6)) := by
  rw [ha28_1_18_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha28_1_17 j) true 28 17 j (ha28_1_17_contains j)
noncomputable def hk28_1_19 (j : Fin 6) (i k : Fin 16) : CBox := (kernel28_0 j i k).mul (mpower1_19 j i k)
lemma hk28_1_19_contains (j : Fin 6) (i k : Fin 16) :
    (hk28_1_19 j i k).Contains (fullFactor true 28 19 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk28_1_19,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel28_0 j i k) (mpower1_19 j i k) (quadraturePoint j.val (16*i.val+k.val)) 28 19 (kernel28_0_contains j i k) (mpower1_19_contains j i k)
noncomputable def ha28_1_19 : Fin 7 → CBox := ![⟨⟨(-54),54⟩,⟨(-54),54⟩⟩,⟨⟨(-3190),3193⟩,⟨(-3187),3196⟩⟩,⟨⟨(-194),194⟩,⟨(-194),195⟩⟩,⟨⟨(-3),3⟩,⟨(-3),3⟩⟩,⟨⟨34425451,34425452⟩,⟨(-37911140),(-37911139)⟩⟩,⟨⟨(-4044413201453568),(-4044413201453566)⟩,⟨(-14624960867008672),(-14624960867008670)⟩⟩,⟨⟨678023740790816481660,678023740790816491412⟩,⟨1724603902431137822507,1724603902431137832305⟩⟩]
lemma ha28_1_19_eq (j : Fin 7) : ha28_1_19 j = ((ha28_1_18 j).mul (piI.mul (atomPoints j).z)).scale 1 19 := by fin_cases j <;> decide +kernel
lemma ha28_1_19_contains (j : Fin 7) : (ha28_1_19 j).Contains (fullFactor true 28 19 ((j.val:ℝ)/6)) := by
  rw [ha28_1_19_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha28_1_18 j) true 28 18 j (ha28_1_18_contains j)
noncomputable def hk28_1_20 (j : Fin 6) (i k : Fin 16) : CBox := (kernel28_0 j i k).mul (mpower1_20 j i k)
lemma hk28_1_20_contains (j : Fin 6) (i k : Fin 16) :
    (hk28_1_20 j i k).Contains (fullFactor true 28 20 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk28_1_20,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel28_0 j i k) (mpower1_20 j i k) (quadraturePoint j.val (16*i.val+k.val)) 28 20 (kernel28_0_contains j i k) (mpower1_20_contains j i k)
noncomputable def ha28_1_20 : Fin 7 → CBox := ![⟨⟨(-25),25⟩,⟨(-25),25⟩⟩,⟨⟨(-1817),1817⟩,⟨(-1819),1815⟩⟩,⟨⟨(-98),98⟩,⟨(-98),98⟩⟩,⟨⟨(-2),2⟩,⟨(-2),2⟩⟩,⟨⟨(-11365795),(-11365794)⟩,⟨(-5079817),(-5079816)⟩⟩,⟨⟨(-2844939705163059),(-2844939705163057)⟩,⟨1341152941746088,1341152941746090⟩⟩,⟨⟨305013740303017263092,305013740303017264954⟩,⟨(-138609802094244642422),(-138609802094244640568)⟩⟩]
lemma ha28_1_20_eq (j : Fin 7) : ha28_1_20 j = ((ha28_1_19 j).mul (piI.mul (atomPoints j).z)).scale 1 20 := by fin_cases j <;> decide +kernel
lemma ha28_1_20_contains (j : Fin 7) : (ha28_1_20 j).Contains (fullFactor true 28 20 ((j.val:ℝ)/6)) := by
  rw [ha28_1_20_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha28_1_19 j) true 28 19 j (ha28_1_19_contains j)
noncomputable def hk28_1_21 (j : Fin 6) (i k : Fin 16) : CBox := (kernel28_0 j i k).mul (mpower1_21 j i k)
lemma hk28_1_21_contains (j : Fin 6) (i k : Fin 16) :
    (hk28_1_21 j i k).Contains (fullFactor true 28 21 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk28_1_21,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel28_0 j i k) (mpower1_21 j i k) (quadraturePoint j.val (16*i.val+k.val)) 28 21 (kernel28_0_contains j i k) (mpower1_21_contains j i k)
noncomputable def ha28_1_21 : Fin 7 → CBox := ![⟨⟨(-11),11⟩,⟨(-11),11⟩⟩,⟨⟨(-986),985⟩,⟨(-985),986⟩⟩,⟨⟨(-48),48⟩,⟨(-48),48⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-297404),(-297403)⟩,⟨2867027,2867028⟩⟩,⟨⟨356319626872007,356319626872009⟩,⟨508468577852757,508468577852759⟩⟩,⟨⟨(-26561764647803454745),(-26561764647803454408)⟩,⟨(-51208825282387177984),(-51208825282387177646)⟩⟩]
lemma ha28_1_21_eq (j : Fin 7) : ha28_1_21 j = ((ha28_1_20 j).mul (piI.mul (atomPoints j).z)).scale 1 21 := by fin_cases j <;> decide +kernel
lemma ha28_1_21_contains (j : Fin 7) : (ha28_1_21 j).Contains (fullFactor true 28 21 ((j.val:ℝ)/6)) := by
  rw [ha28_1_21_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha28_1_20 j) true 28 20 j (ha28_1_20_contains j)
noncomputable def hk28_1_22 (j : Fin 6) (i k : Fin 16) : CBox := (kernel28_0 j i k).mul (mpower1_22 j i k)
lemma hk28_1_22_contains (j : Fin 6) (i k : Fin 16) :
    (hk28_1_22 j i k).Contains (fullFactor true 28 22 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk28_1_22,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel28_0 j i k) (mpower1_22 j i k) (quadraturePoint j.val (16*i.val+k.val)) 28 22 (kernel28_0_contains j i k) (mpower1_22_contains j i k)
noncomputable def ha28_1_22 : Fin 7 → CBox := ![⟨⟨(-5),5⟩,⟨(-5),5⟩⟩,⟨⟨(-510),511⟩,⟨(-511),510⟩⟩,⟨⟨(-22),22⟩,⟨(-22),22⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨622559,622560⟩,⟨(-135026),(-135025)⟩⟩,⟨⟨83013043581483,83013043581485⟩,⟨(-82444915483969),(-82444915483968)⟩⟩,⟨⟨(-8178582266590750576),(-8178582266590750517)⟩,⟨4796858029667616359,4796858029667616418⟩⟩]
lemma ha28_1_22_eq (j : Fin 7) : ha28_1_22 j = ((ha28_1_21 j).mul (piI.mul (atomPoints j).z)).scale 1 22 := by fin_cases j <;> decide +kernel
lemma ha28_1_22_contains (j : Fin 7) : (ha28_1_22 j).Contains (fullFactor true 28 22 ((j.val:ℝ)/6)) := by
  rw [ha28_1_22_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha28_1_21 j) true 28 21 j (ha28_1_21_contains j)
noncomputable def hk28_1_23 (j : Fin 6) (i k : Fin 16) : CBox := (kernel28_0 j i k).mul (mpower1_23 j i k)
lemma hk28_1_23_contains (j : Fin 6) (i k : Fin 16) :
    (hk28_1_23 j i k).Contains (fullFactor true 28 23 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk28_1_23,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel28_0 j i k) (mpower1_23 j i k) (quadraturePoint j.val (16*i.val+k.val)) 28 23 (kernel28_0_contains j i k) (mpower1_23_contains j i k)
noncomputable def ha28_1_23 : Fin 7 → CBox := ![⟨⟨(-3),3⟩,⟨(-3),3⟩⟩,⟨⟨(-253),253⟩,⟨(-253),253⟩⟩,⟨⟨(-10),10⟩,⟨(-10),10⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-68140),(-68139)⟩,⟨(-116157),(-116156)⟩⟩,⟨⟨(-17186017015360),(-17186017015359)⟩,⟨(-12220282123144),(-12220282123142)⟩⟩,⟨⟨819882568341981990,819882568341982001⟩,⟨1244884843592842478,1244884843592842489⟩⟩]
lemma ha28_1_23_eq (j : Fin 7) : ha28_1_23 j = ((ha28_1_22 j).mul (piI.mul (atomPoints j).z)).scale 1 23 := by fin_cases j <;> decide +kernel
lemma ha28_1_23_contains (j : Fin 7) : (ha28_1_23 j).Contains (fullFactor true 28 23 ((j.val:ℝ)/6)) := by
  rw [ha28_1_23_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha28_1_22 j) true 28 22 j (ha28_1_22_contains j)
noncomputable def hk28_1_24 (j : Fin 6) (i k : Fin 16) : CBox := (kernel28_0 j i k).mul (mpower1_24 j i k)
lemma hk28_1_24_contains (j : Fin 6) (i k : Fin 16) :
    (hk28_1_24 j i k).Contains (fullFactor true 28 24 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk28_1_24,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel28_0 j i k) (mpower1_24 j i k) (quadraturePoint j.val (16*i.val+k.val)) 28 24 (kernel28_0_contains j i k) (mpower1_24_contains j i k)
noncomputable def ha28_1_24 : Fin 7 → CBox := ![⟨⟨(-2),2⟩,⟨(-2),2⟩⟩,⟨⟨(-121),121⟩,⟨(-121),121⟩⟩,⟨⟨(-5),5⟩,⟨(-5),5⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-18058),(-18057)⟩,⟨20450,20452⟩⟩,⟨⟨(-1575802991513),(-1575802991512)⟩,⟨3284032228473,3284032228474⟩⟩,⟨⟨180889978563891695,180889978563891698⟩,⟨(-133098896054967576),(-133098896054967574)⟩⟩]
lemma ha28_1_24_eq (j : Fin 7) : ha28_1_24 j = ((ha28_1_23 j).mul (piI.mul (atomPoints j).z)).scale 1 24 := by fin_cases j <;> decide +kernel
lemma ha28_1_24_contains (j : Fin 7) : (ha28_1_24 j).Contains (fullFactor true 28 24 ((j.val:ℝ)/6)) := by
  rw [ha28_1_24_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha28_1_23 j) true 28 23 j (ha28_1_23_contains j)
noncomputable def hk28_1_25 (j : Fin 6) (i k : Fin 16) : CBox := (kernel28_0 j i k).mul (mpower1_25 j i k)
lemma hk28_1_25_contains (j : Fin 6) (i k : Fin 16) :
    (hk28_1_25 j i k).Contains (fullFactor true 28 25 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk28_1_25,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel28_0 j i k) (mpower1_25 j i k) (quadraturePoint j.val (16*i.val+k.val)) 28 25 (kernel28_0_contains j i k) (mpower1_25_contains j i k)
noncomputable def ha28_1_25 : Fin 7 → CBox := ![⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-56),56⟩,⟨(-56),56⟩⟩,⟨⟨(-3),3⟩,⟨(-3),3⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨4873,4875⟩,⟨2097,2098⟩⟩,⟨⟨581043593500,581043593501⟩,⟨164986451134,164986451135⟩⟩,⟨⟨(-20583595893836469),(-20583595893836468)⟩,⟨(-25128239863626808),(-25128239863626806)⟩⟩]
lemma ha28_1_25_eq (j : Fin 7) : ha28_1_25 j = ((ha28_1_24 j).mul (piI.mul (atomPoints j).z)).scale 1 25 := by fin_cases j <;> decide +kernel
lemma ha28_1_25_contains (j : Fin 7) : (ha28_1_25 j).Contains (fullFactor true 28 25 ((j.val:ℝ)/6)) := by
  rw [ha28_1_25_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha28_1_24 j) true 28 24 j (ha28_1_24_contains j)
noncomputable def hk28_1_26 (j : Fin 6) (i k : Fin 16) : CBox := (kernel28_0 j i k).mul (mpower1_26 j i k)
lemma hk28_1_26_contains (j : Fin 6) (i k : Fin 16) :
    (hk28_1_26 j i k).Contains (fullFactor true 28 26 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk28_1_26,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel28_0 j i k) (mpower1_26 j i k) (quadraturePoint j.val (16*i.val+k.val)) 28 26 (kernel28_0_contains j i k) (mpower1_26_contains j i k)
noncomputable def ha28_1_26 : Fin 7 → CBox := ![⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-25),25⟩,⟨(-25),25⟩⟩,⟨⟨(-2),2⟩,⟨(-2),2⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨88,89⟩,⟨(-989),(-988)⟩⟩,⟨⟨10184098676,10184098677⟩,⟨(-95766764589),(-95766764587)⟩⟩,⟨⟨(-3341295292824767),(-3341295292824765)⟩,⟨3040242870013470,3040242870013472⟩⟩]
lemma ha28_1_26_eq (j : Fin 7) : ha28_1_26 j = ((ha28_1_25 j).mul (piI.mul (atomPoints j).z)).scale 1 26 := by fin_cases j <;> decide +kernel
lemma ha28_1_26_contains (j : Fin 7) : (ha28_1_26 j).Contains (fullFactor true 28 26 ((j.val:ℝ)/6)) := by
  rw [ha28_1_26_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha28_1_25 j) true 28 25 j (ha28_1_25_contains j)
noncomputable def hk28_1_27 (j : Fin 6) (i k : Fin 16) : CBox := (kernel28_0 j i k).mul (mpower1_27 j i k)
lemma hk28_1_27_contains (j : Fin 6) (i k : Fin 16) :
    (hk28_1_27 j i k).Contains (fullFactor true 28 27 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk28_1_27,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel28_0 j i k) (mpower1_27 j i k) (quadraturePoint j.val (16*i.val+k.val)) 28 27 (kernel28_0_contains j i k) (mpower1_27_contains j i k)
noncomputable def ha28_1_27 : Fin 7 → CBox := ![⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-11),11⟩,⟨(-11),11⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-175),(-173)⟩,⟨40,41⟩⟩,⟨⟨(-14755862815),(-14755862814)⟩,⟨957183581,957183582⟩⟩,⟨⟨429844533006577,429844533006579⟩,⟨425726952013757,425726952013758⟩⟩]
lemma ha28_1_27_eq (j : Fin 7) : ha28_1_27 j = ((ha28_1_26 j).mul (piI.mul (atomPoints j).z)).scale 1 27 := by fin_cases j <;> decide +kernel
lemma ha28_1_27_contains (j : Fin 7) : (ha28_1_27 j).Contains (fullFactor true 28 27 ((j.val:ℝ)/6)) := by
  rw [ha28_1_27_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha28_1_26 j) true 28 26 j (ha28_1_26_contains j)
noncomputable def hk28_1_28 (j : Fin 6) (i k : Fin 16) : CBox := (kernel28_0 j i k).mul (mpower1_28 j i k)
lemma hk28_1_28_contains (j : Fin 6) (i k : Fin 16) :
    (hk28_1_28 j i k).Contains (fullFactor true 28 28 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk28_1_28,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel28_0 j i k) (mpower1_28 j i k) (quadraturePoint j.val (16*i.val+k.val)) 28 28 (kernel28_0_contains j i k) (mpower1_28_contains j i k)
noncomputable def ha28_1_28 : Fin 7 → CBox := ![⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-5),5⟩,⟨(-5),5⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨15,17⟩,⟨26,27⟩⟩,⟨⟨510821671,510821672⟩,⟨2128854238,2128854239⟩⟩,⟨⟨52021348549814,52021348549815⟩,⟨(-58289999246842),(-58289999246840)⟩⟩]
lemma ha28_1_28_eq (j : Fin 7) : ha28_1_28 j = ((ha28_1_27 j).mul (piI.mul (atomPoints j).z)).scale 1 28 := by fin_cases j <;> decide +kernel
lemma ha28_1_28_contains (j : Fin 7) : (ha28_1_28 j).Contains (fullFactor true 28 28 ((j.val:ℝ)/6)) := by
  rw [ha28_1_28_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha28_1_27 j) true 28 27 j (ha28_1_27_contains j)
noncomputable def hk28_1_29 (j : Fin 6) (i k : Fin 16) : CBox := (kernel28_0 j i k).mul (mpower1_29 j i k)
lemma hk28_1_29_contains (j : Fin 6) (i k : Fin 16) :
    (hk28_1_29 j i k).Contains (fullFactor true 28 29 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk28_1_29,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel28_0 j i k) (mpower1_29 j i k) (quadraturePoint j.val (16*i.val+k.val)) 28 29 (kernel28_0_contains j i k) (mpower1_29_contains j i k)
noncomputable def ha28_1_29 : Fin 7 → CBox := ![⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-2),2⟩,⟨(-2),2⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨3,4⟩,⟨(-5),(-3)⟩⟩,⟨⟨287490534,287490535⟩,⟨(-123662777),(-123662776)⟩⟩,⟨⟨(-7594997523036),(-7594997523035)⟩,⟨(-6100177086664),(-6100177086663)⟩⟩]
lemma ha28_1_29_eq (j : Fin 7) : ha28_1_29 j = ((ha28_1_28 j).mul (piI.mul (atomPoints j).z)).scale 1 29 := by fin_cases j <;> decide +kernel
lemma ha28_1_29_contains (j : Fin 7) : (ha28_1_29 j).Contains (fullFactor true 28 29 ((j.val:ℝ)/6)) := by
  rw [ha28_1_29_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha28_1_28 j) true 28 28 j (ha28_1_28_contains j)
noncomputable def hk28_1_30 (j : Fin 6) (i k : Fin 16) : CBox := (kernel28_0 j i k).mul (mpower1_30 j i k)
lemma hk28_1_30_contains (j : Fin 6) (i k : Fin 16) :
    (hk28_1_30 j i k).Contains (fullFactor true 28 30 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk28_1_30,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel28_0 j i k) (mpower1_30 j i k) (quadraturePoint j.val (16*i.val+k.val)) 28 30 (kernel28_0_contains j i k) (mpower1_30_contains j i k)
noncomputable def ha28_1_30 : Fin 7 → CBox := ![⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),0⟩,⟨(-1),0⟩⟩,⟨⟨(-23589337),(-23589336)⟩,⟨(-36246255),(-36246254)⟩⟩,⟨⟨(-686725338050),(-686725338049)⟩,⟨952372817681,952372817682⟩⟩]
lemma ha28_1_30_eq (j : Fin 7) : ha28_1_30 j = ((ha28_1_29 j).mul (piI.mul (atomPoints j).z)).scale 1 30 := by fin_cases j <;> decide +kernel
lemma ha28_1_30_contains (j : Fin 7) : (ha28_1_30 j).Contains (fullFactor true 28 30 ((j.val:ℝ)/6)) := by
  rw [ha28_1_30_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha28_1_29 j) true 28 29 j (ha28_1_29_contains j)
end SharpPlanar.CachedData

end OAI
