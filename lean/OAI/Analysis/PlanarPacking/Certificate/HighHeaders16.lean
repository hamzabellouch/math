import OAI.Analysis.PlanarPacking.Certificate.KernelValues20
import OAI.Analysis.PlanarPacking.Certificate.Powers20
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
noncomputable def hk16_0_0 (j : Fin 6) (i k : Fin 16) : CBox := (power16 j i k).conj.mul (mpower0_0 j i k)
lemma hk16_0_0_contains (j : Fin 6) (i k : Fin 16) :
    (hk16_0_0 j i k).Contains (fullFactor false 16 0 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk16_0_0,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power16 j i k) (mpower0_0 j i k) (quadraturePoint j.val (16*i.val+k.val)) 16 0 (power16_contains j i k) (mpower0_0_contains j i k)
noncomputable def ha16_0_0 : Fin 7 → CBox := ![⟨⟨999999999999999999999999999809,1000000000000000000000000000255⟩,⟨(-255),255⟩⟩,⟨⟨(-500000000000000000041666486146),(-499999999999999999969218260206)⟩,⟨866025403784438646724483957650,866025403784438646796678072649⟩⟩,⟨⟨(-500000000000000000087874065327),(-499999999999999999890356441924)⟩,⟨(-866025403784438646868859290461),(-866025403784438646671155673552)⟩⟩,⟨⟨999999999999999999947733200609,1000000000000000000052266799407⟩,⟨(-33413865663),71119733151⟩⟩,⟨⟨(-500000000000000000292003818150),(-499999999999999999751535167376)⟩,⟨866025403784438646480988208164,866025403784438647021320888286⟩⟩,⟨⟨(-500000000000000000312831245029),(-499999999999999999632745023075)⟩,⟨(-866025403784438647119544536264),(-866025403784438646439323361456)⟩⟩,⟨⟨999999999999999999895148835489,1000000000000000000104851164575⟩,⟨(-67145296991),142557032095⟩⟩]
lemma ha16_0_0_eq (j : Fin 7) : ha16_0_0 j = ((atomPoints j).direct.powBin 7 16).conj := by fin_cases j <;> decide +kernel
lemma ha16_0_0_contains (j : Fin 7) : (ha16_0_0 j).Contains (fullFactor false 16 0 ((j.val:ℝ)/6)) := by
  rw [ha16_0_0_eq]
  simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @direct_factor_zero_full ((atomPoints j).direct.powBin 7 16) ((j.val:ℝ)/6) 16 (@direct_power_bin_contains (atomPoints j) ((j.val:ℝ)/6) (atomPoints_contains j) 16 (by norm_num))
noncomputable def hk16_0_1 (j : Fin 6) (i k : Fin 16) : CBox := (power16 j i k).conj.mul (mpower0_1 j i k)
lemma hk16_0_1_contains (j : Fin 6) (i k : Fin 16) :
    (hk16_0_1 j i k).Contains (fullFactor false 16 1 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk16_0_1,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power16 j i k) (mpower0_1 j i k) (quadraturePoint j.val (16*i.val+k.val)) 16 1 (power16_contains j i k) (mpower0_1_contains j i k)
noncomputable def ha16_0_1 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-453449841058554462666836546856),(-453449841058554462627592420960)⟩,⟨(-261799387799149436560983187798),(-261799387799149436522216052065)⟩⟩,⟨⟨906899682117108925199339593406,906899682117108925409261088246⟩,⟨(-523598775598298873170354839359),(-523598775598298872961848201144)⟩⟩,⟨⟨(-111714615597),52486377448⟩,⟨1570796326794896619147899503503,1570796326794896619317100496522⟩⟩,⟨⟨(-1813799364234217851137837000277),(-1813799364234217850000393378670)⟩,⟨(-1047197551196597746768238033281),(-1047197551196597745632949804767)⟩⟩,⟨⟨2267249205292772312391413409730,2267249205292772314179445159427⟩,⟨(-1308996938995747183514823617665),(-1308996938995747181730195385414)⟩⟩,⟨⟨(-447856124748),210943171751⟩,⟨3141592653589793238130600351851,3141592653589793238799399648350⟩⟩]
lemma ha16_0_1_eq (j : Fin 7) : ha16_0_1 j = ((ha16_0_0 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 1 := by fin_cases j <;> decide +kernel
lemma ha16_0_1_contains (j : Fin 7) : (ha16_0_1 j).Contains (fullFactor false 16 1 ((j.val:ℝ)/6)) := by
  rw [ha16_0_1_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha16_0_0 j) false 16 0 j (ha16_0_0_contains j)
noncomputable def hk16_0_2 (j : Fin 6) (i k : Fin 16) : CBox := (power16 j i k).conj.mul (mpower0_2 j i k)
lemma hk16_0_2_contains (j : Fin 6) (i k : Fin 16) :
    (hk16_0_2 j i k).Contains (fullFactor false 16 2 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk16_0_2,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power16 j i k) (mpower0_2 j i k) (quadraturePoint j.val (16*i.val+k.val)) 16 2 (power16_contains j i k) (mpower0_2_contains j i k)
noncomputable def ha16_0_2 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨68538919452009434848682464886,68538919452009434859049843446⟩,⟨(-118712890786751174413010674317),(-118712890786751174402358711313)⟩⟩,⟨⟨274155677808037739351489029060,274155677808037739461535514162⟩,⟨474851563147004697580194341509,474851563147004697691620478652⟩⟩,⟨⟨(-1233700550136169827424570827429),(-1233700550136169827287753687448)⟩,⟨(-87740453915),41222704452⟩⟩,⟨⟨1096622711232150957101486991300,1096622711232150958293848702609⟩,⟨(-1899406252588018791100867616133),(-1899406252588018789903693443076)⟩⟩,⟨⟨1713472986300235870063986017312,1713472986300235872405513064489⟩,⟨2967822269668779359081737826186,2967822269668779361431712785060⟩⟩,⟨⟨(-4934802200544679309957776750659),(-4934802200544679308891521309086)⟩,⟨(-703490755687),331348759349⟩⟩]
lemma ha16_0_2_eq (j : Fin 7) : ha16_0_2 j = ((ha16_0_1 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 2 := by fin_cases j <;> decide +kernel
lemma ha16_0_2_contains (j : Fin 7) : (ha16_0_2 j).Contains (fullFactor false 16 2 ((j.val:ℝ)/6)) := by
  rw [ha16_0_2_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha16_0_1 j) false 16 1 j (ha16_0_1_contains j)
noncomputable def hk16_0_3 (j : Fin 6) (i k : Fin 16) : CBox := (power16 j i k).conj.mul (mpower0_3 j i k)
lemma hk16_0_3_contains (j : Fin 6) (i k : Fin 16) :
    (hk16_0_3 j i k).Contains (fullFactor false 16 3 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk16_0_3,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power16 j i k) (mpower0_3 j i k) (quadraturePoint j.val (16*i.val+k.val)) 16 3 (power16_contains j i k) (mpower0_3_contains j i k)
noncomputable def ha16_0_3 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨20719308087892496641424336985,20719308087892496643349406855⟩,⟨11962298101967523215080707308,11962298101967523216928233393⟩⟩,⟨⟨(-165754464703139973160610506749),(-165754464703139973121187834581)⟩,⟨95698384815740185705551761201,95698384815740185744269848528⟩⟩,⟨⟨(-21584157578),45940794241⟩,⟨(-645964097506246253694056970855),(-645964097506246253620363516296)⟩⟩,⟨⟨1326035717625119784678323168137,1326035717625119785518329312511⟩,⟨765587078525921485431854541577,765587078525921486266716990420⟩⟩,⟨⟨(-2589913510986562081384232077942),(-2589913510986562079325248108600)⟩,⟨1495287262745940400878840122096,1495287262745940402926967594170⟩⟩,⟨⟨(-346987609383),736693796645⟩,⟨(-5167712780049970029824196662745),(-5167712780049970028691167234710)⟩⟩]
lemma ha16_0_3_eq (j : Fin 7) : ha16_0_3 j = ((ha16_0_2 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 3 := by fin_cases j <;> decide +kernel
lemma ha16_0_3_contains (j : Fin 7) : (ha16_0_3 j).Contains (fullFactor false 16 3 ((j.val:ℝ)/6)) := by
  rw [ha16_0_3_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha16_0_2 j) false 16 2 j (ha16_0_2_contains j)
noncomputable def hk16_0_4 (j : Fin 6) (i k : Fin 16) : CBox := (power16 j i k).conj.mul (mpower0_4 j i k)
lemma hk16_0_4_contains (j : Fin 6) (i k : Fin 16) :
    (hk16_0_4 j i k).Contains (fullFactor false 16 4 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk16_0_4,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power16 j i k) (mpower0_4 j i k) (quadraturePoint j.val (16*i.val+k.val)) 16 4 (power16_contains j i k) (mpower0_4_contains j i k)
noncomputable def ha16_0_4 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1565861159883012430000484294),(-1565861159883012429753659403)⟩,⟨2712151086516110563263935768,2712151086516110563524559871⟩⟩,⟨⟨(-25053778558128198882323097614),(-25053778558128198872106977400)⟩,⟨(-43394417384257769020009782413),(-43394417384257769009550822252)⟩⟩,⟨⟨253669507901048013622451107748,253669507901048013652197914803⟩,⟨(-8476078861),18040907711⟩⟩,⟨⟨(-400860456930051182280824653794),(-400860456930051181842415719321)⟩,⟨694310678148124304000351921904,694310678148124304442388170125⟩⟩,⟨⟨(-978663224926882769281060638439),(-978663224926882767937449160830)⟩,⟨(-1695094429072569102834804987656),(-1695094429072569101481807477850)⟩⟩,⟨⟨4058712126416768217745792923601,4058712126416768218648591437406⟩,⟨(-272523431132),578597954872⟩⟩]
lemma ha16_0_4_eq (j : Fin 7) : ha16_0_4 j = ((ha16_0_3 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 4 := by fin_cases j <;> decide +kernel
lemma ha16_0_4_contains (j : Fin 7) : (ha16_0_4 j).Contains (fullFactor false 16 4 ((j.val:ℝ)/6)) := by
  rw [ha16_0_4_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha16_0_3 j) false 16 3 j (ha16_0_3_contains j)
noncomputable def hk16_0_5 (j : Fin 6) (i k : Fin 16) : CBox := (power16 j i k).conj.mul (mpower0_5 j i k)
lemma hk16_0_5_contains (j : Fin 6) (i k : Fin 16) :
    (hk16_0_5 j i k).Contains (fullFactor false 16 5 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk16_0_5,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power16 j i k) (mpower0_5 j i k) (quadraturePoint j.val (16*i.val+k.val)) 16 5 (power16_contains j i k) (mpower0_5_contains j i k)
noncomputable def ha16_0_5 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-284015797627486289501357103),(-284015797627486289473160559)⟩,⟨(-163976597214335483802633020),(-163976597214335483776263623)⟩⟩,⟨⟨9088505524079561262581484121,9088505524079561264800933227⟩,⟨(-5247251110858735482169182174),(-5247251110858735480012820439)⟩⟩,⟨⟨(-5667718313),2662838709⟩,⟨79692626246167045116004998113,79692626246167045125603902673⟩⟩,⟨⟨(-290832176770545960524830137722),(-290832176770545960338744679479)⟩,⟨(-167912035547479535497965514161),(-167912035547479535313790728509)⟩⟩,⟨⟨887549367585894654311378848381,887549367585894655022631845287⟩,⟨(-512426866294798387161132401872),(-512426866294798386455987971939)⟩⟩,⟨⟨(-363543816882),171231521836⟩,⟨2550164039877345443578061182647,2550164039877345444153423642629⟩⟩]
lemma ha16_0_5_eq (j : Fin 7) : ha16_0_5 j = ((ha16_0_4 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 5 := by fin_cases j <;> decide +kernel
lemma ha16_0_5_contains (j : Fin 7) : (ha16_0_5 j).Contains (fullFactor false 16 5 ((j.val:ℝ)/6)) := by
  rw [ha16_0_5_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha16_0_4 j) false 16 4 j (ha16_0_4_contains j)
noncomputable def hk16_0_6 (j : Fin 6) (i k : Fin 16) : CBox := (power16 j i k).conj.mul (mpower0_6 j i k)
lemma hk16_0_6_contains (j : Fin 6) (i k : Fin 16) :
    (hk16_0_6 j i k).Contains (fullFactor false 16 6 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk16_0_6,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power16 j i k) (mpower0_6 j i k) (quadraturePoint j.val (16*i.val+k.val)) 16 6 (power16_contains j i k) (mpower0_6_contains j i k)
noncomputable def ha16_0_6 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨14309657588033580844761234,14309657588033580847107948⟩,⟨(-24785053981387676528195828),(-24785053981387676525656321)⟩⟩,⟨⟨915818085634149173920272839,915818085634149174299544101⟩,⟨1586243454808811297544326570,1586243454808811297936742686⟩⟩,⟨⟨(-20863480763352960874435238650),(-20863480763352960871855840790)⟩,⟨(-1483805185),697129544⟩⟩,⟨⟨58612357480585547114624177387,58612357480585547179099874492⟩,⟨(-101519581107763923085823799213),(-101519581107763923020544573620)⟩⟩,⟨⟨223588399813024700548931261374,223588399813024700857320265467⟩,⟨387266468459182445585862822882,387266468459182445897438195606⟩⟩,⟨⟨(-1335262768854589496034069218596),(-1335262768854589495728559865624)⟩,⟨(-190351097396),89656615178⟩⟩]
lemma ha16_0_6_eq (j : Fin 7) : ha16_0_6 j = ((ha16_0_5 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 6 := by fin_cases j <;> decide +kernel
lemma ha16_0_6_contains (j : Fin 7) : (ha16_0_6 j).Contains (fullFactor false 16 6 ((j.val:ℝ)/6)) := by
  rw [ha16_0_6_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha16_0_5 j) false 16 5 j (ha16_0_5_contains j)
noncomputable def hk16_0_7 (j : Fin 6) (i k : Fin 16) : CBox := (power16 j i k).conj.mul (mpower0_7 j i k)
lemma hk16_0_7_contains (j : Fin 6) (i k : Fin 16) :
    (hk16_0_7 j i k).Contains (fullFactor false 16 7 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk16_0_7,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power16 j i k) (mpower0_7 j i k) (quadraturePoint j.val (16*i.val+k.val)) 16 7 (power16_contains j i k) (mpower0_7_contains j i k)
noncomputable def ha16_0_7 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1853917702541761442162643,1853917702541761442358500⟩,⟨1070359884617898514030558,1070359884617898514209500⟩⟩,⟨⟨(-237301465925345464641666419),(-237301465925345464582205750)⟩,⟨137006065231091009774302419,137006065231091009831477372⟩⟩,⟨⟨(-156435504),332965105⟩,⟨(-4681754135318688101006906555),(-4681754135318688100413188541)⟩⟩,⟨⟨30374587638444219459852487519,30374587638444219479480671459⟩,⟨17536776349579649246241754375,17536776349579649265588659132⟩⟩,⟨⟨(-144837320511075112738255137216),(-144837320511075112621265188802)⟩,⟨83621865985773321352364358852,83621865985773321467967753342⟩⟩,⟨⟨(-40237794799),85429372741⟩,⟨(-599264529320792076960395983747),(-599264529320792076821376188519)⟩⟩]
lemma ha16_0_7_eq (j : Fin 7) : ha16_0_7 j = ((ha16_0_6 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 7 := by fin_cases j <;> decide +kernel
lemma ha16_0_7_contains (j : Fin 7) : (ha16_0_7 j).Contains (fullFactor false 16 7 ((j.val:ℝ)/6)) := by
  rw [ha16_0_7_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha16_0_6 j) false 16 6 j (ha16_0_6_contains j)
noncomputable def hk16_0_8 (j : Fin 6) (i k : Fin 16) : CBox := (power16 j i k).conj.mul (mpower0_8 j i k)
lemma hk16_0_8_contains (j : Fin 6) (i k : Fin 16) :
    (hk16_0_8 j i k).Contains (fullFactor false 16 8 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk16_0_8,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power16 j i k) (mpower0_8 j i k) (quadraturePoint j.val (16*i.val+k.val)) 16 8 (power16_contains j i k) (mpower0_8_contains j i k)
noncomputable def ha16_0_8 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-70054890629433514733695),(-70054890629433514721760)⟩,⟨121338629888859693708276,121338629888859693721482⟩⟩,⟨⟨(-17934052001134979773483222),(-17934052001134979765941951)⟩,⟨(-31062689251548081595288265),(-31062689251548081587406005)⟩⟩,⟨⟨919260274839426580187481593,919260274839426580306983950⟩,⟨(-30716040),65377546⟩⟩,⟨⟨(-4591117312290554823886071952),(-4591117312290554818806450149)⟩,⟨7952048448396308884629775253,7952048448396308889793733950⟩⟩,⟨⟨(-27365191652122466707690443225),(-27365191652122466669772214732)⟩,⟨(-47397902300335817877624312226),(-47397902300335817839188568924)⟩⟩,⟨⟨235330630358893204515620576300,235330630358893204570962602886⟩,⟨(-15801345068),33548036226⟩⟩]
lemma ha16_0_8_eq (j : Fin 7) : ha16_0_8 j = ((ha16_0_7 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 8 := by fin_cases j <;> decide +kernel
lemma ha16_0_8_contains (j : Fin 7) : (ha16_0_8 j).Contains (fullFactor false 16 8 ((j.val:ℝ)/6)) := by
  rw [ha16_0_8_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha16_0_7 j) false 16 7 j (ha16_0_7_contains j)
noncomputable def hk16_0_9 (j : Fin 6) (i k : Fin 16) : CBox := (power16 j i k).conj.mul (mpower0_9 j i k)
lemma hk16_0_9_contains (j : Fin 6) (i k : Fin 16) :
    (hk16_0_9 j i k).Contains (fullFactor false 16 9 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk16_0_9,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power16 j i k) (mpower0_9 j i k) (quadraturePoint j.val (16*i.val+k.val)) 16 9 (power16_contains j i k) (mpower0_9_contains j i k)
noncomputable def ha16_0_9 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-7059195338064676366980),(-7059195338064676366188)⟩,⟨(-4075628328693792152859),(-4075628328693792152150)⟩⟩,⟨⟨3614308013089114299266165,3614308013089114300194813⟩,⟨(-2086721704291221582456196),(-2086721704291221581572086)⟩⟩,⟨⟨(-11410535),5360961⟩,⟨160441184787359821863060144,160441184787359821884427941⟩⟩,⟨⟨(-1850525702701626522025524368),(-1850525702701626520817926205)⟩,⟨(-1068401512597105450653757128),(-1068401512597105449468274629)⟩⟩,⟨⟨13787490894657571023172860107,13787490894657571034397251573⟩,⟨(-7960211579480062802868047623),(-7960211579480062791812743919)⟩⟩,⟨⟨(-11710473795),5515709954⟩,⟨82145886611128228789567204599,82145886611128228809146694651⟩⟩]
lemma ha16_0_9_eq (j : Fin 7) : ha16_0_9 j = ((ha16_0_8 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 9 := by fin_cases j <;> decide +kernel
lemma ha16_0_9_contains (j : Fin 7) : (ha16_0_9 j).Contains (fullFactor false 16 9 ((j.val:ℝ)/6)) := by
  rw [ha16_0_9_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha16_0_8 j) false 16 8 j (ha16_0_8_contains j)
noncomputable def hk16_0_10 (j : Fin 6) (i k : Fin 16) : CBox := (power16 j i k).conj.mul (mpower0_10 j i k)
lemma hk16_0_10_contains (j : Fin 6) (i k : Fin 16) :
    (hk16_0_10 j i k).Contains (fullFactor false 16 10 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk16_0_10,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power16 j i k) (mpower0_10 j i k) (quadraturePoint j.val (16*i.val+k.val)) 16 10 (power16_contains j i k) (mpower0_10_contains j i k)
noncomputable def ha16_0_10 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨213399400269781075710,213399400269781075749⟩,⟨(-369618603571988403213),(-369618603571988403169)⟩⟩,⟨⟨218520985876255821493353,218520985876255821586633⟩,⟨378489450057716124822786,378489450057716124921239⟩⟩,⟨⟨(-25202042373060605482960405),(-25202042373060605479523737)⟩,⟨(-1792363),842098⟩⟩,⟨⟨223765489537285961147066909,223765489537285961396066051⟩,⟨(-387573196859101311987579652),(-387573196859101311733427199)⟩⟩,⟨⟨2083978518259580816085493563,2083978518259580818986398816⟩,⟨3609556675507699248518616798,3609556675507699251468645189⟩⟩,⟨⟨(-25806891390014060015908492673),(-25806891390014060009675268575)⟩,⟨(-3678953845),1732811388⟩⟩]
lemma ha16_0_10_eq (j : Fin 7) : ha16_0_10 j = ((ha16_0_9 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 10 := by fin_cases j <;> decide +kernel
lemma ha16_0_10_contains (j : Fin 7) : (ha16_0_10 j).Contains (fullFactor false 16 10 ((j.val:ℝ)/6)) := by
  rw [ha16_0_10_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha16_0_9 j) false 16 9 j (ha16_0_9_contains j)
noncomputable def hk16_0_11 (j : Fin 6) (i k : Fin 16) : CBox := (power16 j i k).conj.mul (mpower0_11 j i k)
lemma hk16_0_11_contains (j : Fin 6) (i k : Fin 16) :
    (hk16_0_11 j i k).Contains (fullFactor false 16 11 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk16_0_11,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power16 j i k) (mpower0_11 j i k) (quadraturePoint j.val (16*i.val+k.val)) 16 11 (power16_contains j i k) (mpower0_11_contains j i k)
noncomputable def ha16_0_11 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨17593804388058740563,17593804388058740566⟩,⟨10157787699515332859,10157787699515332862⟩⟩,⟨⟨(-36032111386744300681469),(-36032111386744300671981)⟩,⟨20803149208607401693437,20803149208607401702384⟩⟩,⟨⟨(-120252),255949⟩,⟨(-3598843235212085340739342),(-3598843235212085340237130)⟩⟩,⟨⟨73793764120052327760013457,73793764120052327808638865⟩,⟨42604849579227958656330423,42604849579227958703875365⟩⟩,⟨⟨(-859072479885680692002741520),(-859072479885680691297901891)⟩,⟨495985727515397111957524334,495985727515397112649516942⟩⟩,⟨⟨(-494889776),1050706762⟩,⟨(-7370430945714350778221739635),(-7370430945714350776418074184)⟩⟩]
lemma ha16_0_11_eq (j : Fin 7) : ha16_0_11 j = ((ha16_0_10 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 11 := by fin_cases j <;> decide +kernel
lemma ha16_0_11_contains (j : Fin 7) : (ha16_0_11 j).Contains (fullFactor false 16 11 ((j.val:ℝ)/6)) := by
  rw [ha16_0_11_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha16_0_10 j) false 16 10 j (ha16_0_10_contains j)
noncomputable def hk16_0_12 (j : Fin 6) (i k : Fin 16) : CBox := (power16 j i k).conj.mul (mpower0_12 j i k)
lemma hk16_0_12_contains (j : Fin 6) (i k : Fin 16) :
    (hk16_0_12 j i k).Contains (fullFactor false 16 12 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk16_0_12,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power16 j i k) (mpower0_12 j i k) (quadraturePoint j.val (16*i.val+k.val)) 16 12 (power16_contains j i k) (mpower0_12_contains j i k)
noncomputable def ha16_0_12 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-443217100187807443),(-443217100187807442)⟩,⟨767674536308627877,767674536308627878⟩⟩,⟨⟨(-1815417242369259285882),(-1815417242369259285095)⟩,⟨(-3144394900720139785396),(-3144394900720139784557)⟩⟩,⟨⟨471087477881817150337648,471087477881817150404888⟩,⟨(-15741),33504⟩⟩,⟨⟨(-7435949024744486038007907),(-7435949024744486029686079)⟩,⟨12879441513349692554718068,12879441513349692563245801⟩⟩,⟨⟨(-108207299850538926523843114),(-108207299850538926372529311)⟩,⟨(-187420541090973602909166540),(-187420541090973602754797808)⟩⟩,⟨⟨1929574309403923047681544576,1929574309403923048159885113⟩,⟨(-129561841),275074388⟩⟩]
lemma ha16_0_12_eq (j : Fin 7) : ha16_0_12 j = ((ha16_0_11 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 12 := by fin_cases j <;> decide +kernel
lemma ha16_0_12_contains (j : Fin 7) : (ha16_0_12 j).Contains (fullFactor false 16 12 ((j.val:ℝ)/6)) := by
  rw [ha16_0_12_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha16_0_11 j) false 16 11 j (ha16_0_11_contains j)
noncomputable def hk16_0_13 (j : Fin 6) (i k : Fin 16) : CBox := (power16 j i k).conj.mul (mpower0_13 j i k)
lemma hk16_0_13_contains (j : Fin 6) (i k : Fin 16) :
    (hk16_0_13 j i k).Contains (fullFactor false 16 13 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk16_0_13,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power16 j i k) (mpower0_13 j i k) (quadraturePoint j.val (16*i.val+k.val)) 16 13 (power16_contains j i k) (mpower0_13_contains j i k)
noncomputable def ha16_0_13 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-30919495943783800),(-30919495943783799)⟩,⟨(-17851379306351119),(-17851379306351118)⟩⟩,⟨⟨253292510771476882251,253292510771476882320⟩,⟨(-146238499277628361542),(-146238499277628361477)⟩⟩,⟨⟨(-4049),1902⟩,⟨56921729219679268114154,56921729219679268122461⟩⟩,⟨⟨(-2074972248239938620325396),(-2074972248239938618944910)⟩,⟨(-1197985786082331538239416),(-1197985786082331536894895)⟩⟩,⟨⟨37743525322001707879191293,37743525322001707910398850⟩,⟨(-21791234504823142529663850),(-21791234504823142499122285)⟩⟩,⟨⟨(-66474745),31310041⟩,⟨466302805767612564366635917,466302805767612564483716446⟩⟩]
lemma ha16_0_13_eq (j : Fin 7) : ha16_0_13 j = ((ha16_0_12 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 13 := by fin_cases j <;> decide +kernel
lemma ha16_0_13_contains (j : Fin 7) : (ha16_0_13 j).Contains (fullFactor false 16 13 ((j.val:ℝ)/6)) := by
  rw [ha16_0_13_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha16_0_12 j) false 16 12 j (ha16_0_12_contains j)
noncomputable def hk16_0_14 (j : Fin 6) (i k : Fin 16) : CBox := (power16 j i k).conj.mul (mpower0_14 j i k)
lemma hk16_0_14_contains (j : Fin 6) (i k : Fin 16) :
    (hk16_0_14 j i k).Contains (fullFactor false 16 14 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk16_0_14,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power16 j i k) (mpower0_14 j i k) (quadraturePoint j.val (16*i.val+k.val)) 16 14 (power16_contains j i k) (mpower0_14_contains j i k)
noncomputable def ha16_0_14 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨667640024824732,667640024824733⟩,⟨(-1156386444162984),(-1156386444162983)⟩⟩,⟨⟨10938614166728417756,10938614166728417762⟩,⟨18946235501166317748,18946235501166317754⟩⟩,⟨⟨(-6386603083791852241634),(-6386603083791852240680)⟩,⟨(-455),214⟩⟩,⟨⟨179218254507678396467702,179218254507678396669413⟩,⟨(-310415122451108950133811),(-310415122451108949926302)⟩⟩,⟨⟨4074951323393142875491402,4074951323393142881215633⟩,⟨7058022730486958378409522,7058022730486958384267789⟩⟩,⟨⟨(-104638104924845707132418567),(-104638104924845707105812683)⟩,⟨(-14916898),7025957⟩⟩]
lemma ha16_0_14_eq (j : Fin 7) : ha16_0_14 j = ((ha16_0_13 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 14 := by fin_cases j <;> decide +kernel
lemma ha16_0_14_contains (j : Fin 7) : (ha16_0_14 j).Contains (fullFactor false 16 14 ((j.val:ℝ)/6)) := by
  rw [ha16_0_14_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha16_0_13 j) false 16 13 j (ha16_0_13_contains j)
noncomputable def hk16_0_15 (j : Fin 6) (i k : Fin 16) : CBox := (power16 j i k).conj.mul (mpower0_15 j i k)
lemma hk16_0_15_contains (j : Fin 6) (i k : Fin 16) :
    (hk16_0_15 j i k).Contains (fullFactor false 16 15 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk16_0_15,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power16 j i k) (mpower0_15 j i k) (quadraturePoint j.val (16*i.val+k.val)) 16 15 (power16_contains j i k) (mpower0_15_contains j i k)
noncomputable def ha16_0_15 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨40365501752147,40365501752148⟩,⟨23305033302576,23305033302577⟩⟩,⟨⟨(-1322696761414360853),(-1322696761414360852)⟩,⟨763659331258827443,763659331258827444⟩⟩,⟨⟨(-23),48⟩,⟨(-668803510981146723307),(-668803510981146723204)⟩⟩,⟨⟨43342127478025776405707,43342127478025776434819⟩,⟨25023588966689257650977,25023588966689257679221⟩⟩,⟨⟨(-1231857353275977869763401),(-1231857353275977868737019)⟩,⟨711213174517105745878554,711213174517105746879886⟩⟩,⟨⟨(-1471513),3124188⟩,⟨(-21915353447830215830452285),(-21915353447830215824810202)⟩⟩]
lemma ha16_0_15_eq (j : Fin 7) : ha16_0_15 j = ((ha16_0_14 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 15 := by fin_cases j <;> decide +kernel
lemma ha16_0_15_contains (j : Fin 7) : (ha16_0_15 j).Contains (fullFactor false 16 15 ((j.val:ℝ)/6)) := by
  rw [ha16_0_15_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha16_0_14 j) false 16 14 j (ha16_0_14_contains j)
noncomputable def hk16_0_16 (j : Fin 6) (i k : Fin 16) : CBox := (power16 j i k).conj.mul (mpower0_16 j i k)
lemma hk16_0_16_contains (j : Fin 6) (i k : Fin 16) :
    (hk16_0_16 j i k).Contains (fullFactor false 16 16 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk16_0_16,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power16 j i k) (mpower0_16 j i k) (quadraturePoint j.val (16*i.val+k.val)) 16 16 (power16_contains j i k) (mpower0_16_contains j i k)
noncomputable def ha16_0_16 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-762655431407),(-762655431406)⟩,⟨1320957955864,1320957955865⟩⟩,⟨⟨(-49981386352667222),(-49981386352667221)⟩,⟨(-86570300595549324),(-86570300595549323)⟩⟩,⟨⟨65659631149794723617,65659631149794723629⟩,⟨(-3),5⟩⟩,⟨⟨(-3275580136008399051412),(-3275580136008399047703)⟩,⟨5673471219829920492825,5673471219829920496654⟩⟩,⟨⟨(-116371983552042445763693),(-116371983552042445599479)⟩,⟨(-201562188089707223685470),(-201562188089707223516886)⟩⟩,⟨⟨4303069587032947006788710,4303069587032947007910229⟩,⟨(-288931),613433⟩⟩]
lemma ha16_0_16_eq (j : Fin 7) : ha16_0_16 j = ((ha16_0_15 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 16 := by fin_cases j <;> decide +kernel
lemma ha16_0_16_contains (j : Fin 7) : (ha16_0_16 j).Contains (fullFactor false 16 16 ((j.val:ℝ)/6)) := by
  rw [ha16_0_16_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha16_0_15 j) false 16 15 j (ha16_0_15_contains j)
noncomputable def hk16_0_17 (j : Fin 6) (i k : Fin 16) : CBox := (power16 j i k).conj.mul (mpower0_17 j i k)
lemma hk16_0_17_contains (j : Fin 6) (i k : Fin 16) :
    (hk16_0_17 j i k).Contains (fullFactor false 16 17 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk16_0_17,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power16 j i k) (mpower0_17 j i k) (quadraturePoint j.val (16*i.val+k.val)) 16 17 (power16_contains j i k) (mpower0_17_contains j i k)
noncomputable def ha16_0_17 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-40685409901),(-40685409900)⟩,⟨(-23489732359),(-23489732358)⟩⟩,⟨⟨5332718046471330,5332718046471331⟩,⟨(-3078846199642598),(-3078846199642597)⟩⟩,⟨⟨(-1),1⟩,⟨6066935731106195666,6066935731106195668⟩⟩,⟨⟨(-698970019787090239450),(-698970019787090238975)⟩,⟨(-403550529079554596961),(-403550529079554596502)⟩⟩,⟨⟨31040504379613153626774,31040504379613153652835⟩,⟨(-17921243559351411754986),(-17921243559351411729639)⟩⟩,⟨⟨(-113363),53395⟩,⟨795205400147551278383567,795205400147551278593356⟩⟩]
lemma ha16_0_17_eq (j : Fin 7) : ha16_0_17 j = ((ha16_0_16 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 17 := by fin_cases j <;> decide +kernel
lemma ha16_0_17_contains (j : Fin 7) : (ha16_0_17 j).Contains (fullFactor false 16 17 ((j.val:ℝ)/6)) := by
  rw [ha16_0_17_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha16_0_16 j) false 16 16 j (ha16_0_16_contains j)
noncomputable def hk16_0_18 (j : Fin 6) (i k : Fin 16) : CBox := (power16 j i k).conj.mul (mpower0_18 j i k)
lemma hk16_0_18_contains (j : Fin 6) (i k : Fin 16) :
    (hk16_0_18 j i k).Contains (fullFactor false 16 18 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk16_0_18,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power16 j i k) (mpower0_18 j i k) (quadraturePoint j.val (16*i.val+k.val)) 16 18 (power16_contains j i k) (mpower0_18_contains j i k)
noncomputable def ha16_0_18 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨683288616,683288617⟩,⟨(-1183490601),(-1183490600)⟩⟩,⟨⟨179120011154259,179120011154260⟩,⟨310244959971482,310244959971483⟩⟩,⟨⟨(-529440020073462377),(-529440020073462376)⟩,⟨(-1),1⟩⟩,⟨⟨46955236204022331344,46955236204022331399⟩,⟨(-81328854786764263410),(-81328854786764263354)⟩⟩,⟨⟨2606539218020916333847,2606539218020916337543⟩,⟨4514658357533078056366,4514658357533078060172⟩⟩,⟨⟨(-138789524622137721165084),(-138789524622137721128026)⟩,⟨(-19786),9320⟩⟩]
lemma ha16_0_18_eq (j : Fin 7) : ha16_0_18 j = ((ha16_0_17 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 18 := by fin_cases j <;> decide +kernel
lemma ha16_0_18_contains (j : Fin 7) : (ha16_0_18 j).Contains (fullFactor false 16 18 ((j.val:ℝ)/6)) := by
  rw [ha16_0_18_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha16_0_17 j) false 16 17 j (ha16_0_17_contains j)
noncomputable def hk16_0_19 (j : Fin 6) (i k : Fin 16) : CBox := (power16 j i k).conj.mul (mpower0_19 j i k)
lemma hk16_0_19_contains (j : Fin 6) (i k : Fin 16) :
    (hk16_0_19 j i k).Contains (fullFactor false 16 19 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk16_0_19,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power16 j i k) (mpower0_19 j i k) (quadraturePoint j.val (16*i.val+k.val)) 16 19 (power16_contains j i k) (mpower0_19_contains j i k)
noncomputable def ha16_0_19 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨32614433,32614434⟩,⟨18829951,18829952⟩⟩,⟨⟨(-17099355913328),(-17099355913327)⟩,⟨9872317739528,9872317739529⟩⟩,⟨⟨(-1),1⟩,⟨(-43770654673137423),(-43770654673137422)⟩⟩,⟨⟨8964987113086656141,8964987113086656148⟩,⟨5175937723022106877,5175937723022106885⟩⟩,⟨⟨(-622070944276038605772),(-622070944276038605244)⟩,⟨359152827132815577250,359152827132815577761⟩⟩,⟨⟨(-1542),3272⟩,⟨(-22948428997269873113632),(-22948428997269873107430)⟩⟩]
lemma ha16_0_19_eq (j : Fin 7) : ha16_0_19 j = ((ha16_0_18 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 19 := by fin_cases j <;> decide +kernel
lemma ha16_0_19_contains (j : Fin 7) : (ha16_0_19 j).Contains (fullFactor false 16 19 ((j.val:ℝ)/6)) := by
  rw [ha16_0_19_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha16_0_18 j) false 16 18 j (ha16_0_18_contains j)
noncomputable def hk16_0_20 (j : Fin 6) (i k : Fin 16) : CBox := (power16 j i k).conj.mul (mpower0_20 j i k)
lemma hk16_0_20_contains (j : Fin 6) (i k : Fin 16) :
    (hk16_0_20 j i k).Contains (fullFactor false 16 20 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk16_0_20,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power16 j i k) (mpower0_20 j i k) (quadraturePoint j.val (16*i.val+k.val)) 16 20 (power16_contains j i k) (mpower0_20_contains j i k)
noncomputable def ha16_0_20 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-492967),(-492966)⟩,⟨853843,853844⟩⟩,⟨⟨(-516913348074),(-516913348073)⟩,⟨(-895320181974),(-895320181973)⟩⟩,⟨⟨3437739179098606,3437739179098608⟩,⟨(-1),1⟩⟩,⟨⟨(-542022930869484434),(-542022930869484433)⟩,⟨938811255133340262,938811255133340263⟩⟩,⟨⟨(-47012995134852432639),(-47012995134852432571)⟩,⟨(-81428896189552855193),(-81428896189552855123)⟩⟩,⟨⟨3604730797462500933420,3604730797462500934407⟩,⟨(-243),514⟩⟩]
lemma ha16_0_20_eq (j : Fin 7) : ha16_0_20 j = ((ha16_0_19 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 20 := by fin_cases j <;> decide +kernel
lemma ha16_0_20_contains (j : Fin 7) : (ha16_0_20 j).Contains (fullFactor false 16 20 ((j.val:ℝ)/6)) := by
  rw [ha16_0_20_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha16_0_19 j) false 16 19 j (ha16_0_19_contains j)
noncomputable def hk16_0_21 (j : Fin 6) (i k : Fin 16) : CBox := (power16 j i k).conj.mul (mpower0_21 j i k)
lemma hk16_0_21_contains (j : Fin 6) (i k : Fin 16) :
    (hk16_0_21 j i k).Contains (fullFactor false 16 21 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk16_0_21,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power16 j i k) (mpower0_21 j i k) (quadraturePoint j.val (16*i.val+k.val)) 16 21 (power16_contains j i k) (mpower0_21_contains j i k)
noncomputable def ha16_0_21 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-21290),(-21289)⟩,⟨(-12292),(-12291)⟩⟩,⟨⟨44646528671,44646528672⟩,⟨(-25776685347),(-25776685346)⟩⟩,⟨⟨(-1),1⟩,⟨257142289286047,257142289286048⟩⟩,⟨⟨(-93630556896327456),(-93630556896327455)⟩,⟨(-54057627228469228),(-54057627228469227)⟩⟩,⟨⟨10151445319802585611,10151445319802585620⟩,⟨(-5860939688051789416),(-5860939688051789406)⟩⟩,⟨⟨(-77),37⟩,⟨539266466260812848869,539266466260812849019⟩⟩]
lemma ha16_0_21_eq (j : Fin 7) : ha16_0_21 j = ((ha16_0_20 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 21 := by fin_cases j <;> decide +kernel
lemma ha16_0_21_contains (j : Fin 7) : (ha16_0_21 j).Contains (fullFactor false 16 21 ((j.val:ℝ)/6)) := by
  rw [ha16_0_21_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha16_0_20 j) false 16 20 j (ha16_0_20_contains j)
noncomputable def hk16_0_22 (j : Fin 6) (i k : Fin 16) : CBox := (power16 j i k).conj.mul (mpower0_22 j i k)
lemma hk16_0_22_contains (j : Fin 6) (i k : Fin 16) :
    (hk16_0_22 j i k).Contains (fullFactor false 16 22 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk16_0_22,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power16 j i k) (mpower0_22 j i k) (quadraturePoint j.val (16*i.val+k.val)) 16 22 (power16_contains j i k) (mpower0_22_contains j i k)
noncomputable def ha16_0_22 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨292,293⟩,⟨(-507),(-506)⟩⟩,⟨⟨1226967353,1226967354⟩,⟨2125169795,2125169796⟩⟩,⟨⟨(-18359916521553),(-18359916521552)⟩,⟨(-1),1⟩⟩,⟨⟨5146274077922863,5146274077922864⟩,⟨(-8913608172637076),(-8913608172637075)⟩⟩,⟨⟨697450191936225609,697450191936225611⟩,⟨1208019168182208036,1208019168182208039⟩⟩,⟨⟨(-77007071306013533811),(-77007071306013533788)⟩,⟨(-11),6⟩⟩]
lemma ha16_0_22_eq (j : Fin 7) : ha16_0_22 j = ((ha16_0_21 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 22 := by fin_cases j <;> decide +kernel
lemma ha16_0_22_contains (j : Fin 7) : (ha16_0_22 j).Contains (fullFactor false 16 22 ((j.val:ℝ)/6)) := by
  rw [ha16_0_22_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha16_0_21 j) false 16 21 j (ha16_0_21_contains j)
noncomputable def hk16_0_23 (j : Fin 6) (i k : Fin 16) : CBox := (power16 j i k).conj.mul (mpower0_23 j i k)
lemma hk16_0_23_contains (j : Fin 6) (i k : Fin 16) :
    (hk16_0_23 j i k).Contains (fullFactor false 16 23 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk16_0_23,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power16 j i k) (mpower0_23 j i k) (quadraturePoint j.val (16*i.val+k.val)) 16 23 (power16_contains j i k) (mpower0_23_contains j i k)
noncomputable def ha16_0_23 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨11,12⟩,⟨6,7⟩⟩,⟨⟨(-96759679),(-96759678)⟩,⟨55864226,55864227⟩⟩,⟨⟨(-1),1⟩,⟨(-1253899540536),(-1253899540535)⟩⟩,⟨⟨811679013105350,811679013105351⟩,⟨468623096711943,468623096711944⟩⟩,⟨⟨(-137503773339017308),(-137503773339017306)⟩,⟨79387840551870928,79387840551870929⟩⟩,⟨⟨(-1),2⟩,⟨(-10518471716932064457),(-10518471716932064453)⟩⟩]
lemma ha16_0_23_eq (j : Fin 7) : ha16_0_23 j = ((ha16_0_22 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 23 := by fin_cases j <;> decide +kernel
lemma ha16_0_23_contains (j : Fin 7) : (ha16_0_23 j).Contains (fullFactor false 16 23 ((j.val:ℝ)/6)) := by
  rw [ha16_0_23_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha16_0_22 j) false 16 22 j (ha16_0_22_contains j)
noncomputable def hk16_0_24 (j : Fin 6) (i k : Fin 16) : CBox := (power16 j i k).conj.mul (mpower0_24 j i k)
lemma hk16_0_24_contains (j : Fin 6) (i k : Fin 16) :
    (hk16_0_24 j i k).Contains (fullFactor false 16 24 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk16_0_24,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power16 j i k) (mpower0_24 j i k) (quadraturePoint j.val (16*i.val+k.val)) 16 24 (power16_contains j i k) (mpower0_24_contains j i k)
noncomputable def ha16_0_24 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),0⟩,⟨0,1⟩⟩,⟨⟨(-2437537),(-2437536)⟩,⟨(-4221938),(-4221937)⟩⟩,⟨⟨82067533018,82067533019⟩,⟨(-1),1⟩⟩,⟨⟨(-40895079942577),(-40895079942576)⟩,⟨70832356240132,70832356240133⟩⟩,⟨⟨(-8659870022990125),(-8659870022990124)⟩,⟨(-14999334866761558),(-14999334866761557)⟩⟩,⟨⟨1376864728037741370,1376864728037741371⟩,⟨(-1),1⟩⟩]
lemma ha16_0_24_eq (j : Fin 7) : ha16_0_24 j = ((ha16_0_23 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 24 := by fin_cases j <;> decide +kernel
lemma ha16_0_24_contains (j : Fin 7) : (ha16_0_24 j).Contains (fullFactor false 16 24 ((j.val:ℝ)/6)) := by
  rw [ha16_0_24_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha16_0_23 j) false 16 23 j (ha16_0_23_contains j)
noncomputable def hk16_0_25 (j : Fin 6) (i k : Fin 16) : CBox := (power16 j i k).conj.mul (mpower0_25 j i k)
lemma hk16_0_25_contains (j : Fin 6) (i k : Fin 16) :
    (hk16_0_25 j i k).Contains (fullFactor false 16 25 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk16_0_25,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power16 j i k) (mpower0_25 j i k) (quadraturePoint j.val (16*i.val+k.val)) 16 25 (power16_contains j i k) (mpower0_25_contains j i k)
noncomputable def ha16_0_25 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),0⟩,⟨(-1),0⟩⟩,⟨⟨176848,176849⟩,⟨(-102104),(-102103)⟩⟩,⟨⟨(-1),1⟩,⟨5156455176,5156455177⟩⟩,⟨⟨(-5934037600013),(-5934037600012)⟩,⟨(-3426018205749),(-3426018205748)⟩⟩,⟨⟨1570726674205044,1570726674205046⟩,⟨(-906859468175609),(-906859468175608)⟩⟩,⟨⟨(-1),1⟩,⟨173021924583611076,173021924583611077⟩⟩]
lemma ha16_0_25_eq (j : Fin 7) : ha16_0_25 j = ((ha16_0_24 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 25 := by fin_cases j <;> decide +kernel
lemma ha16_0_25_contains (j : Fin 7) : (ha16_0_25 j).Contains (fullFactor false 16 25 ((j.val:ℝ)/6)) := by
  rw [ha16_0_25_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha16_0_24 j) false 16 24 j (ha16_0_24_contains j)
noncomputable def hk16_0_26 (j : Fin 6) (i k : Fin 16) : CBox := (power16 j i k).conj.mul (mpower0_26 j i k)
lemma hk16_0_26_contains (j : Fin 6) (i k : Fin 16) :
    (hk16_0_26 j i k).Contains (fullFactor false 16 26 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk16_0_26,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power16 j i k) (mpower0_26 j i k) (quadraturePoint j.val (16*i.val+k.val)) 16 26 (power16_contains j i k) (mpower0_26_contains j i k)
noncomputable def ha16_0_26 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨0,1⟩,⟨(-1),0⟩⟩,⟨⟨4112,4113⟩,⟨7122,7123⟩⟩,⟨⟨(-311528495),(-311528494)⟩,⟨(-1),1⟩⟩,⟨⟨275978298108,275978298109⟩,⟨(-478008434111),(-478008434110)⟩⟩,⟨⟨91313559072398,91313559072399⟩,⟨158159723733336,158159723733337⟩⟩,⟨⟨(-20906323353147685),(-20906323353147684)⟩,⟨(-1),1⟩⟩]
lemma ha16_0_26_eq (j : Fin 7) : ha16_0_26 j = ((ha16_0_25 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 26 := by fin_cases j <;> decide +kernel
lemma ha16_0_26_contains (j : Fin 7) : (ha16_0_26 j).Contains (fullFactor false 16 26 ((j.val:ℝ)/6)) := by
  rw [ha16_0_26_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha16_0_25 j) false 16 25 j (ha16_0_25_contains j)
noncomputable def hk16_0_27 (j : Fin 6) (i k : Fin 16) : CBox := (power16 j i k).conj.mul (mpower0_27 j i k)
lemma hk16_0_27_contains (j : Fin 6) (i k : Fin 16) :
    (hk16_0_27 j i k).Contains (fullFactor false 16 27 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk16_0_27,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power16 j i k) (mpower0_27 j i k) (quadraturePoint j.val (16*i.val+k.val)) 16 27 (power16_contains j i k) (mpower0_27_contains j i k)
noncomputable def ha16_0_27 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨0,1⟩,⟨0,1⟩⟩,⟨⟨(-277),(-276)⟩,⟨159,160⟩⟩,⟨⟨(-1),1⟩,⟨(-18123994),(-18123993)⟩⟩,⟨⟨37079204566,37079204567⟩,⟨21407688737,21407688739⟩⟩,⟨⟨(-15335599573286),(-15335599573285)⟩,⟨8854012541820,8854012541821⟩⟩,⟨⟨(-1),1⟩,⟨(-2432561179993389),(-2432561179993388)⟩⟩]
lemma ha16_0_27_eq (j : Fin 7) : ha16_0_27 j = ((ha16_0_26 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 27 := by fin_cases j <;> decide +kernel
lemma ha16_0_27_contains (j : Fin 7) : (ha16_0_27 j).Contains (fullFactor false 16 27 ((j.val:ℝ)/6)) := by
  rw [ha16_0_27_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha16_0_26 j) false 16 26 j (ha16_0_26_contains j)
noncomputable def hk16_0_28 (j : Fin 6) (i k : Fin 16) : CBox := (power16 j i k).conj.mul (mpower0_28 j i k)
lemma hk16_0_28_contains (j : Fin 6) (i k : Fin 16) :
    (hk16_0_28 j i k).Contains (fullFactor false 16 28 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk16_0_28,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power16 j i k) (mpower0_28 j i k) (quadraturePoint j.val (16*i.val+k.val)) 16 28 (power16_contains j i k) (mpower0_28_contains j i k)
noncomputable def ha16_0_28 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),0⟩,⟨0,1⟩⟩,⟨⟨(-6),(-5)⟩,⟨(-11),(-10)⟩⟩,⟨⟨1016753,1016754⟩,⟨(-1),1⟩⟩,⟨⟨(-1601291374),(-1601291373)⟩,⟨2773518015,2773518016⟩⟩,⟨⟨(-827848236791),(-827848236790)⟩,⟨(-1433875207079),(-1433875207078)⟩⟩,⟨⟨272932726159819,272932726159820⟩,⟨(-1),1⟩⟩]
lemma ha16_0_28_eq (j : Fin 7) : ha16_0_28 j = ((ha16_0_27 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 28 := by fin_cases j <;> decide +kernel
lemma ha16_0_28_contains (j : Fin 7) : (ha16_0_28 j).Contains (fullFactor false 16 28 ((j.val:ℝ)/6)) := by
  rw [ha16_0_28_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha16_0_27 j) false 16 27 j (ha16_0_27_contains j)
noncomputable def hk16_0_29 (j : Fin 6) (i k : Fin 16) : CBox := (power16 j i k).conj.mul (mpower0_29 j i k)
lemma hk16_0_29_contains (j : Fin 6) (i k : Fin 16) :
    (hk16_0_29 j i k).Contains (fullFactor false 16 29 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk16_0_29,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power16 j i k) (mpower0_29 j i k) (quadraturePoint j.val (16*i.val+k.val)) 16 29 (power16_contains j i k) (mpower0_29_contains j i k)
noncomputable def ha16_0_29 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),0⟩,⟨(-1),0⟩⟩,⟨⟨0,1⟩,⟨(-1),0⟩⟩,⟨⟨(-1),1⟩,⟨55072,55073⟩⟩,⟨⟨(-200304916),(-200304915)⟩,⟨(-115646097),(-115646096)⟩⟩,⟨⟨129444017721,129444017722⟩,⟨(-74734538477),(-74734538476)⟩⟩,⟨⟨(-1),1⟩,⟨29567015428549,29567015428550⟩⟩]
lemma ha16_0_29_eq (j : Fin 7) : ha16_0_29 j = ((ha16_0_28 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 29 := by fin_cases j <;> decide +kernel
lemma ha16_0_29_contains (j : Fin 7) : (ha16_0_29 j).Contains (fullFactor false 16 29 ((j.val:ℝ)/6)) := by
  rw [ha16_0_29_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha16_0_28 j) false 16 28 j (ha16_0_28_contains j)
noncomputable def hk16_0_30 (j : Fin 6) (i k : Fin 16) : CBox := (power16 j i k).conj.mul (mpower0_30 j i k)
lemma hk16_0_30_contains (j : Fin 6) (i k : Fin 16) :
    (hk16_0_30 j i k).Contains (fullFactor false 16 30 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk16_0_30,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power16 j i k) (mpower0_30 j i k) (quadraturePoint j.val (16*i.val+k.val)) 16 30 (power16_contains j i k) (mpower0_30_contains j i k)
noncomputable def ha16_0_30 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨0,1⟩,⟨(-1),0⟩⟩,⟨⟨0,1⟩,⟨0,1⟩⟩,⟨⟨(-2884),(-2883)⟩,⟨(-1),1⟩⟩,⟨⟨8073620,8073621⟩,⟨(-13983922),(-13983921)⟩⟩,⟨⟨6521818806,6521818807⟩,⟨11296121531,11296121532⟩⟩,⟨⟨(-3096250615297),(-3096250615296)⟩,⟨(-1),1⟩⟩]
lemma ha16_0_30_eq (j : Fin 7) : ha16_0_30 j = ((ha16_0_29 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 30 := by fin_cases j <;> decide +kernel
lemma ha16_0_30_contains (j : Fin 7) : (ha16_0_30 j).Contains (fullFactor false 16 30 ((j.val:ℝ)/6)) := by
  rw [ha16_0_30_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha16_0_29 j) false 16 29 j (ha16_0_29_contains j)
noncomputable def hk16_1_0 (j : Fin 6) (i k : Fin 16) : CBox := (kernel16_0 j i k).mul (mpower1_0 j i k)
lemma hk16_1_0_contains (j : Fin 6) (i k : Fin 16) :
    (hk16_1_0 j i k).Contains (fullFactor true 16 0 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk16_1_0,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel16_0 j i k) (mpower1_0 j i k) (quadraturePoint j.val (16*i.val+k.val)) 16 0 (kernel16_0_contains j i k) (mpower1_0_contains j i k)
noncomputable def ha16_1_0 : Fin 7 → CBox := ![⟨⟨(-3),3⟩,⟨(-3),3⟩⟩,⟨⟨(-3),2⟩,⟨(-4),0⟩⟩,⟨⟨0,4⟩,⟨(-2),2⟩⟩,⟨⟨25900948433,25900948436⟩,⟨29186647703,29186647707⟩⟩,⟨⟨(-35362811819921003609),(-35362811819921003509)⟩,⟨25936559903539299125,25936559903539299225⟩⟩,⟨⟨2558988247663461789901146,2558988247663461822219051⟩,⟨(-15737954547823165151092270),(-15737954547823165118709214)⟩⟩,⟨⟨53107114358929705735138510744,53107114358929705810825491739⟩,⟨(-1990265249209479056273496423),(-1990265249209478981209968663)⟩⟩]
lemma ha16_1_0_eq (j : Fin 7) : ha16_1_0 j = atomKernel16_0 j := by fin_cases j <;> decide +kernel
lemma ha16_1_0_contains (j : Fin 7) : (ha16_1_0 j).Contains (fullFactor true 16 0 ((j.val:ℝ)/6)) := by
  rw [ha16_1_0_eq]
  simpa only [fullFactor,ite_true] using atomKernel16_0_contains j
noncomputable def hk16_1_1 (j : Fin 6) (i k : Fin 16) : CBox := (kernel16_0 j i k).mul (mpower1_1 j i k)
lemma hk16_1_1_contains (j : Fin 6) (i k : Fin 16) :
    (hk16_1_1 j i k).Contains (fullFactor true 16 1 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk16_1_1,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel16_0 j i k) (mpower1_1 j i k) (quadraturePoint j.val (16*i.val+k.val)) 16 1 (kernel16_0_contains j i k) (mpower1_1_contains j i k)
noncomputable def ha16_1_1 : Fin 7 → CBox := ![⟨⟨(-28),28⟩,⟨(-28),28⟩⟩,⟨⟨(-31),23⟩,⟨(-8),42⟩⟩,⟨⟨(-30),11⟩,⟨(-31),10⟩⟩,⟨⟨75794229201,75794229231⟩,⟨(-214907164993),(-214907164965)⟩⟩,⟨⟨173413891756673643302,173413891756673643917⟩,⟨124072675056722227766,124072675056722228381⟩⟩,⟨⟨(-66096511680512424745057204),(-66096511680512424589790778)⟩,⟨630096109946563809592209,630096109946563964496528⟩⟩,⟨⟨(-17159000623478874601575700458),(-17159000623478874316252730094)⟩,⟨(-191397454004269867419843465767),(-191397454004269867131829260053)⟩⟩]
lemma ha16_1_1_eq (j : Fin 7) : ha16_1_1 j = ((ha16_1_0 j).mul (piI.mul (atomPoints j).z)).scale 1 1 := by fin_cases j <;> decide +kernel
lemma ha16_1_1_contains (j : Fin 7) : (ha16_1_1 j).Contains (fullFactor true 16 1 ((j.val:ℝ)/6)) := by
  rw [ha16_1_1_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha16_1_0 j) true 16 0 j (ha16_1_0_contains j)
noncomputable def hk16_1_2 (j : Fin 6) (i k : Fin 16) : CBox := (kernel16_0 j i k).mul (mpower1_2 j i k)
lemma hk16_1_2_contains (j : Fin 6) (i k : Fin 16) :
    (hk16_1_2 j i k).Contains (fullFactor true 16 2 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk16_1_2,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel16_0 j i k) (mpower1_2 j i k) (quadraturePoint j.val (16*i.val+k.val)) 16 2 (kernel16_0_contains j i k) (mpower1_2_contains j i k)
noncomputable def ha16_1_2 : Fin 7 → CBox := ![⟨⟨(-130),130⟩,⟨(-130),130⟩⟩,⟨⟨(-104),197⟩,⟨(-204),89⟩⟩,⟨⟨(-107),100⟩,⟨(-53),154⟩⟩,⟨⟨(-656151427379),(-656151427264)⟩,⟨110503197729,110503197847⟩⟩,⟨⟨155215278913991613146,155215278913991615035⟩,⟨(-494592317822908282939),(-494592317822908281050)⟩⟩,⟨⟨24563117624381976371901844,24563117624381976743072495⟩,⟨134790018730789871186533032,134790018730789871558668099⟩⟩,⟨⟨(-343959593517194279799311401329),(-343959593517194279251404864260)⟩,⟨48950469967399627017259360017,48950469967399627559610208607⟩⟩]
lemma ha16_1_2_eq (j : Fin 7) : ha16_1_2 j = ((ha16_1_1 j).mul (piI.mul (atomPoints j).z)).scale 1 2 := by fin_cases j <;> decide +kernel
lemma ha16_1_2_contains (j : Fin 7) : (ha16_1_2 j).Contains (fullFactor true 16 2 ((j.val:ℝ)/6)) := by
  rw [ha16_1_2_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha16_1_1 j) true 16 1 j (ha16_1_1_contains j)
noncomputable def hk16_1_3 (j : Fin 6) (i k : Fin 16) : CBox := (kernel16_0 j i k).mul (mpower1_3 j i k)
lemma hk16_1_3_contains (j : Fin 6) (i k : Fin 16) :
    (hk16_1_3 j i k).Contains (fullFactor true 16 3 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk16_1_3,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel16_0 j i k) (mpower1_3 j i k) (quadraturePoint j.val (16*i.val+k.val)) 16 3 (kernel16_0_contains j i k) (mpower1_3_contains j i k)
noncomputable def ha16_1_3 : Fin 7 → CBox := ![⟨⟨(-400),400⟩,⟨(-400),400⟩⟩,⟨⟨(-757),377⟩,⟨(-472),651⟩⟩,⟨⟨(-256),440⟩,⟨(-425),271⟩⟩,⟨⟨807127237475,807127237785⟩,⟨1013027675009,1013027675317⟩⟩,⟨⟨(-840072546677271221374),(-840072546677271217507)⟩,⟨10796916803272233743,10796916803272237609⟩⟩,⟨⟨177785734026401981014338986,177785734026401981608841366⟩,⟨(-65093632085839843735282329),(-65093632085839843142262265)⟩⟩,⟨⟨80449289390754261673915759125,80449289390754262361280265325⟩,⟨410951818164637086090139401074,410951818164637086784914943166⟩⟩]
lemma ha16_1_3_eq (j : Fin 7) : ha16_1_3 j = ((ha16_1_2 j).mul (piI.mul (atomPoints j).z)).scale 1 3 := by fin_cases j <;> decide +kernel
lemma ha16_1_3_contains (j : Fin 7) : (ha16_1_3 j).Contains (fullFactor true 16 3 ((j.val:ℝ)/6)) := by
  rw [ha16_1_3_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha16_1_2 j) true 16 2 j (ha16_1_2_contains j)
noncomputable def hk16_1_4 (j : Fin 6) (i k : Fin 16) : CBox := (kernel16_0 j i k).mul (mpower1_4 j i k)
lemma hk16_1_4_contains (j : Fin 6) (i k : Fin 16) :
    (hk16_1_4 j i k).Contains (fullFactor true 16 4 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk16_1_4,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel16_0 j i k) (mpower1_4 j i k) (quadraturePoint j.val (16*i.val+k.val)) 16 4 (kernel16_0_contains j i k) (mpower1_4_contains j i k)
noncomputable def ha16_1_4 : Fin 7 → CBox := ![⟨⟨(-922),922⟩,⟨(-922),922⟩⟩,⟨⟨(-1162),2056⟩,⟨(-1599),1609⟩⟩,⟨⟨(-1089),665⟩,⟨(-901),853⟩⟩,⟨⟨722667435480,722667436094⟩,⟨(-1747472052200),(-1747472051585)⟩⟩,⟨⟨330722749117346092801,330722749117346098734⟩,⟨966191228075115295111,966191228075115301046⟩⟩,⟨⟨(-97785536319491083281806297),(-97785536319491082571151650)⟩,⟨(-170115395489784926217503086),(-170115395489784925505292316)⟩⟩,⟨⟨367212870777440732128401144570,367212870777440732789074389818⟩,⟨(-91917570002480830322462534998),(-91917570002480829669032086353)⟩⟩]
lemma ha16_1_4_eq (j : Fin 7) : ha16_1_4 j = ((ha16_1_3 j).mul (piI.mul (atomPoints j).z)).scale 1 4 := by fin_cases j <;> decide +kernel
lemma ha16_1_4_contains (j : Fin 7) : (ha16_1_4 j).Contains (fullFactor true 16 4 ((j.val:ℝ)/6)) := by
  rw [ha16_1_4_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha16_1_3 j) true 16 3 j (ha16_1_3_contains j)
noncomputable def hk16_1_5 (j : Fin 6) (i k : Fin 16) : CBox := (kernel16_0 j i k).mul (mpower1_5 j i k)
lemma hk16_1_5_contains (j : Fin 6) (i k : Fin 16) :
    (hk16_1_5 j i k).Contains (fullFactor true 16 5 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk16_1_5,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel16_0 j i k) (mpower1_5 j i k) (quadraturePoint j.val (16*i.val+k.val)) 16 5 (kernel16_0_contains j i k) (mpower1_5_contains j i k)
noncomputable def ha16_1_5 : Fin 7 → CBox := ![⟨⟨(-1700),1700⟩,⟨(-1700),1700⟩⟩,⟨⟨(-4342),2979⟩,⟨(-3996),3316⟩⟩,⟨⟨(-1583),1951⟩,⟨(-1525),2009⟩⟩,⟨⟨(-2194343531025),(-2194343530048)⟩,⟨250747193822,250747194798⟩⟩,⟨⟨792526036450294726125,792526036450294733411⟩,⟨(-598411928712212552263),(-598411928712212544979)⟩⟩,⟨⟨(-125220181099945675473526022),(-125220181099945674791017847)⟩,⟨103859198813383626491669797,103859198813383627172970042⟩⟩,⟨⟨(-80173906213056706889737199994),(-80173906213056706392759759395)⟩,⟨(-261751113535616935058496470323),(-261751113535616934555960291244)⟩⟩]
lemma ha16_1_5_eq (j : Fin 7) : ha16_1_5 j = ((ha16_1_4 j).mul (piI.mul (atomPoints j).z)).scale 1 5 := by fin_cases j <;> decide +kernel
lemma ha16_1_5_contains (j : Fin 7) : (ha16_1_5 j).Contains (fullFactor true 16 5 ((j.val:ℝ)/6)) := by
  rw [ha16_1_5_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha16_1_4 j) true 16 4 j (ha16_1_4_contains j)
noncomputable def hk16_1_6 (j : Fin 6) (i k : Fin 16) : CBox := (kernel16_0 j i k).mul (mpower1_6 j i k)
lemma hk16_1_6_contains (j : Fin 6) (i k : Fin 16) :
    (hk16_1_6 j i k).Contains (fullFactor true 16 6 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk16_1_6,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel16_0 j i k) (mpower1_6 j i k) (quadraturePoint j.val (16*i.val+k.val)) 16 6 (kernel16_0_contains j i k) (mpower1_6_contains j i k)
noncomputable def ha16_1_6 : Fin 7 → CBox := ![⟨⟨(-2612),2612⟩,⟨(-2612),2612⟩⟩,⟨⟨(-6283),7603⟩,⟨(-6083),7797⟩⟩,⟨⟨(-2910),3024⟩,⟨(-3324),2611⟩⟩,⟨⟨1248475313948,1248475315241⟩,⟨1749951891998,1749951893291⟩⟩,⟨⟨(-660936015318381254452),(-660936015318381247000)⟩,⟨(-459109057754482555487),(-459109057754482548034)⟩⟩,⟨⟨85414796293133637657809885,85414796293133638202082959⟩,⟨73068825486432390647110027,73068825486432391192102083⟩⟩,⟨⟨(-155022593889746777855529754917),(-155022593889746777537021937847)⟩,⟨56443324576027397697941537698,56443324576027398012948099458⟩⟩]
lemma ha16_1_6_eq (j : Fin 7) : ha16_1_6 j = ((ha16_1_5 j).mul (piI.mul (atomPoints j).z)).scale 1 6 := by fin_cases j <;> decide +kernel
lemma ha16_1_6_contains (j : Fin 7) : (ha16_1_6 j).Contains (fullFactor true 16 6 ((j.val:ℝ)/6)) := by
  rw [ha16_1_6_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha16_1_5 j) true 16 5 j (ha16_1_5_contains j)
noncomputable def hk16_1_7 (j : Fin 6) (i k : Fin 16) : CBox := (kernel16_0 j i k).mul (mpower1_7 j i k)
lemma hk16_1_7_contains (j : Fin 6) (i k : Fin 16) :
    (hk16_1_7 j i k).Contains (fullFactor true 16 7 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk16_1_7,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel16_0 j i k) (mpower1_7 j i k) (quadraturePoint j.val (16*i.val+k.val)) 16 7 (kernel16_0_contains j i k) (mpower1_7_contains j i k)
noncomputable def ha16_1_7 : Fin 7 → CBox := ![⟨⟨(-3439),3439⟩,⟨(-3439),3439⟩⟩,⟨⟨(-11558),11023⟩,⟨(-12578),9999⟩⟩,⟨⟨(-4573),3968⟩,⟨(-4062),4479⟩⟩,⟨⟨772296567089,772296568556⟩,⟨(-1618557776830),(-1618557775363)⟩⟩,⟨⟨(-159932175530838942804),(-159932175530838936269)⟩,⟨535604446456639983204,535604446456639989738⟩⟩,⟨⟨34049958861360727324490221,34049958861360727697480197⟩,⟨(-57201067251999297343347995),(-57201067251999296970686305)⟩⟩,⟨⟨33275346735905410659939090744,33275346735905410831088463454⟩,⟨78456010105941935464730751236,78456010105941935637745817625⟩⟩]
lemma ha16_1_7_eq (j : Fin 7) : ha16_1_7 j = ((ha16_1_6 j).mul (piI.mul (atomPoints j).z)).scale 1 7 := by fin_cases j <;> decide +kernel
lemma ha16_1_7_contains (j : Fin 7) : (ha16_1_7 j).Contains (fullFactor true 16 7 ((j.val:ℝ)/6)) := by
  rw [ha16_1_7_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha16_1_6 j) true 16 6 j (ha16_1_6_contains j)
noncomputable def hk16_1_8 (j : Fin 6) (i k : Fin 16) : CBox := (kernel16_0 j i k).mul (mpower1_8 j i k)
lemma hk16_1_8_contains (j : Fin 6) (i k : Fin 16) :
    (hk16_1_8 j i k).Contains (fullFactor true 16 8 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk16_1_8,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel16_0 j i k) (mpower1_8 j i k) (quadraturePoint j.val (16*i.val+k.val)) 16 8 (kernel16_0_contains j i k) (mpower1_8_contains j i k)
noncomputable def ha16_1_8 : Fin 7 → CBox := ![⟨⟨(-3962),3962⟩,⟨(-3962),3962⟩⟩,⟨⟨(-16409),15723⟩,⟨(-14705),17425⟩⟩,⟨⟨(-5058),5698⟩,⟨(-5312),5444⟩⟩,⟨⟨(-1306704646423),(-1306704644966)⟩,⟨79423829221,79423830677⟩⟩,⟨⟨339605126373248506647,339605126373248511661⟩,⟨(-9093341614568992035),(-9093341614568987022)⟩⟩,⟨⟨(-32208106372270897666660573),(-32208106372270897443416545)⟩,⟨(-12352145282172659499883396),(-12352145282172659276531770)⟩⟩,⟨⟨34632308989444358629963146809,34632308989444358712190757246⟩,⟨(-16861261458343508627933597675),(-16861261458343508546565869029)⟩⟩]
lemma ha16_1_8_eq (j : Fin 7) : ha16_1_8 j = ((ha16_1_7 j).mul (piI.mul (atomPoints j).z)).scale 1 8 := by fin_cases j <;> decide +kernel
lemma ha16_1_8_contains (j : Fin 7) : (ha16_1_8 j).Contains (fullFactor true 16 8 ((j.val:ℝ)/6)) := by
  rw [ha16_1_8_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha16_1_7 j) true 16 7 j (ha16_1_7_contains j)
noncomputable def hk16_1_9 (j : Fin 6) (i k : Fin 16) : CBox := (kernel16_0 j i k).mul (mpower1_9 j i k)
lemma hk16_1_9_contains (j : Fin 6) (i k : Fin 16) :
    (hk16_1_9 j i k).Contains (fullFactor true 16 9 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk16_1_9,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel16_0 j i k) (mpower1_9 j i k) (quadraturePoint j.val (16*i.val+k.val)) 16 9 (kernel16_0_contains j i k) (mpower1_9_contains j i k)
noncomputable def ha16_1_9 : Fin 7 → CBox := ![⟨⟨(-4057),4057⟩,⟨(-4057),4057⟩⟩,⟨⟨(-19468),21176⟩,⟨(-21338),19305⟩⟩,⟨⟨(-6157),5883⟩,⟨(-6239),5801⟩⟩,⟨⟨455964118414,455964119699⟩,⟨716693968583,716693969869⟩⟩,⟨⟨(-61848217878660003105),(-61848217878659999686)⟩,⟨(-172799151219901248337),(-172799151219901244918)⟩⟩,⟨⟨(-3086426515184659624845011),(-3086426515184659505964761)⟩,⟨15586591945547874307302054,15586591945547874426165626⟩⟩,⟨⟨(-7487719887316651116338819348),(-7487719887316651081952636189)⟩,⟨(-13543563769022368030278952905),(-13543563769022367995544187992)⟩⟩]
lemma ha16_1_9_eq (j : Fin 7) : ha16_1_9 j = ((ha16_1_8 j).mul (piI.mul (atomPoints j).z)).scale 1 9 := by fin_cases j <;> decide +kernel
lemma ha16_1_9_contains (j : Fin 7) : (ha16_1_9 j).Contains (fullFactor true 16 9 ((j.val:ℝ)/6)) := by
  rw [ha16_1_9_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha16_1_8 j) true 16 8 j (ha16_1_8_contains j)
noncomputable def hk16_1_10 (j : Fin 6) (i k : Fin 16) : CBox := (kernel16_0 j i k).mul (mpower1_10 j i k)
lemma hk16_1_10_contains (j : Fin 6) (i k : Fin 16) :
    (hk16_1_10 j i k).Contains (fullFactor true 16 10 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk16_1_10,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel16_0 j i k) (mpower1_10 j i k) (quadraturePoint j.val (16*i.val+k.val)) 16 10 (kernel16_0_contains j i k) (mpower1_10_contains j i k)
noncomputable def ha16_1_10 : Fin 7 → CBox := ![⟨⟨(-3739),3739⟩,⟨(-3739),3739⟩⟩,⟨⟨(-24168),22102⟩,⟨(-22673),23597⟩⟩,⟨⟨(-6110),6020⟩,⟨(-5886),6243⟩⟩,⟨⟨237070122218,237070123240⟩,⟨(-435742772623),(-435742771601)⟩⟩,⟨⟨(-70460811551106122837),(-70460811551106120738)⟩,⟨54759040788742504750,54759040788742506849⟩⟩,⟨⟨6584962806960290010752570,6584962806960290067705615⟩,⟨163125079810063848064158,163125079810063905009390⟩⟩,⟨⟨(-4750016714838929780131191631),(-4750016714838929766926681825)⟩,⟨2958147187703659165637835196,2958147187703659178716417879⟩⟩]
lemma ha16_1_10_eq (j : Fin 7) : ha16_1_10 j = ((ha16_1_9 j).mul (piI.mul (atomPoints j).z)).scale 1 10 := by fin_cases j <;> decide +kernel
lemma ha16_1_10_contains (j : Fin 7) : (ha16_1_10 j).Contains (fullFactor true 16 10 ((j.val:ℝ)/6)) := by
  rw [ha16_1_10_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha16_1_9 j) true 16 9 j (ha16_1_9_contains j)
noncomputable def hk16_1_11 (j : Fin 6) (i k : Fin 16) : CBox := (kernel16_0 j i k).mul (mpower1_11 j i k)
lemma hk16_1_11_contains (j : Fin 6) (i k : Fin 16) :
    (hk16_1_11 j i k).Contains (fullFactor true 16 11 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk16_1_11,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel16_0 j i k) (mpower1_11 j i k) (quadraturePoint j.val (16*i.val+k.val)) 16 11 (kernel16_0_contains j i k) (mpower1_11_contains j i k)
noncomputable def ha16_1_11 : Fin 7 → CBox := ![⟨⟨(-3133),3133⟩,⟨(-3133),3133⟩⟩,⟨⟨(-23067),24819⟩,⟨(-23916),23970⟩⟩,⟨⟨(-5451),5658⟩,⟨(-5613),5496⟩⟩,⟨⟨(-263345627645),(-263345626906)⟩,⟨2011442301,2011443039⟩⟩,⟨⟨32705402051095491351,32705402051095492523⟩,⟨22049883830187379661,22049883830187380833⟩⟩,⟨⟨(-361037111936081702838604),(-361037111936081678041572)⟩,⟨(-2456037480379854346536216),(-2456037480379854321730501)⟩⟩,⟨⟨1052170280997595765472152129,1052170280997595769994279265⟩,⟨1508815711093426874414982607,1508815711093426878978073886⟩⟩]
lemma ha16_1_11_eq (j : Fin 7) : ha16_1_11 j = ((ha16_1_10 j).mul (piI.mul (atomPoints j).z)).scale 1 11 := by fin_cases j <;> decide +kernel
lemma ha16_1_11_contains (j : Fin 7) : (ha16_1_11 j).Contains (fullFactor true 16 11 ((j.val:ℝ)/6)) := by
  rw [ha16_1_11_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha16_1_10 j) true 16 10 j (ha16_1_10_contains j)
noncomputable def hk16_1_12 (j : Fin 6) (i k : Fin 16) : CBox := (kernel16_0 j i k).mul (mpower1_12 j i k)
lemma hk16_1_12_contains (j : Fin 6) (i k : Fin 16) :
    (hk16_1_12 j i k).Contains (fullFactor true 16 12 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk16_1_12,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel16_0 j i k) (mpower1_12 j i k) (quadraturePoint j.val (16*i.val+k.val)) 16 12 (kernel16_0_contains j i k) (mpower1_12_contains j i k)
noncomputable def ha16_1_12 : Fin 7 → CBox := ![⟨⟨(-2406),2406⟩,⟨(-2406),2406⟩⟩,⟨⟨(-23266),22163⟩,⟨(-23003),22426⟩⟩,⟨⟨(-4731),4596⟩,⟨(-4684),4643⟩⟩,⟨⟨62961654318,62961654807⟩,⟨111629252877,111629253366⟩⟩,⟨⟨4359156910004727590,4359156910004728190⟩,⟨(-15376003163963917957),(-15376003163963917357)⟩⟩,⟨⟨(-814946661038109714623227),(-814946661038109704720217)⟩,⟨267061920975924068969387,267061920975924078868072⟩⟩,⟨⟨437566939797545679519660527,437566939797545680965039528⟩,⟨(-340227472365358019913991442),(-340227472365358018480712981)⟩⟩]
lemma ha16_1_12_eq (j : Fin 7) : ha16_1_12 j = ((ha16_1_11 j).mul (piI.mul (atomPoints j).z)).scale 1 12 := by fin_cases j <;> decide +kernel
lemma ha16_1_12_contains (j : Fin 7) : (ha16_1_12 j).Contains (fullFactor true 16 12 ((j.val:ℝ)/6)) := by
  rw [ha16_1_12_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha16_1_11 j) true 16 11 j (ha16_1_11_contains j)
noncomputable def hk16_1_13 (j : Fin 6) (i k : Fin 16) : CBox := (kernel16_0 j i k).mul (mpower1_13 j i k)
lemma hk16_1_13_contains (j : Fin 6) (i k : Fin 16) :
    (hk16_1_13 j i k).Contains (fullFactor true 16 13 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk16_1_13,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel16_0 j i k) (mpower1_13 j i k) (quadraturePoint j.val (16*i.val+k.val)) 16 13 (kernel16_0_contains j i k) (mpower1_13_contains j i k)
noncomputable def ha16_1_13 : Fin 7 → CBox := ![⟨⟨(-1706),1706⟩,⟨(-1706),1706⟩⟩,⟨⟨(-19649),20134⟩,⟨(-19564),20219⟩⟩,⟨⟨(-3597),3632⟩,⟨(-3580),3649⟩⟩,⟨⟨30157912641,30157912940⟩,⟨(-49041169486),(-49041169186)⟩⟩,⟨⟨(-5972511159259968556),(-5972511159259968271)⟩,⟨243143679910657157,243143679910657442⟩⟩,⟨⟨128076772774941510252505,128076772774941513900129⟩,⟨241631177674373828632827,241631177674373832282029⟩⟩,⟨⟨(-100825667203851765301751305),(-100825667203851764882429635)⟩,⟨(-116629227663983228794515690),(-116629227663983228371926029)⟩⟩]
lemma ha16_1_13_eq (j : Fin 7) : ha16_1_13 j = ((ha16_1_12 j).mul (piI.mul (atomPoints j).z)).scale 1 13 := by fin_cases j <;> decide +kernel
lemma ha16_1_13_contains (j : Fin 7) : (ha16_1_13 j).Contains (fullFactor true 16 13 ((j.val:ℝ)/6)) := by
  rw [ha16_1_13_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha16_1_12 j) true 16 12 j (ha16_1_12_contains j)
noncomputable def hk16_1_14 (j : Fin 6) (i k : Fin 16) : CBox := (kernel16_0 j i k).mul (mpower1_14 j i k)
lemma hk16_1_14_contains (j : Fin 6) (i k : Fin 16) :
    (hk16_1_14 j i k).Contains (fullFactor true 16 14 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk16_1_14,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel16_0 j i k) (mpower1_14 j i k) (quadraturePoint j.val (16*i.val+k.val)) 16 14 (kernel16_0_contains j i k) (mpower1_14_contains j i k)
noncomputable def ha16_1_14 : Fin 7 → CBox := ![⟨⟨(-1123),1123⟩,⟨(-1123),1123⟩⟩,⟨⟨(-16221),16129⟩,⟨(-16419),15932⟩⟩,⟨⟨(-2595),2608⟩,⟨(-2620),2583⟩⟩,⟨⟨(-23990184211),(-23990184040)⟩,⟨(-1090656327),(-1090656156)⟩⟩,⟨⟨726700322907348574,726700322907348700⟩,⟨1944606263306918905,1944606263306919031⟩⟩,⟨⟨64066412623825242196848,64066412623825243445459⟩,⟨(-49529541998499009832540),(-49529541998499008584398)⟩⟩,⟨⟨(-28729914589754833443284389),(-28729914589754833328561493)⟩,⟨27570283634787122878821998,27570283634787122992733512⟩⟩]
lemma ha16_1_14_eq (j : Fin 7) : ha16_1_14 j = ((ha16_1_13 j).mul (piI.mul (atomPoints j).z)).scale 1 14 := by fin_cases j <;> decide +kernel
lemma ha16_1_14_contains (j : Fin 7) : (ha16_1_14 j).Contains (fullFactor true 16 14 ((j.val:ℝ)/6)) := by
  rw [ha16_1_14_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha16_1_13 j) true 16 13 j (ha16_1_13_contains j)
noncomputable def hk16_1_15 (j : Fin 6) (i k : Fin 16) : CBox := (kernel16_0 j i k).mul (mpower1_15 j i k)
lemma hk16_1_15_contains (j : Fin 6) (i k : Fin 16) :
    (hk16_1_15 j i k).Contains (fullFactor true 16 15 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk16_1_15,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel16_0 j i k) (mpower1_15 j i k) (quadraturePoint j.val (16*i.val+k.val)) 16 15 (kernel16_0_contains j i k) (mpower1_15_contains j i k)
noncomputable def ha16_1_15 : Fin 7 → CBox := ![⟨⟨(-690),690⟩,⟨(-690),690⟩⟩,⟨⟨(-12313),12240⟩,⟨(-12141),12412⟩⟩,⟨⟨(-1756),1739⟩,⟨(-1744),1751⟩⟩,⟨⟨4154702862,4154702953⟩,⟨8375675889,8375675980⟩⟩,⟨⟨525523326775000076,525523326775000128⟩,⟨(-420274619814902357),(-420274619814902305)⟩⟩,⟨⟨(-16497675921983197678725),(-16497675921983197280109)⟩,⟨(-15123090385341000151049),(-15123090385340999752317)⟩⟩,⟨⟨6996781634661517200929028,6996781634661517229809924⟩,⟨6571167002771297178795268,6571167002771297207862177⟩⟩]
lemma ha16_1_15_eq (j : Fin 7) : ha16_1_15 j = ((ha16_1_14 j).mul (piI.mul (atomPoints j).z)).scale 1 15 := by fin_cases j <;> decide +kernel
lemma ha16_1_15_contains (j : Fin 7) : (ha16_1_15 j).Contains (fullFactor true 16 15 ((j.val:ℝ)/6)) := by
  rw [ha16_1_15_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha16_1_14 j) true 16 14 j (ha16_1_14_contains j)
noncomputable def hk16_1_16 (j : Fin 6) (i k : Fin 16) : CBox := (kernel16_0 j i k).mul (mpower1_16 j i k)
lemma hk16_1_16_contains (j : Fin 6) (i k : Fin 16) :
    (hk16_1_16 j i k).Contains (fullFactor true 16 16 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk16_1_16,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel16_0 j i k) (mpower1_16 j i k) (quadraturePoint j.val (16*i.val+k.val)) 16 16 (kernel16_0_contains j i k) (mpower1_16_contains j i k)
noncomputable def ha16_1_16 : Fin 7 → CBox := ![⟨⟨(-398),398⟩,⟨(-398),398⟩⟩,⟨⟨(-8686),8784⟩,⟨(-8792),8679⟩⟩,⟨⟨(-1097),1104⟩,⟨(-1099),1102⟩⟩,⟨⟨1939221641,1939221687⟩,⟨(-2807902978),(-2807902931)⟩⟩,⟨⟨(-171126210582893626),(-171126210582893605)⟩,⟨(-111940389598287301),(-111940389598287280)⟩⟩,⟨⟨(-3135181561848804109411),(-3135181561848803990040)⟩,⟨4878072426380454488944,4878072426380454608292⟩⟩,⟨⟨1400927874765968976318933,1400927874765968983222942⟩,⟨(-1656215671067409590268458),(-1656215671067409583403957)⟩⟩]
lemma ha16_1_16_eq (j : Fin 7) : ha16_1_16 j = ((ha16_1_15 j).mul (piI.mul (atomPoints j).z)).scale 1 16 := by fin_cases j <;> decide +kernel
lemma ha16_1_16_contains (j : Fin 7) : (ha16_1_16 j).Contains (fullFactor true 16 16 ((j.val:ℝ)/6)) := by
  rw [ha16_1_16_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha16_1_15 j) true 16 15 j (ha16_1_15_contains j)
noncomputable def hk16_1_17 (j : Fin 6) (i k : Fin 16) : CBox := (kernel16_0 j i k).mul (mpower1_17 j i k)
lemma hk16_1_17_contains (j : Fin 6) (i k : Fin 16) :
    (hk16_1_17 j i k).Contains (fullFactor true 16 17 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk16_1_17,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel16_0 j i k) (mpower1_17 j i k) (quadraturePoint j.val (16*i.val+k.val)) 16 17 (kernel16_0_contains j i k) (mpower1_17_contains j i k)
noncomputable def ha16_1_17 : Fin 7 → CBox := ![⟨⟨(-216),216⟩,⟨(-216),216⟩⟩,⟨⟨(-5884),5816⟩,⟨(-5835),5865⟩⟩,⟨⟨(-653),652⟩,⟨(-654),651⟩⟩,⟨⟨(-1166560582),(-1166560559)⟩,⟨(-115279913),(-115279890)⟩⟩,⟨⟨(-15167422501097453),(-15167422501097444)⟩,⟨56484166837484507,56484166837484516⟩⟩,⟨⟨1302146713231019342510,1302146713231019376141⟩,⟨551323166683312568665,551323166683312602300⟩⟩,⟨⟨(-367276167032015402492579),(-367276167032015400957039)⟩,⟨(-279281991910390503207727),(-279281991910390501664395)⟩⟩]
lemma ha16_1_17_eq (j : Fin 7) : ha16_1_17 j = ((ha16_1_16 j).mul (piI.mul (atomPoints j).z)).scale 1 17 := by fin_cases j <;> decide +kernel
lemma ha16_1_17_contains (j : Fin 7) : (ha16_1_17 j).Contains (fullFactor true 16 17 ((j.val:ℝ)/6)) := by
  rw [ha16_1_17_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha16_1_16 j) true 16 16 j (ha16_1_16_contains j)
noncomputable def hk16_1_18 (j : Fin 6) (i k : Fin 16) : CBox := (kernel16_0 j i k).mul (mpower1_18 j i k)
lemma hk16_1_18_contains (j : Fin 6) (i k : Fin 16) :
    (hk16_1_18 j i k).Contains (fullFactor true 16 18 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk16_1_18,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel16_0 j i k) (mpower1_18 j i k) (quadraturePoint j.val (16*i.val+k.val)) 16 18 (kernel16_0_contains j i k) (mpower1_18_contains j i k)
noncomputable def ha16_1_18 : Fin 7 → CBox := ![⟨⟨(-111),111⟩,⟨(-111),111⟩⟩,⟨⟨(-3683),3718⟩,⟨(-3700),3701⟩⟩,⟨⟨(-366),365⟩,⟨(-365),366⟩⟩,⟨⟨150692759,150692770⟩,⟨349186637,349186649⟩⟩,⟨⟨15774460676362512,15774460676362516⟩,⟨(-862239933917983),(-862239933917979)⟩⟩,⟨⟨74178325538178316302,74178325538178325253⟩,⟨(-317108582911588424521),(-317108582911588415570)⟩⟩,⟨⟨(-52196103731795287670827),(-52196103731795287345005)⟩,⟨76593639936003126204614,76593639936003126529008⟩⟩]
lemma ha16_1_18_eq (j : Fin 7) : ha16_1_18 j = ((ha16_1_17 j).mul (piI.mul (atomPoints j).z)).scale 1 18 := by fin_cases j <;> decide +kernel
lemma ha16_1_18_contains (j : Fin 7) : (ha16_1_18 j).Contains (fullFactor true 16 18 ((j.val:ℝ)/6)) := by
  rw [ha16_1_18_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha16_1_17 j) true 16 17 j (ha16_1_17_contains j)
noncomputable def hk16_1_19 (j : Fin 6) (i k : Fin 16) : CBox := (kernel16_0 j i k).mul (mpower1_19 j i k)
lemma hk16_1_19_contains (j : Fin 6) (i k : Fin 16) :
    (hk16_1_19 j i k).Contains (fullFactor true 16 19 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk16_1_19,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel16_0 j i k) (mpower1_19 j i k) (quadraturePoint j.val (16*i.val+k.val)) 16 19 (kernel16_0_contains j i k) (mpower1_19_contains j i k)
noncomputable def ha16_1_19 : Fin 7 → CBox := ![⟨⟨(-54),54⟩,⟨(-54),54⟩⟩,⟨⟨(-2225),2211⟩,⟨(-2221),2214⟩⟩,⟨⟨(-194),195⟩,⟨(-194),194⟩⟩,⟨⟨71436037,71436043⟩,⟨(-92524992),(-92524986)⟩⟩,⟨⟨(-1467761579589366),(-1467761579589363)⟩,⟨(-3766907213360389),(-3766907213360387)⟩⟩,⟨⟨(-70932979255338572311),(-70932979255338570053)⟩,⟨(-4194697222675565795),(-4194697222675563538)⟩⟩,⟨⟨15072771877084077644234,15072771877084077709156⟩,⟨9163118159105693082853,9163118159105693148017⟩⟩]
lemma ha16_1_19_eq (j : Fin 7) : ha16_1_19 j = ((ha16_1_18 j).mul (piI.mul (atomPoints j).z)).scale 1 19 := by fin_cases j <;> decide +kernel
lemma ha16_1_19_contains (j : Fin 7) : (ha16_1_19 j).Contains (fullFactor true 16 19 ((j.val:ℝ)/6)) := by
  rw [ha16_1_19_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha16_1_18 j) true 16 18 j (ha16_1_18_contains j)
noncomputable def hk16_1_20 (j : Fin 6) (i k : Fin 16) : CBox := (kernel16_0 j i k).mul (mpower1_20 j i k)
lemma hk16_1_20_contains (j : Fin 6) (i k : Fin 16) :
    (hk16_1_20 j i k).Contains (fullFactor true 16 20 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk16_1_20,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel16_0 j i k) (mpower1_20 j i k) (quadraturePoint j.val (16*i.val+k.val)) 16 20 (kernel16_0_contains j i k) (mpower1_20_contains j i k)
noncomputable def ha16_1_20 : Fin 7 → CBox := ![⟨⟨(-25),25⟩,⟨(-25),25⟩⟩,⟨⟨(-1261),1265⟩,⟨(-1260),1265⟩⟩,⟨⟨(-98),98⟩,⟨(-98),98⟩⟩,⟨⟨(-33740338),(-33740334)⟩,⟨(-5153541),(-5153537)⟩⟩,⟨⟨(-758944432181703),(-758944432181701)⟩,⟨624462490362091,624462490362092⟩⟩,⟨⟨1641093731746318589,1641093731746319131⟩,⟨14636828276602889005,14636828276602889547⟩⟩,⟨⟨1512899666891436919156,1512899666891436931538⟩,⟨(-2807438057603362280053),(-2807438057603362267710)⟩⟩]
lemma ha16_1_20_eq (j : Fin 7) : ha16_1_20 j = ((ha16_1_19 j).mul (piI.mul (atomPoints j).z)).scale 1 20 := by fin_cases j <;> decide +kernel
lemma ha16_1_20_contains (j : Fin 7) : (ha16_1_20 j).Contains (fullFactor true 16 20 ((j.val:ℝ)/6)) := by
  rw [ha16_1_20_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha16_1_19 j) true 16 19 j (ha16_1_19_contains j)
noncomputable def hk16_1_21 (j : Fin 6) (i k : Fin 16) : CBox := (kernel16_0 j i k).mul (mpower1_21 j i k)
lemma hk16_1_21_contains (j : Fin 6) (i k : Fin 16) :
    (hk16_1_21 j i k).Contains (fullFactor true 16 21 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk16_1_21,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel16_0 j i k) (mpower1_21 j i k) (quadraturePoint j.val (16*i.val+k.val)) 16 21 (kernel16_0_contains j i k) (mpower1_21_contains j i k)
noncomputable def ha16_1_21 : Fin 7 → CBox := ![⟨⟨(-11),11⟩,⟨(-11),11⟩⟩,⟨⟨(-685),685⟩,⟨(-686),684⟩⟩,⟨⟨(-48),48⟩,⟨(-48),48⟩⟩,⟨⟨3293285,3293287⟩,⟨8901883,8901885⟩⟩,⟨⟨192146728783256,192146728783257⟩,⟨121906276705541,121906276705543⟩⟩,⟨⟨2792378380608537401,2792378380608537526⟩,⟨(-810149790594419348),(-810149790594419223)⟩⟩,⟨⟨(-496276865357941984591),(-496276865357941982355)⟩,⟨(-235045620509659402288),(-235045620509659400047)⟩⟩]
lemma ha16_1_21_eq (j : Fin 7) : ha16_1_21 j = ((ha16_1_20 j).mul (piI.mul (atomPoints j).z)).scale 1 21 := by fin_cases j <;> decide +kernel
lemma ha16_1_21_contains (j : Fin 7) : (ha16_1_21 j).Contains (fullFactor true 16 21 ((j.val:ℝ)/6)) := by
  rw [ha16_1_21_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha16_1_20 j) true 16 20 j (ha16_1_20_contains j)
noncomputable def hk16_1_22 (j : Fin 6) (i k : Fin 16) : CBox := (kernel16_0 j i k).mul (mpower1_22 j i k)
lemma hk16_1_22_contains (j : Fin 6) (i k : Fin 16) :
    (hk16_1_22 j i k).Contains (fullFactor true 16 22 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk16_1_22,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel16_0 j i k) (mpower1_22 j i k) (quadraturePoint j.val (16*i.val+k.val)) 16 22 (kernel16_0_contains j i k) (mpower1_22_contains j i k)
noncomputable def ha16_1_22 : Fin 7 → CBox := ![⟨⟨(-5),5⟩,⟨(-5),5⟩⟩,⟨⟨(-355),355⟩,⟨(-355),355⟩⟩,⟨⟨(-22),22⟩,⟨(-22),22⟩⟩,⟨⟨1643334,1643336⟩,⟨(-1909785),(-1909783)⟩⟩,⟨⟨12365222514303,12365222514305⟩,⟨(-48747603390860),(-48747603390859)⟩⟩,⟨⟨(-239835813129811706),(-239835813129811678)⟩,⟨(-492595443543864927),(-492595443543864899)⟩⟩,⟨⟨(-34344012927123102099),(-34344012927123101711)⟩,⟨83463817621576003531,83463817621576003918⟩⟩]
lemma ha16_1_22_eq (j : Fin 7) : ha16_1_22 j = ((ha16_1_21 j).mul (piI.mul (atomPoints j).z)).scale 1 22 := by fin_cases j <;> decide +kernel
lemma ha16_1_22_contains (j : Fin 7) : (ha16_1_22 j).Contains (fullFactor true 16 22 ((j.val:ℝ)/6)) := by
  rw [ha16_1_22_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha16_1_21 j) true 16 21 j (ha16_1_21_contains j)
noncomputable def hk16_1_23 (j : Fin 6) (i k : Fin 16) : CBox := (kernel16_0 j i k).mul (mpower1_23 j i k)
lemma hk16_1_23_contains (j : Fin 6) (i k : Fin 16) :
    (hk16_1_23 j i k).Contains (fullFactor true 16 23 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk16_1_23,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel16_0 j i k) (mpower1_23 j i k) (quadraturePoint j.val (16*i.val+k.val)) 16 23 (kernel16_0_contains j i k) (mpower1_23_contains j i k)
noncomputable def ha16_1_23 : Fin 7 → CBox := ![⟨⟨(-3),3⟩,⟨(-3),3⟩⟩,⟨⟨(-176),176⟩,⟨(-176),176⟩⟩,⟨⟨(-10),10⟩,⟨(-10),10⟩⟩,⟨⟨(-626363),(-626361)⟩,⟨(-129999),(-129997)⟩⟩,⟨⟨(-10606570469184),(-10606570469182)⟩,⟨727947874188,727947874189⟩⟩,⟨⟨(-80151332297122232),(-80151332297122225)⟩,⟨57684249972704638,57684249972704645⟩⟩,⟨⟨13384300400462115406,13384300400462115471⟩,⟨4710645390307683617,4710645390307683682⟩⟩]
lemma ha16_1_23_eq (j : Fin 7) : ha16_1_23 j = ((ha16_1_22 j).mul (piI.mul (atomPoints j).z)).scale 1 23 := by fin_cases j <;> decide +kernel
lemma ha16_1_23_contains (j : Fin 7) : (ha16_1_23 j).Contains (fullFactor true 16 23 ((j.val:ℝ)/6)) := by
  rw [ha16_1_23_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha16_1_22 j) true 16 22 j (ha16_1_22_contains j)
noncomputable def hk16_1_24 (j : Fin 6) (i k : Fin 16) : CBox := (kernel16_0 j i k).mul (mpower1_24 j i k)
lemma hk16_1_24_contains (j : Fin 6) (i k : Fin 16) :
    (hk16_1_24 j i k).Contains (fullFactor true 16 24 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk16_1_24,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel16_0 j i k) (mpower1_24 j i k) (quadraturePoint j.val (16*i.val+k.val)) 16 24 (kernel16_0_contains j i k) (mpower1_24_contains j i k)
noncomputable def ha16_1_24 : Fin 7 → CBox := ![⟨⟨(-2),2⟩,⟨(-2),2⟩⟩,⟨⟨(-84),84⟩,⟨(-84),84⟩⟩,⟨⟨(-5),5⟩,⟨(-5),5⟩⟩,⟨⟨46188,46190⟩,⟨148646,148648⟩⟩,⟨⟨809826931477,809826931479⟩,⟨1995797519498,1995797519499⟩⟩,⟨⟨12171176039912591,12171176039912594⟩,⟨11950608854121036,11950608854121039⟩⟩,⟨⟨604043674408891099,604043674408891110⟩,⟨(-2050649622462992639),(-2050649622462992628)⟩⟩]
lemma ha16_1_24_eq (j : Fin 7) : ha16_1_24 j = ((ha16_1_23 j).mul (piI.mul (atomPoints j).z)).scale 1 24 := by fin_cases j <;> decide +kernel
lemma ha16_1_24_contains (j : Fin 7) : (ha16_1_24 j).Contains (fullFactor true 16 24 ((j.val:ℝ)/6)) := by
  rw [ha16_1_24_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha16_1_23 j) true 16 23 j (ha16_1_23_contains j)
noncomputable def hk16_1_25 (j : Fin 6) (i k : Fin 16) : CBox := (kernel16_0 j i k).mul (mpower1_25 j i k)
lemma hk16_1_25_contains (j : Fin 6) (i k : Fin 16) :
    (hk16_1_25 j i k).Contains (fullFactor true 16 25 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk16_1_25,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel16_0 j i k) (mpower1_25 j i k) (quadraturePoint j.val (16*i.val+k.val)) 16 25 (kernel16_0_contains j i k) (mpower1_25_contains j i k)
noncomputable def ha16_1_25 : Fin 7 → CBox := ![⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-39),39⟩,⟨(-39),39⟩⟩,⟨⟨(-3),3⟩,⟨(-3),3⟩⟩,⟨⟨25144,25145⟩,⟨(-26265),(-26264)⟩⟩,⟨⟨319735460367,319735460368⟩,⟨(-270629453254),(-270629453253)⟩⟩,⟨⟨1609982176704411,1609982176704413⟩,⟨(-2325589250842123),(-2325589250842121)⟩⟩,⟨⟨(-300734899579534681),(-300734899579534678)⟩,⟨(-71846403169724296),(-71846403169724293)⟩⟩]
lemma ha16_1_25_eq (j : Fin 7) : ha16_1_25 j = ((ha16_1_24 j).mul (piI.mul (atomPoints j).z)).scale 1 25 := by fin_cases j <;> decide +kernel
lemma ha16_1_25_contains (j : Fin 7) : (ha16_1_25 j).Contains (fullFactor true 16 25 ((j.val:ℝ)/6)) := by
  rw [ha16_1_25_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha16_1_24 j) true 16 24 j (ha16_1_24_contains j)
noncomputable def hk16_1_26 (j : Fin 6) (i k : Fin 16) : CBox := (kernel16_0 j i k).mul (mpower1_26 j i k)
lemma hk16_1_26_contains (j : Fin 6) (i k : Fin 16) :
    (hk16_1_26 j i k).Contains (fullFactor true 16 26 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk16_1_26,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel16_0 j i k) (mpower1_26 j i k) (quadraturePoint j.val (16*i.val+k.val)) 16 26 (kernel16_0_contains j i k) (mpower1_26_contains j i k)
noncomputable def ha16_1_26 : Fin 7 → CBox := ![⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-18),18⟩,⟨(-18),18⟩⟩,⟨⟨(-2),2⟩,⟨(-2),2⟩⟩,⟨⟨(-7898),(-7896)⟩,⟨(-2082),(-2081)⟩⟩,⟨⟨(-66723782481),(-66723782480)⟩,⟨(-41041318590),(-41041318589)⟩⟩,⟨⟨(-409024581160782),(-409024581160780)⟩,⟨(-189974214810452),(-189974214810451)⟩⟩,⟨⟨(-7806508917887070),(-7806508917887068)⟩,⟨42286630507565997,42286630507565999⟩⟩]
lemma ha16_1_26_eq (j : Fin 7) : ha16_1_26 j = ((ha16_1_25 j).mul (piI.mul (atomPoints j).z)).scale 1 26 := by fin_cases j <;> decide +kernel
lemma ha16_1_26_contains (j : Fin 7) : (ha16_1_26 j).Contains (fullFactor true 16 26 ((j.val:ℝ)/6)) := by
  rw [ha16_1_26_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha16_1_25 j) true 16 25 j (ha16_1_25_contains j)
noncomputable def hk16_1_27 (j : Fin 6) (i k : Fin 16) : CBox := (kernel16_0 j i k).mul (mpower1_27 j i k)
lemma hk16_1_27_contains (j : Fin 6) (i k : Fin 16) :
    (hk16_1_27 j i k).Contains (fullFactor true 16 27 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk16_1_27,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel16_0 j i k) (mpower1_27 j i k) (quadraturePoint j.val (16*i.val+k.val)) 16 27 (kernel16_0_contains j i k) (mpower1_27_contains j i k)
noncomputable def ha16_1_27 : Fin 7 → CBox := ![⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-8),8⟩,⟨(-8),8⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨433,435⟩,⟨1712,1713⟩⟩,⟨⟨(-3277782738),(-3277782737)⟩,⟨13720569678,13720569679⟩⟩,⟨⟨(-18074919792447),(-18074919792445)⟩,⟨66843936942736,66843936942737⟩⟩,⟨⟨5709776970757746,5709776970757747⟩,⟨749970538260544,749970538260545⟩⟩]
lemma ha16_1_27_eq (j : Fin 7) : ha16_1_27 j = ((ha16_1_26 j).mul (piI.mul (atomPoints j).z)).scale 1 27 := by fin_cases j <;> decide +kernel
lemma ha16_1_27_contains (j : Fin 7) : (ha16_1_27 j).Contains (fullFactor true 16 27 ((j.val:ℝ)/6)) := by
  rw [ha16_1_27_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha16_1_26 j) true 16 26 j (ha16_1_26_contains j)
noncomputable def hk16_1_28 (j : Fin 6) (i k : Fin 16) : CBox := (kernel16_0 j i k).mul (mpower1_28 j i k)
lemma hk16_1_28_contains (j : Fin 6) (i k : Fin 16) :
    (hk16_1_28 j i k).Contains (fullFactor true 16 28 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk16_1_28,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel16_0 j i k) (mpower1_28 j i k) (quadraturePoint j.val (16*i.val+k.val)) 16 28 (kernel16_0_contains j i k) (mpower1_28_contains j i k)
noncomputable def ha16_1_28 : Fin 7 → CBox := ![⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-4),4⟩,⟨(-4),4⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨268,269⟩,⟨(-253),(-252)⟩⟩,⟨⟨2441281889,2441281891⟩,⟨(-201722608),(-201722607)⟩⟩,⟨⟨10207411708651,10207411708652⟩,⟨955817026427,955817026428⟩⟩,⟨⟨58429256050481,58429256050482⟩,⟨(-741392064265433),(-741392064265432)⟩⟩]
lemma ha16_1_28_eq (j : Fin 7) : ha16_1_28 j = ((ha16_1_27 j).mul (piI.mul (atomPoints j).z)).scale 1 28 := by fin_cases j <;> decide +kernel
lemma ha16_1_28_contains (j : Fin 7) : (ha16_1_28 j).Contains (fullFactor true 16 28 ((j.val:ℝ)/6)) := by
  rw [ha16_1_28_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha16_1_27 j) true 16 27 j (ha16_1_27_contains j)
noncomputable def hk16_1_29 (j : Fin 6) (i k : Fin 16) : CBox := (kernel16_0 j i k).mul (mpower1_29 j i k)
lemma hk16_1_29_contains (j : Fin 6) (i k : Fin 16) :
    (hk16_1_29 j i k).Contains (fullFactor true 16 29 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk16_1_29,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel16_0 j i k) (mpower1_29 j i k) (quadraturePoint j.val (16*i.val+k.val)) 16 29 (kernel16_0_contains j i k) (mpower1_29_contains j i k)
noncomputable def ha16_1_29 : Fin 7 → CBox := ![⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-2),2⟩,⟨(-2),2⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-71),(-70)⟩,⟨(-23),(-22)⟩⟩,⟨⟨(-159702364),(-159702363)⟩,⟨(-378379804),(-378379803)⟩⟩,⟨⟨(-113252964480),(-113252964479)⟩,⟨(-1461154667679),(-1461154667678)⟩⟩,⟨⟨(-92695086422804),(-92695086422803)⟩,⟨(-2475030705968),(-2475030705967)⟩⟩]
lemma ha16_1_29_eq (j : Fin 7) : ha16_1_29 j = ((ha16_1_28 j).mul (piI.mul (atomPoints j).z)).scale 1 29 := by fin_cases j <;> decide +kernel
lemma ha16_1_29_contains (j : Fin 7) : (ha16_1_29 j).Contains (fullFactor true 16 29 ((j.val:ℝ)/6)) := by
  rw [ha16_1_29_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha16_1_28 j) true 16 28 j (ha16_1_28_contains j)
noncomputable def hk16_1_30 (j : Fin 6) (i k : Fin 16) : CBox := (kernel16_0 j i k).mul (mpower1_30 j i k)
lemma hk16_1_30_contains (j : Fin 6) (i k : Fin 16) :
    (hk16_1_30 j i k).Contains (fullFactor true 16 30 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk16_1_30,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel16_0 j i k) (mpower1_30 j i k) (quadraturePoint j.val (16*i.val+k.val)) 16 30 (kernel16_0_contains j i k) (mpower1_30_contains j i k)
noncomputable def ha16_1_30 : Fin 7 → CBox := ![⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨2,3⟩,⟨13,15⟩⟩,⟨⟨(-50203487),(-50203486)⟩,⟨43706782,43706783⟩⟩,⟨⟨(-196316158072),(-196316158070)⟩,⟨49725682648,49725682649⟩⟩,⟨⟨282275565067,282275565068⟩,⟨11172970518026,11172970518027⟩⟩]
lemma ha16_1_30_eq (j : Fin 7) : ha16_1_30 j = ((ha16_1_29 j).mul (piI.mul (atomPoints j).z)).scale 1 30 := by fin_cases j <;> decide +kernel
lemma ha16_1_30_contains (j : Fin 7) : (ha16_1_30 j).Contains (fullFactor true 16 30 ((j.val:ℝ)/6)) := by
  rw [ha16_1_30_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha16_1_29 j) true 16 29 j (ha16_1_29_contains j)
end SharpPlanar.CachedData

end OAI
