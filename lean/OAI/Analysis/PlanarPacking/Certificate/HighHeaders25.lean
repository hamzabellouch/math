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
noncomputable def hk25_0_0 (j : Fin 6) (i k : Fin 16) : CBox := (power25 j i k).conj.mul (mpower0_0 j i k)
lemma hk25_0_0_contains (j : Fin 6) (i k : Fin 16) :
    (hk25_0_0 j i k).Contains (fullFactor false 25 0 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk25_0_0,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power25 j i k) (mpower0_0 j i k) (quadraturePoint j.val (16*i.val+k.val)) 25 0 (power25_contains j i k) (mpower0_0_contains j i k)
noncomputable def ha25_0_0 : Fin 7 → CBox := ![⟨⟨999999999999999999999999999701,1000000000000000000000000000399⟩,⟨(-399),399⟩⟩,⟨⟨866025403784438646722288648609,866025403784438646795338456630⟩,⟨499999999999999999971409335005,500000000000000000045598081167⟩⟩,⟨⟨499999999999999999882622206269,500000000000000000083362961311⟩,⟨866025403784438646672755213395,866025403784438646874329600784⟩⟩,⟨⟨(-111124583049),52209165099⟩,⟨999999999999999999918333125951,1000000000000000000081666874074⟩⟩,⟨⟨(-500000000000000000309217399782),(-499999999999999999758812265101)⟩,⟨866025403784438646469186844397,866025403784438647018982551708⟩⟩,⟨⟨(-866025403784438647134603431931),(-866025403784438646441939091151)⟩,⟨499999999999999999611451721834,500000000000000000303511197067⟩⟩,⟨⟨(-1000000000000000000163829944649),(-999999999999999999836170055451)⟩,⟨(-222745362649),104914526549⟩⟩]
lemma ha25_0_0_eq (j : Fin 7) : ha25_0_0 j = ((atomPoints j).direct.powBin 7 25).conj := by fin_cases j <;> decide +kernel
lemma ha25_0_0_contains (j : Fin 7) : (ha25_0_0 j).Contains (fullFactor false 25 0 ((j.val:ℝ)/6)) := by
  rw [ha25_0_0_eq]
  simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @direct_factor_zero_full ((atomPoints j).direct.powBin 7 25) ((j.val:ℝ)/6) 25 (@direct_power_bin_contains (atomPoints j) ((j.val:ℝ)/6) (atomPoints_contains j) 25 (by norm_num))
noncomputable def hk25_0_1 (j : Fin 6) (i k : Fin 16) : CBox := (power25 j i k).conj.mul (mpower0_1 j i k)
lemma hk25_0_1_contains (j : Fin 6) (i k : Fin 16) :
    (hk25_0_1 j i k).Contains (fullFactor false 25 1 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk25_0_1,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power25 j i k) (mpower0_1 j i k) (quadraturePoint j.val (16*i.val+k.val)) 25 1 (power25_contains j i k) (mpower0_1_contains j i k)
noncomputable def ha25_0_1 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-261799387799149436563041766137),(-261799387799149436523363296147)⟩,⟨453449841058554462626442959834,453449841058554462666135125549⟩⟩,⟨⟨(-906899682117108925414989583821),(-906899682117108925201014627613)⟩,⟨523598775598298872953748928506,523598775598298873165630822280⟩⟩,⟨⟨(-1570796326794896619363282025817),(-1570796326794896619101717974223)⟩,⟨(-174554086870),82009964763⟩⟩,⟨⟨(-1813799364234217851132939599600),(-1813799364234217849975676660195)⟩,⟨(-1047197551196597746804290074346),(-1047197551196597745648190922602)⟩⟩,⟨⟨(-1308996938995747183490423789158),(-1308996938995747181674449653123)⟩,⟨(-2267249205292772314218869256092),(-2267249205292772312398261374058)⟩⟩,⟨⟨(-329598705862),699775194920⟩,⟨(-3141592653589793238984686950548),(-3141592653589793237945313049766)⟩⟩]
lemma ha25_0_1_eq (j : Fin 7) : ha25_0_1 j = ((ha25_0_0 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 1 := by fin_cases j <;> decide +kernel
lemma ha25_0_1_contains (j : Fin 7) : (ha25_0_1 j).Contains (fullFactor false 25 1 ((j.val:ℝ)/6)) := by
  rw [ha25_0_1_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha25_0_0 j) false 25 0 j (ha25_0_0_contains j)
noncomputable def hk25_0_2 (j : Fin 6) (i k : Fin 16) : CBox := (power25 j i k).conj.mul (mpower0_2 j i k)
lemma hk25_0_2_contains (j : Fin 6) (i k : Fin 16) :
    (hk25_0_2 j i k).Contains (fullFactor false 25 2 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk25_0_2,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power25 j i k) (mpower0_2 j i k) (quadraturePoint j.val (16*i.val+k.val)) 25 2 (power25_contains j i k) (mpower0_2_contains j i k)
noncomputable def ha25_0_2 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-118712890786751174412827042648),(-118712890786751174402057783094)⟩,⟨(-68538919452009434859588777995),(-68538919452009434848982812685)⟩⟩,⟨⟨(-274155677808037739459062024603),(-274155677808037739347248259824)⟩,⟨(-474851563147004697694619911921),(-474851563147004697581071387369)⟩⟩,⟨⟨(-64410475706),137094459242⟩,⟨(-1233700550136169827460841715720),(-1233700550136169827251482799169)⟩⟩,⟨⟨1096622711232150957117447452574,1096622711232150958331602311728⟩,⟨(-1899406252588018791095739070136),(-1899406252588018789877810156015)⟩⟩,⟨⟨2967822269668779359090701790529,2967822269668779361483318806917⟩,⟨(-1713472986300235872373573763662),(-1713472986300235869991015024381)⟩⟩,⟨⟨4934802200544679308600472695569,4934802200544679310248825364353⟩,⟨(-517732436485),1099204305763⟩⟩]
lemma ha25_0_2_eq (j : Fin 7) : ha25_0_2 j = ((ha25_0_1 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 2 := by fin_cases j <;> decide +kernel
lemma ha25_0_2_contains (j : Fin 7) : (ha25_0_2 j).Contains (fullFactor false 25 2 ((j.val:ℝ)/6)) := by
  rw [ha25_0_2_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha25_0_1 j) false 25 1 j (ha25_0_1_contains j)
noncomputable def hk25_0_3 (j : Fin 6) (i k : Fin 16) : CBox := (power25 j i k).conj.mul (mpower0_3 j i k)
lemma hk25_0_3_contains (j : Fin 6) (i k : Fin 16) :
    (hk25_0_3 j i k).Contains (fullFactor false 25 3 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk25_0_3,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power25 j i k) (mpower0_3 j i k) (quadraturePoint j.val (16*i.val+k.val)) 25 3 (power25_contains j i k) (mpower0_3_contains j i k)
noncomputable def ha25_0_3 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨11962298101967523215133127888,11962298101967523217022295216⟩,⟨(-20719308087892496643317357082),(-20719308087892496641371815103)⟩⟩,⟨⟨165754464703139973121493981340,165754464703139973161657506473⟩,⟨(-95698384815740185743406437791),(-95698384815740185704071453481)⟩⟩,⟨⟨645964097506246253601372123603,645964097506246253713048363554⟩,⟨(-33725246216),71782491001⟩⟩,⟨⟨1326035717625119784660253224918,1326035717625119785514748911972⟩,⟨765587078525921485442997045552,765587078525921486293073981766⟩⟩,⟨⟨1495287262745940400815160917841,1495287262745940402899095296159⟩,⟨2589913510986562079333070643191,2589913510986562081429266827705⟩⟩,⟨⟨(-1151084057260),542168139663⟩,⟨5167712780049970028386381839356,5167712780049970030128982058284⟩⟩]
lemma ha25_0_3_eq (j : Fin 7) : ha25_0_3 j = ((ha25_0_2 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 3 := by fin_cases j <;> decide +kernel
lemma ha25_0_3_contains (j : Fin 7) : (ha25_0_3 j).Contains (fullFactor false 25 3 ((j.val:ℝ)/6)) := by
  rw [ha25_0_3_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha25_0_2 j) false 25 2 j (ha25_0_2_contains j)
noncomputable def hk25_0_4 (j : Fin 6) (i k : Fin 16) : CBox := (power25 j i k).conj.mul (mpower0_4 j i k)
lemma hk25_0_4_contains (j : Fin 6) (i k : Fin 16) :
    (hk25_0_4 j i k).Contains (fullFactor false 25 4 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk25_0_4,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power25 j i k) (mpower0_4 j i k) (quadraturePoint j.val (16*i.val+k.val)) 25 4 (power25_contains j i k) (mpower0_4_contains j i k)
noncomputable def ha25_0_4 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2712151086516110563257060669,2712151086516110563520364565⟩,⟨1565861159883012429760521241,1565861159883012430012796958⟩⟩,⟨⟨25053778558128198871719433745,25053778558128198882097057212⟩,⟨43394417384257769009630971286,43394417384257769020283886299⟩⟩,⟨⟨(-28188918299),13243873220⟩,⟨253669507901048013614993205277,253669507901048013659655817276⟩⟩,⟨⟨(-400860456930051182294625142191),(-400860456930051181848249920759)⟩,⟨694310678148124303990890521759,694310678148124304440513476786⟩⟩,⟨⟨(-1695094429072569102864280162450),(-1695094429072569101486927314767)⟩,⟨978663224926882767895771219107,978663224926882769262818262050⟩⟩,⟨⟨(-4058712126416768218887969327293),(-4058712126416768217506415033860)⟩,⟨(-904059304489),425817861144⟩⟩]
lemma ha25_0_4_eq (j : Fin 7) : ha25_0_4 j = ((ha25_0_3 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 4 := by fin_cases j <;> decide +kernel
lemma ha25_0_4_contains (j : Fin 7) : (ha25_0_4 j).Contains (fullFactor false 25 4 ((j.val:ℝ)/6)) := by
  rw [ha25_0_4_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha25_0_3 j) false 25 3 j (ha25_0_3_contains j)
noncomputable def hk25_0_5 (j : Fin 6) (i k : Fin 16) : CBox := (power25 j i k).conj.mul (mpower0_5 j i k)
lemma hk25_0_5_contains (j : Fin 6) (i k : Fin 16) :
    (hk25_0_5 j i k).Contains (fullFactor false 25 5 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk25_0_5,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power25 j i k) (mpower0_5 j i k) (quadraturePoint j.val (16*i.val+k.val)) 25 5 (power25_contains j i k) (mpower0_5_contains j i k)
noncomputable def ha25_0_5 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-163976597214335483803922399),(-163976597214335483776982193)⟩,⟨284015797627486289472440601,284015797627486289500917772⟩⟩,⟨⟨(-9088505524079561264858341411),(-9088505524079561262598270496)⟩,⟨5247251110858735479931653486,5247251110858735482121840383⟩⟩,⟨⟨(-79692626246167045127946871835),(-79692626246167045113662028952)⟩,⟨(-8855809865),4160685482⟩⟩,⟨⟨(-290832176770545960524044868013),(-290832176770545960334781497454)⟩,⟨(-167912035547479535503746249223),(-167912035547479535316234553093)⟩⟩,⟨⟨(-512426866294798387151580715930),(-512426866294798386434165452683)⟩,⟨(-887549367585894655038065010719),(-887549367585894654314059588722)⟩⟩,⟨⟨(-267549252868),568037213879⟩,⟨(-2550164039877345444303829206689),(-2550164039877345443427655618678)⟩⟩]
lemma ha25_0_5_eq (j : Fin 7) : ha25_0_5 j = ((ha25_0_4 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 5 := by fin_cases j <;> decide +kernel
lemma ha25_0_5_contains (j : Fin 7) : (ha25_0_5 j).Contains (fullFactor false 25 5 ((j.val:ℝ)/6)) := by
  rw [ha25_0_5_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha25_0_4 j) false 25 4 j (ha25_0_4_contains j)
noncomputable def hk25_0_6 (j : Fin 6) (i k : Fin 16) : CBox := (power25 j i k).conj.mul (mpower0_6 j i k)
lemma hk25_0_6_contains (j : Fin 6) (i k : Fin 16) :
    (hk25_0_6 j i k).Contains (fullFactor false 25 6 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk25_0_6,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power25 j i k) (mpower0_6 j i k) (quadraturePoint j.val (16*i.val+k.val)) 25 6 (power25_contains j i k) (mpower0_6_contains j i k)
noncomputable def ha25_0_6 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-24785053981387676528157489),(-24785053981387676525593493)⟩,⟨(-14309657588033580847220467),(-14309657588033580844823941)⟩⟩,⟨⟨(-915818085634149174291281399),(-915818085634149173906106533)⟩,⟨(-1586243454808811297946762304),(-1586243454808811297547256346)⟩⟩,⟨⟨(-1089264913),2318445602⟩,⟨(-20863480763352960875048626542),(-20863480763352960871242452898)⟩⟩,⟨⟨58612357480585547115477233093,58612357480585547181117731692⟩,⟨(-101519581107763923085549688374),(-101519581107763923019161162116)⟩⟩,⟨⟨387266468459182445587032516516,387266468459182445904172184376⟩,⟨(-223588399813024700853152556247),(-223588399813024700539409391072)⟩⟩,⟨⟨1335262768854589495649807696486,1335262768854589496112821387781⟩,⟨(-140088461214),297423589682⟩⟩]
lemma ha25_0_6_eq (j : Fin 7) : ha25_0_6 j = ((ha25_0_5 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 6 := by fin_cases j <;> decide +kernel
lemma ha25_0_6_contains (j : Fin 7) : (ha25_0_6 j).Contains (fullFactor false 25 6 ((j.val:ℝ)/6)) := by
  rw [ha25_0_6_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha25_0_5 j) false 25 5 j (ha25_0_5_contains j)
noncomputable def hk25_0_7 (j : Fin 6) (i k : Fin 16) : CBox := (power25 j i k).conj.mul (mpower0_7 j i k)
lemma hk25_0_7_contains (j : Fin 6) (i k : Fin 16) :
    (hk25_0_7 j i k).Contains (fullFactor false 25 7 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk25_0_7,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power25 j i k) (mpower0_7 j i k) (quadraturePoint j.val (16*i.val+k.val)) 25 7 (power25_contains j i k) (mpower0_7_contains j i k)
noncomputable def ha25_0_7 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1070359884617898514035249,1070359884617898514217916⟩,⟨(-1853917702541761442355632),(-1853917702541761442157943)⟩⟩,⟨⟨237301465925345464582644044,237301465925345464643165350⟩,⟨(-137006065231091009830241274),(-137006065231091009772183144)⟩⟩,⟨⟨4681754135318688100275544620,4681754135318688101144550476⟩,⟨(-244430475),520257977⟩⟩,⟨⟨30374587638444219459438571765,30374587638444219479398657688⟩,⟨17536776349579649246496988046,17536776349579649266192400594⟩⟩,⟨⟨83621865985773321348803187686,83621865985773321466409033738⟩,⟨144837320511075112621702653198,144837320511075112740773643127⟩⟩,⟨⟨(-133483394908),62871554372⟩,⟨599264529320792076786032297659,599264529320792076995739874627⟩⟩]
lemma ha25_0_7_eq (j : Fin 7) : ha25_0_7 j = ((ha25_0_6 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 7 := by fin_cases j <;> decide +kernel
lemma ha25_0_7_contains (j : Fin 7) : (ha25_0_7 j).Contains (fullFactor false 25 7 ((j.val:ℝ)/6)) := by
  rw [ha25_0_7_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha25_0_6 j) false 25 6 j (ha25_0_6_contains j)
noncomputable def hk25_0_8 (j : Fin 6) (i k : Fin 16) : CBox := (power25 j i k).conj.mul (mpower0_8 j i k)
lemma hk25_0_8_contains (j : Fin 6) (i k : Fin 16) :
    (hk25_0_8 j i k).Contains (fullFactor false 25 8 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk25_0_8,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power25 j i k) (mpower0_8 j i k) (quadraturePoint j.val (16*i.val+k.val)) 25 8 (power25_contains j i k) (mpower0_8_contains j i k)
noncomputable def ha25_0_8 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨121338629888859693707968,121338629888859693721294⟩,⟨70054890629433514722067,70054890629433514734246⟩⟩,⟨⟨17934052001134979765664539,17934052001134979773321417⟩,⟨31062689251548081587463378,31062689251548081595484475⟩⟩,⟨⟨(-102152415),47993812⟩,⟨919260274839426580160455273,919260274839426580334010271⟩⟩,⟨⟨(-4591117312290554824044131097),(-4591117312290554818873270168)⟩,⟨7952048448396308884521412362,7952048448396308889772262795⟩⟩,⟨⟨(-47397902300335817878448491358),(-47397902300335817839331728813)⟩,⟨27365191652122466668606824194,27365191652122466707180353428⟩⟩,⟨⟨(-235330630358893204584842116379),(-235330630358893204501741062815)⟩,⟨(-52418806603),24689601667⟩⟩]
lemma ha25_0_8_eq (j : Fin 7) : ha25_0_8 j = ((ha25_0_7 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 8 := by fin_cases j <;> decide +kernel
lemma ha25_0_8_contains (j : Fin 7) : (ha25_0_8 j).Contains (fullFactor false 25 8 ((j.val:ℝ)/6)) := by
  rw [ha25_0_8_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha25_0_7 j) false 25 7 j (ha25_0_7_contains j)
noncomputable def hk25_0_9 (j : Fin 6) (i k : Fin 16) : CBox := (power25 j i k).conj.mul (mpower0_9 j i k)
lemma hk25_0_9_contains (j : Fin 6) (i k : Fin 16) :
    (hk25_0_9 j i k).Contains (fullFactor false 25 9 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk25_0_9,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power25 j i k) (mpower0_9 j i k) (quadraturePoint j.val (16*i.val+k.val)) 25 9 (power25_contains j i k) (mpower0_9_contains j i k)
noncomputable def ha25_0_9 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-4075628328693792152891),(-4075628328693792152168)⟩,⟨7059195338064676366170,7059195338064676366969⟩⟩,⟨⟨(-3614308013089114300217643),(-3614308013089114299272840)⟩,⟨2086721704291221581539808,2086721704291221582437369⟩⟩,⟨⟨(-160441184787359821889144924),(-160441184787359821858343161)⟩,⟨(-17828960),8376501⟩⟩,⟨⟨(-1850525702701626522020527803),(-1850525702701626520792709015)⟩,⟨(-1068401512597105450690539161),(-1068401512597105449483824354)⟩⟩,⟨⟨(-7960211579480062802719668516),(-7960211579480062791473745553)⟩,⟨(-13787490894657571034636995564),(-13787490894657571023214503631)⟩⟩,⟨⟨(-8618296802),18297615304⟩,⟨(-82145886611128228813991558831),(-82145886611128228784722340421)⟩⟩]
lemma ha25_0_9_eq (j : Fin 7) : ha25_0_9 j = ((ha25_0_8 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 9 := by fin_cases j <;> decide +kernel
lemma ha25_0_9_contains (j : Fin 7) : (ha25_0_9 j).Contains (fullFactor false 25 9 ((j.val:ℝ)/6)) := by
  rw [ha25_0_9_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha25_0_8 j) false 25 8 j (ha25_0_8_contains j)
noncomputable def hk25_0_10 (j : Fin 6) (i k : Fin 16) : CBox := (power25 j i k).conj.mul (mpower0_10 j i k)
lemma hk25_0_10_contains (j : Fin 6) (i k : Fin 16) :
    (hk25_0_10 j i k).Contains (fullFactor false 25 10 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk25_0_10,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power25 j i k) (mpower0_10 j i k) (quadraturePoint j.val (16*i.val+k.val)) 25 10 (power25_contains j i k) (mpower0_10_contains j i k)
noncomputable def ha25_0_10 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-369618603571988403213),(-369618603571988403169)⟩,⟨(-213399400269781075751),(-213399400269781075711)⟩⟩,⟨⟨(-218520985876255821584661),(-218520985876255821489973)⟩,⟨(-378489450057716124923630),(-378489450057716124823485)⟩⟩,⟨⟨(-1315778),2800567⟩,⟨(-25202042373060605483701347),(-25202042373060605478782795)⟩⟩,⟨⟨223765489537285961150323636,223765489537285961403769662⟩,⟨(-387573196859101311986533174),(-387573196859101311728145723)⟩⟩,⟨⟨3609556675507699248529519048,3609556675507699251531410020⟩,⟨(-2083978518259580818947553256),(-2083978518259580815996743999)⟩⟩,⟨⟨25806891390014060008153209604,25806891390014060017430551645⟩,⟨(-2707517792),5748365382⟩⟩]
lemma ha25_0_10_eq (j : Fin 7) : ha25_0_10 j = ((ha25_0_9 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 10 := by fin_cases j <;> decide +kernel
lemma ha25_0_10_contains (j : Fin 7) : (ha25_0_10 j).Contains (fullFactor false 25 10 ((j.val:ℝ)/6)) := by
  rw [ha25_0_10_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha25_0_9 j) false 25 9 j (ha25_0_9_contains j)
noncomputable def hk25_0_11 (j : Fin 6) (i k : Fin 16) : CBox := (power25 j i k).conj.mul (mpower0_11 j i k)
lemma hk25_0_11_contains (j : Fin 6) (i k : Fin 16) :
    (hk25_0_11 j i k).Contains (fullFactor false 25 11 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk25_0_11,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power25 j i k) (mpower0_11 j i k) (quadraturePoint j.val (16*i.val+k.val)) 25 11 (power25_contains j i k) (mpower0_11_contains j i k)
noncomputable def ha25_0_11 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨10157787699515332859,10157787699515332862⟩,⟨(-17593804388058740566),(-17593804388058740563)⟩⟩,⟨⟨36032111386744300672047,36032111386744300681697⟩,⟨(-20803149208607401702196),(-20803149208607401693115)⟩⟩,⟨⟨3598843235212085340131324,3598843235212085340845148⟩,⟨(-187893),399921⟩⟩,⟨⟨73793764120052327759007866,73793764120052327808439616⟩,⟨42604849579227958656950502,42604849579227958705342129⟩⟩,⟨⟨495985727515397111936401987,495985727515397112640271720⟩,⟨859072479885680691300496621,859072479885680692017679515⟩⟩,⟨⟨(-1641729315),773265274⟩,⟨7370430945714350775983375158,7370430945714350778656438661⟩⟩]
lemma ha25_0_11_eq (j : Fin 7) : ha25_0_11 j = ((ha25_0_10 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 11 := by fin_cases j <;> decide +kernel
lemma ha25_0_11_contains (j : Fin 7) : (ha25_0_11 j).Contains (fullFactor false 25 11 ((j.val:ℝ)/6)) := by
  rw [ha25_0_11_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha25_0_10 j) false 25 10 j (ha25_0_10_contains j)
noncomputable def hk25_0_12 (j : Fin 6) (i k : Fin 16) : CBox := (power25 j i k).conj.mul (mpower0_12 j i k)
lemma hk25_0_12_contains (j : Fin 6) (i k : Fin 16) :
    (hk25_0_12 j i k).Contains (fullFactor false 25 12 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk25_0_12,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power25 j i k) (mpower0_12 j i k) (quadraturePoint j.val (16*i.val+k.val)) 25 12 (power25_contains j i k) (mpower0_12_contains j i k)
noncomputable def ha25_0_12 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨767674536308627877,767674536308627878⟩,⟨443217100187807442,443217100187807443⟩⟩,⟨⟨1815417242369259285067,1815417242369259285866⟩,⟨3144394900720139784562,3144394900720139785416⟩⟩,⟨⟨(-52350),24596⟩,⟨471087477881817150323798,471087477881817150418738⟩⟩,⟨⟨(-7435949024744486038263906),(-7435949024744486029794303)⟩,⟨12879441513349692554542560,12879441513349692563211025⟩⟩,⟨⟨(-187420541090973602912425505),(-187420541090973602755363890)⟩,⟨108207299850538926367921130,108207299850538926521826120⟩⟩,⟨⟨(-1929574309403923048273689052),(-1929574309403923047567740637)⟩,⟨(-429803730),202440376⟩⟩]
lemma ha25_0_12_eq (j : Fin 7) : ha25_0_12 j = ((ha25_0_11 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 12 := by fin_cases j <;> decide +kernel
lemma ha25_0_12_contains (j : Fin 7) : (ha25_0_12 j).Contains (fullFactor false 25 12 ((j.val:ℝ)/6)) := by
  rw [ha25_0_12_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha25_0_11 j) false 25 11 j (ha25_0_11_contains j)
noncomputable def hk25_0_13 (j : Fin 6) (i k : Fin 16) : CBox := (power25 j i k).conj.mul (mpower0_13 j i k)
lemma hk25_0_13_contains (j : Fin 6) (i k : Fin 16) :
    (hk25_0_13 j i k).Contains (fullFactor false 25 13 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk25_0_13,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power25 j i k) (mpower0_13 j i k) (quadraturePoint j.val (16*i.val+k.val)) 25 13 (power25_contains j i k) (mpower0_13_contains j i k)
noncomputable def ha25_0_13 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-17851379306351119),(-17851379306351118)⟩,⟨30919495943783799,30919495943783800⟩⟩,⟨⟨(-253292510771476882322),(-253292510771476882251)⟩,⟨146238499277628361475,146238499277628361541⟩⟩,⟨⟨(-56921729219679268124135),(-56921729219679268112481)⟩,⟨(-6326),2972⟩⟩,⟨⟨(-2074972248239938620319794),(-2074972248239938618916635)⟩,⟨(-1197985786082331538280660),(-1197985786082331536912330)⟩⟩,⟨⟨(-21791234504823142529257660),(-21791234504823142498194270)⟩,⟨(-37743525322001707911055154),(-37743525322001707879305293)⟩⟩,⟨⟨(-48921939),103866788⟩,⟨(-466302805767612564511218417),(-466302805767612564339133947)⟩⟩]
lemma ha25_0_13_eq (j : Fin 7) : ha25_0_13 j = ((ha25_0_12 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 13 := by fin_cases j <;> decide +kernel
lemma ha25_0_13_contains (j : Fin 7) : (ha25_0_13 j).Contains (fullFactor false 25 13 ((j.val:ℝ)/6)) := by
  rw [ha25_0_13_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha25_0_12 j) false 25 12 j (ha25_0_12_contains j)
noncomputable def hk25_0_14 (j : Fin 6) (i k : Fin 16) : CBox := (power25 j i k).conj.mul (mpower0_14 j i k)
lemma hk25_0_14_contains (j : Fin 6) (i k : Fin 16) :
    (hk25_0_14 j i k).Contains (fullFactor false 25 14 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk25_0_14,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power25 j i k) (mpower0_14 j i k) (quadraturePoint j.val (16*i.val+k.val)) 25 14 (power25_contains j i k) (mpower0_14_contains j i k)
noncomputable def ha25_0_14 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1156386444162984),(-1156386444162983)⟩,⟨(-667640024824733),(-667640024824732)⟩⟩,⟨⟨(-10938614166728417761),(-10938614166728417755)⟩,⟨(-18946235501166317755),(-18946235501166317748)⟩⟩,⟨⟨(-334),710⟩,⟨(-6386603083791852241821),(-6386603083791852240493)⟩⟩,⟨⟨179218254507678396470310,179218254507678396675583⟩,⟨(-310415122451108950132973),(-310415122451108949922072)⟩⟩,⟨⟨7058022730486958378430840,7058022730486958384390518⟩,⟨(-4074951323393142881139676),(-4074951323393142875317864)⟩⟩,⟨⟨104638104924845707099641256,104638104924845707138589995⟩,⟨(-10978058),23307653⟩⟩]
lemma ha25_0_14_eq (j : Fin 7) : ha25_0_14 j = ((ha25_0_13 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 14 := by fin_cases j <;> decide +kernel
lemma ha25_0_14_contains (j : Fin 7) : (ha25_0_14 j).Contains (fullFactor false 25 14 ((j.val:ℝ)/6)) := by
  rw [ha25_0_14_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha25_0_13 j) false 25 13 j (ha25_0_13_contains j)
noncomputable def hk25_0_15 (j : Fin 6) (i k : Fin 16) : CBox := (power25 j i k).conj.mul (mpower0_15 j i k)
lemma hk25_0_15_contains (j : Fin 6) (i k : Fin 16) :
    (hk25_0_15 j i k).Contains (fullFactor false 25 15 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk25_0_15,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power25 j i k) (mpower0_15 j i k) (quadraturePoint j.val (16*i.val+k.val)) 25 15 (power25_contains j i k) (mpower0_15_contains j i k)
noncomputable def ha25_0_15 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨23305033302576,23305033302577⟩,⟨(-40365501752148),(-40365501752147)⟩⟩,⟨⟨1322696761414360852,1322696761414360853⟩,⟨(-763659331258827444),(-763659331258827443)⟩⟩,⟨⟨668803510981146723184,668803510981146723326⟩,⟨(-35),75⟩⟩,⟨⟨43342127478025776405116,43342127478025776434702⟩,⟨25023588966689257651341,25023588966689257680083⟩⟩,⟨⟨711213174517105745848266,711213174517105746866629⟩,⟨1231857353275977868740739,1231857353275977869784821⟩⟩,⟨⟨(-4881544),2299240⟩,⟨21915353447830215823517662,21915353447830215831744826⟩⟩]
lemma ha25_0_15_eq (j : Fin 7) : ha25_0_15 j = ((ha25_0_14 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 15 := by fin_cases j <;> decide +kernel
lemma ha25_0_15_contains (j : Fin 7) : (ha25_0_15 j).Contains (fullFactor false 25 15 ((j.val:ℝ)/6)) := by
  rw [ha25_0_15_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha25_0_14 j) false 25 14 j (ha25_0_14_contains j)
noncomputable def hk25_0_16 (j : Fin 6) (i k : Fin 16) : CBox := (power25 j i k).conj.mul (mpower0_16 j i k)
lemma hk25_0_16_contains (j : Fin 6) (i k : Fin 16) :
    (hk25_0_16 j i k).Contains (fullFactor false 25 16 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk25_0_16,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power25 j i k) (mpower0_16 j i k) (quadraturePoint j.val (16*i.val+k.val)) 25 16 (power25_contains j i k) (mpower0_16_contains j i k)
noncomputable def ha25_0_16 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1320957955864,1320957955865⟩,⟨762655431406,762655431407⟩⟩,⟨⟨49981386352667221,49981386352667222⟩,⟨86570300595549323,86570300595549324⟩⟩,⟨⟨(-8),4⟩,⟨65659631149794723615,65659631149794723630⟩⟩,⟨⟨(-3275580136008399051525),(-3275580136008399047751)⟩,⟨5673471219829920492747,5673471219829920496639⟩⟩,⟨⟨(-201562188089707223688975),(-201562188089707223517495)⟩,⟨116371983552042445594523,116371983552042445761524⟩⟩,⟨⟨(-4303069587032947008164019),(-4303069587032947006534921)⟩,⟨(-958489),451455⟩⟩]
lemma ha25_0_16_eq (j : Fin 7) : ha25_0_16 j = ((ha25_0_15 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 16 := by fin_cases j <;> decide +kernel
lemma ha25_0_16_contains (j : Fin 7) : (ha25_0_16 j).Contains (fullFactor false 25 16 ((j.val:ℝ)/6)) := by
  rw [ha25_0_16_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha25_0_15 j) false 25 15 j (ha25_0_15_contains j)
noncomputable def hk25_0_17 (j : Fin 6) (i k : Fin 16) : CBox := (power25 j i k).conj.mul (mpower0_17 j i k)
lemma hk25_0_17_contains (j : Fin 6) (i k : Fin 16) :
    (hk25_0_17 j i k).Contains (fullFactor false 25 17 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk25_0_17,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power25 j i k) (mpower0_17 j i k) (quadraturePoint j.val (16*i.val+k.val)) 25 17 (power25_contains j i k) (mpower0_17_contains j i k)
noncomputable def ha25_0_17 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-23489732359),(-23489732358)⟩,⟨40685409900,40685409901⟩⟩,⟨⟨(-5332718046471331),(-5332718046471330)⟩,⟨3078846199642597,3078846199642598⟩⟩,⟨⟨(-6066935731106195668),(-6066935731106195666)⟩,⟨(-1),1⟩⟩,⟨⟨(-698970019787090239449),(-698970019787090238966)⟩,⟨(-403550529079554596975),(-403550529079554596508)⟩⟩,⟨⟨(-17921243559351411754652),(-17921243559351411728876)⟩,⟨(-31040504379613153653375),(-31040504379613153626867)⟩⟩,⟨⟨(-83429),177129⟩,⟨(-795205400147551278640256),(-795205400147551278336667)⟩⟩]
lemma ha25_0_17_eq (j : Fin 7) : ha25_0_17 j = ((ha25_0_16 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 17 := by fin_cases j <;> decide +kernel
lemma ha25_0_17_contains (j : Fin 7) : (ha25_0_17 j).Contains (fullFactor false 25 17 ((j.val:ℝ)/6)) := by
  rw [ha25_0_17_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha25_0_16 j) false 25 16 j (ha25_0_16_contains j)
noncomputable def hk25_0_18 (j : Fin 6) (i k : Fin 16) : CBox := (power25 j i k).conj.mul (mpower0_18 j i k)
lemma hk25_0_18_contains (j : Fin 6) (i k : Fin 16) :
    (hk25_0_18 j i k).Contains (fullFactor false 25 18 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk25_0_18,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power25 j i k) (mpower0_18 j i k) (quadraturePoint j.val (16*i.val+k.val)) 25 18 (power25_contains j i k) (mpower0_18_contains j i k)
noncomputable def ha25_0_18 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1183490601),(-1183490600)⟩,⟨(-683288617),(-683288616)⟩⟩,⟨⟨(-179120011154260),(-179120011154259)⟩,⟨(-310244959971483),(-310244959971482)⟩⟩,⟨⟨(-1),1⟩,⟨(-529440020073462377),(-529440020073462376)⟩⟩,⟨⟨46955236204022331345,46955236204022331401⟩,⟨(-81328854786764263410),(-81328854786764263353)⟩⟩,⟨⟨4514658357533078056380,4514658357533078060250⟩,⟨(-2606539218020916337495),(-2606539218020916333736)⟩⟩,⟨⟨138789524622137721119840,138789524622137721173269⟩,⟨(-14562),30915⟩⟩]
lemma ha25_0_18_eq (j : Fin 7) : ha25_0_18 j = ((ha25_0_17 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 18 := by fin_cases j <;> decide +kernel
lemma ha25_0_18_contains (j : Fin 7) : (ha25_0_18 j).Contains (fullFactor false 25 18 ((j.val:ℝ)/6)) := by
  rw [ha25_0_18_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha25_0_17 j) false 25 17 j (ha25_0_17_contains j)
noncomputable def hk25_0_19 (j : Fin 6) (i k : Fin 16) : CBox := (power25 j i k).conj.mul (mpower0_19 j i k)
lemma hk25_0_19_contains (j : Fin 6) (i k : Fin 16) :
    (hk25_0_19 j i k).Contains (fullFactor false 25 19 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk25_0_19,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power25 j i k) (mpower0_19 j i k) (quadraturePoint j.val (16*i.val+k.val)) 25 19 (power25_contains j i k) (mpower0_19_contains j i k)
noncomputable def ha25_0_19 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨18829951,18829952⟩,⟨(-32614434),(-32614433)⟩⟩,⟨⟨17099355913327,17099355913328⟩,⟨(-9872317739529),(-9872317739528)⟩⟩,⟨⟨43770654673137422,43770654673137423⟩,⟨(-1),1⟩⟩,⟨⟨8964987113086656141,8964987113086656148⟩,⟨5175937723022106878,5175937723022106885⟩⟩,⟨⟨359152827132815577235,359152827132815577755⟩,⟨622070944276038605246,622070944276038605783⟩⟩,⟨⟨(-5112),2408⟩,⟨22948428997269873106077,22948428997269873114985⟩⟩]
lemma ha25_0_19_eq (j : Fin 7) : ha25_0_19 j = ((ha25_0_18 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 19 := by fin_cases j <;> decide +kernel
lemma ha25_0_19_contains (j : Fin 7) : (ha25_0_19 j).Contains (fullFactor false 25 19 ((j.val:ℝ)/6)) := by
  rw [ha25_0_19_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha25_0_18 j) false 25 18 j (ha25_0_18_contains j)
noncomputable def hk25_0_20 (j : Fin 6) (i k : Fin 16) : CBox := (power25 j i k).conj.mul (mpower0_20 j i k)
lemma hk25_0_20_contains (j : Fin 6) (i k : Fin 16) :
    (hk25_0_20 j i k).Contains (fullFactor false 25 20 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk25_0_20,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power25 j i k) (mpower0_20 j i k) (quadraturePoint j.val (16*i.val+k.val)) 25 20 (power25_contains j i k) (mpower0_20_contains j i k)
noncomputable def ha25_0_20 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨853843,853844⟩,⟨492966,492967⟩⟩,⟨⟨516913348073,516913348074⟩,⟨895320181973,895320181974⟩⟩,⟨⟨(-1),1⟩,⟨3437739179098606,3437739179098608⟩⟩,⟨⟨(-542022930869484434),(-542022930869484433)⟩,⟨938811255133340262,938811255133340263⟩⟩,⟨⟨(-81428896189552855194),(-81428896189552855123)⟩,⟨47012995134852432569,47012995134852432638⟩⟩,⟨⟨(-3604730797462500934619),(-3604730797462500933208)⟩,⟨(-803),379⟩⟩]
lemma ha25_0_20_eq (j : Fin 7) : ha25_0_20 j = ((ha25_0_19 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 20 := by fin_cases j <;> decide +kernel
lemma ha25_0_20_contains (j : Fin 7) : (ha25_0_20 j).Contains (fullFactor false 25 20 ((j.val:ℝ)/6)) := by
  rw [ha25_0_20_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha25_0_19 j) false 25 19 j (ha25_0_19_contains j)
noncomputable def hk25_0_21 (j : Fin 6) (i k : Fin 16) : CBox := (power25 j i k).conj.mul (mpower0_21 j i k)
lemma hk25_0_21_contains (j : Fin 6) (i k : Fin 16) :
    (hk25_0_21 j i k).Contains (fullFactor false 25 21 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk25_0_21,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power25 j i k) (mpower0_21 j i k) (quadraturePoint j.val (16*i.val+k.val)) 25 21 (power25_contains j i k) (mpower0_21_contains j i k)
noncomputable def ha25_0_21 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-12292),(-12291)⟩,⟨21289,21290⟩⟩,⟨⟨(-44646528672),(-44646528671)⟩,⟨25776685346,25776685347⟩⟩,⟨⟨(-257142289286048),(-257142289286047)⟩,⟨(-1),1⟩⟩,⟨⟨(-93630556896327456),(-93630556896327455)⟩,⟨(-54057627228469228),(-54057627228469227)⟩⟩,⟨⟨(-5860939688051789416),(-5860939688051789406)⟩,⟨(-10151445319802585620),(-10151445319802585611)⟩⟩,⟨⟨(-57),121⟩,⟨(-539266466260812849051),(-539266466260812848837)⟩⟩]
lemma ha25_0_21_eq (j : Fin 7) : ha25_0_21 j = ((ha25_0_20 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 21 := by fin_cases j <;> decide +kernel
lemma ha25_0_21_contains (j : Fin 7) : (ha25_0_21 j).Contains (fullFactor false 25 21 ((j.val:ℝ)/6)) := by
  rw [ha25_0_21_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha25_0_20 j) false 25 20 j (ha25_0_20_contains j)
noncomputable def hk25_0_22 (j : Fin 6) (i k : Fin 16) : CBox := (power25 j i k).conj.mul (mpower0_22 j i k)
lemma hk25_0_22_contains (j : Fin 6) (i k : Fin 16) :
    (hk25_0_22 j i k).Contains (fullFactor false 25 22 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk25_0_22,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power25 j i k) (mpower0_22 j i k) (quadraturePoint j.val (16*i.val+k.val)) 25 22 (power25_contains j i k) (mpower0_22_contains j i k)
noncomputable def ha25_0_22 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-507),(-506)⟩,⟨(-293),(-292)⟩⟩,⟨⟨(-1226967354),(-1226967353)⟩,⟨(-2125169796),(-2125169795)⟩⟩,⟨⟨(-1),1⟩,⟨(-18359916521553),(-18359916521552)⟩⟩,⟨⟨5146274077922863,5146274077922864⟩,⟨(-8913608172637076),(-8913608172637075)⟩⟩,⟨⟨1208019168182208036,1208019168182208039⟩,⟨(-697450191936225611),(-697450191936225609)⟩⟩,⟨⟨77007071306013533783,77007071306013533815⟩,⟨(-9),18⟩⟩]
lemma ha25_0_22_eq (j : Fin 7) : ha25_0_22 j = ((ha25_0_21 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 22 := by fin_cases j <;> decide +kernel
lemma ha25_0_22_contains (j : Fin 7) : (ha25_0_22 j).Contains (fullFactor false 25 22 ((j.val:ℝ)/6)) := by
  rw [ha25_0_22_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha25_0_21 j) false 25 21 j (ha25_0_21_contains j)
noncomputable def hk25_0_23 (j : Fin 6) (i k : Fin 16) : CBox := (power25 j i k).conj.mul (mpower0_23 j i k)
lemma hk25_0_23_contains (j : Fin 6) (i k : Fin 16) :
    (hk25_0_23 j i k).Contains (fullFactor false 25 23 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk25_0_23,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power25 j i k) (mpower0_23 j i k) (quadraturePoint j.val (16*i.val+k.val)) 25 23 (power25_contains j i k) (mpower0_23_contains j i k)
noncomputable def ha25_0_23 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨6,7⟩,⟨(-12),(-11)⟩⟩,⟨⟨96759678,96759679⟩,⟨(-55864227),(-55864226)⟩⟩,⟨⟨1253899540535,1253899540536⟩,⟨(-1),1⟩⟩,⟨⟨811679013105350,811679013105351⟩,⟨468623096711943,468623096711944⟩⟩,⟨⟨79387840551870928,79387840551870929⟩,⟨137503773339017306,137503773339017308⟩⟩,⟨⟨(-3),2⟩,⟨10518471716932064453,10518471716932064458⟩⟩]
lemma ha25_0_23_eq (j : Fin 7) : ha25_0_23 j = ((ha25_0_22 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 23 := by fin_cases j <;> decide +kernel
lemma ha25_0_23_contains (j : Fin 7) : (ha25_0_23 j).Contains (fullFactor false 25 23 ((j.val:ℝ)/6)) := by
  rw [ha25_0_23_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha25_0_22 j) false 25 22 j (ha25_0_22_contains j)
noncomputable def hk25_0_24 (j : Fin 6) (i k : Fin 16) : CBox := (power25 j i k).conj.mul (mpower0_24 j i k)
lemma hk25_0_24_contains (j : Fin 6) (i k : Fin 16) :
    (hk25_0_24 j i k).Contains (fullFactor false 25 24 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk25_0_24,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power25 j i k) (mpower0_24 j i k) (quadraturePoint j.val (16*i.val+k.val)) 25 24 (power25_contains j i k) (mpower0_24_contains j i k)
noncomputable def ha25_0_24 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨0,1⟩,⟨0,1⟩⟩,⟨⟨2437536,2437537⟩,⟨4221937,4221938⟩⟩,⟨⟨(-1),1⟩,⟨82067533018,82067533019⟩⟩,⟨⟨(-40895079942577),(-40895079942576)⟩,⟨70832356240132,70832356240133⟩⟩,⟨⟨(-14999334866761558),(-14999334866761557)⟩,⟨8659870022990124,8659870022990125⟩⟩,⟨⟨(-1376864728037741371),(-1376864728037741370)⟩,⟨(-1),1⟩⟩]
lemma ha25_0_24_eq (j : Fin 7) : ha25_0_24 j = ((ha25_0_23 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 24 := by fin_cases j <;> decide +kernel
lemma ha25_0_24_contains (j : Fin 7) : (ha25_0_24 j).Contains (fullFactor false 25 24 ((j.val:ℝ)/6)) := by
  rw [ha25_0_24_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha25_0_23 j) false 25 23 j (ha25_0_23_contains j)
noncomputable def hk25_0_25 (j : Fin 6) (i k : Fin 16) : CBox := (power25 j i k).conj.mul (mpower0_25 j i k)
lemma hk25_0_25_contains (j : Fin 6) (i k : Fin 16) :
    (hk25_0_25 j i k).Contains (fullFactor false 25 25 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk25_0_25,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power25 j i k) (mpower0_25 j i k) (quadraturePoint j.val (16*i.val+k.val)) 25 25 (power25_contains j i k) (mpower0_25_contains j i k)
noncomputable def ha25_0_25 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),0⟩,⟨0,1⟩⟩,⟨⟨(-176849),(-176848)⟩,⟨102103,102104⟩⟩,⟨⟨(-5156455177),(-5156455176)⟩,⟨(-1),1⟩⟩,⟨⟨(-5934037600013),(-5934037600012)⟩,⟨(-3426018205749),(-3426018205748)⟩⟩,⟨⟨(-906859468175609),(-906859468175608)⟩,⟨(-1570726674205046),(-1570726674205044)⟩⟩,⟨⟨(-1),1⟩,⟨(-173021924583611077),(-173021924583611076)⟩⟩]
lemma ha25_0_25_eq (j : Fin 7) : ha25_0_25 j = ((ha25_0_24 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 25 := by fin_cases j <;> decide +kernel
lemma ha25_0_25_contains (j : Fin 7) : (ha25_0_25 j).Contains (fullFactor false 25 25 ((j.val:ℝ)/6)) := by
  rw [ha25_0_25_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha25_0_24 j) false 25 24 j (ha25_0_24_contains j)
noncomputable def hk25_0_26 (j : Fin 6) (i k : Fin 16) : CBox := (power25 j i k).conj.mul (mpower0_26 j i k)
lemma hk25_0_26_contains (j : Fin 6) (i k : Fin 16) :
    (hk25_0_26 j i k).Contains (fullFactor false 25 26 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk25_0_26,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power25 j i k) (mpower0_26 j i k) (quadraturePoint j.val (16*i.val+k.val)) 25 26 (power25_contains j i k) (mpower0_26_contains j i k)
noncomputable def ha25_0_26 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),0⟩,⟨(-1),0⟩⟩,⟨⟨(-4113),(-4112)⟩,⟨(-7123),(-7122)⟩⟩,⟨⟨(-1),1⟩,⟨(-311528495),(-311528494)⟩⟩,⟨⟨275978298108,275978298109⟩,⟨(-478008434111),(-478008434110)⟩⟩,⟨⟨158159723733336,158159723733337⟩,⟨(-91313559072399),(-91313559072398)⟩⟩,⟨⟨20906323353147684,20906323353147685⟩,⟨(-1),1⟩⟩]
lemma ha25_0_26_eq (j : Fin 7) : ha25_0_26 j = ((ha25_0_25 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 26 := by fin_cases j <;> decide +kernel
lemma ha25_0_26_contains (j : Fin 7) : (ha25_0_26 j).Contains (fullFactor false 25 26 ((j.val:ℝ)/6)) := by
  rw [ha25_0_26_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha25_0_25 j) false 25 25 j (ha25_0_25_contains j)
noncomputable def hk25_0_27 (j : Fin 6) (i k : Fin 16) : CBox := (power25 j i k).conj.mul (mpower0_27 j i k)
lemma hk25_0_27_contains (j : Fin 6) (i k : Fin 16) :
    (hk25_0_27 j i k).Contains (fullFactor false 25 27 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk25_0_27,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power25 j i k) (mpower0_27 j i k) (quadraturePoint j.val (16*i.val+k.val)) 25 27 (power25_contains j i k) (mpower0_27_contains j i k)
noncomputable def ha25_0_27 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨0,1⟩,⟨(-1),0⟩⟩,⟨⟨276,277⟩,⟨(-160),(-159)⟩⟩,⟨⟨18123993,18123994⟩,⟨(-1),1⟩⟩,⟨⟨37079204566,37079204567⟩,⟨21407688737,21407688739⟩⟩,⟨⟨8854012541820,8854012541821⟩,⟨15335599573285,15335599573286⟩⟩,⟨⟨(-1),1⟩,⟨2432561179993388,2432561179993389⟩⟩]
lemma ha25_0_27_eq (j : Fin 7) : ha25_0_27 j = ((ha25_0_26 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 27 := by fin_cases j <;> decide +kernel
lemma ha25_0_27_contains (j : Fin 7) : (ha25_0_27 j).Contains (fullFactor false 25 27 ((j.val:ℝ)/6)) := by
  rw [ha25_0_27_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha25_0_26 j) false 25 26 j (ha25_0_26_contains j)
noncomputable def hk25_0_28 (j : Fin 6) (i k : Fin 16) : CBox := (power25 j i k).conj.mul (mpower0_28 j i k)
lemma hk25_0_28_contains (j : Fin 6) (i k : Fin 16) :
    (hk25_0_28 j i k).Contains (fullFactor false 25 28 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk25_0_28,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power25 j i k) (mpower0_28 j i k) (quadraturePoint j.val (16*i.val+k.val)) 25 28 (power25_contains j i k) (mpower0_28_contains j i k)
noncomputable def ha25_0_28 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨0,1⟩,⟨0,1⟩⟩,⟨⟨5,6⟩,⟨10,11⟩⟩,⟨⟨(-1),1⟩,⟨1016753,1016754⟩⟩,⟨⟨(-1601291374),(-1601291373)⟩,⟨2773518015,2773518016⟩⟩,⟨⟨(-1433875207079),(-1433875207078)⟩,⟨827848236790,827848236791⟩⟩,⟨⟨(-272932726159820),(-272932726159819)⟩,⟨(-1),1⟩⟩]
lemma ha25_0_28_eq (j : Fin 7) : ha25_0_28 j = ((ha25_0_27 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 28 := by fin_cases j <;> decide +kernel
lemma ha25_0_28_contains (j : Fin 7) : (ha25_0_28 j).Contains (fullFactor false 25 28 ((j.val:ℝ)/6)) := by
  rw [ha25_0_28_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha25_0_27 j) false 25 27 j (ha25_0_27_contains j)
noncomputable def hk25_0_29 (j : Fin 6) (i k : Fin 16) : CBox := (power25 j i k).conj.mul (mpower0_29 j i k)
lemma hk25_0_29_contains (j : Fin 6) (i k : Fin 16) :
    (hk25_0_29 j i k).Contains (fullFactor false 25 29 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk25_0_29,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power25 j i k) (mpower0_29 j i k) (quadraturePoint j.val (16*i.val+k.val)) 25 29 (power25_contains j i k) (mpower0_29_contains j i k)
noncomputable def ha25_0_29 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),0⟩,⟨0,1⟩⟩,⟨⟨(-1),0⟩,⟨0,1⟩⟩,⟨⟨(-55073),(-55072)⟩,⟨(-1),1⟩⟩,⟨⟨(-200304916),(-200304915)⟩,⟨(-115646097),(-115646096)⟩⟩,⟨⟨(-74734538477),(-74734538476)⟩,⟨(-129444017722),(-129444017721)⟩⟩,⟨⟨(-1),1⟩,⟨(-29567015428550),(-29567015428549)⟩⟩]
lemma ha25_0_29_eq (j : Fin 7) : ha25_0_29 j = ((ha25_0_28 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 29 := by fin_cases j <;> decide +kernel
lemma ha25_0_29_contains (j : Fin 7) : (ha25_0_29 j).Contains (fullFactor false 25 29 ((j.val:ℝ)/6)) := by
  rw [ha25_0_29_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha25_0_28 j) false 25 28 j (ha25_0_28_contains j)
noncomputable def hk25_0_30 (j : Fin 6) (i k : Fin 16) : CBox := (power25 j i k).conj.mul (mpower0_30 j i k)
lemma hk25_0_30_contains (j : Fin 6) (i k : Fin 16) :
    (hk25_0_30 j i k).Contains (fullFactor false 25 30 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk25_0_30,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power25 j i k) (mpower0_30 j i k) (quadraturePoint j.val (16*i.val+k.val)) 25 30 (power25_contains j i k) (mpower0_30_contains j i k)
noncomputable def ha25_0_30 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),0⟩,⟨(-1),0⟩⟩,⟨⟨(-1),0⟩,⟨(-1),0⟩⟩,⟨⟨(-1),1⟩,⟨(-2884),(-2883)⟩⟩,⟨⟨8073620,8073621⟩,⟨(-13983922),(-13983921)⟩⟩,⟨⟨11296121531,11296121532⟩,⟨(-6521818807),(-6521818806)⟩⟩,⟨⟨3096250615296,3096250615297⟩,⟨(-1),1⟩⟩]
lemma ha25_0_30_eq (j : Fin 7) : ha25_0_30 j = ((ha25_0_29 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 30 := by fin_cases j <;> decide +kernel
lemma ha25_0_30_contains (j : Fin 7) : (ha25_0_30 j).Contains (fullFactor false 25 30 ((j.val:ℝ)/6)) := by
  rw [ha25_0_30_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha25_0_29 j) false 25 29 j (ha25_0_29_contains j)
noncomputable def hk25_1_0 (j : Fin 6) (i k : Fin 16) : CBox := (kernel25_0 j i k).mul (mpower1_0 j i k)
lemma hk25_1_0_contains (j : Fin 6) (i k : Fin 16) :
    (hk25_1_0 j i k).Contains (fullFactor true 25 0 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk25_1_0,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel25_0 j i k) (mpower1_0 j i k) (quadraturePoint j.val (16*i.val+k.val)) 25 0 (kernel25_0_contains j i k) (mpower1_0_contains j i k)
noncomputable def ha25_1_0 : Fin 7 → CBox := ![⟨⟨(-3),3⟩,⟨(-3),3⟩⟩,⟨⟨(-4),3⟩,⟨(-2),4⟩⟩,⟨⟨(-2),2⟩,⟨(-4),0⟩⟩,⟨⟨(-2),2⟩,⟨(-3),0⟩⟩,⟨⟨10340074628317,10340074628320⟩,⟨(-51331061870575),(-51331061870572)⟩⟩,⟨⟨25007424357324989033834,25007424357324989135643⟩,⟨(-12960697545205626522481),(-12960697545205626421114)⟩⟩,⟨⟨4265780981286296484845899622,4265780981286296520258313301⟩,⟨(-8830170284357607012539510376),(-8830170284357606977137540426)⟩⟩]
lemma ha25_1_0_eq (j : Fin 7) : ha25_1_0 j = atomKernel25_0 j := by fin_cases j <;> decide +kernel
lemma ha25_1_0_contains (j : Fin 7) : (ha25_1_0 j).Contains (fullFactor true 25 0 ((j.val:ℝ)/6)) := by
  rw [ha25_1_0_eq]
  simpa only [fullFactor,ite_true] using atomKernel25_0_contains j
noncomputable def hk25_1_1 (j : Fin 6) (i k : Fin 16) : CBox := (kernel25_0 j i k).mul (mpower1_1 j i k)
lemma hk25_1_1_contains (j : Fin 6) (i k : Fin 16) :
    (hk25_1_1 j i k).Contains (fullFactor true 25 1 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk25_1_1,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel25_0 j i k) (mpower1_1 j i k) (quadraturePoint j.val (16*i.val+k.val)) 25 1 (kernel25_0_contains j i k) (mpower1_1_contains j i k)
noncomputable def ha25_1_1 : Fin 7 → CBox := ![⟨⟨(-28),28⟩,⟨(-28),28⟩⟩,⟨⟨(-31),46⟩,⟨(-42),31⟩⟩,⟨⟨(-31),10⟩,⟨(-11),30⟩⟩,⟨⟨(-21),6⟩,⟨(-11),19⟩⟩,⟨⟨(-252817850132719),(-252817850132700)⟩,⟨30013822947977,30013822947997⟩⟩,⟨⟨(-70561141275445737041550),(-70561141275445736555506)⟩,⟨(-93034447094966848163873),(-93034447094966847676205)⟩⟩,⟨⟨(-32686974824484623380691466343),(-32686974824484623246100477472)⟩,⟨(-13745775507675035894603552736),(-13745775507675035760026548446)⟩⟩]
lemma ha25_1_1_eq (j : Fin 7) : ha25_1_1 j = ((ha25_1_0 j).mul (piI.mul (atomPoints j).z)).scale 1 1 := by fin_cases j <;> decide +kernel
lemma ha25_1_1_contains (j : Fin 7) : (ha25_1_1 j).Contains (fullFactor true 25 1 ((j.val:ℝ)/6)) := by
  rw [ha25_1_1_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha25_1_0 j) true 25 0 j (ha25_1_0_contains j)
noncomputable def hk25_1_2 (j : Fin 6) (i k : Fin 16) : CBox := (kernel25_0 j i k).mul (mpower1_2 j i k)
lemma hk25_1_2_contains (j : Fin 6) (i k : Fin 16) :
    (hk25_1_2 j i k).Contains (fullFactor true 25 2 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk25_1_2,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel25_0 j i k) (mpower1_2 j i k) (quadraturePoint j.val (16*i.val+k.val)) 25 2 (kernel25_0_contains j i k) (mpower1_2_contains j i k)
noncomputable def ha25_1_2 : Fin 7 → CBox := ![⟨⟨(-130),130⟩,⟨(-130),130⟩⟩,⟨⟨(-255),177⟩,⟨(-205),219⟩⟩,⟨⟨(-53),154⟩,⟨(-100),107⟩⟩,⟨⟨(-37),79⟩,⟨(-43),70⟩⟩,⟨⟨260886349632600,260886349632662⟩,⟨561267047948791,561267047948851⟩⟩,⟨⟨(-165188345469972477744359),(-165188345469972476576378)⟩,⟨176893890314855271819936,176893890314855272985051⟩⟩,⟨⟨(-21749305191965104494679921231),(-21749305191965104238974319955)⟩,⟨60307303792541003787230446104,60307303792541004043063180637⟩⟩]
lemma ha25_1_2_eq (j : Fin 7) : ha25_1_2 j = ((ha25_1_1 j).mul (piI.mul (atomPoints j).z)).scale 1 2 := by fin_cases j <;> decide +kernel
lemma ha25_1_2_contains (j : Fin 7) : (ha25_1_2 j).Contains (fullFactor true 25 2 ((j.val:ℝ)/6)) := by
  rw [ha25_1_2_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha25_1_1 j) true 25 1 j (ha25_1_1_contains j)
noncomputable def hk25_1_3 (j : Fin 6) (i k : Fin 16) : CBox := (kernel25_0 j i k).mul (mpower1_3 j i k)
lemma hk25_1_3_contains (j : Fin 6) (i k : Fin 16) :
    (hk25_1_3 j i k).Contains (fullFactor true 25 3 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk25_1_3,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel25_0 j i k) (mpower1_3 j i k) (quadraturePoint j.val (16*i.val+k.val)) 25 3 (kernel25_0_contains j i k) (mpower1_3_contains j i k)
noncomputable def ha25_1_3 : Fin 7 → CBox := ![⟨⟨(-400),400⟩,⟨(-400),400⟩⟩,⟨⟨(-707),924⟩,⟨(-779),840⟩⟩,⟨⟨(-425),271⟩,⟨(-440),256⟩⟩,⟨⟨(-148),155⟩,⟨(-201),104⟩⟩,⟨⟨732570627845894,732570627846018⟩,⟨(-685270587233500),(-685270587233373)⟩⟩,⟨⟨279668964369348591191938,279668964369348593053648⟩,⟨183418678460675947148676,183418678460675949013573⟩⟩,⟨⟨73951728098799313987339584899,73951728098799314311519435334⟩,⟨22404400888518113079861395758,22404400888518113403756126697⟩⟩]
lemma ha25_1_3_eq (j : Fin 7) : ha25_1_3 j = ((ha25_1_2 j).mul (piI.mul (atomPoints j).z)).scale 1 3 := by fin_cases j <;> decide +kernel
lemma ha25_1_3_contains (j : Fin 7) : (ha25_1_3 j).Contains (fullFactor true 25 3 ((j.val:ℝ)/6)) := by
  rw [ha25_1_3_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha25_1_2 j) true 25 2 j (ha25_1_2_contains j)
noncomputable def hk25_1_4 (j : Fin 6) (i k : Fin 16) : CBox := (kernel25_0 j i k).mul (mpower1_4 j i k)
lemma hk25_1_4_contains (j : Fin 6) (i k : Fin 16) :
    (hk25_1_4 j i k).Contains (fullFactor true 25 4 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk25_1_4,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel25_0 j i k) (mpower1_4 j i k) (quadraturePoint j.val (16*i.val+k.val)) 25 4 (kernel25_0_contains j i k) (mpower1_4_contains j i k)
noncomputable def ha25_1_4 : Fin 7 → CBox := ![⟨⟨(-922),922⟩,⟨(-922),922⟩⟩,⟨⟨(-2495),2136⟩,⟨(-2469),2151⟩⟩,⟨⟨(-901),853⟩,⟨(-665),1089⟩⟩,⟨⟨(-367),238⟩,⟨(-272),332⟩⟩,⟨⟨(-1069012085092607),(-1069012085092412)⟩,⟨(-586509794379631),(-586509794379439)⟩⟩,⟨⟨138086835047750505029783,138086835047750507263004⟩,⟨(-317928302837332978858734),(-317928302837332976627948)⟩⟩,⟨⟨16754177742024521258665722084,16754177742024521566357314057⟩,⟨(-67812141316065853021566187166),(-67812141316065852713490164143)⟩⟩]
lemma ha25_1_4_eq (j : Fin 7) : ha25_1_4 j = ((ha25_1_3 j).mul (piI.mul (atomPoints j).z)).scale 1 4 := by fin_cases j <;> decide +kernel
lemma ha25_1_4_contains (j : Fin 7) : (ha25_1_4 j).Contains (fullFactor true 25 4 ((j.val:ℝ)/6)) := by
  rw [ha25_1_4_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha25_1_3 j) true 25 3 j (ha25_1_3_contains j)
noncomputable def hk25_1_5 (j : Fin 6) (i k : Fin 16) : CBox := (kernel25_0 j i k).mul (mpower1_5 j i k)
lemma hk25_1_5_contains (j : Fin 6) (i k : Fin 16) :
    (hk25_1_5 j i k).Contains (fullFactor true 25 5 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk25_1_5,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel25_0 j i k) (mpower1_5 j i k) (quadraturePoint j.val (16*i.val+k.val)) 25 5 (kernel25_0_contains j i k) (mpower1_5_contains j i k)
noncomputable def ha25_1_5 : Fin 7 → CBox := ![⟨⟨(-1700),1700⟩,⟨(-1700),1700⟩⟩,⟨⟨(-5111),5425⟩,⟨(-4887),5641⟩⟩,⟨⟨(-1525),2009⟩,⟨(-1951),1583⟩⟩,⟨⟨(-413),547⟩,⟨(-432),529⟩⟩,⟨⟨(-217946909698971),(-217946909698733)⟩,⟨1165519137536813,1165519137537052⟩⟩,⟨⟨(-279217297914728741462206),(-279217297914728739324059)⟩,⟨(-68041419016536676685572),(-68041419016536674546165)⟩⟩,⟨⟨(-49603479234880927410934724214),(-49603479234880927176727466788)⟩,⟨(-9553291772914737353007843843),(-9553291772914737119175058491)⟩⟩]
lemma ha25_1_5_eq (j : Fin 7) : ha25_1_5 j = ((ha25_1_4 j).mul (piI.mul (atomPoints j).z)).scale 1 5 := by fin_cases j <;> decide +kernel
lemma ha25_1_5_contains (j : Fin 7) : (ha25_1_5 j).Contains (fullFactor true 25 5 ((j.val:ℝ)/6)) := by
  rw [ha25_1_5_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha25_1_4 j) true 25 4 j (ha25_1_4_contains j)
noncomputable def hk25_1_6 (j : Fin 6) (i k : Fin 16) : CBox := (kernel25_0 j i k).mul (mpower1_6 j i k)
lemma hk25_1_6_contains (j : Fin 6) (i k : Fin 16) :
    (hk25_1_6 j i k).Contains (fullFactor true 25 6 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk25_1_6,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel25_0 j i k) (mpower1_6 j i k) (quadraturePoint j.val (16*i.val+k.val)) 25 6 (kernel25_0_contains j i k) (mpower1_6_contains j i k)
noncomputable def ha25_1_6 : Fin 7 → CBox := ![⟨⟨(-2612),2612⟩,⟨(-2612),2612⟩⟩,⟨⟨(-9960),10026⟩,⟨(-10570),9412⟩⟩,⟨⟨(-3324),2611⟩,⟨(-3024),2910⟩⟩,⟨⟨(-626),646⟩,⟨(-716),556⟩⟩,⟨⟨952492180075809,952492180076055⟩,⟨(-126544096993189),(-126544096992944)⟩⟩,⟨⟨(-13552531702071274740440),(-13552531702071273032518)⟩,⟨198101205864318969645098,198101205864318971352690⟩⟩,⟨⟨(-4197162280006775796660391078),(-4197162280006775648578121935)⟩,⟨30152218126794634822794761002,30152218126794634971163417058⟩⟩]
lemma ha25_1_6_eq (j : Fin 7) : ha25_1_6 j = ((ha25_1_5 j).mul (piI.mul (atomPoints j).z)).scale 1 6 := by fin_cases j <;> decide +kernel
lemma ha25_1_6_contains (j : Fin 7) : (ha25_1_6 j).Contains (fullFactor true 25 6 ((j.val:ℝ)/6)) := by
  rw [ha25_1_6_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha25_1_5 j) true 25 5 j (ha25_1_5_contains j)
noncomputable def hk25_1_7 (j : Fin 6) (i k : Fin 16) : CBox := (kernel25_0 j i k).mul (mpower1_7 j i k)
lemma hk25_1_7_contains (j : Fin 6) (i k : Fin 16) :
    (hk25_1_7 j i k).Contains (fullFactor true 25 7 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk25_1_7,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel25_0 j i k) (mpower1_7 j i k) (quadraturePoint j.val (16*i.val+k.val)) 25 7 (kernel25_0_contains j i k) (mpower1_7_contains j i k)
noncomputable def ha25_1_7 : Fin 7 → CBox := ![⟨⟨(-3439),3439⟩,⟨(-3439),3439⟩⟩,⟨⟨(-16595),15907⟩,⟨(-15633),16866⟩⟩,⟨⟨(-4062),4479⟩,⟨(-3968),4573⟩⟩,⟨⟨(-784),659⟩,⟨(-697),747⟩⟩,⟨⟨(-289713933681168),(-289713933680952)⟩,⟨(-601249166751071),(-601249166750855)⟩⟩,⟨⟨116978169696799790134198,116978169696799791302988⟩,⟨(-12022510436979685339007),(-12022510436979684170342)⟩⟩,⟨⟨15666937145186253230891626372,15666937145186253311451350737⟩,⟨1356325593276120189673749810,1356325593276120270053017692⟩⟩]
lemma ha25_1_7_eq (j : Fin 7) : ha25_1_7 j = ((ha25_1_6 j).mul (piI.mul (atomPoints j).z)).scale 1 7 := by fin_cases j <;> decide +kernel
lemma ha25_1_7_contains (j : Fin 7) : (ha25_1_7 j).Contains (fullFactor true 25 7 ((j.val:ℝ)/6)) := by
  rw [ha25_1_7_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha25_1_6 j) true 25 6 j (ha25_1_6_contains j)
noncomputable def hk25_1_8 (j : Fin 6) (i k : Fin 16) : CBox := (kernel25_0 j i k).mul (mpower1_8 j i k)
lemma hk25_1_8_contains (j : Fin 6) (i k : Fin 16) :
    (hk25_1_8 j i k).Contains (fullFactor true 25 8 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk25_1_8,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel25_0 j i k) (mpower1_8 j i k) (quadraturePoint j.val (16*i.val+k.val)) 25 8 (kernel25_0_contains j i k) (mpower1_8_contains j i k)
noncomputable def ha25_1_8 : Fin 7 → CBox := ![⟨⟨(-3962),3962⟩,⟨(-3962),3962⟩⟩,⟨⟨(-22509),23741⟩,⟨(-23555),22694⟩⟩,⟨⟨(-5312),5444⟩,⟨(-5698),5058⟩⟩,⟨⟨(-679),755⟩,⟨(-686),748⟩⟩,⟨⟨(-292343096855569),(-292343096855403)⟩,⟨281197756304022,281197756304189⟩⟩,⟨⟨(-16437978550148815494398),(-16437978550148814794654)⟩,⟨(-58677867324027633991312),(-58677867324027633291374)⟩⟩,⟨⟨244486712421613164350056881,244486712421613202525501010⟩,⟨(-7103549972786668007969613984),(-7103549972786667969697459298)⟩⟩]
lemma ha25_1_8_eq (j : Fin 7) : ha25_1_8 j = ((ha25_1_7 j).mul (piI.mul (atomPoints j).z)).scale 1 8 := by fin_cases j <;> decide +kernel
lemma ha25_1_8_contains (j : Fin 7) : (ha25_1_8 j).Contains (fullFactor true 25 8 ((j.val:ℝ)/6)) := by
  rw [ha25_1_8_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha25_1_7 j) true 25 7 j (ha25_1_7_contains j)
noncomputable def hk25_1_9 (j : Fin 6) (i k : Fin 16) : CBox := (kernel25_0 j i k).mul (mpower1_9 j i k)
lemma hk25_1_9_contains (j : Fin 6) (i k : Fin 16) :
    (hk25_1_9 j i k).Contains (fullFactor true 25 9 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk25_1_9,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel25_0 j i k) (mpower1_9 j i k) (quadraturePoint j.val (16*i.val+k.val)) 25 9 (kernel25_0_contains j i k) (mpower1_9_contains j i k)
noncomputable def ha25_1_9 : Fin 7 → CBox := ![⟨⟨(-4057),4057⟩,⟨(-4057),4057⟩⟩,⟨⟨(-29954),28549⟩,⟨(-29139),29363⟩⟩,⟨⟨(-6239),5801⟩,⟨(-5883),6157⟩⟩,⟨⟨(-627),639⟩,⟨(-664),602⟩⟩,⟨⟨193570510611875,193570510611989⟩,⟨102723012619895,102723012620009⟩⟩,⟨⟨(-25348789759298101560929),(-25348789759298101188362)⟩,⟨12053458463357661934324,12053458463357662306767⟩⟩,⟨⟨(-2855223556477147259068799363),(-2855223556477147242907479980)⟩,⟨50112168789207822075376704,50112168789207838191606664⟩⟩]
lemma ha25_1_9_eq (j : Fin 7) : ha25_1_9 j = ((ha25_1_8 j).mul (piI.mul (atomPoints j).z)).scale 1 9 := by fin_cases j <;> decide +kernel
lemma ha25_1_9_contains (j : Fin 7) : (ha25_1_9 j).Contains (fullFactor true 25 9 ((j.val:ℝ)/6)) := by
  rw [ha25_1_9_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha25_1_8 j) true 25 8 j (ha25_1_8_contains j)
noncomputable def hk25_1_10 (j : Fin 6) (i k : Fin 16) : CBox := (kernel25_0 j i k).mul (mpower1_10 j i k)
lemma hk25_1_10_contains (j : Fin 6) (i k : Fin 16) :
    (hk25_1_10 j i k).Contains (fullFactor true 25 10 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk25_1_10,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel25_0 j i k) (mpower1_10 j i k) (quadraturePoint j.val (16*i.val+k.val)) 25 10 (kernel25_0_contains j i k) (mpower1_10_contains j i k)
noncomputable def ha25_1_10 : Fin 7 → CBox := ![⟨⟨(-3739),3739⟩,⟨(-3739),3739⟩⟩,⟨⟨(-32720),33881⟩,⟨(-33125),33476⟩⟩,⟨⟨(-5886),6243⟩,⟨(-6020),6110⟩⟩,⟨⟨(-521),485⟩,⟨(-497),509⟩⟩,⟨⟨18125088549951,18125088550022⟩,⟨(-104995564817822),(-104995564817751)⟩⟩,⟨⟨6709522642049826115681,6709522642049826294098⟩,⟨9506799887446045577094,9506799887446045755567⟩⟩,⟨⟨71709124999040651499629688,71709124999040657622937064⟩,⟨1030087687847850492075730587,1030087687847850498217529816⟩⟩]
lemma ha25_1_10_eq (j : Fin 7) : ha25_1_10 j = ((ha25_1_9 j).mul (piI.mul (atomPoints j).z)).scale 1 10 := by fin_cases j <;> decide +kernel
lemma ha25_1_10_contains (j : Fin 7) : (ha25_1_10 j).Contains (fullFactor true 25 10 ((j.val:ℝ)/6)) := by
  rw [ha25_1_10_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha25_1_9 j) true 25 9 j (ha25_1_9_contains j)
noncomputable def hk25_1_11 (j : Fin 6) (i k : Fin 16) : CBox := (kernel25_0 j i k).mul (mpower1_11 j i k)
lemma hk25_1_11_contains (j : Fin 6) (i k : Fin 16) :
    (hk25_1_11 j i k).Contains (fullFactor true 25 11 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk25_1_11,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel25_0 j i k) (mpower1_11 j i k) (quadraturePoint j.val (16*i.val+k.val)) 25 11 (kernel25_0_contains j i k) (mpower1_11_contains j i k)
noncomputable def ha25_1_11 : Fin 7 → CBox := ![⟨⟨(-3133),3133⟩,⟨(-3133),3133⟩⟩,⟨⟨(-34809),34119⟩,⟨(-34782),34145⟩⟩,⟨⟨(-5613),5496⟩,⟨(-5658),5451⟩⟩,⟨⟨(-356),371⟩,⟨(-357),370⟩⟩,⟨⟨(-46594940462897),(-46594940462857)⟩,⟨6851635796179,6851635796219⟩⟩,⟨⟨3101140120536544640988,3101140120536544718708⟩,⟨(-3100552119676879333236),(-3100552119676879255536)⟩⟩,⟨⟨336928036359550851459564795,336928036359550853581371510⟩,⟨(-41124230695144795050846040),(-41124230695144792935743444)⟩⟩]
lemma ha25_1_11_eq (j : Fin 7) : ha25_1_11 j = ((ha25_1_10 j).mul (piI.mul (atomPoints j).z)).scale 1 11 := by fin_cases j <;> decide +kernel
lemma ha25_1_11_contains (j : Fin 7) : (ha25_1_11 j).Contains (fullFactor true 25 11 ((j.val:ℝ)/6)) := by
  rw [ha25_1_11_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha25_1_10 j) true 25 10 j (ha25_1_10_contains j)
noncomputable def hk25_1_12 (j : Fin 6) (i k : Fin 16) : CBox := (kernel25_0 j i k).mul (mpower1_12 j i k)
lemma hk25_1_12_contains (j : Fin 6) (i k : Fin 16) :
    (hk25_1_12 j i k).Contains (fullFactor true 25 12 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk25_1_12,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel25_0 j i k) (mpower1_12 j i k) (quadraturePoint j.val (16*i.val+k.val)) 25 12 (kernel25_0_contains j i k) (mpower1_12_contains j i k)
noncomputable def ha25_1_12 : Fin 7 → CBox := ![⟨⟨(-2406),2406⟩,⟨(-2406),2406⟩⟩,⟨⟨(-32574),32817⟩,⟨(-32385),33006⟩⟩,⟨⟨(-4684),4643⟩,⟨(-4596),4731⟩⟩,⟨⟨(-240),242⟩,⟨(-246),236⟩⟩,⟨⟨8521868935341,8521868935363⟩,⟨17073787583910,17073787583932⟩⟩,⟨⟨(-1237568491587701306373),(-1237568491587701275354)⟩,⟨(-873778414476682069232),(-873778414476682038208)⟩⟩,⟨⟨(-17647231275364937624514087),(-17647231275364936954782137)⟩,⟨(-100744489808592621676157539),(-100744489808592621004244494)⟩⟩]
lemma ha25_1_12_eq (j : Fin 7) : ha25_1_12 j = ((ha25_1_11 j).mul (piI.mul (atomPoints j).z)).scale 1 12 := by fin_cases j <;> decide +kernel
lemma ha25_1_12_contains (j : Fin 7) : (ha25_1_12 j).Contains (fullFactor true 25 12 ((j.val:ℝ)/6)) := by
  rw [ha25_1_12_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha25_1_11 j) true 25 11 j (ha25_1_11_contains j)
noncomputable def hk25_1_13 (j : Fin 6) (i k : Fin 16) : CBox := (kernel25_0 j i k).mul (mpower1_13 j i k)
lemma hk25_1_13_contains (j : Fin 6) (i k : Fin 16) :
    (hk25_1_13 j i k).Contains (fullFactor true 25 13 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk25_1_13,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel25_0 j i k) (mpower1_13 j i k) (quadraturePoint j.val (16*i.val+k.val)) 25 13 (kernel25_0_contains j i k) (mpower1_13_contains j i k)
noncomputable def ha25_1_13 : Fin 7 → CBox := ![⟨⟨(-1706),1706⟩,⟨(-1706),1706⟩⟩,⟨⟨(-28615),28649⟩,⟨(-28850),28414⟩⟩,⟨⟨(-3580),3649⟩,⟨(-3632),3597⟩⟩,⟨⟨(-150),145⟩,⟨(-147),148⟩⟩,⟨⟨5074388082163,5074388082174⟩,⟨(-5018755128165),(-5018755128154)⟩⟩,⟨⟨(-207539828682312096036),(-207539828682312084604)⟩,⟨436249245738152118720,436249245738152130151⟩⟩,⟨⟨(-27729022779975267569166961),(-27729022779975267372765280)⟩,⟨6357057107219053486051818,6357057107219053681809506⟩⟩]
lemma ha25_1_13_eq (j : Fin 7) : ha25_1_13 j = ((ha25_1_12 j).mul (piI.mul (atomPoints j).z)).scale 1 13 := by fin_cases j <;> decide +kernel
lemma ha25_1_13_contains (j : Fin 7) : (ha25_1_13 j).Contains (fullFactor true 25 13 ((j.val:ℝ)/6)) := by
  rw [ha25_1_13_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha25_1_12 j) true 25 12 j (ha25_1_12_contains j)
noncomputable def hk25_1_14 (j : Fin 6) (i k : Fin 16) : CBox := (kernel25_0 j i k).mul (mpower1_14 j i k)
lemma hk25_1_14_contains (j : Fin 6) (i k : Fin 16) :
    (hk25_1_14 j i k).Contains (fullFactor true 25 14 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk25_1_14,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel25_0 j i k) (mpower1_14 j i k) (quadraturePoint j.val (16*i.val+k.val)) 25 14 (kernel25_0_contains j i k) (mpower1_14_contains j i k)
noncomputable def ha25_1_14 : Fin 7 → CBox := ![⟨⟨(-1123),1123⟩,⟨(-1123),1123⟩⟩,⟨⟨(-23350),23215⟩,⟨(-23168),23397⟩⟩,⟨⟨(-2620),2583⟩,⟨(-2608),2595⟩⟩,⟨⟨(-83),85⟩,⟨(-83),85⟩⟩,⟨⟨(-2205435801041),(-2205435801035)⟩,⟨(-1131315366539),(-1131315366533)⟩⟩,⟨⟨137741333009233024631,137741333009233028544⟩,⟨38614935626199733157,38614935626199737069⟩⟩,⟨⟨2011590739560218877279301,2011590739560218930411785⟩,⟨7066895524930774814545945,7066895524930774867852531⟩⟩]
lemma ha25_1_14_eq (j : Fin 7) : ha25_1_14 j = ((ha25_1_13 j).mul (piI.mul (atomPoints j).z)).scale 1 14 := by fin_cases j <;> decide +kernel
lemma ha25_1_14_contains (j : Fin 7) : (ha25_1_14 j).Contains (fullFactor true 25 14 ((j.val:ℝ)/6)) := by
  rw [ha25_1_14_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha25_1_13 j) true 25 13 j (ha25_1_13_contains j)
noncomputable def hk25_1_15 (j : Fin 6) (i k : Fin 16) : CBox := (kernel25_0 j i k).mul (mpower1_15 j i k)
lemma hk25_1_15_contains (j : Fin 6) (i k : Fin 16) :
    (hk25_1_15 j i k).Contains (fullFactor true 25 15 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk25_1_15,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel25_0 j i k) (mpower1_15 j i k) (quadraturePoint j.val (16*i.val+k.val)) 25 15 (kernel25_0_contains j i k) (mpower1_15_contains j i k)
noncomputable def ha25_1_15 : Fin 7 → CBox := ![⟨⟨(-690),690⟩,⟨(-690),690⟩⟩,⟨⟨(-17608),17733⟩,⟨(-17712),17629⟩⟩,⟨⟨(-1744),1751⟩,⟨(-1739),1756⟩⟩,⟨⟨(-45),45⟩,⟨(-45),44⟩⟩,⟨⟨(-125642892723),(-125642892720)⟩,⟨793562374613,793562374616⟩⟩,⟨⟨4049435259578303484,4049435259578304735⟩,⟨(-39327387716239953010),(-39327387716239951760)⟩⟩,⟨⟨1676068040839744234466085,1676068040839744247969471⟩,⟨(-572725414314307775335459),(-572725414314307761875479)⟩⟩]
lemma ha25_1_15_eq (j : Fin 7) : ha25_1_15 j = ((ha25_1_14 j).mul (piI.mul (atomPoints j).z)).scale 1 15 := by fin_cases j <;> decide +kernel
lemma ha25_1_15_contains (j : Fin 7) : (ha25_1_15 j).Contains (fullFactor true 25 15 ((j.val:ℝ)/6)) := by
  rw [ha25_1_15_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha25_1_14 j) true 25 14 j (ha25_1_14_contains j)
noncomputable def hk25_1_16 (j : Fin 6) (i k : Fin 16) : CBox := (kernel25_0 j i k).mul (mpower1_16 j i k)
lemma hk25_1_16_contains (j : Fin 6) (i k : Fin 16) :
    (hk25_1_16 j i k).Contains (fullFactor true 25 16 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk25_1_16,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel25_0 j i k) (mpower1_16 j i k) (quadraturePoint j.val (16*i.val+k.val)) 25 16 (kernel25_0_contains j i k) (mpower1_16_contains j i k)
noncomputable def ha25_1_16 : Fin 7 → CBox := ![⟨⟨(-398),398⟩,⟨(-398),398⟩⟩,⟨⟨(-12613),12534⟩,⟨(-12568),12579⟩⟩,⟨⟨(-1099),1102⟩,⟨(-1104),1097⟩⟩,⟨⟨(-23),23⟩,⟨(-23),23⟩⟩,⟨⟨241040210382,241040210384⟩,⟨(-38878816312),(-38878816310)⟩⟩,⟨⟨(-10219753680707307939),(-10219753680707307564)⟩,⟨697208464868361140,697208464868361515⟩⟩,⟨⟨(-148927956352225314415830),(-148927956352225311219110)⟩,⟨(-371548922873836931325925),(-371548922873836928119167)⟩⟩]
lemma ha25_1_16_eq (j : Fin 7) : ha25_1_16 j = ((ha25_1_15 j).mul (piI.mul (atomPoints j).z)).scale 1 16 := by fin_cases j <;> decide +kernel
lemma ha25_1_16_contains (j : Fin 7) : (ha25_1_16 j).Contains (fullFactor true 25 16 ((j.val:ℝ)/6)) := by
  rw [ha25_1_16_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha25_1_15 j) true 25 15 j (ha25_1_15_contains j)
noncomputable def hk25_1_17 (j : Fin 6) (i k : Fin 16) : CBox := (kernel25_0 j i k).mul (mpower1_17 j i k)
lemma hk25_1_17_contains (j : Fin 6) (i k : Fin 16) :
    (hk25_1_17 j i k).Contains (fullFactor true 25 17 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk25_1_17,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel25_0 j i k) (mpower1_17 j i k) (quadraturePoint j.val (16*i.val+k.val)) 25 17 (kernel25_0_contains j i k) (mpower1_17_contains j i k)
noncomputable def ha25_1_17 : Fin 7 → CBox := ![⟨⟨(-216),216⟩,⟨(-216),216⟩⟩,⟨⟨(-8401),8439⟩,⟨(-8414),8427⟩⟩,⟨⟨(-654),651⟩,⟨(-652),653⟩⟩,⟨⟨(-11),11⟩,⟨(-11),11⟩⟩,⟨⟨(-32051855906),(-32051855905)⟩,⟨(-62040464858),(-62040464856)⟩⟩,⟨⟨590948645534448402,590948645534448509⟩,⟨2427039517196943610,2427039517196943717⟩⟩,⟨⟨(-77276949014398349291829),(-77276949014398348575105)⟩,⟨35738218570038813539736,35738218570038814254297⟩⟩]
lemma ha25_1_17_eq (j : Fin 7) : ha25_1_17 j = ((ha25_1_16 j).mul (piI.mul (atomPoints j).z)).scale 1 17 := by fin_cases j <;> decide +kernel
lemma ha25_1_17_contains (j : Fin 7) : (ha25_1_17 j).Contains (fullFactor true 25 17 ((j.val:ℝ)/6)) := by
  rw [ha25_1_17_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha25_1_16 j) true 25 16 j (ha25_1_16_contains j)
noncomputable def hk25_1_18 (j : Fin 6) (i k : Fin 16) : CBox := (kernel25_0 j i k).mul (mpower1_18 j i k)
lemma hk25_1_18_contains (j : Fin 6) (i k : Fin 16) :
    (hk25_1_18 j i k).Contains (fullFactor true 25 18 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk25_1_18,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel25_0 j i k) (mpower1_18 j i k) (quadraturePoint j.val (16*i.val+k.val)) 25 18 (kernel25_0_contains j i k) (mpower1_18_contains j i k)
noncomputable def ha25_1_18 : Fin 7 → CBox := ![⟨⟨(-111),111⟩,⟨(-111),111⟩⟩,⟨⟨(-5333),5319⟩,⟨(-5333),5319⟩⟩,⟨⟨(-365),366⟩,⟨(-365),366⟩⟩,⟨⟨(-5),5⟩,⟨(-5),5⟩⟩,⟨⟨(-13225349478),(-13225349477)⟩,⟨13449591499,13449591500⟩⟩,⟨⟨527720378730931689,527720378730931719⟩,⟨(-229087573199306733),(-229087573199306704)⟩⟩,⟨⟨7975677207434517189944,7975677207434517340798⟩,⟨15129910550449668669527,15129910550449668820817⟩⟩]
lemma ha25_1_18_eq (j : Fin 7) : ha25_1_18 j = ((ha25_1_17 j).mul (piI.mul (atomPoints j).z)).scale 1 18 := by fin_cases j <;> decide +kernel
lemma ha25_1_18_contains (j : Fin 7) : (ha25_1_18 j).Contains (fullFactor true 25 18 ((j.val:ℝ)/6)) := by
  rw [ha25_1_18_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha25_1_17 j) true 25 17 j (ha25_1_17_contains j)
noncomputable def hk25_1_19 (j : Fin 6) (i k : Fin 16) : CBox := (kernel25_0 j i k).mul (mpower1_19 j i k)
lemma hk25_1_19_contains (j : Fin 6) (i k : Fin 16) :
    (hk25_1_19 j i k).Contains (fullFactor true 25 19 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk25_1_19,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel25_0 j i k) (mpower1_19 j i k) (quadraturePoint j.val (16*i.val+k.val)) 25 19 (kernel25_0_contains j i k) (mpower1_19_contains j i k)
noncomputable def ha25_1_19 : Fin 7 → CBox := ![⟨⟨(-54),54⟩,⟨(-54),54⟩⟩,⟨⟨(-3190),3193⟩,⟨(-3187),3196⟩⟩,⟨⟨(-194),194⟩,⟨(-195),194⟩⟩,⟨⟨(-3),3⟩,⟨(-3),3⟩⟩,⟨⟨4325162428,4325162429⟩,⟨2143160336,2143160337⟩⟩,⟨⟨(-68819298744275403),(-68819298744275394)⟩,⟨(-104976128469875914),(-104976128469875906)⟩⟩,⟨⟨2796677963146087861346,2796677963146087891601⟩,⟨(-1665335374814732796860),(-1665335374814732766688)⟩⟩]
lemma ha25_1_19_eq (j : Fin 7) : ha25_1_19 j = ((ha25_1_18 j).mul (piI.mul (atomPoints j).z)).scale 1 19 := by fin_cases j <;> decide +kernel
lemma ha25_1_19_contains (j : Fin 7) : (ha25_1_19 j).Contains (fullFactor true 25 19 ((j.val:ℝ)/6)) := by
  rw [ha25_1_19_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha25_1_18 j) true 25 18 j (ha25_1_18_contains j)
noncomputable def hk25_1_20 (j : Fin 6) (i k : Fin 16) : CBox := (kernel25_0 j i k).mul (mpower1_20 j i k)
lemma hk25_1_20_contains (j : Fin 6) (i k : Fin 16) :
    (hk25_1_20 j i k).Contains (fullFactor true 25 20 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk25_1_20,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel25_0 j i k) (mpower1_20 j i k) (quadraturePoint j.val (16*i.val+k.val)) 25 20 (kernel25_0_contains j i k) (mpower1_20_contains j i k)
noncomputable def ha25_1_20 : Fin 7 → CBox := ![⟨⟨(-25),25⟩,⟨(-25),25⟩⟩,⟨⟨(-1817),1817⟩,⟨(-1819),1815⟩⟩,⟨⟨(-98),98⟩,⟨(-98),98⟩⟩,⟨⟨(-2),2⟩,⟨(-2),2⟩⟩,⟨⟨167360739,167360740⟩,⟨(-1161492778),(-1161492777)⟩⟩,⟨⟨(-19019439151102675),(-19019439151102672)⟩,⟨17754121229023339,17754121229023343⟩⟩,⟨⟨(-326935550134593826382),(-326935550134593820648)⟩,⟨(-489308566882390542433),(-489308566882390536684)⟩⟩]
lemma ha25_1_20_eq (j : Fin 7) : ha25_1_20 j = ((ha25_1_19 j).mul (piI.mul (atomPoints j).z)).scale 1 20 := by fin_cases j <;> decide +kernel
lemma ha25_1_20_contains (j : Fin 7) : (ha25_1_20 j).Contains (fullFactor true 25 20 ((j.val:ℝ)/6)) := by
  rw [ha25_1_20_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha25_1_19 j) true 25 19 j (ha25_1_19_contains j)
noncomputable def hk25_1_21 (j : Fin 6) (i k : Fin 16) : CBox := (kernel25_0 j i k).mul (mpower1_21 j i k)
lemma hk25_1_21_contains (j : Fin 6) (i k : Fin 16) :
    (hk25_1_21 j i k).Contains (fullFactor true 25 21 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk25_1_21,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel25_0 j i k) (mpower1_21 j i k) (quadraturePoint j.val (16*i.val+k.val)) 25 21 (kernel25_0_contains j i k) (mpower1_21_contains j i k)
noncomputable def ha25_1_21 : Fin 7 → CBox := ![⟨⟨(-11),11⟩,⟨(-11),11⟩⟩,⟨⟨(-986),985⟩,⟨(-985),986⟩⟩,⟨⟨(-48),48⟩,⟨(-48),48⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-267604537),(-267604536)⟩,⟨46993846,46993847⟩⟩,⟨⟨4091729900917561,4091729900917563⟩,⟨3104558209922431,3104558209922433⟩⟩,⟨⟨(-81215056720649091311),(-81215056720649090270)⟩,⟨60592947391959683998,60592947391959685037⟩⟩]
lemma ha25_1_21_eq (j : Fin 7) : ha25_1_21 j = ((ha25_1_20 j).mul (piI.mul (atomPoints j).z)).scale 1 21 := by fin_cases j <;> decide +kernel
lemma ha25_1_21_contains (j : Fin 7) : (ha25_1_21 j).Contains (fullFactor true 25 21 ((j.val:ℝ)/6)) := by
  rw [ha25_1_21_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha25_1_20 j) true 25 20 j (ha25_1_20_contains j)
noncomputable def hk25_1_22 (j : Fin 6) (i k : Fin 16) : CBox := (kernel25_0 j i k).mul (mpower1_22 j i k)
lemma hk25_1_22_contains (j : Fin 6) (i k : Fin 16) :
    (hk25_1_22 j i k).Contains (fullFactor true 25 22 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk25_1_22,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel25_0 j i k) (mpower1_22 j i k) (quadraturePoint j.val (16*i.val+k.val)) 25 22 (kernel25_0_contains j i k) (mpower1_22_contains j i k)
noncomputable def ha25_1_22 : Fin 7 → CBox := ![⟨⟨(-5),5⟩,⟨(-5),5⟩⟩,⟨⟨(-510),511⟩,⟨(-511),510⟩⟩,⟨⟨(-22),22⟩,⟨(-22),22⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨28301241,28301243⟩,⟨52959892,52959893⟩⟩,⟨⟨445509698946538,445509698946540⟩,⟨(-859203815443372),(-859203815443371)⟩⟩,⟨⟨10638760653854011578,10638760653854011759⟩,⟨12813270162925862671,12813270162925862852⟩⟩]
lemma ha25_1_22_eq (j : Fin 7) : ha25_1_22 j = ((ha25_1_21 j).mul (piI.mul (atomPoints j).z)).scale 1 22 := by fin_cases j <;> decide +kernel
lemma ha25_1_22_contains (j : Fin 7) : (ha25_1_22 j).Contains (fullFactor true 25 22 ((j.val:ℝ)/6)) := by
  rw [ha25_1_22_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha25_1_21 j) true 25 21 j (ha25_1_21_contains j)
noncomputable def hk25_1_23 (j : Fin 6) (i k : Fin 16) : CBox := (kernel25_0 j i k).mul (mpower1_23 j i k)
lemma hk25_1_23_contains (j : Fin 6) (i k : Fin 16) :
    (hk25_1_23 j i k).Contains (fullFactor true 25 23 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk25_1_23,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel25_0 j i k) (mpower1_23 j i k) (quadraturePoint j.val (16*i.val+k.val)) 25 23 (kernel25_0_contains j i k) (mpower1_23_contains j i k)
noncomputable def ha25_1_23 : Fin 7 → CBox := ![⟨⟨(-3),3⟩,⟨(-3),3⟩⟩,⟨⟨(-253),253⟩,⟨(-253),253⟩⟩,⟨⟨(-10),10⟩,⟨(-10),10⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨8773376,8773377⟩,⟨(-9174111),(-9174110)⟩⟩,⟨⟨(-166255507325723),(-166255507325722)⟩,⟨(-52821627528463),(-52821627528462)⟩⟩,⟨⟨1924842453373807696,1924842453373807727⟩,⟨(-1774905758864966824),(-1774905758864966793)⟩⟩]
lemma ha25_1_23_eq (j : Fin 7) : ha25_1_23 j = ((ha25_1_22 j).mul (piI.mul (atomPoints j).z)).scale 1 23 := by fin_cases j <;> decide +kernel
lemma ha25_1_23_contains (j : Fin 7) : (ha25_1_23 j).Contains (fullFactor true 25 23 ((j.val:ℝ)/6)) := by
  rw [ha25_1_23_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha25_1_22 j) true 25 22 j (ha25_1_22_contains j)
noncomputable def hk25_1_24 (j : Fin 6) (i k : Fin 16) : CBox := (kernel25_0 j i k).mul (mpower1_24 j i k)
lemma hk25_1_24_contains (j : Fin 6) (i k : Fin 16) :
    (hk25_1_24 j i k).Contains (fullFactor true 25 24 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk25_1_24,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel25_0 j i k) (mpower1_24 j i k) (quadraturePoint j.val (16*i.val+k.val)) 25 24 (kernel25_0_contains j i k) (mpower1_24_contains j i k)
noncomputable def ha25_1_24 : Fin 7 → CBox := ![⟨⟨(-2),2⟩,⟨(-2),2⟩⟩,⟨⟨(-121),121⟩,⟨(-121),121⟩⟩,⟨⟨(-5),5⟩,⟨(-5),5⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-2319962),(-2319961)⟩,⟨(-1109620),(-1109618)⟩⟩,⟨⟨(-4112391435164),(-4112391435162)⟩,⟨29850229324399,29850229324400⟩⟩,⟨⟨(-282111043114363796),(-282111043114363790)⟩,⟨(-275724008831798844),(-275724008831798838)⟩⟩]
lemma ha25_1_24_eq (j : Fin 7) : ha25_1_24 j = ((ha25_1_23 j).mul (piI.mul (atomPoints j).z)).scale 1 24 := by fin_cases j <;> decide +kernel
lemma ha25_1_24_contains (j : Fin 7) : (ha25_1_24 j).Contains (fullFactor true 25 24 ((j.val:ℝ)/6)) := by
  rw [ha25_1_24_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha25_1_23 j) true 25 23 j (ha25_1_23_contains j)
noncomputable def hk25_1_25 (j : Fin 6) (i k : Fin 16) : CBox := (kernel25_0 j i k).mul (mpower1_25 j i k)
lemma hk25_1_25_contains (j : Fin 6) (i k : Fin 16) :
    (hk25_1_25 j i k).Contains (fullFactor true 25 25 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk25_1_25,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel25_0 j i k) (mpower1_25 j i k) (quadraturePoint j.val (16*i.val+k.val)) 25 25 (kernel25_0_contains j i k) (mpower1_25_contains j i k)
noncomputable def ha25_1_25 : Fin 7 → CBox := ![⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-56),56⟩,⟨(-56),56⟩⟩,⟨⟨(-3),3⟩,⟨(-3),3⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-64435),(-64434)⟩,⟨495986,495987⟩⟩,⟨⟨4993736064346,4993736064348⟩,⟨(-168933217242),(-168933217241)⟩⟩,⟨⟨(-37706945543723463),(-37706945543723461)⟩,⟨42819357775355523,42819357775355525⟩⟩]
lemma ha25_1_25_eq (j : Fin 7) : ha25_1_25 j = ((ha25_1_24 j).mul (piI.mul (atomPoints j).z)).scale 1 25 := by fin_cases j <;> decide +kernel
lemma ha25_1_25_contains (j : Fin 7) : (ha25_1_25 j).Contains (fullFactor true 25 25 ((j.val:ℝ)/6)) := by
  rw [ha25_1_25_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha25_1_24 j) true 25 24 j (ha25_1_24_contains j)
noncomputable def hk25_1_26 (j : Fin 6) (i k : Fin 16) : CBox := (kernel25_0 j i k).mul (mpower1_26 j i k)
lemma hk25_1_26_contains (j : Fin 6) (i k : Fin 16) :
    (hk25_1_26 j i k).Contains (fullFactor true 25 26 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk25_1_26,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel25_0 j i k) (mpower1_26 j i k) (quadraturePoint j.val (16*i.val+k.val)) 25 26 (kernel25_0_contains j i k) (mpower1_26_contains j i k)
noncomputable def ha25_1_26 : Fin 7 → CBox := ![⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-25),25⟩,⟨(-25),25⟩⟩,⟨⟨(-2),2⟩,⟨(-2),2⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨91888,91889⟩,⟨(-17459),(-17457)⟩⟩,⟨⟨(-161817525651),(-161817525649)⟩,⟨(-780073447887),(-780073447886)⟩⟩,⟨⟨6219314442978888,6219314442978889⟩,⟨4927708760340872,4927708760340874⟩⟩]
lemma ha25_1_26_eq (j : Fin 7) : ha25_1_26 j = ((ha25_1_25 j).mul (piI.mul (atomPoints j).z)).scale 1 26 := by fin_cases j <;> decide +kernel
lemma ha25_1_26_contains (j : Fin 7) : (ha25_1_26 j).Contains (fullFactor true 25 26 ((j.val:ℝ)/6)) := by
  rw [ha25_1_26_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha25_1_25 j) true 25 25 j (ha25_1_25_contains j)
noncomputable def hk25_1_27 (j : Fin 6) (i k : Fin 16) : CBox := (kernel25_0 j i k).mul (mpower1_27 j i k)
lemma hk25_1_27_contains (j : Fin 6) (i k : Fin 16) :
    (hk25_1_27 j i k).Contains (fullFactor true 25 27 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk25_1_27,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel25_0 j i k) (mpower1_27 j i k) (quadraturePoint j.val (16*i.val+k.val)) 25 27 (kernel25_0_contains j i k) (mpower1_27_contains j i k)
noncomputable def ha25_1_27 : Fin 7 → CBox := ![⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-11),11⟩,⟨(-11),11⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-8145),(-8144)⟩,⟨(-14744),(-14743)⟩⟩,⟨⟨(-113809706222),(-113809706221)⟩,⟨44832672410,44832672412⟩⟩,⟨⟨615787522655033,615787522655034⟩,⟨(-866051807310952),(-866051807310951)⟩⟩]
lemma ha25_1_27_eq (j : Fin 7) : ha25_1_27 j = ((ha25_1_26 j).mul (piI.mul (atomPoints j).z)).scale 1 27 := by fin_cases j <;> decide +kernel
lemma ha25_1_27_contains (j : Fin 7) : (ha25_1_27 j).Contains (fullFactor true 25 27 ((j.val:ℝ)/6)) := by
  rw [ha25_1_27_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha25_1_26 j) true 25 26 j (ha25_1_26_contains j)
noncomputable def hk25_1_28 (j : Fin 6) (i k : Fin 16) : CBox := (kernel25_0 j i k).mul (mpower1_28 j i k)
lemma hk25_1_28_contains (j : Fin 6) (i k : Fin 16) :
    (hk25_1_28 j i k).Contains (fullFactor true 25 28 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk25_1_28,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel25_0 j i k) (mpower1_28 j i k) (quadraturePoint j.val (16*i.val+k.val)) 25 28 (kernel25_0_contains j i k) (mpower1_28_contains j i k)
noncomputable def ha25_1_28 : Fin 7 → CBox := ![⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-5),5⟩,⟨(-5),5⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1993),(-1991)⟩,⟨2141,2142⟩⟩,⟨⟨9403981726,9403981727⟩,⟨15477516605,15477516606⟩⟩,⟨⟨(-115820146981043),(-115820146981042)⟩,⟨(-73607261641238),(-73607261641237)⟩⟩]
lemma ha25_1_28_eq (j : Fin 7) : ha25_1_28 j = ((ha25_1_27 j).mul (piI.mul (atomPoints j).z)).scale 1 28 := by fin_cases j <;> decide +kernel
lemma ha25_1_28_contains (j : Fin 7) : (ha25_1_28 j).Contains (fullFactor true 25 28 ((j.val:ℝ)/6)) := by
  rw [ha25_1_28_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha25_1_27 j) true 25 27 j (ha25_1_27_contains j)
noncomputable def hk25_1_29 (j : Fin 6) (i k : Fin 16) : CBox := (kernel25_0 j i k).mul (mpower1_29 j i k)
lemma hk25_1_29_contains (j : Fin 6) (i k : Fin 16) :
    (hk25_1_29 j i k).Contains (fullFactor true 25 29 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk25_1_29,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel25_0 j i k) (mpower1_29 j i k) (quadraturePoint j.val (16*i.val+k.val)) 25 29 (kernel25_0_contains j i k) (mpower1_29_contains j i k)
noncomputable def ha25_1_29 : Fin 7 → CBox := ![⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-2),2⟩,⟨(-2),2⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨445,446⟩,⟨205,206⟩⟩,⟨⟨1951964330,1951964331⟩,⟨(-1700653180),(-1700653179)⟩⟩,⟨⟨(-8415510377825),(-8415510377824)⟩,⟨14898312032474,14898312032475⟩⟩]
lemma ha25_1_29_eq (j : Fin 7) : ha25_1_29 j = ((ha25_1_28 j).mul (piI.mul (atomPoints j).z)).scale 1 29 := by fin_cases j <;> decide +kernel
lemma ha25_1_29_contains (j : Fin 7) : (ha25_1_29 j).Contains (fullFactor true 25 29 ((j.val:ℝ)/6)) := by
  rw [ha25_1_29_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha25_1_28 j) true 25 28 j (ha25_1_28_contains j)
noncomputable def hk25_1_30 (j : Fin 6) (i k : Fin 16) : CBox := (kernel25_0 j i k).mul (mpower1_30 j i k)
lemma hk25_1_30_contains (j : Fin 6) (i k : Fin 16) :
    (hk25_1_30 j i k).Contains (fullFactor true 25 30 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk25_1_30,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel25_0 j i k) (mpower1_30 j i k) (quadraturePoint j.val (16*i.val+k.val)) 25 30 (kernel25_0_contains j i k) (mpower1_30_contains j i k)
noncomputable def ha25_1_30 : Fin 7 → CBox := ![⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨9,10⟩,⟨(-80),(-78)⟩⟩,⟨⟨(-277415001),(-277415000)⟩,⟨(-225885785),(-225885784)⟩⟩,⟨⟨1845946709663,1845946709664⟩,⟨919704036103,919704036104⟩⟩]
lemma ha25_1_30_eq (j : Fin 7) : ha25_1_30 j = ((ha25_1_29 j).mul (piI.mul (atomPoints j).z)).scale 1 30 := by fin_cases j <;> decide +kernel
lemma ha25_1_30_contains (j : Fin 7) : (ha25_1_30 j).Contains (fullFactor true 25 30 ((j.val:ℝ)/6)) := by
  rw [ha25_1_30_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha25_1_29 j) true 25 29 j (ha25_1_29_contains j)
end SharpPlanar.CachedData

end OAI
