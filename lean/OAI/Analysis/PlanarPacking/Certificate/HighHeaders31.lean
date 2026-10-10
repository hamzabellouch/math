import OAI.Analysis.PlanarPacking.Certificate.Powers40
import OAI.Analysis.PlanarPacking.Certificate.KernelValues40
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
noncomputable def hk31_0_0 (j : Fin 6) (i k : Fin 16) : CBox := (power31 j i k).conj.mul (mpower0_0 j i k)
lemma hk31_0_0_contains (j : Fin 6) (i k : Fin 16) :
    (hk31_0_0 j i k).Contains (fullFactor false 31 0 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk31_0_0,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power31 j i k) (mpower0_0 j i k) (quadraturePoint j.val (16*i.val+k.val)) 31 0 (power31_contains j i k) (mpower0_0_contains j i k)
noncomputable def ha31_0_0 : Fin 7 → CBox := ![⟨⟨999999999999999999999999999629,1000000000000000000000000000495⟩,⟨(-495),495⟩⟩,⟨⟨(-866025403784438646859265180121),(-866025403784438646656005308407)⟩,⟨(-500000000000000000112642480794),(-499999999999999999908446715259)⟩⟩,⟨⟨499999999999999999700748754523,500000000000000000257072853273⟩,⟨866025403784438646497394466211,866025403784438647054403581409⟩⟩,⟨⟨(-64739364723),137794482981⟩,⟨(-1000000000000000000101266923852),(-999999999999999999898733076179)⟩⟩,⟨⟨(-500000000000000000803454492878),(-499999999999999999280902291575)⟩,⟨866025403784438645978345754771,866025403784438647500397174436⟩⟩,⟨⟨866025403784438645836046380502,866025403784438647752279226158⟩,⟨(-500000000000000000905144916009),(-499999999999999998989409103426)⟩⟩,⟨⟨(-1000000000000000000203149131365),(-999999999999999999796850868759)⟩,⟨(-276204249685),130094012921⟩⟩]
lemma ha31_0_0_eq (j : Fin 7) : ha31_0_0 j = ((atomPoints j).direct.powBin 7 31).conj := by fin_cases j <;> decide +kernel
lemma ha31_0_0_contains (j : Fin 7) : (ha31_0_0 j).Contains (fullFactor false 31 0 ((j.val:ℝ)/6)) := by
  rw [ha31_0_0_eq]
  simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @direct_factor_zero_full ((atomPoints j).direct.powBin 7 31) ((j.val:ℝ)/6) 31 (@direct_power_bin_contains (atomPoints j) ((j.val:ℝ)/6) (atomPoints_contains j) 31 (by norm_num))
noncomputable def hk31_0_1 (j : Fin 6) (i k : Fin 16) : CBox := (power31 j i k).conj.mul (mpower0_1 j i k)
lemma hk31_0_1_contains (j : Fin 6) (i k : Fin 16) :
    (hk31_0_1 j i k).Contains (fullFactor false 31 1 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk31_0_1,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power31 j i k) (mpower0_1 j i k) (quadraturePoint j.val (16*i.val+k.val)) 31 1 (power31_contains j i k) (mpower0_1_contains j i k)
noncomputable def ha31_0_1 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨261799387799149436490396145539,261799387799149436598146131692⟩,⟨(-453449841058554462699607079697),(-453449841058554462591737084061)⟩⟩,⟨⟨(-906899682117108925603562615365),(-906899682117108925017377282586)⟩,⟨523598775598298872763291495209,523598775598298873347539395762⟩⟩,⟨⟨1570796326794896619070930288036,1570796326794896619394069712013⟩,⟨(-101692356306),216447067720⟩⟩,⟨⟨(-1813799364234217852141212027662),(-1813799364234217848947661486029)⟩,⟨(-1047197551196597747839417821547),(-1047197551196597744647258614664)⟩⟩,⟨⟨1308996938995747180045945886281,1308996938995747185065497182142⟩,⟨2267249205292772310812037966859,2267249205292772315835940703962⟩⟩,⟨⟨(-408702395269),867721241701⟩,⟨(-3141592653589793239108211818680),(-3141592653589793237821788181710)⟩⟩]
lemma ha31_0_1_eq (j : Fin 7) : ha31_0_1 j = ((ha31_0_0 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 1 := by fin_cases j <;> decide +kernel
lemma ha31_0_1_contains (j : Fin 7) : (ha31_0_1 j).Contains (fullFactor false 31 1 ((j.val:ℝ)/6)) := by
  rw [ha31_0_1_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha31_0_0 j) false 31 0 j (ha31_0_0_contains j)
noncomputable def hk31_0_2 (j : Fin 6) (i k : Fin 16) : CBox := (power31 j i k).conj.mul (mpower0_2 j i k)
lemma hk31_0_2_contains (j : Fin 6) (i k : Fin 16) :
    (hk31_0_2 j i k).Contains (fullFactor false 31 2 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk31_0_2,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power31 j i k) (mpower0_2 j i k) (quadraturePoint j.val (16*i.val+k.val)) 31 2 (power31_contains j i k) (mpower0_2_contains j i k)
noncomputable def ha31_0_2 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨118712890786751174392971806063,118712890786751174421589979752⟩,⟨68538919452009434840352032838,68538919452009434868779079406⟩⟩,⟨⟨(-274155677808037739554309130949),(-274155677808037739247524980946)⟩,⟨(-474851563147004697793356520348),(-474851563147004697484919098359)⟩⟩,⟨⟨(-169997129461),79868989875⟩,⟨1233700550136169827227302206982,1233700550136169827485022307913⟩⟩,⟨⟨1096622711232150956069273590788,1096622711232150959415585553773⟩,⟨(-1899406252588018792151599487742),(-1899406252588018788801275183036)⟩⟩,⟨⟨(-2967822269668779363600060382316),(-2967822269668779357014340205942)⟩,⟨1713472986300235867859308578441,1713472986300235874435340013771⟩⟩,⟨⟨4934802200544679308406440286559,4934802200544679310442857773483⟩,⟨(-641988221241),1363013339146⟩⟩]
lemma ha31_0_2_eq (j : Fin 7) : ha31_0_2 j = ((ha31_0_1 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 2 := by fin_cases j <;> decide +kernel
lemma ha31_0_2_contains (j : Fin 7) : (ha31_0_2 j).Contains (fullFactor false 31 2 ((j.val:ℝ)/6)) := by
  rw [ha31_0_2_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha31_0_1 j) false 31 1 j (ha31_0_1_contains j)
noncomputable def hk31_0_3 (j : Fin 6) (i k : Fin 16) : CBox := (power31 j i k).conj.mul (mpower0_3 j i k)
lemma hk31_0_3_contains (j : Fin 6) (i k : Fin 16) :
    (hk31_0_3 j i k).Contains (fullFactor false 31 3 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk31_0_3,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power31 j i k) (mpower0_3 j i k) (quadraturePoint j.val (16*i.val+k.val)) 31 3 (power31_contains j i k) (mpower0_3_contains j i k)
noncomputable def ha31_0_3 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-11962298101967523218626305405),(-11962298101967523213626772634)⟩,⟨20719308087892496639786012953,20719308087892496644846778128⟩⟩,⟨⟨165754464703139973087930500808,165754464703139973196123084659⟩,⟨(-95698384815740185776653949966),(-95698384815740185669261462335)⟩⟩,⟨⟨(-645964097506246253725709292020),(-645964097506246253588711195141)⟩,⟨(-89010288842),41819305307⟩⟩,⟨⟨1326035717625119783908690033264,1326035717625119786251878541120⟩,⟨765587078525921484711233644691,765587078525921487049837046171⟩⟩,⟨⟨(-1495287262745940404698325769704),(-1495287262745940398954896109459)⟩,⟨(-2589913510986562083276472322933),(-2589913510986562077521103337542)⟩⟩,⟨⟨(-1427344231002),672288493181⟩,⟨5167712780049970028183191575788,5167712780049970030332172321978⟩⟩]
lemma ha31_0_3_eq (j : Fin 7) : ha31_0_3 j = ((ha31_0_2 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 3 := by fin_cases j <;> decide +kernel
lemma ha31_0_3_contains (j : Fin 7) : (ha31_0_3 j).Contains (fullFactor false 31 3 ((j.val:ℝ)/6)) := by
  rw [ha31_0_3_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha31_0_2 j) false 31 2 j (ha31_0_2_contains j)
noncomputable def hk31_0_4 (j : Fin 6) (i k : Fin 16) : CBox := (power31 j i k).conj.mul (mpower0_4 j i k)
lemma hk31_0_4_contains (j : Fin 6) (i k : Fin 16) :
    (hk31_0_4 j i k).Contains (fullFactor false 31 4 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk31_0_4,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power31 j i k) (mpower0_4 j i k) (quadraturePoint j.val (16*i.val+k.val)) 31 4 (power31_contains j i k) (mpower0_4_contains j i k)
noncomputable def ha31_0_4 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-2712151086516110563720565312),(-2712151086516110563049479653)⟩,⟨(-1565861159883012430222761401),(-1565861159883012429563339800)⟩⟩,⟨⟨25053778558128198862606199374,25053778558128198890801235545⟩,⟨43394417384257769000844072630,43394417384257769029306953569⟩⟩,⟨⟨(-16422402792),34954258690⟩,⟨(-253669507901048013664627752258),(-253669507901048013610021270297)⟩⟩,⟨⟨(-400860456930051182690865356132),(-400860456930051181465099500041)⟩,⟨694310678148124303597372954824,694310678148124304826473648065⟩⟩,⟨⟨1695094429072569100300997486440,1695094429072569104073273331925⟩,⟨(-978663224926882770440411853259),(-978663224926882766678230749160)⟩⟩,⟨⟨(-4058712126416768219047554587219),(-4058712126416768217346829774033)⟩,⟨(-1121033537565),528014147818⟩⟩]
lemma ha31_0_4_eq (j : Fin 7) : ha31_0_4 j = ((ha31_0_3 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 4 := by fin_cases j <;> decide +kernel
lemma ha31_0_4_contains (j : Fin 7) : (ha31_0_4 j).Contains (fullFactor false 31 4 ((j.val:ℝ)/6)) := by
  rw [ha31_0_4_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha31_0_3 j) false 31 3 j (ha31_0_3_contains j)
noncomputable def hk31_0_5 (j : Fin 6) (i k : Fin 16) : CBox := (power31 j i k).conj.mul (mpower0_5 j i k)
lemma hk31_0_5_contains (j : Fin 6) (i k : Fin 16) :
    (hk31_0_5 j i k).Contains (fullFactor false 31 5 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk31_0_5,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power31 j i k) (mpower0_5 j i k) (quadraturePoint j.val (16*i.val+k.val)) 31 5 (power31_contains j i k) (mpower0_5_contains j i k)
noncomputable def ha31_0_5 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨163976597214335483756333401,163976597214335483825909824⟩,⟨(-284015797627486289521882745),(-284015797627486289450702768)⟩⟩,⟨⟨(-9088505524079561266748128201),(-9088505524079561260757946745)⟩,⟨5247251110858735478022982143,5247251110858735483944839230⟩⟩,⟨⟨79692626246167045112100049511,79692626246167045129508851276⟩,⟨(-5159249997),10981204232⟩⟩,⟨⟨(-290832176770545960685715486502),(-290832176770545960169945244475)⟩,⟨(-167912035547479535669722961912),(-167912035547479535155740880166)⟩⟩,⟨⟨512426866294798385796662753378,512426866294798387768167278440⟩,⟨887549367585894653693108182664,887549367585894655671092353963⟩⟩,⟨⟨(-331761073556),704366145209⟩,⟨(-2550164039877345444404099582730),(-2550164039877345443327385242699)⟩⟩]
lemma ha31_0_5_eq (j : Fin 7) : ha31_0_5 j = ((ha31_0_4 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 5 := by fin_cases j <;> decide +kernel
lemma ha31_0_5_contains (j : Fin 7) : (ha31_0_5 j).Contains (fullFactor false 31 5 ((j.val:ℝ)/6)) := by
  rw [ha31_0_5_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha31_0_4 j) false 31 4 j (ha31_0_4_contains j)
noncomputable def hk31_0_6 (j : Fin 6) (i k : Fin 16) : CBox := (power31 j i k).conj.mul (mpower0_6 j i k)
lemma hk31_0_6_contains (j : Fin 6) (i k : Fin 16) :
    (hk31_0_6 j i k).Contains (fullFactor false 31 6 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk31_0_6,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power31 j i k) (mpower0_6 j i k) (quadraturePoint j.val (16*i.val+k.val)) 31 6 (power31_contains j i k) (mpower0_6_contains j i k)
noncomputable def ha31_0_6 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨24785053981387676523696509,24785053981387676529987028⟩,⟨14309657588033580843021994,14309657588033580849139232⟩⟩,⟨⟨(-915818085634149174609454721),(-915818085634149173572980540)⟩,⟨(-1586243454808811298276592321),(-1586243454808811297226059258)⟩⟩,⟨⟨(-2874872546),1350688491⟩,⟨20863480763352960870833527636,20863480763352960875457551804⟩⟩,⟨⟨58612357480585547059454372670,58612357480585547239054534054⟩,⟨(-101519581107763923141983380301),(-101519581107763922961622455293)⟩⟩,⟨⟨(-387266468459182446180382469245),(-387266468459182445316091353251)⟩,⟨223588399813024700261246363741,223588399813024701122189197231⟩⟩,⟨⟨1335262768854589495597306250395,1335262768854589496165322833905⟩,⟨(-173709691906),368805251205⟩⟩]
lemma ha31_0_6_eq (j : Fin 7) : ha31_0_6 j = ((ha31_0_5 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 6 := by fin_cases j <;> decide +kernel
lemma ha31_0_6_contains (j : Fin 7) : (ha31_0_6 j).Contains (fullFactor false 31 6 ((j.val:ℝ)/6)) := by
  rw [ha31_0_6_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha31_0_5 j) false 31 5 j (ha31_0_5_contains j)
noncomputable def hk31_0_7 (j : Fin 6) (i k : Fin 16) : CBox := (power31 j i k).conj.mul (mpower0_7 j i k)
lemma hk31_0_7_contains (j : Fin 6) (i k : Fin 16) :
    (hk31_0_7 j i k).Contains (fullFactor false 31 7 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk31_0_7,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power31 j i k) (mpower0_7 j i k) (quadraturePoint j.val (16*i.val+k.val)) 31 7 (power31_contains j i k) (mpower0_7_contains j i k)
noncomputable def ha31_0_7 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1070359884617898514361440),(-1070359884617898513900463)⟩,⟨1853917702541761442016049,1853917702541761442492481⟩⟩,⟨⟨237301465925345464534593072,237301465925345464692507806⟩,⟨(-137006065231091009877839892),(-137006065231091009722347612)⟩⟩,⟨⟨(-4681754135318688101236313090),(-4681754135318688100183782006)⟩,⟨(-645119891),303093789⟩⟩,⟨⟨30374587638444219442223030941,30374587638444219496283578828⟩,⟨17536776349579649229734987404,17536776349579649283527051325⟩⟩,⟨⟨(-83621865985773321567028502174),(-83621865985773321244770458738)⟩,⟨(-144837320511075112844076048102),(-144837320511075112520370895094)⟩⟩,⟨⟨(-165519409685),77960727422⟩,⟨599264529320792076762469703753,599264529320792077019302468548⟩⟩]
lemma ha31_0_7_eq (j : Fin 7) : ha31_0_7 j = ((ha31_0_6 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 7 := by fin_cases j <;> decide +kernel
lemma ha31_0_7_contains (j : Fin 7) : (ha31_0_7 j).Contains (fullFactor false 31 7 ((j.val:ℝ)/6)) := by
  rw [ha31_0_7_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha31_0_6 j) false 31 6 j (ha31_0_6_contains j)
noncomputable def hk31_0_8 (j : Fin 6) (i k : Fin 16) : CBox := (power31 j i k).conj.mul (mpower0_8 j i k)
lemma hk31_0_8_contains (j : Fin 6) (i k : Fin 16) :
    (hk31_0_8 j i k).Contains (fullFactor false 31 8 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk31_0_8,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power31 j i k) (mpower0_8 j i k) (quadraturePoint j.val (16*i.val+k.val)) 31 8 (power31_contains j i k) (mpower0_8_contains j i k)
noncomputable def ha31_0_8 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-121338629888859693730251),(-121338629888859693698681)⟩,⟨(-70054890629433514743640),(-70054890629433514713245)⟩⟩,⟨⟨17934052001134979759141083,17934052001134979779552062⟩,⟨31062689251548081581173520,31062689251548081601943387⟩⟩,⟨⟨(-59512327),126668995⟩,⟨(-919260274839426580352027818),(-919260274839426580142437726)⟩⟩,⟨⟨(-4591117312290554828582332046),(-4591117312290554814484988662)⟩,⟨7952048448396308880014394314,7952048448396308894192724812⟩⟩,⟨⟨47397902300335817806170988517,47397902300335817912254124333⟩,⟨(-27365191652122466740107997474),(-27365191652122466634562193256)⟩⟩,⟨⟨(-235330630358893204594095125374),(-235330630358893204492488053826)⟩,⟨(-64999320187),30615106068⟩⟩]
lemma ha31_0_8_eq (j : Fin 7) : ha31_0_8 j = ((ha31_0_7 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 8 := by fin_cases j <;> decide +kernel
lemma ha31_0_8_contains (j : Fin 7) : (ha31_0_8 j).Contains (fullFactor false 31 8 ((j.val:ℝ)/6)) := by
  rw [ha31_0_8_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha31_0_7 j) false 31 7 j (ha31_0_7_contains j)
noncomputable def hk31_0_9 (j : Fin 6) (i k : Fin 16) : CBox := (power31 j i k).conj.mul (mpower0_9 j i k)
lemma hk31_0_9_contains (j : Fin 6) (i k : Fin 16) :
    (hk31_0_9 j i k).Contains (fullFactor false 31 9 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk31_0_9,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power31 j i k) (mpower0_9 j i k) (quadraturePoint j.val (16*i.val+k.val)) 31 9 (power31_contains j i k) (mpower0_9_contains j i k)
noncomputable def ha31_0_9 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨4075628328693792151655,4075628328693792153437⟩,⟨(-7059195338064676367490),(-7059195338064676365630)⟩⟩,⟨⟨(-3614308013089114300969172),(-3614308013089114298540982)⟩,⟨2086721704291221580780769,2086721704291221583162338⟩⟩,⟨⟨160441184787359821855198506,160441184787359821892289579⟩,⟨(-10386861),22107911⟩⟩,⟨⟨(-1850525702701626523049216025),(-1850525702701626519743878290)⟩,⟨(-1068401512597105451746626477),(-1068401512597105448462624877)⟩⟩,⟨⟨7960211579480062781570563845,7960211579480062812297931908⟩,⟨13787490894657571013568435288,13787490894657571044470655583⟩⟩,⟨⟨(-10686688035),22689042977⟩,⟨(-82145886611128228817221468285),(-82145886611128228781492430969)⟩⟩]
lemma ha31_0_9_eq (j : Fin 7) : ha31_0_9 j = ((ha31_0_8 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 9 := by fin_cases j <;> decide +kernel
lemma ha31_0_9_contains (j : Fin 7) : (ha31_0_9 j).Contains (fullFactor false 31 9 ((j.val:ℝ)/6)) := by
  rw [ha31_0_9_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha31_0_8 j) false 31 8 j (ha31_0_8_contains j)
noncomputable def hk31_0_10 (j : Fin 6) (i k : Fin 16) : CBox := (power31 j i k).conj.mul (mpower0_10 j i k)
lemma hk31_0_10_contains (j : Fin 6) (i k : Fin 16) :
    (hk31_0_10 j i k).Contains (fullFactor false 31 10 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk31_0_10,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power31 j i k) (mpower0_10 j i k) (quadraturePoint j.val (16*i.val+k.val)) 31 10 (power31_contains j i k) (mpower0_10_contains j i k)
noncomputable def ha31_0_10 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨369618603571988403140,369618603571988403240⟩,⟨213399400269781075684,213399400269781075779⟩⟩,⟨⟨(-218520985876255821660580),(-218520985876255821410486)⟩,⟨(-378489450057716125002330),(-378489450057716124746845)⟩⟩,⟨⟨(-3472703),1631565⟩,⟨25202042373060605478288834,25202042373060605484195308⟩⟩,⟨⟨223765489537285960936444117,223765489537285961624956073⟩,⟨(-387573196859101312201981131),(-387573196859101311508479130)⟩⟩,⟨⟨(-3609556675507699254105856192),(-3609556675507699246004184261)⟩,⟨2083978518259580813404097090,2083978518259580821455136748⟩⟩,⟨⟨25806891390014060007138503623,25806891390014060018445257626⟩,⟨(-3357322063),7127973074⟩⟩]
lemma ha31_0_10_eq (j : Fin 7) : ha31_0_10 j = ((ha31_0_9 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 10 := by fin_cases j <;> decide +kernel
lemma ha31_0_10_contains (j : Fin 7) : (ha31_0_10 j).Contains (fullFactor false 31 10 ((j.val:ℝ)/6)) := by
  rw [ha31_0_10_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha31_0_9 j) false 31 9 j (ha31_0_9_contains j)
noncomputable def hk31_0_11 (j : Fin 6) (i k : Fin 16) : CBox := (power31 j i k).conj.mul (mpower0_11 j i k)
lemma hk31_0_11_contains (j : Fin 6) (i k : Fin 16) :
    (hk31_0_11 j i k).Contains (fullFactor false 31 11 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk31_0_11,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power31 j i k) (mpower0_11 j i k) (quadraturePoint j.val (16*i.val+k.val)) 31 11 (power31_contains j i k) (mpower0_11_contains j i k)
noncomputable def ha31_0_11 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-10157787699515332864),(-10157787699515332858)⟩,⟨17593804388058740562,17593804388058740567⟩⟩,⟨⟨36032111386744300664751,36032111386744300689189⟩,⟨(-20803149208607401709424),(-20803149208607401685548)⟩⟩,⟨⟨(-3598843235212085340915685),(-3598843235212085340060786)⟩,⟨(-495901),232987⟩⟩,⟨⟨73793764120052327717183445,73793764120052327849460811⟩,⟨42604849579227958616227937,42604849579227958747455924⟩⟩,⟨⟨(-495985727515397113237075196),(-495985727515397111319353465)⟩,⟨(-859072479885680692630396271),(-859072479885680690699468347)⟩⟩,⟨⟨(-2035744350),958848939⟩,⟨7370430945714350775693575808,7370430945714350778946238011⟩⟩]
lemma ha31_0_11_eq (j : Fin 7) : ha31_0_11 j = ((ha31_0_10 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 11 := by fin_cases j <;> decide +kernel
lemma ha31_0_11_contains (j : Fin 7) : (ha31_0_11 j).Contains (fullFactor false 31 11 ((j.val:ℝ)/6)) := by
  rw [ha31_0_11_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha31_0_10 j) false 31 10 j (ha31_0_10_contains j)
noncomputable def hk31_0_12 (j : Fin 6) (i k : Fin 16) : CBox := (power31 j i k).conj.mul (mpower0_12 j i k)
lemma hk31_0_12_contains (j : Fin 6) (i k : Fin 16) :
    (hk31_0_12 j i k).Contains (fullFactor false 31 12 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk31_0_12,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power31 j i k) (mpower0_12 j i k) (quadraturePoint j.val (16*i.val+k.val)) 31 12 (power31_contains j i k) (mpower0_12_contains j i k)
noncomputable def ha31_0_12 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-767674536308627878),(-767674536308627877)⟩,⟨(-443217100187807443),(-443217100187807442)⟩⟩,⟨⟨1815417242369259284406,1815417242369259286497⟩,⟨3144394900720139783926,3144394900720139786069⟩⟩,⟨⟨(-30498),64914⟩,⟨(-471087477881817150427972),(-471087477881817150314565)⟩⟩,⟨⟨(-7435949024744486045614150),(-7435949024744486022686875)⟩,⟨12879441513349692547242821,12879441513349692570370574⟩⟩,⟨⟨187420541090973602624239862,187420541090973603046099564⟩,⟨(-108207299850538926652028440),(-108207299850538926233302025)⟩⟩,⟨⟨(-1929574309403923048349558345),(-1929574309403923047491871344)⟩,⟨(-532956625),251026066⟩⟩]
lemma ha31_0_12_eq (j : Fin 7) : ha31_0_12 j = ((ha31_0_11 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 12 := by fin_cases j <;> decide +kernel
lemma ha31_0_12_contains (j : Fin 7) : (ha31_0_12 j).Contains (fullFactor false 31 12 ((j.val:ℝ)/6)) := by
  rw [ha31_0_12_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha31_0_11 j) false 31 11 j (ha31_0_11_contains j)
noncomputable def hk31_0_13 (j : Fin 6) (i k : Fin 16) : CBox := (power31 j i k).conj.mul (mpower0_13 j i k)
lemma hk31_0_13_contains (j : Fin 6) (i k : Fin 16) :
    (hk31_0_13 j i k).Contains (fullFactor false 31 13 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk31_0_13,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power31 j i k) (mpower0_13 j i k) (quadraturePoint j.val (16*i.val+k.val)) 31 13 (power31_contains j i k) (mpower0_13_contains j i k)
noncomputable def ha31_0_13 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨17851379306351118,17851379306351119⟩,⟨(-30919495943783800),(-30919495943783799)⟩⟩,⟨⟨(-253292510771476882374),(-253292510771476882200)⟩,⟨146238499277628361422,146238499277628361592⟩⟩,⟨⟨56921729219679268111365,56921729219679268125250⟩,⟨(-3686),7844⟩⟩,⟨⟨(-2074972248239938621473249),(-2074972248239938617740593)⟩,⟨(-1197985786082331539464838),(-1197985786082331535767272)⟩⟩,⟨⟨21791234504823142471084117,21791234504823142555478342⟩,⟨37743525322001707852898993,37743525322001707937974990⟩⟩,⟨⟨(-60663204),128794817⟩,⟨(-466302805767612564529553064),(-466302805767612564320799299)⟩⟩]
lemma ha31_0_13_eq (j : Fin 7) : ha31_0_13 j = ((ha31_0_12 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 13 := by fin_cases j <;> decide +kernel
lemma ha31_0_13_contains (j : Fin 7) : (ha31_0_13 j).Contains (fullFactor false 31 13 ((j.val:ℝ)/6)) := by
  rw [ha31_0_13_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha31_0_12 j) false 31 12 j (ha31_0_12_contains j)
noncomputable def hk31_0_14 (j : Fin 6) (i k : Fin 16) : CBox := (power31 j i k).conj.mul (mpower0_14 j i k)
lemma hk31_0_14_contains (j : Fin 6) (i k : Fin 16) :
    (hk31_0_14 j i k).Contains (fullFactor false 31 14 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk31_0_14,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power31 j i k) (mpower0_14 j i k) (quadraturePoint j.val (16*i.val+k.val)) 31 14 (power31_contains j i k) (mpower0_14_contains j i k)
noncomputable def ha31_0_14 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1156386444162983,1156386444162984⟩,⟨667640024824732,667640024824733⟩⟩,⟨⟨(-10938614166728417765),(-10938614166728417752)⟩,⟨(-18946235501166317758),(-18946235501166317744)⟩⟩,⟨⟨(-881),414⟩,⟨6386603083791852240367,6386603083791852241947⟩⟩,⟨⟨179218254507678396299010,179218254507678396852736⟩,⟨(-310415122451108950305530),(-310415122451108949746137)⟩⟩,⟨⟨(-7058022730486958389424515),(-7058022730486958373492873)⟩,⟨4074951323393142870248277,4074951323393142886042932⟩⟩,⟨⟨104638104924845707095526970,104638104924845707142704280⟩,⟨(-13612792),28901490⟩⟩]
lemma ha31_0_14_eq (j : Fin 7) : ha31_0_14 j = ((ha31_0_13 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 14 := by fin_cases j <;> decide +kernel
lemma ha31_0_14_contains (j : Fin 7) : (ha31_0_14 j).Contains (fullFactor false 31 14 ((j.val:ℝ)/6)) := by
  rw [ha31_0_14_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha31_0_13 j) false 31 13 j (ha31_0_13_contains j)
noncomputable def hk31_0_15 (j : Fin 6) (i k : Fin 16) : CBox := (power31 j i k).conj.mul (mpower0_15 j i k)
lemma hk31_0_15_contains (j : Fin 6) (i k : Fin 16) :
    (hk31_0_15 j i k).Contains (fullFactor false 31 15 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk31_0_15,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power31 j i k) (mpower0_15 j i k) (quadraturePoint j.val (16*i.val+k.val)) 31 15 (power31_contains j i k) (mpower0_15_contains j i k)
noncomputable def ha31_0_15 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-23305033302577),(-23305033302576)⟩,⟨40365501752147,40365501752148⟩⟩,⟨⟨1322696761414360852,1322696761414360854⟩,⟨(-763659331258827444),(-763659331258827442)⟩⟩,⟨⟨(-668803510981146723340),(-668803510981146723171)⟩,⟨(-93),44⟩⟩,⟨⟨43342127478025776380551,43342127478025776458796⟩,⟨25023588966689257627423,25023588966689257704818⟩⟩,⟨⟨(-711213174517105747722409),(-711213174517105744963456)⟩,⟨(-1231857353275977870663420),(-1231857353275977867878901)⟩⟩,⟨⟨(-6053114),2851057⟩,⟨21915353447830215822655968,21915353447830215832606520⟩⟩]
lemma ha31_0_15_eq (j : Fin 7) : ha31_0_15 j = ((ha31_0_14 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 15 := by fin_cases j <;> decide +kernel
lemma ha31_0_15_contains (j : Fin 7) : (ha31_0_15 j).Contains (fullFactor false 31 15 ((j.val:ℝ)/6)) := by
  rw [ha31_0_15_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha31_0_14 j) false 31 14 j (ha31_0_14_contains j)
noncomputable def hk31_0_16 (j : Fin 6) (i k : Fin 16) : CBox := (power31 j i k).conj.mul (mpower0_16 j i k)
lemma hk31_0_16_contains (j : Fin 6) (i k : Fin 16) :
    (hk31_0_16 j i k).Contains (fullFactor false 31 16 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk31_0_16,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power31 j i k) (mpower0_16 j i k) (quadraturePoint j.val (16*i.val+k.val)) 31 16 (power31_contains j i k) (mpower0_16_contains j i k)
noncomputable def ha31_0_16 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1320957955865),(-1320957955864)⟩,⟨(-762655431407),(-762655431406)⟩⟩,⟨⟨49981386352667221,49981386352667222⟩,⟨86570300595549323,86570300595549325⟩⟩,⟨⟨(-5),10⟩,⟨(-65659631149794723632),(-65659631149794723614)⟩⟩,⟨⟨(-3275580136008399054762),(-3275580136008399044620)⟩,⟨5673471219829920489532,5673471219829920499793⟩⟩,⟨⟨201562188089707223376477,201562188089707223832735⟩,⟨(-116371983552042445901551),(-116371983552042445449747)⟩⟩,⟨⟨(-4303069587032947008333212),(-4303069587032947006365728)⟩,⟨(-1188527),559804⟩⟩]
lemma ha31_0_16_eq (j : Fin 7) : ha31_0_16 j = ((ha31_0_15 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 16 := by fin_cases j <;> decide +kernel
lemma ha31_0_16_contains (j : Fin 7) : (ha31_0_16 j).Contains (fullFactor false 31 16 ((j.val:ℝ)/6)) := by
  rw [ha31_0_16_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha31_0_15 j) false 31 15 j (ha31_0_15_contains j)
noncomputable def hk31_0_17 (j : Fin 6) (i k : Fin 16) : CBox := (power31 j i k).conj.mul (mpower0_17 j i k)
lemma hk31_0_17_contains (j : Fin 6) (i k : Fin 16) :
    (hk31_0_17 j i k).Contains (fullFactor false 31 17 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk31_0_17,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power31 j i k) (mpower0_17 j i k) (quadraturePoint j.val (16*i.val+k.val)) 31 17 (power31_contains j i k) (mpower0_17_contains j i k)
noncomputable def ha31_0_17 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨23489732358,23489732359⟩,⟨(-40685409901),(-40685409900)⟩⟩,⟨⟨(-5332718046471331),(-5332718046471330)⟩,⟨3078846199642597,3078846199642598⟩⟩,⟨⟨6066935731106195666,6066935731106195669⟩,⟨(-1),1⟩⟩,⟨⟨(-698970019787090239837),(-698970019787090238570)⟩,⟨(-403550529079554597374),(-403550529079554596122)⟩⟩,⟨⟨17921243559351411706580,17921243559351411776216⟩,⟨31040504379613153605151,31040504379613153675514⟩⟩,⟨⟨(-103452),219640⟩,⟨(-795205400147551278671523),(-795205400147551278305400)⟩⟩]
lemma ha31_0_17_eq (j : Fin 7) : ha31_0_17 j = ((ha31_0_16 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 17 := by fin_cases j <;> decide +kernel
lemma ha31_0_17_contains (j : Fin 7) : (ha31_0_17 j).Contains (fullFactor false 31 17 ((j.val:ℝ)/6)) := by
  rw [ha31_0_17_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha31_0_16 j) false 31 16 j (ha31_0_16_contains j)
noncomputable def hk31_0_18 (j : Fin 6) (i k : Fin 16) : CBox := (power31 j i k).conj.mul (mpower0_18 j i k)
lemma hk31_0_18_contains (j : Fin 6) (i k : Fin 16) :
    (hk31_0_18 j i k).Contains (fullFactor false 31 18 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk31_0_18,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power31 j i k) (mpower0_18 j i k) (quadraturePoint j.val (16*i.val+k.val)) 31 18 (power31_contains j i k) (mpower0_18_contains j i k)
noncomputable def ha31_0_18 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1183490600,1183490601⟩,⟨683288616,683288617⟩⟩,⟨⟨(-179120011154260),(-179120011154259)⟩,⟨(-310244959971483),(-310244959971482)⟩⟩,⟨⟨(-1),1⟩,⟨529440020073462376,529440020073462377⟩⟩,⟨⟨46955236204022331300,46955236204022331447⟩,⟨(-81328854786764263455),(-81328854786764263307)⟩⟩,⟨⟨(-4514658357533078063470),(-4514658357533078053221)⟩,⟨2606539218020916330493,2606539218020916340631⟩⟩,⟨⟨138789524622137721114383,138789524622137721178727⟩,⟨(-18056),38335⟩⟩]
lemma ha31_0_18_eq (j : Fin 7) : ha31_0_18 j = ((ha31_0_17 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 18 := by fin_cases j <;> decide +kernel
lemma ha31_0_18_contains (j : Fin 7) : (ha31_0_18 j).Contains (fullFactor false 31 18 ((j.val:ℝ)/6)) := by
  rw [ha31_0_18_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha31_0_17 j) false 31 17 j (ha31_0_17_contains j)
noncomputable def hk31_0_19 (j : Fin 6) (i k : Fin 16) : CBox := (power31 j i k).conj.mul (mpower0_19 j i k)
lemma hk31_0_19_contains (j : Fin 6) (i k : Fin 16) :
    (hk31_0_19 j i k).Contains (fullFactor false 31 19 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk31_0_19,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power31 j i k) (mpower0_19 j i k) (quadraturePoint j.val (16*i.val+k.val)) 31 19 (power31_contains j i k) (mpower0_19_contains j i k)
noncomputable def ha31_0_19 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-18829952),(-18829951)⟩,⟨32614433,32614434⟩⟩,⟨⟨17099355913327,17099355913328⟩,⟨(-9872317739529),(-9872317739528)⟩⟩,⟨⟨(-43770654673137423),(-43770654673137422)⟩,⟨(-1),1⟩⟩,⟨⟨8964987113086656136,8964987113086656153⟩,⟨5175937723022106873,5175937723022106890⟩⟩,⟨⟨(-359152827132815578187),(-359152827132815576788)⟩,⟨(-622070944276038606226),(-622070944276038604811)⟩⟩,⟨⟨(-6339),2986⟩,⟨22948428997269873105174,22948428997269873115888⟩⟩]
lemma ha31_0_19_eq (j : Fin 7) : ha31_0_19 j = ((ha31_0_18 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 19 := by fin_cases j <;> decide +kernel
lemma ha31_0_19_contains (j : Fin 7) : (ha31_0_19 j).Contains (fullFactor false 31 19 ((j.val:ℝ)/6)) := by
  rw [ha31_0_19_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha31_0_18 j) false 31 18 j (ha31_0_18_contains j)
noncomputable def hk31_0_20 (j : Fin 6) (i k : Fin 16) : CBox := (power31 j i k).conj.mul (mpower0_20 j i k)
lemma hk31_0_20_contains (j : Fin 6) (i k : Fin 16) :
    (hk31_0_20 j i k).Contains (fullFactor false 31 20 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk31_0_20,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power31 j i k) (mpower0_20 j i k) (quadraturePoint j.val (16*i.val+k.val)) 31 20 (power31_contains j i k) (mpower0_20_contains j i k)
noncomputable def ha31_0_20 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-853844),(-853843)⟩,⟨(-492967),(-492966)⟩⟩,⟨⟨516913348073,516913348074⟩,⟨895320181973,895320181974⟩⟩,⟨⟨(-1),1⟩,⟨(-3437739179098608),(-3437739179098606)⟩⟩,⟨⟨(-542022930869484435),(-542022930869484432)⟩,⟨938811255133340261,938811255133340264⟩⟩,⟨⟨81428896189552855066,81428896189552855252⟩,⟨(-47012995134852432695),(-47012995134852432510)⟩⟩,⟨⟨(-3604730797462500934761),(-3604730797462500933066)⟩,⟨(-996),470⟩⟩]
lemma ha31_0_20_eq (j : Fin 7) : ha31_0_20 j = ((ha31_0_19 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 20 := by fin_cases j <;> decide +kernel
lemma ha31_0_20_contains (j : Fin 7) : (ha31_0_20 j).Contains (fullFactor false 31 20 ((j.val:ℝ)/6)) := by
  rw [ha31_0_20_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha31_0_19 j) false 31 19 j (ha31_0_19_contains j)
noncomputable def hk31_0_21 (j : Fin 6) (i k : Fin 16) : CBox := (power31 j i k).conj.mul (mpower0_21 j i k)
lemma hk31_0_21_contains (j : Fin 6) (i k : Fin 16) :
    (hk31_0_21 j i k).Contains (fullFactor false 31 21 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk31_0_21,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power31 j i k) (mpower0_21 j i k) (quadraturePoint j.val (16*i.val+k.val)) 31 21 (power31_contains j i k) (mpower0_21_contains j i k)
noncomputable def ha31_0_21 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨12291,12292⟩,⟨(-21290),(-21289)⟩⟩,⟨⟨(-44646528672),(-44646528671)⟩,⟨25776685346,25776685347⟩⟩,⟨⟨257142289286047,257142289286048⟩,⟨(-1),1⟩⟩,⟨⟨(-93630556896327456),(-93630556896327454)⟩,⟨(-54057627228469228),(-54057627228469227)⟩⟩,⟨⟨5860939688051789399,5860939688051789423⟩,⟨10151445319802585603,10151445319802585628⟩⟩,⟨⟨(-71),150⟩,⟨(-539266466260812849072),(-539266466260812848816)⟩⟩]
lemma ha31_0_21_eq (j : Fin 7) : ha31_0_21 j = ((ha31_0_20 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 21 := by fin_cases j <;> decide +kernel
lemma ha31_0_21_contains (j : Fin 7) : (ha31_0_21 j).Contains (fullFactor false 31 21 ((j.val:ℝ)/6)) := by
  rw [ha31_0_21_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha31_0_20 j) false 31 20 j (ha31_0_20_contains j)
noncomputable def hk31_0_22 (j : Fin 6) (i k : Fin 16) : CBox := (power31 j i k).conj.mul (mpower0_22 j i k)
lemma hk31_0_22_contains (j : Fin 6) (i k : Fin 16) :
    (hk31_0_22 j i k).Contains (fullFactor false 31 22 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk31_0_22,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power31 j i k) (mpower0_22 j i k) (quadraturePoint j.val (16*i.val+k.val)) 31 22 (power31_contains j i k) (mpower0_22_contains j i k)
noncomputable def ha31_0_22 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨506,507⟩,⟨292,293⟩⟩,⟨⟨(-1226967354),(-1226967353)⟩,⟨(-2125169796),(-2125169795)⟩⟩,⟨⟨(-1),1⟩,⟨18359916521552,18359916521553⟩⟩,⟨⟨5146274077922863,5146274077922864⟩,⟨(-8913608172637076),(-8913608172637075)⟩⟩,⟨⟨(-1208019168182208040),(-1208019168182208036)⟩,⟨697450191936225608,697450191936225612⟩⟩,⟨⟨77007071306013533780,77007071306013533818⟩,⟨(-11),22⟩⟩]
lemma ha31_0_22_eq (j : Fin 7) : ha31_0_22 j = ((ha31_0_21 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 22 := by fin_cases j <;> decide +kernel
lemma ha31_0_22_contains (j : Fin 7) : (ha31_0_22 j).Contains (fullFactor false 31 22 ((j.val:ℝ)/6)) := by
  rw [ha31_0_22_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha31_0_21 j) false 31 21 j (ha31_0_21_contains j)
noncomputable def hk31_0_23 (j : Fin 6) (i k : Fin 16) : CBox := (power31 j i k).conj.mul (mpower0_23 j i k)
lemma hk31_0_23_contains (j : Fin 6) (i k : Fin 16) :
    (hk31_0_23 j i k).Contains (fullFactor false 31 23 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk31_0_23,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power31 j i k) (mpower0_23 j i k) (quadraturePoint j.val (16*i.val+k.val)) 31 23 (power31_contains j i k) (mpower0_23_contains j i k)
noncomputable def ha31_0_23 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-7),(-6)⟩,⟨11,12⟩⟩,⟨⟨96759678,96759679⟩,⟨(-55864227),(-55864226)⟩⟩,⟨⟨(-1253899540536),(-1253899540535)⟩,⟨(-1),1⟩⟩,⟨⟨811679013105350,811679013105351⟩,⟨468623096711943,468623096711944⟩⟩,⟨⟨(-79387840551870929),(-79387840551870928)⟩,⟨(-137503773339017308),(-137503773339017306)⟩⟩,⟨⟨(-4),2⟩,⟨10518471716932064452,10518471716932064458⟩⟩]
lemma ha31_0_23_eq (j : Fin 7) : ha31_0_23 j = ((ha31_0_22 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 23 := by fin_cases j <;> decide +kernel
lemma ha31_0_23_contains (j : Fin 7) : (ha31_0_23 j).Contains (fullFactor false 31 23 ((j.val:ℝ)/6)) := by
  rw [ha31_0_23_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha31_0_22 j) false 31 22 j (ha31_0_22_contains j)
noncomputable def hk31_0_24 (j : Fin 6) (i k : Fin 16) : CBox := (power31 j i k).conj.mul (mpower0_24 j i k)
lemma hk31_0_24_contains (j : Fin 6) (i k : Fin 16) :
    (hk31_0_24 j i k).Contains (fullFactor false 31 24 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk31_0_24,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power31 j i k) (mpower0_24 j i k) (quadraturePoint j.val (16*i.val+k.val)) 31 24 (power31_contains j i k) (mpower0_24_contains j i k)
noncomputable def ha31_0_24 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),0⟩,⟨(-1),0⟩⟩,⟨⟨2437536,2437537⟩,⟨4221937,4221938⟩⟩,⟨⟨(-1),1⟩,⟨(-82067533019),(-82067533018)⟩⟩,⟨⟨(-40895079942577),(-40895079942576)⟩,⟨70832356240132,70832356240133⟩⟩,⟨⟨14999334866761557,14999334866761558⟩,⟨(-8659870022990125),(-8659870022990124)⟩⟩,⟨⟨(-1376864728037741371),(-1376864728037741370)⟩,⟨(-1),1⟩⟩]
lemma ha31_0_24_eq (j : Fin 7) : ha31_0_24 j = ((ha31_0_23 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 24 := by fin_cases j <;> decide +kernel
lemma ha31_0_24_contains (j : Fin 7) : (ha31_0_24 j).Contains (fullFactor false 31 24 ((j.val:ℝ)/6)) := by
  rw [ha31_0_24_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha31_0_23 j) false 31 23 j (ha31_0_23_contains j)
noncomputable def hk31_0_25 (j : Fin 6) (i k : Fin 16) : CBox := (power31 j i k).conj.mul (mpower0_25 j i k)
lemma hk31_0_25_contains (j : Fin 6) (i k : Fin 16) :
    (hk31_0_25 j i k).Contains (fullFactor false 31 25 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk31_0_25,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power31 j i k) (mpower0_25 j i k) (quadraturePoint j.val (16*i.val+k.val)) 31 25 (power31_contains j i k) (mpower0_25_contains j i k)
noncomputable def ha31_0_25 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨0,1⟩,⟨(-1),0⟩⟩,⟨⟨(-176849),(-176848)⟩,⟨102103,102104⟩⟩,⟨⟨5156455176,5156455177⟩,⟨(-1),1⟩⟩,⟨⟨(-5934037600013),(-5934037600012)⟩,⟨(-3426018205749),(-3426018205748)⟩⟩,⟨⟨906859468175608,906859468175609⟩,⟨1570726674205044,1570726674205046⟩⟩,⟨⟨(-1),1⟩,⟨(-173021924583611077),(-173021924583611076)⟩⟩]
lemma ha31_0_25_eq (j : Fin 7) : ha31_0_25 j = ((ha31_0_24 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 25 := by fin_cases j <;> decide +kernel
lemma ha31_0_25_contains (j : Fin 7) : (ha31_0_25 j).Contains (fullFactor false 31 25 ((j.val:ℝ)/6)) := by
  rw [ha31_0_25_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha31_0_24 j) false 31 24 j (ha31_0_24_contains j)
noncomputable def hk31_0_26 (j : Fin 6) (i k : Fin 16) : CBox := (power31 j i k).conj.mul (mpower0_26 j i k)
lemma hk31_0_26_contains (j : Fin 6) (i k : Fin 16) :
    (hk31_0_26 j i k).Contains (fullFactor false 31 26 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk31_0_26,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power31 j i k) (mpower0_26 j i k) (quadraturePoint j.val (16*i.val+k.val)) 31 26 (power31_contains j i k) (mpower0_26_contains j i k)
noncomputable def ha31_0_26 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨0,1⟩,⟨0,1⟩⟩,⟨⟨(-4113),(-4112)⟩,⟨(-7123),(-7122)⟩⟩,⟨⟨(-1),1⟩,⟨311528494,311528495⟩⟩,⟨⟨275978298108,275978298109⟩,⟨(-478008434111),(-478008434110)⟩⟩,⟨⟨(-158159723733337),(-158159723733336)⟩,⟨91313559072398,91313559072399⟩⟩,⟨⟨20906323353147684,20906323353147685⟩,⟨(-1),1⟩⟩]
lemma ha31_0_26_eq (j : Fin 7) : ha31_0_26 j = ((ha31_0_25 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 26 := by fin_cases j <;> decide +kernel
lemma ha31_0_26_contains (j : Fin 7) : (ha31_0_26 j).Contains (fullFactor false 31 26 ((j.val:ℝ)/6)) := by
  rw [ha31_0_26_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha31_0_25 j) false 31 25 j (ha31_0_25_contains j)
noncomputable def hk31_0_27 (j : Fin 6) (i k : Fin 16) : CBox := (power31 j i k).conj.mul (mpower0_27 j i k)
lemma hk31_0_27_contains (j : Fin 6) (i k : Fin 16) :
    (hk31_0_27 j i k).Contains (fullFactor false 31 27 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk31_0_27,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power31 j i k) (mpower0_27 j i k) (quadraturePoint j.val (16*i.val+k.val)) 31 27 (power31_contains j i k) (mpower0_27_contains j i k)
noncomputable def ha31_0_27 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),0⟩,⟨0,1⟩⟩,⟨⟨276,277⟩,⟨(-160),(-159)⟩⟩,⟨⟨(-18123994),(-18123993)⟩,⟨(-1),1⟩⟩,⟨⟨37079204566,37079204567⟩,⟨21407688737,21407688739⟩⟩,⟨⟨(-8854012541821),(-8854012541820)⟩,⟨(-15335599573286),(-15335599573285)⟩⟩,⟨⟨(-1),1⟩,⟨2432561179993388,2432561179993389⟩⟩]
lemma ha31_0_27_eq (j : Fin 7) : ha31_0_27 j = ((ha31_0_26 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 27 := by fin_cases j <;> decide +kernel
lemma ha31_0_27_contains (j : Fin 7) : (ha31_0_27 j).Contains (fullFactor false 31 27 ((j.val:ℝ)/6)) := by
  rw [ha31_0_27_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha31_0_26 j) false 31 26 j (ha31_0_26_contains j)
noncomputable def hk31_0_28 (j : Fin 6) (i k : Fin 16) : CBox := (power31 j i k).conj.mul (mpower0_28 j i k)
lemma hk31_0_28_contains (j : Fin 6) (i k : Fin 16) :
    (hk31_0_28 j i k).Contains (fullFactor false 31 28 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk31_0_28,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power31 j i k) (mpower0_28 j i k) (quadraturePoint j.val (16*i.val+k.val)) 31 28 (power31_contains j i k) (mpower0_28_contains j i k)
noncomputable def ha31_0_28 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),0⟩,⟨(-1),0⟩⟩,⟨⟨5,6⟩,⟨10,11⟩⟩,⟨⟨(-1),1⟩,⟨(-1016754),(-1016753)⟩⟩,⟨⟨(-1601291374),(-1601291373)⟩,⟨2773518015,2773518016⟩⟩,⟨⟨1433875207078,1433875207079⟩,⟨(-827848236791),(-827848236790)⟩⟩,⟨⟨(-272932726159820),(-272932726159819)⟩,⟨(-1),1⟩⟩]
lemma ha31_0_28_eq (j : Fin 7) : ha31_0_28 j = ((ha31_0_27 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 28 := by fin_cases j <;> decide +kernel
lemma ha31_0_28_contains (j : Fin 7) : (ha31_0_28 j).Contains (fullFactor false 31 28 ((j.val:ℝ)/6)) := by
  rw [ha31_0_28_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha31_0_27 j) false 31 27 j (ha31_0_27_contains j)
noncomputable def hk31_0_29 (j : Fin 6) (i k : Fin 16) : CBox := (power31 j i k).conj.mul (mpower0_29 j i k)
lemma hk31_0_29_contains (j : Fin 6) (i k : Fin 16) :
    (hk31_0_29 j i k).Contains (fullFactor false 31 29 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk31_0_29,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power31 j i k) (mpower0_29 j i k) (quadraturePoint j.val (16*i.val+k.val)) 31 29 (power31_contains j i k) (mpower0_29_contains j i k)
noncomputable def ha31_0_29 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨0,1⟩,⟨(-1),0⟩⟩,⟨⟨(-1),0⟩,⟨0,1⟩⟩,⟨⟨55072,55073⟩,⟨(-1),1⟩⟩,⟨⟨(-200304916),(-200304915)⟩,⟨(-115646097),(-115646096)⟩⟩,⟨⟨74734538476,74734538477⟩,⟨129444017721,129444017722⟩⟩,⟨⟨(-1),1⟩,⟨(-29567015428550),(-29567015428549)⟩⟩]
lemma ha31_0_29_eq (j : Fin 7) : ha31_0_29 j = ((ha31_0_28 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 29 := by fin_cases j <;> decide +kernel
lemma ha31_0_29_contains (j : Fin 7) : (ha31_0_29 j).Contains (fullFactor false 31 29 ((j.val:ℝ)/6)) := by
  rw [ha31_0_29_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha31_0_28 j) false 31 28 j (ha31_0_28_contains j)
noncomputable def hk31_0_30 (j : Fin 6) (i k : Fin 16) : CBox := (power31 j i k).conj.mul (mpower0_30 j i k)
lemma hk31_0_30_contains (j : Fin 6) (i k : Fin 16) :
    (hk31_0_30 j i k).Contains (fullFactor false 31 30 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk31_0_30,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power31 j i k) (mpower0_30 j i k) (quadraturePoint j.val (16*i.val+k.val)) 31 30 (power31_contains j i k) (mpower0_30_contains j i k)
noncomputable def ha31_0_30 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨0,1⟩,⟨0,1⟩⟩,⟨⟨(-1),0⟩,⟨(-1),0⟩⟩,⟨⟨(-1),1⟩,⟨2883,2884⟩⟩,⟨⟨8073620,8073621⟩,⟨(-13983922),(-13983921)⟩⟩,⟨⟨(-11296121532),(-11296121531)⟩,⟨6521818806,6521818807⟩⟩,⟨⟨3096250615296,3096250615297⟩,⟨(-1),1⟩⟩]
lemma ha31_0_30_eq (j : Fin 7) : ha31_0_30 j = ((ha31_0_29 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 30 := by fin_cases j <;> decide +kernel
lemma ha31_0_30_contains (j : Fin 7) : (ha31_0_30 j).Contains (fullFactor false 31 30 ((j.val:ℝ)/6)) := by
  rw [ha31_0_30_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha31_0_29 j) false 31 29 j (ha31_0_29_contains j)
noncomputable def hk31_1_0 (j : Fin 6) (i k : Fin 16) : CBox := (kernel31_0 j i k).mul (mpower1_0 j i k)
lemma hk31_1_0_contains (j : Fin 6) (i k : Fin 16) :
    (hk31_1_0 j i k).Contains (fullFactor true 31 0 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk31_1_0,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel31_0 j i k) (mpower1_0 j i k) (quadraturePoint j.val (16*i.val+k.val)) 31 0 (kernel31_0_contains j i k) (mpower1_0_contains j i k)
noncomputable def ha31_1_0 : Fin 7 → CBox := ![⟨⟨(-3),3⟩,⟨(-3),3⟩⟩,⟨⟨(-3),4⟩,⟨(-4),2⟩⟩,⟨⟨(-2),4⟩,⟨(-4),2⟩⟩,⟨⟨0,3⟩,⟨(-2),2⟩⟩,⟨⟨(-4030720336),(-4030720333)⟩,⟨4299209323,4299209326⟩⟩,⟨⟨407412577843147764126,407412577843147767566⟩,⟨58579429178108479865,58579429178108483303⟩⟩,⟨⟨(-2224103963996790476325329693),(-2224103963996790455774833313)⟩,⟨2270745127693704504337839885,2270745127693704524857452908⟩⟩]
lemma ha31_1_0_eq (j : Fin 7) : ha31_1_0 j = atomKernel31_0 j := by fin_cases j <;> decide +kernel
lemma ha31_1_0_contains (j : Fin 7) : (ha31_1_0 j).Contains (fullFactor true 31 0 ((j.val:ℝ)/6)) := by
  rw [ha31_1_0_eq]
  simpa only [fullFactor,ite_true] using atomKernel31_0_contains j
noncomputable def hk31_1_1 (j : Fin 6) (i k : Fin 16) : CBox := (kernel31_0 j i k).mul (mpower1_1 j i k)
lemma hk31_1_1_contains (j : Fin 6) (i k : Fin 16) :
    (hk31_1_1 j i k).Contains (fullFactor true 31 1 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk31_1_1,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel31_0 j i k) (mpower1_1 j i k) (quadraturePoint j.val (16*i.val+k.val)) 31 1 (kernel31_0_contains j i k) (mpower1_1_contains j i k)
noncomputable def ha31_1_1 : Fin 7 → CBox := ![⟨⟨(-28),28⟩,⟨(-28),28⟩⟩,⟨⟨(-46),31⟩,⟨(-31),42⟩⟩,⟨⟨(-41),21⟩,⟨(-31),30⟩⟩,⟨⟨(-19),11⟩,⟨(-21),6⟩⟩,⟨⟨25970278706,25970278725⟩,⟨12107049782,12107049802⟩⟩,⟨⟨(-47628420768149630847),(-47628420768149614376)⟩,⟨(-1705658777325531325301),(-1705658777325531308820)⟩⟩,⟨⟨8617347244127811818499525611,8617347244127811896482648040⟩,⟨7604911897842197952003746458,7604911897842198030092082194⟩⟩]
lemma ha31_1_1_eq (j : Fin 7) : ha31_1_1 j = ((ha31_1_0 j).mul (piI.mul (atomPoints j).z)).scale 1 1 := by fin_cases j <;> decide +kernel
lemma ha31_1_1_contains (j : Fin 7) : (ha31_1_1 j).Contains (fullFactor true 31 1 ((j.val:ℝ)/6)) := by
  rw [ha31_1_1_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha31_1_0 j) true 31 0 j (ha31_1_0_contains j)
noncomputable def hk31_1_2 (j : Fin 6) (i k : Fin 16) : CBox := (kernel31_0 j i k).mul (mpower1_2 j i k)
lemma hk31_1_2_contains (j : Fin 6) (i k : Fin 16) :
    (hk31_1_2 j i k).Contains (fullFactor true 31 2 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk31_1_2,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel31_0 j i k) (mpower1_2 j i k) (quadraturePoint j.val (16*i.val+k.val)) 31 2 (kernel31_0_contains j i k) (mpower1_2_contains j i k)
noncomputable def ha31_1_2 : Fin 7 → CBox := ![⟨⟨(-130),130⟩,⟨(-130),130⟩⟩,⟨⟨(-177),255⟩,⟨(-219),205⟩⟩,⟨⟨(-132),179⟩,⟨(-128),182⟩⟩,⟨⟨(-70),43⟩,⟨(-37),79⟩⟩,⟨⟨8290104826,8290104887⟩,⟨(-69164451613),(-69164451553)⟩⟩,⟨⟨(-3467288054675362345310),(-3467288054675362305833)⟩,⟨697940133507067142245,697940133507067181697⟩⟩,⟨⟨12921713344878323947007610477,12921713344878324095364975222⟩,⟨(-16272732548135652174226306945),(-16272732548135652026043512041)⟩⟩]
lemma ha31_1_2_eq (j : Fin 7) : ha31_1_2 j = ((ha31_1_1 j).mul (piI.mul (atomPoints j).z)).scale 1 2 := by fin_cases j <;> decide +kernel
lemma ha31_1_2_contains (j : Fin 7) : (ha31_1_2 j).Contains (fullFactor true 31 2 ((j.val:ℝ)/6)) := by
  rw [ha31_1_2_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha31_1_1 j) true 31 1 j (ha31_1_1_contains j)
noncomputable def hk31_1_3 (j : Fin 6) (i k : Fin 16) : CBox := (kernel31_0 j i k).mul (mpower1_3 j i k)
lemma hk31_1_3_contains (j : Fin 6) (i k : Fin 16) :
    (hk31_1_3 j i k).Contains (fullFactor true 31 3 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk31_1_3,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel31_0 j i k) (mpower1_3 j i k) (quadraturePoint j.val (16*i.val+k.val)) 31 3 (kernel31_0_contains j i k) (mpower1_3_contains j i k)
noncomputable def ha31_1_3 : Fin 7 → CBox := ![⟨⟨(-400),400⟩,⟨(-400),400⟩⟩,⟨⟨(-924),707⟩,⟨(-840),779⟩⟩,⟨⟨(-514),530⟩,⟨(-606),437⟩⟩,⟨⟨(-104),201⟩,⟨(-148),155⟩⟩,⟨⟨(-110700494399),(-110700494275)⟩,⟨22169534400,22169534525⟩⟩,⟨⟨1764440168088632886350,1764440168088632949349⟩,⟨4557778467483777458304,4557778467483777521341⟩⟩,⟨⟨(-20395871468310250607942058962),(-20395871468310250420227306605)⟩,⟨(-14535019260787779429662887352),(-14535019260787779241761107621)⟩⟩]
lemma ha31_1_3_eq (j : Fin 7) : ha31_1_3 j = ((ha31_1_2 j).mul (piI.mul (atomPoints j).z)).scale 1 3 := by fin_cases j <;> decide +kernel
lemma ha31_1_3_contains (j : Fin 7) : (ha31_1_3 j).Contains (fullFactor true 31 3 ((j.val:ℝ)/6)) := by
  rw [ha31_1_3_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha31_1_2 j) true 31 2 j (ha31_1_2_contains j)
noncomputable def hk31_1_4 (j : Fin 6) (i k : Fin 16) : CBox := (kernel31_0 j i k).mul (mpower1_4 j i k)
lemma hk31_1_4_contains (j : Fin 6) (i k : Fin 16) :
    (hk31_1_4 j i k).Contains (fullFactor true 31 4 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk31_1_4,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel31_0 j i k) (mpower1_4 j i k) (quadraturePoint j.val (16*i.val+k.val)) 31 4 (kernel31_0_contains j i k) (mpower1_4_contains j i k)
noncomputable def ha31_1_4 : Fin 7 → CBox := ![⟨⟨(-922),922⟩,⟨(-922),922⟩⟩,⟨⟨(-2136),2495⟩,⟨(-2151),2469⟩⟩,⟨⟨(-1433),1196⟩,⟨(-1221),1408⟩⟩,⟨⟨(-332),272⟩,⟨(-367),238⟩⟩,⟨⟨67543429537,67543429729⟩,⟨119460085078,119460085270⟩⟩,⟨⟨4344292554885931418359,4344292554885931493850⟩,⟨(-2604581690289197134667),(-2604581690289197059216)⟩⟩,⟨⟨(-12164132957218381327222555451),(-12164132957218381148736228505)⟩,⟨19094828067338493653710616205,19094828067338493832052848431⟩⟩]
lemma ha31_1_4_eq (j : Fin 7) : ha31_1_4 j = ((ha31_1_3 j).mul (piI.mul (atomPoints j).z)).scale 1 4 := by fin_cases j <;> decide +kernel
lemma ha31_1_4_contains (j : Fin 7) : (ha31_1_4 j).Contains (fullFactor true 31 4 ((j.val:ℝ)/6)) := by
  rw [ha31_1_4_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha31_1_3 j) true 31 3 j (ha31_1_3_contains j)
noncomputable def hk31_1_5 (j : Fin 6) (i k : Fin 16) : CBox := (kernel31_0 j i k).mul (mpower1_5 j i k)
lemma hk31_1_5_contains (j : Fin 6) (i k : Fin 16) :
    (hk31_1_5 j i k).Contains (fullFactor true 31 5 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk31_1_5,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel31_0 j i k) (mpower1_5 j i k) (quadraturePoint j.val (16*i.val+k.val)) 31 5 (kernel31_0_contains j i k) (mpower1_5_contains j i k)
noncomputable def ha31_1_5 : Fin 7 → CBox := ![⟨⟨(-1700),1700⟩,⟨(-1700),1700⟩⟩,⟨⟨(-5425),5111⟩,⟨(-5641),4887⟩⟩,⟨⟨(-2436),2862⟩,⟨(-2619),2679⟩⟩,⟨⟨(-529),432⟩,⟨(-413),547⟩⟩,⟨⟨89910386027,89910386264⟩,⟨(-98614905428),(-98614905192)⟩⟩,⟨⟨(-2740038877997094277622),(-2740038877997094205331)⟩,⟨(-3182660232125969428172),(-3182660232125969355850)⟩⟩,⟨⟨14247204279578508634765396278,14247204279578508770313430661⟩,⟨8067900187042618666860116120,8067900187042618802491700894⟩⟩]
lemma ha31_1_5_eq (j : Fin 7) : ha31_1_5 j = ((ha31_1_4 j).mul (piI.mul (atomPoints j).z)).scale 1 5 := by fin_cases j <;> decide +kernel
lemma ha31_1_5_contains (j : Fin 7) : (ha31_1_5 j).Contains (fullFactor true 31 5 ((j.val:ℝ)/6)) := by
  rw [ha31_1_5_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha31_1_4 j) true 31 4 j (ha31_1_4_contains j)
noncomputable def hk31_1_6 (j : Fin 6) (i k : Fin 16) : CBox := (kernel31_0 j i k).mul (mpower1_6 j i k)
lemma hk31_1_6_contains (j : Fin 6) (i k : Fin 16) :
    (hk31_1_6 j i k).Contains (fullFactor true 31 6 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk31_1_6,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel31_0 j i k) (mpower1_6 j i k) (quadraturePoint j.val (16*i.val+k.val)) 31 6 (kernel31_0_contains j i k) (mpower1_6_contains j i k)
noncomputable def ha31_1_6 : Fin 7 → CBox := ![⟨⟨(-2612),2612⟩,⟨(-2612),2612⟩⟩,⟨⟨(-10026),9960⟩,⟨(-9412),10570⟩⟩,⟨⟨(-4597),4299⟩,⟨(-4655),4241⟩⟩,⟨⟨(-556),716⟩,⟨(-626),646⟩⟩,⟨⟨(-98641013669),(-98641013427)⟩,⟨(-44324713318),(-44324713075)⟩⟩,⟨⟨(-1845381009114195391786),(-1845381009114195334049)⟩,⟨2239238934368501006673,2239238934368501064392⟩⟩,⟨⟨4409692053250024995566941318,4409692053250025081454065215⟩,⟨(-8826993718143173172616917838),(-8826993718143173086766240773)⟩⟩]
lemma ha31_1_6_eq (j : Fin 7) : ha31_1_6 j = ((ha31_1_5 j).mul (piI.mul (atomPoints j).z)).scale 1 6 := by fin_cases j <;> decide +kernel
lemma ha31_1_6_contains (j : Fin 7) : (ha31_1_6 j).Contains (fullFactor true 31 6 ((j.val:ℝ)/6)) := by
  rw [ha31_1_6_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha31_1_5 j) true 31 5 j (ha31_1_5_contains j)
noncomputable def hk31_1_7 (j : Fin 6) (i k : Fin 16) : CBox := (kernel31_0 j i k).mul (mpower1_7 j i k)
lemma hk31_1_7_contains (j : Fin 6) (i k : Fin 16) :
    (hk31_1_7 j i k).Contains (fullFactor true 31 7 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk31_1_7,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel31_0 j i k) (mpower1_7 j i k) (quadraturePoint j.val (16*i.val+k.val)) 31 7 (kernel31_0_contains j i k) (mpower1_7_contains j i k)
noncomputable def ha31_1_7 : Fin 7 → CBox := ![⟨⟨(-3439),3439⟩,⟨(-3439),3439⟩⟩,⟨⟨(-15907),16595⟩,⟨(-16866),15633⟩⟩,⟨⟨(-6449),6354⟩,⟨(-6146),6657⟩⟩,⟨⟨(-747),697⟩,⟨(-784),659⟩⟩,⟨⟨(-7900485729),(-7900485515)⟩,⟨74698308071,74698308284⟩⟩,⟨⟨1492523583963903809913,1492523583963903849414⟩,⟨851688637917093544881,851688637917093584390⟩⟩,⟨⟨(-4671789546547486452982365223),(-4671789546547486406376588220)⟩,⟨(-2038005515753214138328360498),(-2038005515753214091711635873)⟩⟩]
lemma ha31_1_7_eq (j : Fin 7) : ha31_1_7 j = ((ha31_1_6 j).mul (piI.mul (atomPoints j).z)).scale 1 7 := by fin_cases j <;> decide +kernel
lemma ha31_1_7_contains (j : Fin 7) : (ha31_1_7 j).Contains (fullFactor true 31 7 ((j.val:ℝ)/6)) := by
  rw [ha31_1_7_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha31_1_6 j) true 31 6 j (ha31_1_6_contains j)
noncomputable def hk31_1_8 (j : Fin 6) (i k : Fin 16) : CBox := (kernel31_0 j i k).mul (mpower1_8 j i k)
lemma hk31_1_8_contains (j : Fin 6) (i k : Fin 16) :
    (hk31_1_8 j i k).Contains (fullFactor true 31 8 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk31_1_8,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel31_0 j i k) (mpower1_8 j i k) (quadraturePoint j.val (16*i.val+k.val)) 31 8 (kernel31_0_contains j i k) (mpower1_8_contains j i k)
noncomputable def ha31_1_8 : Fin 7 → CBox := ![⟨⟨(-3962),3962⟩,⟨(-3962),3962⟩⟩,⟨⟨(-23741),22509⟩,⟨(-22694),23555⟩⟩,⟨⟨(-7868),8255⟩,⟨(-8188),7935⟩⟩,⟨⟨(-748),686⟩,⟨(-679),755⟩⟩,⟨⟨44634678501,44634678666⟩,⟨(-9586800753),(-9586800588)⟩⟩,⟨⟨303526042552794978173,303526042552795001829⟩,⟨(-837156160321559299094),(-837156160321559275440)⟩⟩,⟨⟨(-810256673980045127453220706),(-810256673980045105314252305)⟩,⟨2156579603832901580063376879,2156579603832901602201248116⟩⟩]
lemma ha31_1_8_eq (j : Fin 7) : ha31_1_8 j = ((ha31_1_7 j).mul (piI.mul (atomPoints j).z)).scale 1 8 := by fin_cases j <;> decide +kernel
lemma ha31_1_8_contains (j : Fin 7) : (ha31_1_8 j).Contains (fullFactor true 31 8 ((j.val:ℝ)/6)) := by
  rw [ha31_1_8_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha31_1_7 j) true 31 7 j (ha31_1_7_contains j)
noncomputable def hk31_1_9 (j : Fin 6) (i k : Fin 16) : CBox := (kernel31_0 j i k).mul (mpower1_9 j i k)
lemma hk31_1_9_contains (j : Fin 6) (i k : Fin 16) :
    (hk31_1_9 j i k).Contains (fullFactor true 31 9 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk31_1_9,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel31_0 j i k) (mpower1_9 j i k) (quadraturePoint j.val (16*i.val+k.val)) 31 9 (kernel31_0_contains j i k) (mpower1_9_contains j i k)
noncomputable def ha31_1_9 : Fin 7 → CBox := ![⟨⟨(-4057),4057⟩,⟨(-4057),4057⟩⟩,⟨⟨(-28549),29954⟩,⟨(-29363),29139⟩⟩,⟨⟨(-9202),8845⟩,⟨(-9065),8982⟩⟩,⟨⟨(-602),664⟩,⟨(-627),639⟩⟩,⟨⟨(-12436484934),(-12436484821)⟩,⟨(-21298257007),(-21298256893)⟩⟩,⟨⟨(-403756185110019389819),(-403756185110019377228)⟩,⟨(-72264493190854866041),(-72264493190854853450)⟩⟩,⟨⟨882178857450436325141595782,882178857450436334488574715⟩,⟨280101084700267215752930848,280101084700267225098697070⟩⟩]
lemma ha31_1_9_eq (j : Fin 7) : ha31_1_9 j = ((ha31_1_8 j).mul (piI.mul (atomPoints j).z)).scale 1 9 := by fin_cases j <;> decide +kernel
lemma ha31_1_9_contains (j : Fin 7) : (ha31_1_9 j).Contains (fullFactor true 31 9 ((j.val:ℝ)/6)) := by
  rw [ha31_1_9_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha31_1_8 j) true 31 8 j (ha31_1_8_contains j)
noncomputable def hk31_1_10 (j : Fin 6) (i k : Fin 16) : CBox := (kernel31_0 j i k).mul (mpower1_10 j i k)
lemma hk31_1_10_contains (j : Fin 6) (i k : Fin 16) :
    (hk31_1_10 j i k).Contains (fullFactor true 31 10 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk31_1_10,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel31_0 j i k) (mpower1_10 j i k) (quadraturePoint j.val (16*i.val+k.val)) 31 10 (kernel31_0_contains j i k) (mpower1_10_contains j i k)
noncomputable def ha31_1_10 : Fin 7 → CBox := ![⟨⟨(-3739),3739⟩,⟨(-3739),3739⟩⟩,⟨⟨(-33881),32720⟩,⟨(-33476),33125⟩⟩,⟨⟨(-9024),9157⟩,⟨(-8978),9203⟩⟩,⟨⟨(-509),497⟩,⟨(-521),485⟩⟩,⟨⟨(-7955200971),(-7955200900)⟩,⟨8973087660,8973087731⟩⟩,⟨⟨(-1085433284876035825),(-1085433284876029793)⟩,⟨170035979009406642625,170035979009406648657⟩⟩,⟨⟨84580262739715913824265981,84580262739715917374932541⟩,⟨(-323816634509918000756467940),(-323816634509917997204730181)⟩⟩]
lemma ha31_1_10_eq (j : Fin 7) : ha31_1_10 j = ((ha31_1_9 j).mul (piI.mul (atomPoints j).z)).scale 1 10 := by fin_cases j <;> decide +kernel
lemma ha31_1_10_contains (j : Fin 7) : (ha31_1_10 j).Contains (fullFactor true 31 10 ((j.val:ℝ)/6)) := by
  rw [ha31_1_10_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha31_1_9 j) true 31 9 j (ha31_1_9_contains j)
noncomputable def hk31_1_11 (j : Fin 6) (i k : Fin 16) : CBox := (kernel31_0 j i k).mul (mpower1_11 j i k)
lemma hk31_1_11_contains (j : Fin 6) (i k : Fin 16) :
    (hk31_1_11 j i k).Contains (fullFactor true 31 11 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk31_1_11,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel31_0 j i k) (mpower1_11 j i k) (quadraturePoint j.val (16*i.val+k.val)) 31 11 (kernel31_0_contains j i k) (mpower1_11_contains j i k)
noncomputable def ha31_1_11 : Fin 7 → CBox := ![⟨⟨(-3133),3133⟩,⟨(-3133),3133⟩⟩,⟨⟨(-34119),34809⟩,⟨(-34145),34782⟩⟩,⟨⟨(-8303),8348⟩,⟨(-8407),8244⟩⟩,⟨⟨(-370),357⟩,⟨(-356),371⟩⟩,⟨⟨4864593917,4864593958⟩,⟨2105046889,2105046930⟩⟩,⟨⟨63219253415982381898,63219253415982384526⟩,⟨(-10483898199503395770),(-10483898199503393143)⟩⟩,⟨⟨(-107744747142501816369492633),(-107744747142501815142591661)⟩,⟨(-22237945050918130674032227),(-22237945050918129447701604)⟩⟩]
lemma ha31_1_11_eq (j : Fin 7) : ha31_1_11 j = ((ha31_1_10 j).mul (piI.mul (atomPoints j).z)).scale 1 11 := by fin_cases j <;> decide +kernel
lemma ha31_1_11_contains (j : Fin 7) : (ha31_1_11 j).Contains (fullFactor true 31 11 ((j.val:ℝ)/6)) := by
  rw [ha31_1_11_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha31_1_10 j) true 31 10 j (ha31_1_10_contains j)
noncomputable def hk31_1_12 (j : Fin 6) (i k : Fin 16) : CBox := (kernel31_0 j i k).mul (mpower1_12 j i k)
lemma hk31_1_12_contains (j : Fin 6) (i k : Fin 16) :
    (hk31_1_12 j i k).Contains (fullFactor true 31 12 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk31_1_12,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel31_0 j i k) (mpower1_12 j i k) (quadraturePoint j.val (16*i.val+k.val)) 31 12 (kernel31_0_contains j i k) (mpower1_12_contains j i k)
noncomputable def ha31_1_12 : Fin 7 → CBox := ![⟨⟨(-2406),2406⟩,⟨(-2406),2406⟩⟩,⟨⟨(-32817),32574⟩,⟨(-33006),32385⟩⟩,⟨⟨(-7034),6945⟩,⟨(-6966),7013⟩⟩,⟨⟨(-236),246⟩,⟨(-240),242⟩⟩,⟨⟨196141668,196141690⟩,⟨(-2138688999),(-2138688978)⟩⟩,⟨⟨(-7279622200052017099),(-7279622200052016050)⟩,⟨(-20907125268850722394),(-20907125268850721344)⟩⟩,⟨⟨(-5005850506363761899146913),(-5005850506363761510895985)⟩,⟨32770398415280101573530209,32770398415280101962021486⟩⟩]
lemma ha31_1_12_eq (j : Fin 7) : ha31_1_12 j = ((ha31_1_11 j).mul (piI.mul (atomPoints j).z)).scale 1 12 := by fin_cases j <;> decide +kernel
lemma ha31_1_12_contains (j : Fin 7) : (ha31_1_12 j).Contains (fullFactor true 31 12 ((j.val:ℝ)/6)) := by
  rw [ha31_1_12_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha31_1_11 j) true 31 11 j (ha31_1_11_contains j)
noncomputable def hk31_1_13 (j : Fin 6) (i k : Fin 16) : CBox := (kernel31_0 j i k).mul (mpower1_13 j i k)
lemma hk31_1_13_contains (j : Fin 6) (i k : Fin 16) :
    (hk31_1_13 j i k).Contains (fullFactor true 31 13 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk31_1_13,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel31_0 j i k) (mpower1_13 j i k) (quadraturePoint j.val (16*i.val+k.val)) 31 13 (kernel31_0_contains j i k) (mpower1_13_contains j i k)
noncomputable def ha31_1_13 : Fin 7 → CBox := ![⟨⟨(-1706),1706⟩,⟨(-1706),1706⟩⟩,⟨⟨(-28649),28615⟩,⟨(-28414),28850⟩⟩,⟨⟨(-5390),5443⟩,⟨(-5408),5425⟩⟩,⟨⟨(-148),147⟩,⟨(-150),145⟩⟩,⟨⟨(-782918819),(-782918808)⟩,⟨179592589,179592600⟩⟩,⟨⟨(-6175747804123556992),(-6175747804123556604)⟩,⟨3420338874787397377,3420338874787397765⟩⟩,⟨⟨9174979024031312883405940,9174979024031312996954784⟩,⟨917142223173749072919493,917142223173749186381775⟩⟩]
lemma ha31_1_13_eq (j : Fin 7) : ha31_1_13 j = ((ha31_1_12 j).mul (piI.mul (atomPoints j).z)).scale 1 13 := by fin_cases j <;> decide +kernel
lemma ha31_1_13_contains (j : Fin 7) : (ha31_1_13 j).Contains (fullFactor true 31 13 ((j.val:ℝ)/6)) := by
  rw [ha31_1_13_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha31_1_12 j) true 31 12 j (ha31_1_12_contains j)
noncomputable def hk31_1_14 (j : Fin 6) (i k : Fin 16) : CBox := (kernel31_0 j i k).mul (mpower1_14 j i k)
lemma hk31_1_14_contains (j : Fin 6) (i k : Fin 16) :
    (hk31_1_14 j i k).Contains (fullFactor true 31 14 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk31_1_14,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel31_0 j i k) (mpower1_14 j i k) (quadraturePoint j.val (16*i.val+k.val)) 31 14 (kernel31_0_contains j i k) (mpower1_14_contains j i k)
noncomputable def ha31_1_14 : Fin 7 → CBox := ![⟨⟨(-1123),1123⟩,⟨(-1123),1123⟩⟩,⟨⟨(-23215),23350⟩,⟨(-23397),23168⟩⟩,⟨⟨(-3904),3892⟩,⟨(-3911),3885⟩⟩,⟨⟨(-85),83⟩,⟨(-83),85⟩⟩,⟨⟨144008349,144008355⟩,⟨238923544,238923550⟩⟩,⟨⟨1308764795808281890,1308764795808282023⟩,⟨1630056867210863085,1630056867210863219⟩⟩,⟨⟨113500561763983995629020,113500561763984026418501⟩,⟨(-2378807359343961110033518),(-2378807359343961079216443)⟩⟩]
lemma ha31_1_14_eq (j : Fin 7) : ha31_1_14 j = ((ha31_1_13 j).mul (piI.mul (atomPoints j).z)).scale 1 14 := by fin_cases j <;> decide +kernel
lemma ha31_1_14_contains (j : Fin 7) : (ha31_1_14 j).Contains (fullFactor true 31 14 ((j.val:ℝ)/6)) := by
  rw [ha31_1_14_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha31_1_13 j) true 31 13 j (ha31_1_13_contains j)
noncomputable def hk31_1_15 (j : Fin 6) (i k : Fin 16) : CBox := (kernel31_0 j i k).mul (mpower1_15 j i k)
lemma hk31_1_15_contains (j : Fin 6) (i k : Fin 16) :
    (hk31_1_15 j i k).Contains (fullFactor true 31 15 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk31_1_15,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel31_0 j i k) (mpower1_15 j i k) (quadraturePoint j.val (16*i.val+k.val)) 31 15 (kernel31_0_contains j i k) (mpower1_15_contains j i k)
noncomputable def ha31_1_15 : Fin 7 → CBox := ![⟨⟨(-690),690⟩,⟨(-690),690⟩⟩,⟨⟨(-17733),17608⟩,⟨(-17629),17712⟩⟩,⟨⟨(-2621),2616⟩,⟨(-2612),2625⟩⟩,⟨⟨(-44),45⟩,⟨(-45),45⟩⟩,⟨⟨59040013,59040016⟩,⟨(-68491426),(-68491423)⟩⟩,⟨⟨382499681608716706,382499681608716750⟩,⟨(-432983259856220839),(-432983259856220796)⟩⟩,⟨⟨(-574083179772655789504230),(-574083179772655781698221)⟩,⟨2454876831709580220275,2454876831709588018341⟩⟩]
lemma ha31_1_15_eq (j : Fin 7) : ha31_1_15 j = ((ha31_1_14 j).mul (piI.mul (atomPoints j).z)).scale 1 15 := by fin_cases j <;> decide +kernel
lemma ha31_1_15_contains (j : Fin 7) : (ha31_1_15 j).Contains (fullFactor true 31 15 ((j.val:ℝ)/6)) := by
  rw [ha31_1_15_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha31_1_14 j) true 31 14 j (ha31_1_14_contains j)
noncomputable def hk31_1_16 (j : Fin 6) (i k : Fin 16) : CBox := (kernel31_0 j i k).mul (mpower1_16 j i k)
lemma hk31_1_16_contains (j : Fin 6) (i k : Fin 16) :
    (hk31_1_16 j i k).Contains (fullFactor true 31 16 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk31_1_16,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel31_0 j i k) (mpower1_16 j i k) (quadraturePoint j.val (16*i.val+k.val)) 31 16 (kernel31_0_contains j i k) (mpower1_16_contains j i k)
noncomputable def ha31_1_16 : Fin 7 → CBox := ![⟨⟨(-398),398⟩,⟨(-398),398⟩⟩,⟨⟨(-12534),12613⟩,⟨(-12579),12568⟩⟩,⟨⟨(-1646),1652⟩,⟨(-1650),1648⟩⟩,⟨⟨(-23),23⟩,⟨(-23),23⟩⟩,⟨⟨(-25368520),(-25368518)⟩,⟨(-10560958),(-10560956)⟩⟩,⟨⟨(-127391328039926045),(-127391328039926031)⟩,⟨(-78604508945456492),(-78604508945456478)⟩⟩,⟨⟨7291384269136156033132,7291384269136157884705⟩,⟨129535521876882595339194,129535521876882597192856⟩⟩]
lemma ha31_1_16_eq (j : Fin 7) : ha31_1_16 j = ((ha31_1_15 j).mul (piI.mul (atomPoints j).z)).scale 1 16 := by fin_cases j <;> decide +kernel
lemma ha31_1_16_contains (j : Fin 7) : (ha31_1_16 j).Contains (fullFactor true 31 16 ((j.val:ℝ)/6)) := by
  rw [ha31_1_16_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha31_1_15 j) true 31 15 j (ha31_1_15_contains j)
noncomputable def hk31_1_17 (j : Fin 6) (i k : Fin 16) : CBox := (kernel31_0 j i k).mul (mpower1_17 j i k)
lemma hk31_1_17_contains (j : Fin 6) (i k : Fin 16) :
    (hk31_1_17 j i k).Contains (fullFactor true 31 17 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk31_1_17,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel31_0 j i k) (mpower1_17 j i k) (quadraturePoint j.val (16*i.val+k.val)) 31 17 (kernel31_0_contains j i k) (mpower1_17_contains j i k)
noncomputable def ha31_1_17 : Fin 7 → CBox := ![⟨⟨(-216),216⟩,⟨(-216),216⟩⟩,⟨⟨(-8439),8401⟩,⟨(-8427),8414⟩⟩,⟨⟨(-979),976⟩,⟨(-978),977⟩⟩,⟨⟨(-11),11⟩,⟨(-11),11⟩⟩,⟨⟨(-608775),(-608773)⟩,⟨7835640,7835642⟩⟩,⟨⟨(-13611784411086881),(-13611784411086876)⟩,⟨33870167021284595,33870167021284600⟩⟩,⟨⟨27434530278979347766012,27434530278979348180295⟩,⟨(-2979570462312354406720),(-2979570462312353992936)⟩⟩]
lemma ha31_1_17_eq (j : Fin 7) : ha31_1_17 j = ((ha31_1_16 j).mul (piI.mul (atomPoints j).z)).scale 1 17 := by fin_cases j <;> decide +kernel
lemma ha31_1_17_contains (j : Fin 7) : (ha31_1_17 j).Contains (fullFactor true 31 17 ((j.val:ℝ)/6)) := by
  rw [ha31_1_17_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha31_1_16 j) true 31 16 j (ha31_1_16_contains j)
noncomputable def hk31_1_18 (j : Fin 6) (i k : Fin 16) : CBox := (kernel31_0 j i k).mul (mpower1_18 j i k)
lemma hk31_1_18_contains (j : Fin 6) (i k : Fin 16) :
    (hk31_1_18 j i k).Contains (fullFactor true 31 18 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk31_1_18,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel31_0 j i k) (mpower1_18 j i k) (quadraturePoint j.val (16*i.val+k.val)) 31 18 (kernel31_0_contains j i k) (mpower1_18_contains j i k)
noncomputable def ha31_1_18 : Fin 7 → CBox := ![⟨⟨(-111),111⟩,⟨(-111),111⟩⟩,⟨⟨(-5319),5333⟩,⟨(-5319),5333⟩⟩,⟨⟨(-547),548⟩,⟨(-547),548⟩⟩,⟨⟨(-5),5⟩,⟨(-5),5⟩⟩,⟨⟨2062393,2062395⟩,⟨(-503404),(-503402)⟩⟩,⟨⟨8219805971022006,8219805971022009⟩,⟨1764068871831757,1764068871831759⟩⟩,⟨⟨(-883932238299380975839),(-883932238299380888504)⟩,⟨(-5472628847510540996826),(-5472628847510540909381)⟩⟩]
lemma ha31_1_18_eq (j : Fin 7) : ha31_1_18 j = ((ha31_1_17 j).mul (piI.mul (atomPoints j).z)).scale 1 18 := by fin_cases j <;> decide +kernel
lemma ha31_1_18_contains (j : Fin 7) : (ha31_1_18 j).Contains (fullFactor true 31 18 ((j.val:ℝ)/6)) := by
  rw [ha31_1_18_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha31_1_17 j) true 31 17 j (ha31_1_17_contains j)
noncomputable def hk31_1_19 (j : Fin 6) (i k : Fin 16) : CBox := (kernel31_0 j i k).mul (mpower1_19 j i k)
lemma hk31_1_19_contains (j : Fin 6) (i k : Fin 16) :
    (hk31_1_19 j i k).Contains (fullFactor true 31 19 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk31_1_19,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel31_0 j i k) (mpower1_19 j i k) (quadraturePoint j.val (16*i.val+k.val)) 31 19 (kernel31_0_contains j i k) (mpower1_19_contains j i k)
noncomputable def ha31_1_19 : Fin 7 → CBox := ![⟨⟨(-54),54⟩,⟨(-54),54⟩⟩,⟨⟨(-3193),3190⟩,⟨(-3196),3187⟩⟩,⟨⟨(-291),291⟩,⟨(-291),291⟩⟩,⟨⟨(-3),3⟩,⟨(-3),3⟩⟩,⟨⟨(-286894),(-286893)⟩,⟨(-461338),(-461336)⟩⟩,⟨⟨74604885519316,74604885519317⟩,⟨(-1832778071714825),(-1832778071714823)⟩⟩,⟨⟨(-1031359281415900878288),(-1031359281415900860802)⟩,⟨222079800147427553724,222079800147427571189⟩⟩]
lemma ha31_1_19_eq (j : Fin 7) : ha31_1_19 j = ((ha31_1_18 j).mul (piI.mul (atomPoints j).z)).scale 1 19 := by fin_cases j <;> decide +kernel
lemma ha31_1_19_contains (j : Fin 7) : (ha31_1_19 j).Contains (fullFactor true 31 19 ((j.val:ℝ)/6)) := by
  rw [ha31_1_19_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha31_1_18 j) true 31 18 j (ha31_1_18_contains j)
noncomputable def hk31_1_20 (j : Fin 6) (i k : Fin 16) : CBox := (kernel31_0 j i k).mul (mpower1_20 j i k)
lemma hk31_1_20_contains (j : Fin 6) (i k : Fin 16) :
    (hk31_1_20 j i k).Contains (fullFactor true 31 20 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk31_1_20,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel31_0 j i k) (mpower1_20 j i k) (quadraturePoint j.val (16*i.val+k.val)) 31 20 (kernel31_0_contains j i k) (mpower1_20_contains j i k)
noncomputable def ha31_1_20 : Fin 7 → CBox := ![⟨⟨(-25),25⟩,⟨(-25),25⟩⟩,⟨⟨(-1817),1817⟩,⟨(-1815),1819⟩⟩,⟨⟨(-147),147⟩,⟨(-147),147⟩⟩,⟨⟨(-2),2⟩,⟨(-2),2⟩⟩,⟨⟨(-84832),(-84831)⟩,⟨101226,101227⟩⟩,⟨⟨(-376999279622250),(-376999279622249)⟩,⟨49302589220519,49302589220520⟩⟩,⟨⟨49779886621991705999,49779886621991709318⟩,⟨184128227571140357439,184128227571140360762⟩⟩]
lemma ha31_1_20_eq (j : Fin 7) : ha31_1_20 j = ((ha31_1_19 j).mul (piI.mul (atomPoints j).z)).scale 1 20 := by fin_cases j <;> decide +kernel
lemma ha31_1_20_contains (j : Fin 7) : (ha31_1_20 j).Contains (fullFactor true 31 20 ((j.val:ℝ)/6)) := by
  rw [ha31_1_20_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha31_1_19 j) true 31 19 j (ha31_1_19_contains j)
noncomputable def hk31_1_21 (j : Fin 6) (i k : Fin 16) : CBox := (kernel31_0 j i k).mul (mpower1_21 j i k)
lemma hk31_1_21_contains (j : Fin 6) (i k : Fin 16) :
    (hk31_1_21 j i k).Contains (fullFactor true 31 21 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk31_1_21,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel31_0 j i k) (mpower1_21 j i k) (quadraturePoint j.val (16*i.val+k.val)) 31 21 (kernel31_0_contains j i k) (mpower1_21_contains j i k)
noncomputable def ha31_1_21 : Fin 7 → CBox := ![⟨⟨(-11),11⟩,⟨(-11),11⟩⟩,⟨⟨(-985),986⟩,⟨(-986),985⟩⟩,⟨⟨(-71),71⟩,⟨(-71),71⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨28391,28392⟩,⟨11358,11359⟩⟩,⟨⟨22235150667872,22235150667873⟩,⟨71687123886815,71687123886816⟩⟩,⟨⟨31216404187103377246,31216404187103377848⟩,⟨(-10206230554739693482),(-10206230554739692880)⟩⟩]
lemma ha31_1_21_eq (j : Fin 7) : ha31_1_21 j = ((ha31_1_20 j).mul (piI.mul (atomPoints j).z)).scale 1 21 := by fin_cases j <;> decide +kernel
lemma ha31_1_21_contains (j : Fin 7) : (ha31_1_21 j).Contains (fullFactor true 31 21 ((j.val:ℝ)/6)) := by
  rw [ha31_1_21_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha31_1_20 j) true 31 20 j (ha31_1_20_contains j)
noncomputable def hk31_1_22 (j : Fin 6) (i k : Fin 16) : CBox := (kernel31_0 j i k).mul (mpower1_22 j i k)
lemma hk31_1_22_contains (j : Fin 6) (i k : Fin 16) :
    (hk31_1_22 j i k).Contains (fullFactor true 31 22 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk31_1_22,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel31_0 j i k) (mpower1_22 j i k) (quadraturePoint j.val (16*i.val+k.val)) 31 22 (kernel31_0_contains j i k) (mpower1_22_contains j i k)
noncomputable def ha31_1_22 : Fin 7 → CBox := ![⟨⟨(-5),5⟩,⟨(-5),5⟩⟩,⟨⟨(-511),510⟩,⟨(-510),511⟩⟩,⟨⟨(-33),33⟩,⟨(-33),33⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨429,430⟩,⟨(-6745),(-6744)⟩⟩,⟨⟨12600127027732,12600127027734⟩,⟨(-6423944335563),(-6423944335562)⟩⟩,⟨⟨(-1941662418340123829),(-1941662418340123724)⟩,⟨(-5036672282196954575),(-5036672282196954470)⟩⟩]
lemma ha31_1_22_eq (j : Fin 7) : ha31_1_22 j = ((ha31_1_21 j).mul (piI.mul (atomPoints j).z)).scale 1 22 := by fin_cases j <;> decide +kernel
lemma ha31_1_22_contains (j : Fin 7) : (ha31_1_22 j).Contains (fullFactor true 31 22 ((j.val:ℝ)/6)) := by
  rw [ha31_1_22_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha31_1_21 j) true 31 21 j (ha31_1_21_contains j)
noncomputable def hk31_1_23 (j : Fin 6) (i k : Fin 16) : CBox := (kernel31_0 j i k).mul (mpower1_23 j i k)
lemma hk31_1_23_contains (j : Fin 6) (i k : Fin 16) :
    (hk31_1_23 j i k).Contains (fullFactor true 31 23 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk31_1_23,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel31_0 j i k) (mpower1_23 j i k) (quadraturePoint j.val (16*i.val+k.val)) 31 23 (kernel31_0_contains j i k) (mpower1_23_contains j i k)
noncomputable def ha31_1_23 : Fin 7 → CBox := ![⟨⟨(-3),3⟩,⟨(-3),3⟩⟩,⟨⟨(-253),253⟩,⟨(-253),253⟩⟩,⟨⟨(-15),15⟩,⟨(-15),15⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1384),(-1382)⟩,⟨357,359⟩⟩,⟨⟨(-1526871620800),(-1526871620798)⟩,⟨(-2041340551199),(-2041340551198)⟩⟩,⟨⟨(-774911404100471603),(-774911404100471585)⟩,⟨345962886881747506,345962886881747524⟩⟩]
lemma ha31_1_23_eq (j : Fin 7) : ha31_1_23 j = ((ha31_1_22 j).mul (piI.mul (atomPoints j).z)).scale 1 23 := by fin_cases j <;> decide +kernel
lemma ha31_1_23_contains (j : Fin 7) : (ha31_1_23 j).Contains (fullFactor true 31 23 ((j.val:ℝ)/6)) := by
  rw [ha31_1_23_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha31_1_22 j) true 31 22 j (ha31_1_22_contains j)
noncomputable def hk31_1_24 (j : Fin 6) (i k : Fin 16) : CBox := (kernel31_0 j i k).mul (mpower1_24 j i k)
lemma hk31_1_24_contains (j : Fin 6) (i k : Fin 16) :
    (hk31_1_24 j i k).Contains (fullFactor true 31 24 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk31_1_24,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel31_0 j i k) (mpower1_24 j i k) (quadraturePoint j.val (16*i.val+k.val)) 31 24 (kernel31_0_contains j i k) (mpower1_24_contains j i k)
noncomputable def ha31_1_24 : Fin 7 → CBox := ![⟨⟨(-2),2⟩,⟨(-2),2⟩⟩,⟨⟨(-121),121⟩,⟨(-121),121⟩⟩,⟨⟨(-7),7⟩,⟨(-7),7⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨155,157⟩,⟨243,244⟩⟩,⟨⟨(-302670712232),(-302670712231)⟩,⟨319810375675,319810375677⟩⟩,⟨⟨58116196097043786,58116196097043790⟩,⟨113885943591244614,113885943591244618⟩⟩]
lemma ha31_1_24_eq (j : Fin 7) : ha31_1_24 j = ((ha31_1_23 j).mul (piI.mul (atomPoints j).z)).scale 1 24 := by fin_cases j <;> decide +kernel
lemma ha31_1_24_contains (j : Fin 7) : (ha31_1_24 j).Contains (fullFactor true 31 24 ((j.val:ℝ)/6)) := by
  rw [ha31_1_24_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha31_1_23 j) true 31 23 j (ha31_1_23_contains j)
noncomputable def hk31_1_25 (j : Fin 6) (i k : Fin 16) : CBox := (kernel31_0 j i k).mul (mpower1_25 j i k)
lemma hk31_1_25_contains (j : Fin 6) (i k : Fin 16) :
    (hk31_1_25 j i k).Contains (fullFactor true 31 25 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk31_1_25,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel31_0 j i k) (mpower1_25 j i k) (quadraturePoint j.val (16*i.val+k.val)) 31 25 (kernel31_0_contains j i k) (mpower1_25_contains j i k)
noncomputable def ha31_1_25 : Fin 7 → CBox := ![⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-56),56⟩,⟨(-56),56⟩⟩,⟨⟨(-3),3⟩,⟨(-3),3⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨35,36⟩,⟨(-44),(-43)⟩⟩,⟨⟨60787702719,60787702721⟩,⟨40450216126,40450216127⟩⟩,⟨⟨16013297387049045,16013297387049046⟩,⟨(-9249753718951410),(-9249753718951409)⟩⟩]
lemma ha31_1_25_eq (j : Fin 7) : ha31_1_25 j = ((ha31_1_24 j).mul (piI.mul (atomPoints j).z)).scale 1 25 := by fin_cases j <;> decide +kernel
lemma ha31_1_25_contains (j : Fin 7) : (ha31_1_25 j).Contains (fullFactor true 31 25 ((j.val:ℝ)/6)) := by
  rw [ha31_1_25_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha31_1_24 j) true 31 24 j (ha31_1_24_contains j)
noncomputable def hk31_1_26 (j : Fin 6) (i k : Fin 16) : CBox := (kernel31_0 j i k).mul (mpower1_26 j i k)
lemma hk31_1_26_contains (j : Fin 6) (i k : Fin 16) :
    (hk31_1_26 j i k).Contains (fullFactor true 31 26 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk31_1_26,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel31_0 j i k) (mpower1_26 j i k) (quadraturePoint j.val (16*i.val+k.val)) 31 26 (kernel31_0_contains j i k) (mpower1_26_contains j i k)
noncomputable def ha31_1_26 : Fin 7 → CBox := ![⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-25),25⟩,⟨(-25),25⟩⟩,⟨⟨(-2),2⟩,⟨(-2),2⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-10),(-9)⟩,⟨(-4),(-3)⟩⟩,⟨⟨4709154710,4709154711⟩,⟨(-10647117388),(-10647117387)⟩⟩,⟨⟨(-1400306618805461),(-1400306618805460)⟩,⟨(-2157214482656558),(-2157214482656557)⟩⟩]
lemma ha31_1_26_eq (j : Fin 7) : ha31_1_26 j = ((ha31_1_25 j).mul (piI.mul (atomPoints j).z)).scale 1 26 := by fin_cases j <;> decide +kernel
lemma ha31_1_26_contains (j : Fin 7) : (ha31_1_26 j).Contains (fullFactor true 31 26 ((j.val:ℝ)/6)) := by
  rw [ha31_1_26_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha31_1_25 j) true 31 25 j (ha31_1_25_contains j)
noncomputable def hk31_1_27 (j : Fin 6) (i k : Fin 16) : CBox := (kernel31_0 j i k).mul (mpower1_27 j i k)
lemma hk31_1_27_contains (j : Fin 6) (i k : Fin 16) :
    (hk31_1_27 j i k).Contains (fullFactor true 31 27 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk31_1_27,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel31_0 j i k) (mpower1_27 j i k) (quadraturePoint j.val (16*i.val+k.val)) 31 27 (kernel31_0_contains j i k) (mpower1_27_contains j i k)
noncomputable def ha31_1_27 : Fin 7 → CBox := ![⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-11),11⟩,⟨(-11),11⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨1,2⟩⟩,⟨⟨(-1733826218),(-1733826217)⟩,⟨(-434795285),(-434795284)⟩⟩,⟨⟨(-278771014714258),(-278771014714257)⟩,⟨202281891157974,202281891157975⟩⟩]
lemma ha31_1_27_eq (j : Fin 7) : ha31_1_27 j = ((ha31_1_26 j).mul (piI.mul (atomPoints j).z)).scale 1 27 := by fin_cases j <;> decide +kernel
lemma ha31_1_27_contains (j : Fin 7) : (ha31_1_27 j).Contains (fullFactor true 31 27 ((j.val:ℝ)/6)) := by
  rw [ha31_1_27_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha31_1_26 j) true 31 26 j (ha31_1_26_contains j)
noncomputable def hk31_1_28 (j : Fin 6) (i k : Fin 16) : CBox := (kernel31_0 j i k).mul (mpower1_28 j i k)
lemma hk31_1_28_contains (j : Fin 6) (i k : Fin 16) :
    (hk31_1_28 j i k).Contains (fullFactor true 31 28 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk31_1_28,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel31_0 j i k) (mpower1_28 j i k) (quadraturePoint j.val (16*i.val+k.val)) 31 28 (kernel31_0_contains j i k) (mpower1_28_contains j i k)
noncomputable def ha31_1_28 : Fin 7 → CBox := ![⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-5),5⟩,⟨(-5),5⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨0,1⟩,⟨(-1),1⟩⟩,⟨⟨(-19825890),(-19825889)⟩,⟨263907924,263907925⟩⟩,⟨⟨27956819447982,27956819447984⟩,⟨34595222992317,34595222992318⟩⟩]
lemma ha31_1_28_eq (j : Fin 7) : ha31_1_28 j = ((ha31_1_27 j).mul (piI.mul (atomPoints j).z)).scale 1 28 := by fin_cases j <;> decide +kernel
lemma ha31_1_28_contains (j : Fin 7) : (ha31_1_28 j).Contains (fullFactor true 31 28 ((j.val:ℝ)/6)) := by
  rw [ha31_1_28_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha31_1_27 j) true 31 27 j (ha31_1_27_contains j)
noncomputable def hk31_1_29 (j : Fin 6) (i k : Fin 16) : CBox := (kernel31_0 j i k).mul (mpower1_29 j i k)
lemma hk31_1_29_contains (j : Fin 6) (i k : Fin 16) :
    (hk31_1_29 j i k).Contains (fullFactor true 31 29 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk31_1_29,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel31_0 j i k) (mpower1_29 j i k) (quadraturePoint j.val (16*i.val+k.val)) 31 29 (kernel31_0_contains j i k) (mpower1_29_contains j i k)
noncomputable def ha31_1_29 : Fin 7 → CBox := ![⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-2),2⟩,⟨(-2),2⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨37658809,37658810⟩,⟨(-3616451),(-3616450)⟩⟩,⟨⟨4126713975227,4126713975228⟩,⟨(-3705133242665),(-3705133242664)⟩⟩]
lemma ha31_1_29_eq (j : Fin 7) : ha31_1_29 j = ((ha31_1_28 j).mul (piI.mul (atomPoints j).z)).scale 1 29 := by fin_cases j <;> decide +kernel
lemma ha31_1_29_contains (j : Fin 7) : (ha31_1_29 j).Contains (fullFactor true 31 29 ((j.val:ℝ)/6)) := by
  rw [ha31_1_29_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha31_1_28 j) true 31 28 j (ha31_1_28_contains j)
noncomputable def hk31_1_30 (j : Fin 6) (i k : Fin 16) : CBox := (kernel31_0 j i k).mul (mpower1_30 j i k)
lemma hk31_1_30_contains (j : Fin 6) (i k : Fin 16) :
    (hk31_1_30 j i k).Contains (fullFactor true 31 30 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk31_1_30,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel31_0 j i k) (mpower1_30 j i k) (quadraturePoint j.val (16*i.val+k.val)) 31 30 (kernel31_0_contains j i k) (mpower1_30_contains j i k)
noncomputable def ha31_1_30 : Fin 7 → CBox := ![⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1376586),(-1376585)⟩,⟨(-5043344),(-5043343)⟩⟩,⟨⟨(-471807317998),(-471807317997)⟩,⟨(-473531544081),(-473531544080)⟩⟩]
lemma ha31_1_30_eq (j : Fin 7) : ha31_1_30 j = ((ha31_1_29 j).mul (piI.mul (atomPoints j).z)).scale 1 30 := by fin_cases j <;> decide +kernel
lemma ha31_1_30_contains (j : Fin 7) : (ha31_1_30 j).Contains (fullFactor true 31 30 ((j.val:ℝ)/6)) := by
  rw [ha31_1_30_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha31_1_29 j) true 31 29 j (ha31_1_29_contains j)
end SharpPlanar.CachedData

end OAI
