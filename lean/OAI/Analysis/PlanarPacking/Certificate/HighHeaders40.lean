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
noncomputable def hk40_0_0 (j : Fin 6) (i k : Fin 16) : CBox := (power40 j i k).conj.mul (mpower0_0 j i k)
lemma hk40_0_0_contains (j : Fin 6) (i k : Fin 16) :
    (hk40_0_0 j i k).Contains (fullFactor false 40 0 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk40_0_0,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power40 j i k) (mpower0_0 j i k) (quadraturePoint j.val (16*i.val+k.val)) 40 0 (power40_contains j i k) (mpower0_0_contains j i k)
noncomputable def ha40_0_0 : Fin 7 → CBox := ![⟨⟨999999999999999999999999999521,1000000000000000000000000000639⟩,⟨(-639),639⟩⟩,⟨⟨(-500000000000000000166688152963),(-499999999999999999860523712926)⟩,⟨866025403784438646602883133868,866025403784438646908852429614⟩⟩,⟨⟨(-500000000000000000390901517984),(-499999999999999999554674750144)⟩,⟨(-866025403784438647197618749590),(-866025403784438646361249148188)⟩⟩,⟨⟨999999999999999999869333001521,1000000000000000000130666998519⟩,⟨(-83534664159),177799332879⟩⟩,⟨⟨(-500000000000000001197951372854),(-499999999999999998910896090953)⟩,⟨866025403784438645588826182762,866025403784438647875777046111⟩⟩,⟨⟨(-500000000000000001371166930146),(-499999999999999998492773740111)⟩,⟨(-866025403784438648242248529504),(-866025403784438645363751702534)⟩⟩,⟨⟨999999999999999999737872088721,1000000000000000000262127911439⟩,⟨(-167863242479),356392580239⟩⟩]
lemma ha40_0_0_eq (j : Fin 7) : ha40_0_0 j = ((atomPoints j).direct.powBin 7 40).conj := by fin_cases j <;> decide +kernel
lemma ha40_0_0_contains (j : Fin 7) : (ha40_0_0 j).Contains (fullFactor false 40 0 ((j.val:ℝ)/6)) := by
  rw [ha40_0_0_eq]
  simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @direct_factor_zero_full ((atomPoints j).direct.powBin 7 40) ((j.val:ℝ)/6) 40 (@direct_power_bin_contains (atomPoints j) ((j.val:ℝ)/6) (atomPoints_contains j) 40 (by norm_num))
noncomputable def hk40_0_1 (j : Fin 6) (i k : Fin 16) : CBox := (power40 j i k).conj.mul (mpower0_1 j i k)
lemma hk40_0_1_contains (j : Fin 6) (i k : Fin 16) :
    (hk40_0_1 j i k).Contains (fullFactor false 40 1 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk40_0_1,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power40 j i k) (mpower0_1 j i k) (quadraturePoint j.val (16*i.val+k.val)) 40 1 (power40_contains j i k) (mpower0_1_contains j i k)
noncomputable def ha40_0_1 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-453449841058554462725570902817),(-453449841058554462563922378516)⟩,⟨(-261799387799149436626444379466),(-261799387799149436465303720195)⟩⟩,⟨⟨906899682117108924874806238945,906899682117108925753537188779⟩,⟨(-523598775598298873487684445727),(-523598775598298872610323155530)⟩⟩,⟨⟨(-279286538993),131215943622⟩,⟨1570796326794896619024748758755,1570796326794896619440251241307⟩⟩,⟨⟨(-1813799364234217852927405792435),(-1813799364234217848131853602127)⟩,⟨(-1047197551196597748665650154879),(-1047197551196597743872319440226)⟩⟩,⟨⟨2267249205292772309575573391331,2267249205292772317118677340526⟩,⟨(-1308996938995747186285539962162),(-1308996938995747178745757545528)⟩⟩,⟨⟨(-1119640311873),527357929380⟩,⟨3141592653589793237636500879625,3141592653589793239293499120878⟩⟩]
lemma ha40_0_1_eq (j : Fin 7) : ha40_0_1 j = ((ha40_0_0 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 1 := by fin_cases j <;> decide +kernel
lemma ha40_0_1_contains (j : Fin 7) : (ha40_0_1 j).Contains (fullFactor false 40 1 ((j.val:ℝ)/6)) := by
  rw [ha40_0_1_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha40_0_0 j) false 40 0 j (ha40_0_0_contains j)
noncomputable def hk40_0_2 (j : Fin 6) (i k : Fin 16) : CBox := (power40 j i k).conj.mul (mpower0_2 j i k)
lemma hk40_0_2_contains (j : Fin 6) (i k : Fin 16) :
    (hk40_0_2 j i k).Contains (fullFactor false 40 2 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk40_0_2,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power40 j i k) (mpower0_2 j i k) (quadraturePoint j.val (16*i.val+k.val)) 40 2 (power40_contains j i k) (mpower0_2_contains j i k)
noncomputable def ha40_0_2 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨68538919452009434833782851245,68538919452009434876187543349⟩,⟨(-118712890786751174428387292750),(-118712890786751174385689933180)⟩⟩,⟨⟨274155677808037739167430945585,274155677808037739627688907517⟩,⟨474851563147004697410269074473,474851563147004697871883023359⟩⟩,⟨⟨(-1233700550136169827521293196204),(-1233700550136169827191031318702)⟩,⟨(-219351134787),103056761130⟩⟩,⟨⟨1096622711232150955257759184990,1096622711232150960280814029957⟩,⟨(-1899406252588018792974899672978),(-1899406252588018787946963164767)⟩⟩,⟨⟨1713472986300235866157366020278,1713472986300235876032372278262⟩,⟨2967822269668779355395811861400,2967822269668779365279158713116⟩⟩,⟨⟨(-4934802200544679310733906387177),(-4934802200544679308115391673042)⟩,⟨(-1758726889222),828371898377⟩⟩]
lemma ha40_0_2_eq (j : Fin 7) : ha40_0_2 j = ((ha40_0_1 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 2 := by fin_cases j <;> decide +kernel
lemma ha40_0_2_contains (j : Fin 7) : (ha40_0_2 j).Contains (fullFactor false 40 2 ((j.val:ℝ)/6)) := by
  rw [ha40_0_2_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha40_0_1 j) false 40 1 j (ha40_0_1_contains j)
noncomputable def hk40_0_3 (j : Fin 6) (i k : Fin 16) : CBox := (power40 j i k).conj.mul (mpower0_3 j i k)
lemma hk40_0_3_contains (j : Fin 6) (i k : Fin 16) :
    (hk40_0_3 j i k).Contains (fullFactor false 40 3 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk40_0_3,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power40 j i k) (mpower0_3 j i k) (quadraturePoint j.val (16*i.val+k.val)) 40 3 (power40_contains j i k) (mpower0_3_contains j i k)
noncomputable def ha40_0_3 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨20719308087892496638515086378,20719308087892496646033133049⟩,⟨11962298101967523212480234155,11962298101967523219919326288⟩⟩,⟨⟨(-165754464703139973223534005212),(-165754464703139973061872726738)⟩,⟨95698384815740185641303369770,95698384815740185802268324076⟩⟩,⟨⟨(-53960393945),114851985601⟩,⟨(-645964097506246253744700684719),(-645964097506246253569719802447)⟩⟩,⟨⟨1326035717625119783312267730938,1326035717625119786826650499706⟩,⟨765587078525921484144689712350,765587078525921487653880473828⟩⟩,⟨⟨(-2589913510986562084741762039793),(-2589913510986562076108670905087)⟩,⟨1495287262745940397469671043471,1495287262745940406091999333501⟩⟩,⟨⟨(-867469023461),1841734491617⟩,⟨(-5167712780049970030636957717517),(-5167712780049970027878406180433)⟩⟩]
lemma ha40_0_3_eq (j : Fin 7) : ha40_0_3 j = ((ha40_0_2 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 3 := by fin_cases j <;> decide +kernel
lemma ha40_0_3_contains (j : Fin 7) : (ha40_0_3 j).Contains (fullFactor false 40 3 ((j.val:ℝ)/6)) := by
  rw [ha40_0_3_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha40_0_2 j) false 40 2 j (ha40_0_2_contains j)
noncomputable def hk40_0_4 (j : Fin 6) (i k : Fin 16) : CBox := (power40 j i k).conj.mul (mpower0_4 j i k)
lemma hk40_0_4_contains (j : Fin 6) (i k : Fin 16) :
    (hk40_0_4 j i k).Contains (fullFactor false 40 4 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk40_0_4,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power40 j i k) (mpower0_4 j i k) (quadraturePoint j.val (16*i.val+k.val)) 40 4 (power40_contains j i k) (mpower0_4_contains j i k)
noncomputable def ha40_0_4 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1565861159883012430392017439),(-1565861159883012429413258264)⟩,⟨2712151086516110562883115754,2712151086516110563875858808⟩⟩,⟨⟨(-25053778558128198897507063006),(-25053778558128198855286787857)⟩,⟨(-43394417384257769036483115789),(-43394417384257768994022163331)⟩⟩,⟨⟨253669507901048013602563367825,253669507901048013672085654731⟩,⟨(-21190197151),45102269277⟩⟩,⟨⟨(-400860456930051183007141755261),(-400860456930051181168457790744)⟩,⟨694310678148124303285086967587,694310678148124305127423541829⟩⟩,⟨⟨(-978663224926882771352569067744),(-978663224926882765706153216611)⟩,⟨(-1695094429072569105032303208981),(-1695094429072569099376562621129)⟩⟩,⟨⟨4058712126416768217107451884291,4058712126416768219286932477105⟩,⟨(-681308577831),1446494887182⟩⟩]
lemma ha40_0_4_eq (j : Fin 7) : ha40_0_4 j = ((ha40_0_3 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 4 := by fin_cases j <;> decide +kernel
lemma ha40_0_4_contains (j : Fin 7) : (ha40_0_4 j).Contains (fullFactor false 40 4 ((j.val:ℝ)/6)) := by
  rw [ha40_0_4_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha40_0_3 j) false 40 3 j (ha40_0_3_contains j)
noncomputable def hk40_0_5 (j : Fin 6) (i k : Fin 16) : CBox := (power40 j i k).conj.mul (mpower0_5 j i k)
lemma hk40_0_5_contains (j : Fin 6) (i k : Fin 16) :
    (hk40_0_5 j i k).Contains (fullFactor false 40 5 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk40_0_5,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power40 j i k) (mpower0_5 j i k) (quadraturePoint j.val (16*i.val+k.val)) 40 5 (power40_contains j i k) (mpower0_5_contains j i k)
noncomputable def ha40_0_5 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-284015797627486289538145042),(-284015797627486289433281181)⟩,⟨(-163976597214335483843634275),(-163976597214335483740616899)⟩⟩,⟨⟨9088505524079561259329169402,9088505524079561268251100102⟩,⟨(-5247251110858735485349304449),(-5247251110858735476490008179)⟩⟩,⟨⟨(-14169295783),6657096770⟩,⟨79692626246167045109757080349,79692626246167045131851820439⟩⟩,⟨⟨(-290832176770545960811777083215),(-290832176770545960039135196032)⟩,⟨(-167912035547479535802204510180),(-167912035547479535031483891543)⟩⟩,⟨⟨887549367585894653209075219067,887549367585894656173239223352⟩,⟨(-512426866294798388245771679097),(-512426866294798385287684147549)⟩⟩,⟨⟨(-908859542206),428078804589⟩,⟨2550164039877345443176979678730,2550164039877345444554505146789⟩⟩]
lemma ha40_0_5_eq (j : Fin 7) : ha40_0_5 j = ((ha40_0_4 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 5 := by fin_cases j <;> decide +kernel
lemma ha40_0_5_contains (j : Fin 7) : (ha40_0_5 j).Contains (fullFactor false 40 5 ((j.val:ℝ)/6)) := by
  rw [ha40_0_5_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha40_0_4 j) false 40 4 j (ha40_0_4_contains j)
noncomputable def hk40_0_6 (j : Fin 6) (i k : Fin 16) : CBox := (power40 j i k).conj.mul (mpower0_6 j i k)
lemma hk40_0_6_contains (j : Fin 6) (i k : Fin 16) :
    (hk40_0_6 j i k).Contains (fullFactor false 40 6 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk40_0_6,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power40 j i k) (mpower0_6 j i k) (quadraturePoint j.val (16*i.val+k.val)) 40 6 (power40_contains j i k) (mpower0_6_contains j i k)
noncomputable def ha40_0_6 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨14309657588033580841650470,14309657588033580850685982⟩,⟨(-24785053981387676531406181),(-24785053981387676522176189)⟩⟩,⟨⟨915818085634149173305426110,915818085634149174854580144⟩,⟨1586243454808811296976690569,1586243454808811298538910403⟩⟩,⟨⟨(-20863480763352960876070939696),(-20863480763352960870220139744)⟩,⟨(-3709512962),1742823859⟩⟩,⟨⟨58612357480585547016080501268,58612357480585547285299318362⟩,⟨(-101519581107763923185987178760),(-101519581107763922915961134493)⟩⟩,⟨⟨223588399813024700039162551393,223588399813024701330583430068⟩,⟨387266468459182445104892130677,387266468459182446399485374230⟩⟩,⟨⟨(-1335262768854589496244075003089),(-1335262768854589495518554081257)⟩,⟨(-475877743490),224141537943⟩⟩]
lemma ha40_0_6_eq (j : Fin 7) : ha40_0_6 j = ((ha40_0_5 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 6 := by fin_cases j <;> decide +kernel
lemma ha40_0_6_contains (j : Fin 7) : (ha40_0_6 j).Contains (fullFactor false 40 6 ((j.val:ℝ)/6)) := by
  rw [ha40_0_6_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha40_0_5 j) false 40 5 j (ha40_0_5_contains j)
noncomputable def hk40_0_7 (j : Fin 6) (i k : Fin 16) : CBox := (power40 j i k).conj.mul (mpower0_7 j i k)
lemma hk40_0_7_contains (j : Fin 6) (i k : Fin 16) :
    (hk40_0_7 j i k).Contains (fullFactor false 40 7 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk40_0_7,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power40 j i k) (mpower0_7 j i k) (quadraturePoint j.val (16*i.val+k.val)) 40 7 (power40_contains j i k) (mpower0_7_contains j i k)
noncomputable def ha40_0_7 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1853917702541761441902330,1853917702541761442598634⟩,⟨1070359884617898513797874,1070359884617898514477136⟩⟩,⟨⟨(-237301465925345464731750499),(-237301465925345464497287603)⟩,⟨137006065231091009682321563,137006065231091009914510570⟩⟩,⟨⟨(-391088760),832412763⟩,⟨(-4681754135318688101373957011),(-4681754135318688100046138085)⟩⟩,⟨⟨30374587638444219428561195704,30374587638444219509449484540⟩,⟨17536776349579649216757555427,17536776349579649297363458435⟩⟩,⟨⟨(-144837320511075112926020342945),(-144837320511075112441382570561)⟩,⟨83621865985773321161711307149,83621865985773321644967762999⟩⟩,⟨⟨(-100594486996),213573431851⟩,⟨(-599264529320792077054646359429),(-599264529320792076727125812893)⟩⟩]
lemma ha40_0_7_eq (j : Fin 7) : ha40_0_7 j = ((ha40_0_6 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 7 := by fin_cases j <;> decide +kernel
lemma ha40_0_7_contains (j : Fin 7) : (ha40_0_7 j).Contains (fullFactor false 40 7 ((j.val:ℝ)/6)) := by
  rw [ha40_0_7_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha40_0_6 j) false 40 6 j (ha40_0_6_contains j)
noncomputable def hk40_0_8 (j : Fin 6) (i k : Fin 16) : CBox := (power40 j i k).conj.mul (mpower0_8 j i k)
lemma hk40_0_8_contains (j : Fin 6) (i k : Fin 16) :
    (hk40_0_8 j i k).Contains (fullFactor false 40 8 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk40_0_8,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power40 j i k) (mpower0_8 j i k) (quadraturePoint j.val (16*i.val+k.val)) 40 8 (power40_contains j i k) (mpower0_8_contains j i k)
noncomputable def ha40_0_8 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-70054890629433514751212),(-70054890629433514706530)⟩,⟨121338629888859693691239,121338629888859693737199⟩⟩,⟨⟨(-17934052001134979784352242),(-17934052001134979753901685)⟩,⟨(-31062689251548081607080244),(-31062689251548081576290246)⟩⟩,⟨⟨919260274839426580115411405,919260274839426580379054139⟩,⟨(-76790099),163443864⟩⟩,⟨⟨(-4591117312290554832204694957),(-4591117312290554811087504915)⟩,⟨7952048448396308876437734213,7952048448396308897639550867⟩⟩,⟨⟨(-27365191652122466765613560936),(-27365191652122466607381149460)⟩,⟨(-47397902300335817939070332113),(-47397902300335817780322119760)⟩⟩,⟨⟨235330630358893204478608540342,235330630358893204607974638866⟩,⟨(-39503362668),83870090564⟩⟩]
lemma ha40_0_8_eq (j : Fin 7) : ha40_0_8 j = ((ha40_0_7 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 8 := by fin_cases j <;> decide +kernel
lemma ha40_0_8_contains (j : Fin 7) : (ha40_0_8 j).Contains (fullFactor false 40 8 ((j.val:ℝ)/6)) := by
  rw [ha40_0_8_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha40_0_7 j) false 40 7 j (ha40_0_7_contains j)
noncomputable def hk40_0_9 (j : Fin 6) (i k : Fin 16) : CBox := (power40 j i k).conj.mul (mpower0_9 j i k)
lemma hk40_0_9_contains (j : Fin 6) (i k : Fin 16) :
    (hk40_0_9 j i k).Contains (fullFactor false 40 9 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk40_0_9,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power40 j i k) (mpower0_9 j i k) (quadraturePoint j.val (16*i.val+k.val)) 40 9 (power40_contains j i k) (mpower0_9_contains j i k)
noncomputable def ha40_0_9 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-7059195338064676367895),(-7059195338064676365197)⟩,⟨(-4075628328693792153878),(-4075628328693792151264)⟩⟩,⟨⟨3614308013089114297972787,3614308013089114301566872⟩,⟨(-2086721704291221583720864),(-2086721704291221580171137)⟩⟩,⟨⟨(-28526336),13402401⟩,⟨160441184787359821850481523,160441184787359821897006562⟩⟩,⟨⟨(-1850525702701626523851328871),(-1850525702701626518911551690)⟩,⟨(-1068401512597105452589588603),(-1068401512597105447671994508)⟩⟩,⟨⟨13787490894657571006049304159,13787490894657571052271174227⟩,⟨(-7960211579480062819717199574),(-7960211579480062773663918706)⟩⟩,⟨⟨(-29276184486),13789274884⟩,⟨82145886611128228776647566792,82145886611128228822066332465⟩⟩]
lemma ha40_0_9_eq (j : Fin 7) : ha40_0_9 j = ((ha40_0_8 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 9 := by fin_cases j <;> decide +kernel
lemma ha40_0_9_contains (j : Fin 7) : (ha40_0_9 j).Contains (fullFactor false 40 9 ((j.val:ℝ)/6)) := by
  rw [ha40_0_9_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha40_0_8 j) false 40 8 j (ha40_0_8_contains j)
noncomputable def hk40_0_10 (j : Fin 6) (i k : Fin 16) : CBox := (power40 j i k).conj.mul (mpower0_10 j i k)
lemma hk40_0_10_contains (j : Fin 6) (i k : Fin 16) :
    (hk40_0_10 j i k).Contains (fullFactor false 40 10 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk40_0_10,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power40 j i k) (mpower0_10 j i k) (quadraturePoint j.val (16*i.val+k.val)) 40 10 (power40_contains j i k) (mpower0_10_contains j i k)
noncomputable def ha40_0_10 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨213399400269781075664,213399400269781075802⟩,⟨(-369618603571988403261),(-369618603571988403118)⟩⟩,⟨⟨218520985876255821346646,218520985876255821719069⟩,⟨378489450057716124687343,378489450057716125064921⟩⟩,⟨⟨(-25202042373060605484936250),(-25202042373060605477547892)⟩,⟨(-4480907),2105245⟩⟩,⟨⟨223765489537285960770854880,223765489537285961801505647⟩,⟨(-387573196859101312369975253),(-387573196859101311334157054)⟩⟩,⟨⟨2083978518259580811334142233,2083978518259580823397496481⟩,⟨3609556675507699244035680334,3609556675507699256148027198⟩⟩,⟨⟨(-25806891390014060019967316597),(-25806891390014060005616444652)⟩,⟨(-9197384611),4332028468⟩⟩]
lemma ha40_0_10_eq (j : Fin 7) : ha40_0_10 j = ((ha40_0_9 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 10 := by fin_cases j <;> decide +kernel
lemma ha40_0_10_contains (j : Fin 7) : (ha40_0_10 j).Contains (fullFactor false 40 10 ((j.val:ℝ)/6)) := by
  rw [ha40_0_10_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha40_0_9 j) false 40 9 j (ha40_0_9_contains j)
noncomputable def hk40_0_11 (j : Fin 6) (i k : Fin 16) : CBox := (power40 j i k).conj.mul (mpower0_11 j i k)
lemma hk40_0_11_contains (j : Fin 6) (i k : Fin 16) :
    (hk40_0_11 j i k).Contains (fullFactor false 40 11 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk40_0_11,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power40 j i k) (mpower0_11 j i k) (quadraturePoint j.val (16*i.val+k.val)) 40 11 (power40_contains j i k) (mpower0_11_contains j i k)
noncomputable def ha40_0_11 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨17593804388058740561,17593804388058740568⟩,⟨10157787699515332857,10157787699515332865⟩⟩,⟨⟨(-36032111386744300695148),(-36032111386744300659087)⟩,⟨20803149208607401679470,20803149208607401714992⟩⟩,⟨⟨(-300629),639873⟩,⟨(-3598843235212085341021492),(-3598843235212085339954980)⟩⟩,⟨⟨73793764120052327683992599,73793764120052327881446817⟩,⟨42604849579227958584699820,42604849579227958781070884⟩⟩,⟨⟨(-859072479885680693116431834),(-859072479885680690230965508)⟩,⟨495985727515397110826705361,495985727515397113699355731⟩⟩,⟨⟨(-1237224438),2626766903⟩,⟨(-7370430945714350779380937037),(-7370430945714350775258876782)⟩⟩]
lemma ha40_0_11_eq (j : Fin 7) : ha40_0_11 j = ((ha40_0_10 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 11 := by fin_cases j <;> decide +kernel
lemma ha40_0_11_contains (j : Fin 7) : (ha40_0_11 j).Contains (fullFactor false 40 11 ((j.val:ℝ)/6)) := by
  rw [ha40_0_11_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha40_0_10 j) false 40 10 j (ha40_0_10_contains j)
noncomputable def hk40_0_12 (j : Fin 6) (i k : Fin 16) : CBox := (power40 j i k).conj.mul (mpower0_12 j i k)
lemma hk40_0_12_contains (j : Fin 6) (i k : Fin 16) :
    (hk40_0_12 j i k).Contains (fullFactor false 40 12 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk40_0_12,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power40 j i k) (mpower0_12 j i k) (quadraturePoint j.val (16*i.val+k.val)) 40 12 (power40_contains j i k) (mpower0_12_contains j i k)
noncomputable def ha40_0_12 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-443217100187807443),(-443217100187807442)⟩,⟨767674536308627877,767674536308627878⟩⟩,⟨⟨(-1815417242369259286983),(-1815417242369259283876)⟩,⟨(-3144394900720139786589),(-3144394900720139783431)⟩⟩,⟨⟨471087477881817150300715,471087477881817150441822⟩,⟨(-39353),83760⟩⟩,⟨⟨(-7435949024744486051481067),(-7435949024744486017184181)⟩,⟨12879441513349692541449926,12879441513349692575953185⟩⟩,⟨⟨(-108207299850538926752882408),(-108207299850538926125822882)⟩,⟨(-187420541090973603152136075),(-187420541090973602522028398)⟩⟩,⟨⟨1929574309403923047378067406,1929574309403923048463362284⟩,⟨(-323904601),687685968⟩⟩]
lemma ha40_0_12_eq (j : Fin 7) : ha40_0_12 j = ((ha40_0_11 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 12 := by fin_cases j <;> decide +kernel
lemma ha40_0_12_contains (j : Fin 7) : (ha40_0_12 j).Contains (fullFactor false 40 12 ((j.val:ℝ)/6)) := by
  rw [ha40_0_12_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha40_0_11 j) false 40 11 j (ha40_0_11_contains j)
noncomputable def hk40_0_13 (j : Fin 6) (i k : Fin 16) : CBox := (power40 j i k).conj.mul (mpower0_13 j i k)
lemma hk40_0_13_contains (j : Fin 6) (i k : Fin 16) :
    (hk40_0_13 j i k).Contains (fullFactor false 40 13 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk40_0_13,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power40 j i k) (mpower0_13 j i k) (quadraturePoint j.val (16*i.val+k.val)) 40 13 (power40_contains j i k) (mpower0_13_contains j i k)
noncomputable def ha40_0_13 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-30919495943783800),(-30919495943783799)⟩,⟨(-17851379306351119),(-17851379306351118)⟩⟩,⟨⟨253292510771476882160,253292510771476882416⟩,⟨(-146238499277628361631),(-146238499277628361379)⟩⟩,⟨⟨(-10121),4756⟩,⟨56921729219679268109692,56921729219679268126924⟩⟩,⟨⟨(-2074972248239938622372649),(-2074972248239938616807316)⟩,⟨(-1197985786082331540410041),(-1197985786082331534880747)⟩⟩,⟨⟨37743525322001707832315224,37743525322001707959329062⟩,⟨(-21791234504823142575788733),(-21791234504823142449439522)⟩⟩,⟨⟨(-166186861),78275102⟩,⟨466302805767612564293297329,466302805767612564557055034⟩⟩]
lemma ha40_0_13_eq (j : Fin 7) : ha40_0_13 j = ((ha40_0_12 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 13 := by fin_cases j <;> decide +kernel
lemma ha40_0_13_contains (j : Fin 7) : (ha40_0_13 j).Contains (fullFactor false 40 13 ((j.val:ℝ)/6)) := by
  rw [ha40_0_13_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha40_0_12 j) false 40 12 j (ha40_0_12_contains j)
noncomputable def hk40_0_14 (j : Fin 6) (i k : Fin 16) : CBox := (power40 j i k).conj.mul (mpower0_14 j i k)
lemma hk40_0_14_contains (j : Fin 6) (i k : Fin 16) :
    (hk40_0_14 j i k).Contains (fullFactor false 40 14 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk40_0_14,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power40 j i k) (mpower0_14 j i k) (quadraturePoint j.val (16*i.val+k.val)) 40 14 (power40_contains j i k) (mpower0_14_contains j i k)
noncomputable def ha40_0_14 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨667640024824732,667640024824733⟩,⟨(-1156386444162984),(-1156386444162983)⟩⟩,⟨⟨10938614166728417748,10938614166728417768⟩,⟨18946235501166317741,18946235501166317762⟩⟩,⟨⟨(-6386603083791852242134),(-6386603083791852240180)⟩,⟨(-1136),534⟩⟩,⟨⟨179218254507678396166386,179218254507678396994138⟩,⟨(-310415122451108950440080),(-310415122451108949606519)⟩⟩,⟨⟨4074951323393142866200747,4074951323393142889840966⟩,⟨7058022730486958369643718,7058022730486958393417717⟩⟩,⟨⟨(-104638104924845707148875708),(-104638104924845707089355543)⟩,⟨(-37292245),17564892⟩⟩]
lemma ha40_0_14_eq (j : Fin 7) : ha40_0_14 j = ((ha40_0_13 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 14 := by fin_cases j <;> decide +kernel
lemma ha40_0_14_contains (j : Fin 7) : (ha40_0_14 j).Contains (fullFactor false 40 14 ((j.val:ℝ)/6)) := by
  rw [ha40_0_14_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha40_0_13 j) false 40 13 j (ha40_0_13_contains j)
noncomputable def hk40_0_15 (j : Fin 6) (i k : Fin 16) : CBox := (power40 j i k).conj.mul (mpower0_15 j i k)
lemma hk40_0_15_contains (j : Fin 6) (i k : Fin 16) :
    (hk40_0_15 j i k).Contains (fullFactor false 40 15 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk40_0_15,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power40 j i k) (mpower0_15 j i k) (quadraturePoint j.val (16*i.val+k.val)) 40 15 (power40_contains j i k) (mpower0_15_contains j i k)
noncomputable def ha40_0_15 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨40365501752147,40365501752148⟩,⟨23305033302576,23305033302577⟩⟩,⟨⟨(-1322696761414360854),(-1322696761414360851)⟩,⟨763659331258827442,763659331258827445⟩⟩,⟨⟨(-56),119⟩,⟨(-668803510981146723359),(-668803510981146723151)⟩⟩,⟨⟨43342127478025776361057,43342127478025776477583⟩,⟨25023588966689257608905,25023588966689257724562⟩⟩,⟨⟨(-1231857353275977871360365),(-1231857353275977867207097)⟩,⟨711213174517105744257029,711213174517105748385291⟩⟩,⟨⟨(-3678783),7810470⟩,⟨(-21915353447830215833899061),(-21915353447830215821363427)⟩⟩]
lemma ha40_0_15_eq (j : Fin 7) : ha40_0_15 j = ((ha40_0_14 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 15 := by fin_cases j <;> decide +kernel
lemma ha40_0_15_contains (j : Fin 7) : (ha40_0_15 j).Contains (fullFactor false 40 15 ((j.val:ℝ)/6)) := by
  rw [ha40_0_15_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha40_0_14 j) false 40 14 j (ha40_0_14_contains j)
noncomputable def hk40_0_16 (j : Fin 6) (i k : Fin 16) : CBox := (power40 j i k).conj.mul (mpower0_16 j i k)
lemma hk40_0_16_contains (j : Fin 6) (i k : Fin 16) :
    (hk40_0_16 j i k).Contains (fullFactor false 40 16 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk40_0_16,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power40 j i k) (mpower0_16 j i k) (quadraturePoint j.val (16*i.val+k.val)) 40 16 (power40_contains j i k) (mpower0_16_contains j i k)
noncomputable def ha40_0_16 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-762655431407),(-762655431406)⟩,⟨1320957955864,1320957955865⟩⟩,⟨⟨(-49981386352667222),(-49981386352667221)⟩,⟨(-86570300595549325),(-86570300595549323)⟩⟩,⟨⟨65659631149794723612,65659631149794723634⟩,⟨(-6),12⟩⟩,⟨⟨(-3275580136008399057347),(-3275580136008399042196)⟩,⟨5673471219829920486980,5673471219829920502252⟩⟩,⟨⟨(-116371983552042446010015),(-116371983552042445334158)⟩,⟨(-201562188089707223946773),(-201562188089707223266553)⟩⟩,⟨⟨4303069587032947006111938,4303069587032947008587002⟩,⟨(-722328),1533583⟩⟩]
lemma ha40_0_16_eq (j : Fin 7) : ha40_0_16 j = ((ha40_0_15 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 16 := by fin_cases j <;> decide +kernel
lemma ha40_0_16_contains (j : Fin 7) : (ha40_0_16 j).Contains (fullFactor false 40 16 ((j.val:ℝ)/6)) := by
  rw [ha40_0_16_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha40_0_15 j) false 40 15 j (ha40_0_15_contains j)
noncomputable def hk40_0_17 (j : Fin 6) (i k : Fin 16) : CBox := (power40 j i k).conj.mul (mpower0_17 j i k)
lemma hk40_0_17_contains (j : Fin 6) (i k : Fin 16) :
    (hk40_0_17 j i k).Contains (fullFactor false 40 17 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk40_0_17,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power40 j i k) (mpower0_17 j i k) (quadraturePoint j.val (16*i.val+k.val)) 40 17 (power40_contains j i k) (mpower0_17_contains j i k)
noncomputable def ha40_0_17 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-40685409901),(-40685409900)⟩,⟨(-23489732359),(-23489732358)⟩⟩,⟨⟨5332718046471330,5332718046471331⟩,⟨(-3078846199642598),(-3078846199642597)⟩⟩,⟨⟨(-2),1⟩,⟨6066935731106195666,6066935731106195669⟩⟩,⟨⟨(-698970019787090240140),(-698970019787090238255)⟩,⟨(-403550529079554597692),(-403550529079554595823)⟩⟩,⟨⟨31040504379613153588222,31040504379613153693076⟩,⟨(-17921243559351411792920),(-17921243559351411688780)⟩⟩,⟨⟨(-283406),133486⟩,⟨795205400147551278258500,795205400147551278718423⟩⟩]
lemma ha40_0_17_eq (j : Fin 7) : ha40_0_17 j = ((ha40_0_16 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 17 := by fin_cases j <;> decide +kernel
lemma ha40_0_17_contains (j : Fin 7) : (ha40_0_17 j).Contains (fullFactor false 40 17 ((j.val:ℝ)/6)) := by
  rw [ha40_0_17_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha40_0_16 j) false 40 16 j (ha40_0_16_contains j)
noncomputable def hk40_0_18 (j : Fin 6) (i k : Fin 16) : CBox := (power40 j i k).conj.mul (mpower0_18 j i k)
lemma hk40_0_18_contains (j : Fin 6) (i k : Fin 16) :
    (hk40_0_18 j i k).Contains (fullFactor false 40 18 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk40_0_18,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power40 j i k) (mpower0_18 j i k) (quadraturePoint j.val (16*i.val+k.val)) 40 18 (power40_contains j i k) (mpower0_18_contains j i k)
noncomputable def ha40_0_18 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨683288616,683288617⟩,⟨(-1183490601),(-1183490600)⟩⟩,⟨⟨179120011154259,179120011154260⟩,⟨310244959971482,310244959971483⟩⟩,⟨⟨(-529440020073462377),(-529440020073462376)⟩,⟨(-1),1⟩⟩,⟨⟨46955236204022331265,46955236204022331484⟩,⟨(-81328854786764263491),(-81328854786764263270)⟩⟩,⟨⟨2606539218020916327905,2606539218020916343060⟩,⟨4514658357533078050759,4514658357533078066025⟩⟩,⟨⟨(-138789524622137721186912),(-138789524622137721106198)⟩,⟨(-49464),23298⟩⟩]
lemma ha40_0_18_eq (j : Fin 7) : ha40_0_18 j = ((ha40_0_17 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 18 := by fin_cases j <;> decide +kernel
lemma ha40_0_18_contains (j : Fin 7) : (ha40_0_18 j).Contains (fullFactor false 40 18 ((j.val:ℝ)/6)) := by
  rw [ha40_0_18_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha40_0_17 j) false 40 17 j (ha40_0_17_contains j)
noncomputable def hk40_0_19 (j : Fin 6) (i k : Fin 16) : CBox := (power40 j i k).conj.mul (mpower0_19 j i k)
lemma hk40_0_19_contains (j : Fin 6) (i k : Fin 16) :
    (hk40_0_19 j i k).Contains (fullFactor false 40 19 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk40_0_19,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power40 j i k) (mpower0_19 j i k) (quadraturePoint j.val (16*i.val+k.val)) 40 19 (power40_contains j i k) (mpower0_19_contains j i k)
noncomputable def ha40_0_19 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨32614433,32614434⟩,⟨18829951,18829952⟩⟩,⟨⟨(-17099355913328),(-17099355913327)⟩,⟨9872317739528,9872317739529⟩⟩,⟨⟨(-1),1⟩,⟨(-43770654673137423),(-43770654673137422)⟩⟩,⟨⟨8964987113086656132,8964987113086656157⟩,⟨5175937723022106869,5175937723022106894⟩⟩,⟨⟨(-622070944276038606578),(-622070944276038604472)⟩,⟨359152827132815576431,359152827132815578522⟩⟩,⟨⟨(-3853),8179⟩,⟨(-22948428997269873117241),(-22948428997269873103821)⟩⟩]
lemma ha40_0_19_eq (j : Fin 7) : ha40_0_19 j = ((ha40_0_18 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 19 := by fin_cases j <;> decide +kernel
lemma ha40_0_19_contains (j : Fin 7) : (ha40_0_19 j).Contains (fullFactor false 40 19 ((j.val:ℝ)/6)) := by
  rw [ha40_0_19_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha40_0_18 j) false 40 18 j (ha40_0_18_contains j)
noncomputable def hk40_0_20 (j : Fin 6) (i k : Fin 16) : CBox := (power40 j i k).conj.mul (mpower0_20 j i k)
lemma hk40_0_20_contains (j : Fin 6) (i k : Fin 16) :
    (hk40_0_20 j i k).Contains (fullFactor false 40 20 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk40_0_20,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power40 j i k) (mpower0_20 j i k) (quadraturePoint j.val (16*i.val+k.val)) 40 20 (power40_contains j i k) (mpower0_20_contains j i k)
noncomputable def ha40_0_20 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-492967),(-492966)⟩,⟨853843,853844⟩⟩,⟨⟨(-516913348074),(-516913348073)⟩,⟨(-895320181974),(-895320181973)⟩⟩,⟨⟨3437739179098606,3437739179098608⟩,⟨(-1),1⟩⟩,⟨⟨(-542022930869484435),(-542022930869484432)⟩,⟨938811255133340261,938811255133340264⟩⟩,⟨⟨(-47012995134852432738),(-47012995134852432464)⟩,⟨(-81428896189552855299),(-81428896189552855022)⟩⟩,⟨⟨3604730797462500932853,3604730797462500934974⟩,⟨(-606),1285⟩⟩]
lemma ha40_0_20_eq (j : Fin 7) : ha40_0_20 j = ((ha40_0_19 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 20 := by fin_cases j <;> decide +kernel
lemma ha40_0_20_contains (j : Fin 7) : (ha40_0_20 j).Contains (fullFactor false 40 20 ((j.val:ℝ)/6)) := by
  rw [ha40_0_20_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha40_0_19 j) false 40 19 j (ha40_0_19_contains j)
noncomputable def hk40_0_21 (j : Fin 6) (i k : Fin 16) : CBox := (power40 j i k).conj.mul (mpower0_21 j i k)
lemma hk40_0_21_contains (j : Fin 6) (i k : Fin 16) :
    (hk40_0_21 j i k).Contains (fullFactor false 40 21 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk40_0_21,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power40 j i k) (mpower0_21 j i k) (quadraturePoint j.val (16*i.val+k.val)) 40 21 (power40_contains j i k) (mpower0_21_contains j i k)
noncomputable def ha40_0_21 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-21290),(-21289)⟩,⟨(-12292),(-12291)⟩⟩,⟨⟨44646528671,44646528672⟩,⟨(-25776685347),(-25776685346)⟩⟩,⟨⟨(-1),1⟩,⟨257142289286047,257142289286048⟩⟩,⟨⟨(-93630556896327456),(-93630556896327454)⟩,⟨(-54057627228469228),(-54057627228469227)⟩⟩,⟨⟨10151445319802585598,10151445319802585633⟩,⟨(-5860939688051789428),(-5860939688051789393)⟩⟩,⟨⟨(-193),91⟩,⟨539266466260812848784,539266466260812849104⟩⟩]
lemma ha40_0_21_eq (j : Fin 7) : ha40_0_21 j = ((ha40_0_20 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 21 := by fin_cases j <;> decide +kernel
lemma ha40_0_21_contains (j : Fin 7) : (ha40_0_21 j).Contains (fullFactor false 40 21 ((j.val:ℝ)/6)) := by
  rw [ha40_0_21_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha40_0_20 j) false 40 20 j (ha40_0_20_contains j)
noncomputable def hk40_0_22 (j : Fin 6) (i k : Fin 16) : CBox := (power40 j i k).conj.mul (mpower0_22 j i k)
lemma hk40_0_22_contains (j : Fin 6) (i k : Fin 16) :
    (hk40_0_22 j i k).Contains (fullFactor false 40 22 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk40_0_22,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power40 j i k) (mpower0_22 j i k) (quadraturePoint j.val (16*i.val+k.val)) 40 22 (power40_contains j i k) (mpower0_22_contains j i k)
noncomputable def ha40_0_22 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨292,293⟩,⟨(-507),(-506)⟩⟩,⟨⟨1226967353,1226967354⟩,⟨2125169795,2125169796⟩⟩,⟨⟨(-18359916521553),(-18359916521552)⟩,⟨(-1),1⟩⟩,⟨⟨5146274077922863,5146274077922864⟩,⟨(-8913608172637076),(-8913608172637075)⟩⟩,⟨⟨697450191936225607,697450191936225612⟩,⟨1208019168182208035,1208019168182208040⟩⟩,⟨⟨(-77007071306013533823),(-77007071306013533776)⟩,⟨(-28),13⟩⟩]
lemma ha40_0_22_eq (j : Fin 7) : ha40_0_22 j = ((ha40_0_21 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 22 := by fin_cases j <;> decide +kernel
lemma ha40_0_22_contains (j : Fin 7) : (ha40_0_22 j).Contains (fullFactor false 40 22 ((j.val:ℝ)/6)) := by
  rw [ha40_0_22_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha40_0_21 j) false 40 21 j (ha40_0_21_contains j)
noncomputable def hk40_0_23 (j : Fin 6) (i k : Fin 16) : CBox := (power40 j i k).conj.mul (mpower0_23 j i k)
lemma hk40_0_23_contains (j : Fin 6) (i k : Fin 16) :
    (hk40_0_23 j i k).Contains (fullFactor false 40 23 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk40_0_23,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power40 j i k) (mpower0_23 j i k) (quadraturePoint j.val (16*i.val+k.val)) 40 23 (power40_contains j i k) (mpower0_23_contains j i k)
noncomputable def ha40_0_23 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨11,12⟩,⟨6,7⟩⟩,⟨⟨(-96759679),(-96759678)⟩,⟨55864226,55864227⟩⟩,⟨⟨(-1),1⟩,⟨(-1253899540536),(-1253899540535)⟩⟩,⟨⟨811679013105350,811679013105351⟩,⟨468623096711943,468623096711944⟩⟩,⟨⟨(-137503773339017308),(-137503773339017306)⟩,⟨79387840551870928,79387840551870929⟩⟩,⟨⟨(-2),4⟩,⟨(-10518471716932064459),(-10518471716932064452)⟩⟩]
lemma ha40_0_23_eq (j : Fin 7) : ha40_0_23 j = ((ha40_0_22 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 23 := by fin_cases j <;> decide +kernel
lemma ha40_0_23_contains (j : Fin 7) : (ha40_0_23 j).Contains (fullFactor false 40 23 ((j.val:ℝ)/6)) := by
  rw [ha40_0_23_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha40_0_22 j) false 40 22 j (ha40_0_22_contains j)
noncomputable def hk40_0_24 (j : Fin 6) (i k : Fin 16) : CBox := (power40 j i k).conj.mul (mpower0_24 j i k)
lemma hk40_0_24_contains (j : Fin 6) (i k : Fin 16) :
    (hk40_0_24 j i k).Contains (fullFactor false 40 24 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk40_0_24,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power40 j i k) (mpower0_24 j i k) (quadraturePoint j.val (16*i.val+k.val)) 40 24 (power40_contains j i k) (mpower0_24_contains j i k)
noncomputable def ha40_0_24 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),0⟩,⟨0,1⟩⟩,⟨⟨(-2437537),(-2437536)⟩,⟨(-4221938),(-4221937)⟩⟩,⟨⟨82067533018,82067533019⟩,⟨(-1),1⟩⟩,⟨⟨(-40895079942577),(-40895079942576)⟩,⟨70832356240132,70832356240133⟩⟩,⟨⟨(-8659870022990125),(-8659870022990124)⟩,⟨(-14999334866761558),(-14999334866761557)⟩⟩,⟨⟨1376864728037741370,1376864728037741371⟩,⟨(-1),1⟩⟩]
lemma ha40_0_24_eq (j : Fin 7) : ha40_0_24 j = ((ha40_0_23 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 24 := by fin_cases j <;> decide +kernel
lemma ha40_0_24_contains (j : Fin 7) : (ha40_0_24 j).Contains (fullFactor false 40 24 ((j.val:ℝ)/6)) := by
  rw [ha40_0_24_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha40_0_23 j) false 40 23 j (ha40_0_23_contains j)
noncomputable def hk40_0_25 (j : Fin 6) (i k : Fin 16) : CBox := (power40 j i k).conj.mul (mpower0_25 j i k)
lemma hk40_0_25_contains (j : Fin 6) (i k : Fin 16) :
    (hk40_0_25 j i k).Contains (fullFactor false 40 25 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk40_0_25,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power40 j i k) (mpower0_25 j i k) (quadraturePoint j.val (16*i.val+k.val)) 40 25 (power40_contains j i k) (mpower0_25_contains j i k)
noncomputable def ha40_0_25 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),0⟩,⟨(-1),0⟩⟩,⟨⟨176848,176849⟩,⟨(-102104),(-102103)⟩⟩,⟨⟨(-1),1⟩,⟨5156455176,5156455177⟩⟩,⟨⟨(-5934037600013),(-5934037600012)⟩,⟨(-3426018205749),(-3426018205748)⟩⟩,⟨⟨1570726674205044,1570726674205046⟩,⟨(-906859468175609),(-906859468175608)⟩⟩,⟨⟨(-1),1⟩,⟨173021924583611076,173021924583611077⟩⟩]
lemma ha40_0_25_eq (j : Fin 7) : ha40_0_25 j = ((ha40_0_24 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 25 := by fin_cases j <;> decide +kernel
lemma ha40_0_25_contains (j : Fin 7) : (ha40_0_25 j).Contains (fullFactor false 40 25 ((j.val:ℝ)/6)) := by
  rw [ha40_0_25_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha40_0_24 j) false 40 24 j (ha40_0_24_contains j)
noncomputable def hk40_0_26 (j : Fin 6) (i k : Fin 16) : CBox := (power40 j i k).conj.mul (mpower0_26 j i k)
lemma hk40_0_26_contains (j : Fin 6) (i k : Fin 16) :
    (hk40_0_26 j i k).Contains (fullFactor false 40 26 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk40_0_26,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power40 j i k) (mpower0_26 j i k) (quadraturePoint j.val (16*i.val+k.val)) 40 26 (power40_contains j i k) (mpower0_26_contains j i k)
noncomputable def ha40_0_26 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨0,1⟩,⟨(-1),0⟩⟩,⟨⟨4112,4113⟩,⟨7122,7123⟩⟩,⟨⟨(-311528495),(-311528494)⟩,⟨(-1),1⟩⟩,⟨⟨275978298108,275978298109⟩,⟨(-478008434111),(-478008434110)⟩⟩,⟨⟨91313559072398,91313559072399⟩,⟨158159723733336,158159723733337⟩⟩,⟨⟨(-20906323353147685),(-20906323353147684)⟩,⟨(-1),1⟩⟩]
lemma ha40_0_26_eq (j : Fin 7) : ha40_0_26 j = ((ha40_0_25 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 26 := by fin_cases j <;> decide +kernel
lemma ha40_0_26_contains (j : Fin 7) : (ha40_0_26 j).Contains (fullFactor false 40 26 ((j.val:ℝ)/6)) := by
  rw [ha40_0_26_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha40_0_25 j) false 40 25 j (ha40_0_25_contains j)
noncomputable def hk40_0_27 (j : Fin 6) (i k : Fin 16) : CBox := (power40 j i k).conj.mul (mpower0_27 j i k)
lemma hk40_0_27_contains (j : Fin 6) (i k : Fin 16) :
    (hk40_0_27 j i k).Contains (fullFactor false 40 27 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk40_0_27,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power40 j i k) (mpower0_27 j i k) (quadraturePoint j.val (16*i.val+k.val)) 40 27 (power40_contains j i k) (mpower0_27_contains j i k)
noncomputable def ha40_0_27 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨0,1⟩,⟨0,1⟩⟩,⟨⟨(-277),(-276)⟩,⟨159,160⟩⟩,⟨⟨(-1),1⟩,⟨(-18123994),(-18123993)⟩⟩,⟨⟨37079204566,37079204567⟩,⟨21407688737,21407688739⟩⟩,⟨⟨(-15335599573286),(-15335599573285)⟩,⟨8854012541820,8854012541821⟩⟩,⟨⟨(-1),1⟩,⟨(-2432561179993389),(-2432561179993388)⟩⟩]
lemma ha40_0_27_eq (j : Fin 7) : ha40_0_27 j = ((ha40_0_26 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 27 := by fin_cases j <;> decide +kernel
lemma ha40_0_27_contains (j : Fin 7) : (ha40_0_27 j).Contains (fullFactor false 40 27 ((j.val:ℝ)/6)) := by
  rw [ha40_0_27_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha40_0_26 j) false 40 26 j (ha40_0_26_contains j)
noncomputable def hk40_0_28 (j : Fin 6) (i k : Fin 16) : CBox := (power40 j i k).conj.mul (mpower0_28 j i k)
lemma hk40_0_28_contains (j : Fin 6) (i k : Fin 16) :
    (hk40_0_28 j i k).Contains (fullFactor false 40 28 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk40_0_28,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power40 j i k) (mpower0_28 j i k) (quadraturePoint j.val (16*i.val+k.val)) 40 28 (power40_contains j i k) (mpower0_28_contains j i k)
noncomputable def ha40_0_28 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),0⟩,⟨0,1⟩⟩,⟨⟨(-6),(-5)⟩,⟨(-11),(-10)⟩⟩,⟨⟨1016753,1016754⟩,⟨(-1),1⟩⟩,⟨⟨(-1601291374),(-1601291373)⟩,⟨2773518015,2773518016⟩⟩,⟨⟨(-827848236791),(-827848236790)⟩,⟨(-1433875207079),(-1433875207078)⟩⟩,⟨⟨272932726159819,272932726159820⟩,⟨(-1),1⟩⟩]
lemma ha40_0_28_eq (j : Fin 7) : ha40_0_28 j = ((ha40_0_27 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 28 := by fin_cases j <;> decide +kernel
lemma ha40_0_28_contains (j : Fin 7) : (ha40_0_28 j).Contains (fullFactor false 40 28 ((j.val:ℝ)/6)) := by
  rw [ha40_0_28_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha40_0_27 j) false 40 27 j (ha40_0_27_contains j)
noncomputable def hk40_0_29 (j : Fin 6) (i k : Fin 16) : CBox := (power40 j i k).conj.mul (mpower0_29 j i k)
lemma hk40_0_29_contains (j : Fin 6) (i k : Fin 16) :
    (hk40_0_29 j i k).Contains (fullFactor false 40 29 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk40_0_29,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power40 j i k) (mpower0_29 j i k) (quadraturePoint j.val (16*i.val+k.val)) 40 29 (power40_contains j i k) (mpower0_29_contains j i k)
noncomputable def ha40_0_29 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),0⟩,⟨(-1),0⟩⟩,⟨⟨0,1⟩,⟨(-1),0⟩⟩,⟨⟨(-1),1⟩,⟨55072,55073⟩⟩,⟨⟨(-200304916),(-200304915)⟩,⟨(-115646097),(-115646096)⟩⟩,⟨⟨129444017721,129444017722⟩,⟨(-74734538477),(-74734538476)⟩⟩,⟨⟨(-1),1⟩,⟨29567015428549,29567015428550⟩⟩]
lemma ha40_0_29_eq (j : Fin 7) : ha40_0_29 j = ((ha40_0_28 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 29 := by fin_cases j <;> decide +kernel
lemma ha40_0_29_contains (j : Fin 7) : (ha40_0_29 j).Contains (fullFactor false 40 29 ((j.val:ℝ)/6)) := by
  rw [ha40_0_29_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha40_0_28 j) false 40 28 j (ha40_0_28_contains j)
noncomputable def hk40_0_30 (j : Fin 6) (i k : Fin 16) : CBox := (power40 j i k).conj.mul (mpower0_30 j i k)
lemma hk40_0_30_contains (j : Fin 6) (i k : Fin 16) :
    (hk40_0_30 j i k).Contains (fullFactor false 40 30 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk40_0_30,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power40 j i k) (mpower0_30 j i k) (quadraturePoint j.val (16*i.val+k.val)) 40 30 (power40_contains j i k) (mpower0_30_contains j i k)
noncomputable def ha40_0_30 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨0,1⟩,⟨(-1),0⟩⟩,⟨⟨0,1⟩,⟨0,1⟩⟩,⟨⟨(-2884),(-2883)⟩,⟨(-1),1⟩⟩,⟨⟨8073620,8073621⟩,⟨(-13983922),(-13983921)⟩⟩,⟨⟨6521818806,6521818807⟩,⟨11296121531,11296121532⟩⟩,⟨⟨(-3096250615297),(-3096250615296)⟩,⟨(-1),1⟩⟩]
lemma ha40_0_30_eq (j : Fin 7) : ha40_0_30 j = ((ha40_0_29 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 30 := by fin_cases j <;> decide +kernel
lemma ha40_0_30_contains (j : Fin 7) : (ha40_0_30 j).Contains (fullFactor false 40 30 ((j.val:ℝ)/6)) := by
  rw [ha40_0_30_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha40_0_29 j) false 40 29 j (ha40_0_29_contains j)
noncomputable def hk40_1_0 (j : Fin 6) (i k : Fin 16) : CBox := (kernel40_0 j i k).mul (mpower1_0 j i k)
lemma hk40_1_0_contains (j : Fin 6) (i k : Fin 16) :
    (hk40_1_0 j i k).Contains (fullFactor true 40 0 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk40_1_0,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel40_0 j i k) (mpower1_0 j i k) (quadraturePoint j.val (16*i.val+k.val)) 40 0 (kernel40_0_contains j i k) (mpower1_0_contains j i k)
noncomputable def ha40_1_0 : Fin 7 → CBox := ![⟨⟨(-3),3⟩,⟨(-3),3⟩⟩,⟨⟨(-4),4⟩,⟨(-4),4⟩⟩,⟨⟨(-4),2⟩,⟨(-2),4⟩⟩,⟨⟨(-3),0⟩,⟨(-2),2⟩⟩,⟨⟨97,100⟩,⟨(-7038),(-7035)⟩⟩,⟨⟨346384015365736346,346384015365736351⟩,⟨639293806035028343,639293806035028348⟩⟩,⟨⟨177965390395636590606821606,177965390395636592442449226⟩,⟨558868935012030951364803856,558868935012030953210918094⟩⟩]
lemma ha40_1_0_eq (j : Fin 7) : ha40_1_0 j = atomKernel40_0 j := by fin_cases j <;> decide +kernel
lemma ha40_1_0_contains (j : Fin 7) : (ha40_1_0 j).Contains (fullFactor true 40 0 ((j.val:ℝ)/6)) := by
  rw [ha40_1_0_eq]
  simpa only [fullFactor,ite_true] using atomKernel40_0_contains j
noncomputable def hk40_1_1 (j : Fin 6) (i k : Fin 16) : CBox := (kernel40_0 j i k).mul (mpower1_1 j i k)
lemma hk40_1_1_contains (j : Fin 6) (i k : Fin 16) :
    (hk40_1_1 j i k).Contains (fullFactor true 40 1 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk40_1_1,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel40_0 j i k) (mpower1_1 j i k) (quadraturePoint j.val (16*i.val+k.val)) 40 1 (kernel40_0_contains j i k) (mpower1_1_contains j i k)
noncomputable def ha40_1_1 : Fin 7 → CBox := ![⟨⟨(-28),28⟩,⟨(-28),28⟩⟩,⟨⟨(-46),46⟩,⟨(-46),46⟩⟩,⟨⟨(-21),41⟩,⟨(-30),31⟩⟩,⟨⟨(-11),19⟩,⟨(-6),21⟩⟩,⟨⟨(-32668),(-32648)⟩,⟨10198,10217⟩⟩,⟨⟨2367744446448568917,2367744446448568942⟩,⟨(-1865339093500727158),(-1865339093500727133)⟩⟩,⟨⟨1984673118246228857746059855,1984673118246228864763638546⟩,⟨(-747578353067753521244344664),(-747578353067753514266814852)⟩⟩]
lemma ha40_1_1_eq (j : Fin 7) : ha40_1_1 j = ((ha40_1_0 j).mul (piI.mul (atomPoints j).z)).scale 1 1 := by fin_cases j <;> decide +kernel
lemma ha40_1_1_contains (j : Fin 7) : (ha40_1_1 j).Contains (fullFactor true 40 1 ((j.val:ℝ)/6)) := by
  rw [ha40_1_1_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha40_1_0 j) true 40 0 j (ha40_1_0_contains j)
noncomputable def hk40_1_2 (j : Fin 6) (i k : Fin 16) : CBox := (kernel40_0 j i k).mul (mpower1_2 j i k)
lemma hk40_1_2_contains (j : Fin 6) (i k : Fin 16) :
    (hk40_1_2 j i k).Contains (fullFactor true 40 2 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk40_1_2,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel40_0 j i k) (mpower1_2 j i k) (quadraturePoint j.val (16*i.val+k.val)) 40 2 (kernel40_0_contains j i k) (mpower1_2_contains j i k)
noncomputable def ha40_1_2 : Fin 7 → CBox := ![⟨⟨(-130),130⟩,⟨(-130),130⟩⟩,⟨⟨(-262),262⟩,⟨(-262),262⟩⟩,⟨⟨(-179),132⟩,⟨(-182),128⟩⟩,⟨⟨(-43),70⟩,⟨(-79),37⟩⟩,⟨⟨48294,48354⟩,⟨67675,67737⟩⟩,⟨⟨(-4644038374569682974),(-4644038374569682913)⟩,⟨(-4179584643938460437),(-4179584643938460376)⟩⟩,⟨⟨(-1536096813425002938101767972),(-1536096813425002924840000361)⟩,⟨(-3513165506687654169263843136),(-3513165506687654155926786775)⟩⟩]
lemma ha40_1_2_eq (j : Fin 7) : ha40_1_2 j = ((ha40_1_1 j).mul (piI.mul (atomPoints j).z)).scale 1 2 := by fin_cases j <;> decide +kernel
lemma ha40_1_2_contains (j : Fin 7) : (ha40_1_2 j).Contains (fullFactor true 40 2 ((j.val:ℝ)/6)) := by
  rw [ha40_1_2_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha40_1_1 j) true 40 1 j (ha40_1_1_contains j)
noncomputable def hk40_1_3 (j : Fin 6) (i k : Fin 16) : CBox := (kernel40_0 j i k).mul (mpower1_3 j i k)
lemma hk40_1_3_contains (j : Fin 6) (i k : Fin 16) :
    (hk40_1_3 j i k).Contains (fullFactor true 40 3 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk40_1_3,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel40_0 j i k) (mpower1_3 j i k) (quadraturePoint j.val (16*i.val+k.val)) 40 3 (kernel40_0_contains j i k) (mpower1_3_contains j i k)
noncomputable def ha40_1_3 : Fin 7 → CBox := ![⟨⟨(-400),400⟩,⟨(-400),400⟩⟩,⟨⟨(-995),995⟩,⟨(-995),995⟩⟩,⟨⟨(-530),514⟩,⟨(-437),606⟩⟩,⟨⟨(-201),104⟩,⟨(-155),148⟩⟩,⟨⟨79794,79921⟩,⟨(-108681),(-108556)⟩⟩,⟨⟨(-4601340322993136421),(-4601340322993136323)⟩,⟨7305324697201660938,7305324697201661036⟩⟩,⟨⟨(-4132564690618217080853584866),(-4132564690618217063956263624)⟩,⟨2068854820492237686352821530,2068854820492237703157050889⟩⟩]
lemma ha40_1_3_eq (j : Fin 7) : ha40_1_3 j = ((ha40_1_2 j).mul (piI.mul (atomPoints j).z)).scale 1 3 := by fin_cases j <;> decide +kernel
lemma ha40_1_3_contains (j : Fin 7) : (ha40_1_3 j).Contains (fullFactor true 40 3 ((j.val:ℝ)/6)) := by
  rw [ha40_1_3_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha40_1_2 j) true 40 2 j (ha40_1_2_contains j)
noncomputable def hk40_1_4 (j : Fin 6) (i k : Fin 16) : CBox := (kernel40_0 j i k).mul (mpower1_4 j i k)
lemma hk40_1_4_contains (j : Fin 6) (i k : Fin 16) :
    (hk40_1_4 j i k).Contains (fullFactor true 40 4 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk40_1_4,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel40_0 j i k) (mpower1_4 j i k) (quadraturePoint j.val (16*i.val+k.val)) 40 4 (kernel40_0_contains j i k) (mpower1_4_contains j i k)
noncomputable def ha40_1_4 : Fin 7 → CBox := ![⟨⟨(-922),922⟩,⟨(-922),922⟩⟩,⟨⟨(-2832),2832⟩,⟨(-2832),2832⟩⟩,⟨⟨(-1196),1433⟩,⟨(-1408),1221⟩⟩,⟨⟨(-272),332⟩,⟨(-238),367⟩⟩,⟨⟨(-155804),(-155610)⟩,⟨(-51184),(-50989)⟩⟩,⟨⟨8271290302966393984,8271290302966394102⟩,⟨3413165102952179402,3413165102952179520⟩⟩,⟨⟨2061668539877541451666416628,2061668539877541467636323238⟩,⟨3633580723864899643535444287,3633580723864899659590641987⟩⟩]
lemma ha40_1_4_eq (j : Fin 7) : ha40_1_4 j = ((ha40_1_3 j).mul (piI.mul (atomPoints j).z)).scale 1 4 := by fin_cases j <;> decide +kernel
lemma ha40_1_4_contains (j : Fin 7) : (ha40_1_4 j).Contains (fullFactor true 40 4 ((j.val:ℝ)/6)) := by
  rw [ha40_1_4_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha40_1_3 j) true 40 3 j (ha40_1_3_contains j)
noncomputable def hk40_1_5 (j : Fin 6) (i k : Fin 16) : CBox := (kernel40_0 j i k).mul (mpower1_5 j i k)
lemma hk40_1_5_contains (j : Fin 6) (i k : Fin 16) :
    (hk40_1_5 j i k).Contains (fullFactor true 40 5 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk40_1_5,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel40_0 j i k) (mpower1_5 j i k) (quadraturePoint j.val (16*i.val+k.val)) 40 5 (kernel40_0_contains j i k) (mpower1_5_contains j i k)
noncomputable def ha40_1_5 : Fin 7 → CBox := ![⟨⟨(-1700),1700⟩,⟨(-1700),1700⟩⟩,⟨⟨(-6448),6448⟩,⟨(-6448),6448⟩⟩,⟨⟨(-2862),2436⟩,⟨(-2679),2619⟩⟩,⟨⟨(-432),529⟩,⟨(-547),413⟩⟩,⟨⟨(-133),106⟩,⟨159236,159475⟩⟩,⟨⟨1623655690123195417,1623655690123195531⟩,⟨(-7238915776409818093),(-7238915776409817979)⟩⟩,⟨⟨2546765638135768935440963307,2546765638135768947644454795⟩,⟨(-1625405684011285392378477584),(-1625405684011285380236806371)⟩⟩]
lemma ha40_1_5_eq (j : Fin 7) : ha40_1_5 j = ((ha40_1_4 j).mul (piI.mul (atomPoints j).z)).scale 1 5 := by fin_cases j <;> decide +kernel
lemma ha40_1_5_contains (j : Fin 7) : (ha40_1_5 j).Contains (fullFactor true 40 5 ((j.val:ℝ)/6)) := by
  rw [ha40_1_5_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha40_1_4 j) true 40 4 j (ha40_1_4_contains j)
noncomputable def hk40_1_6 (j : Fin 6) (i k : Fin 16) : CBox := (kernel40_0 j i k).mul (mpower1_6 j i k)
lemma hk40_1_6_contains (j : Fin 6) (i k : Fin 16) :
    (hk40_1_6 j i k).Contains (fullFactor true 40 6 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk40_1_6,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel40_0 j i k) (mpower1_6 j i k) (quadraturePoint j.val (16*i.val+k.val)) 40 6 (kernel40_0_contains j i k) (mpower1_6_contains j i k)
noncomputable def ha40_1_6 : Fin 7 → CBox := ![⟨⟨(-2612),2612⟩,⟨(-2612),2612⟩⟩,⟨⟨(-12235),12235⟩,⟨(-12235),12235⟩⟩,⟨⟨(-4299),4597⟩,⟨(-4241),4655⟩⟩,⟨⟨(-716),556⟩,⟨(-646),626⟩⟩,⟨⟨122584,122830⟩,⟨(-40359),(-40114)⟩⟩,⟨⟨(-5119443804201172519),(-5119443804201172427)⟩,⟨(-255784885787529464),(-255784885787529372)⟩⟩,⟨⟨(-1057932829001996977349198973),(-1057932829001996969656601229)⟩,⟨(-1481871526105482806833486306),(-1481871526105482799103944217)⟩⟩]
lemma ha40_1_6_eq (j : Fin 7) : ha40_1_6 j = ((ha40_1_5 j).mul (piI.mul (atomPoints j).z)).scale 1 6 := by fin_cases j <;> decide +kernel
lemma ha40_1_6_contains (j : Fin 7) : (ha40_1_6 j).Contains (fullFactor true 40 6 ((j.val:ℝ)/6)) := by
  rw [ha40_1_6_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha40_1_5 j) true 40 5 j (ha40_1_5_contains j)
noncomputable def hk40_1_7 (j : Fin 6) (i k : Fin 16) : CBox := (kernel40_0 j i k).mul (mpower1_7 j i k)
lemma hk40_1_7_contains (j : Fin 6) (i k : Fin 16) :
    (hk40_1_7 j i k).Contains (fullFactor true 40 7 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk40_1_7,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel40_0 j i k) (mpower1_7 j i k) (quadraturePoint j.val (16*i.val+k.val)) 40 7 (kernel40_0_contains j i k) (mpower1_7_contains j i k)
noncomputable def ha40_1_7 : Fin 7 → CBox := ![⟨⟨(-3439),3439⟩,⟨(-3439),3439⟩⟩,⟨⟨(-19898),19898⟩,⟨(-19898),19898⟩⟩,⟨⟨(-6354),6449⟩,⟨(-6657),6146⟩⟩,⟨⟨(-697),747⟩,⟨(-659),784⟩⟩,⟨⟨(-53228),(-53012)⟩,⟨(-72384),(-72168)⟩⟩,⟨⟨365813296785601149,365813296785601213⟩,⟨3013513439424633265,3013513439424633329⟩⟩,⟨⟨(-736060724431938420772835023),(-736060724431938416576591027)⟩,⟨585496997041533399932033514,585496997041533404109550467⟩⟩]
lemma ha40_1_7_eq (j : Fin 7) : ha40_1_7 j = ((ha40_1_6 j).mul (piI.mul (atomPoints j).z)).scale 1 7 := by fin_cases j <;> decide +kernel
lemma ha40_1_7_contains (j : Fin 7) : (ha40_1_7 j).Contains (fullFactor true 40 7 ((j.val:ℝ)/6)) := by
  rw [ha40_1_7_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha40_1_6 j) true 40 6 j (ha40_1_6_contains j)
noncomputable def hk40_1_8 (j : Fin 6) (i k : Fin 16) : CBox := (kernel40_0 j i k).mul (mpower1_8 j i k)
lemma hk40_1_8_contains (j : Fin 6) (i k : Fin 16) :
    (hk40_1_8 j i k).Contains (fullFactor true 40 8 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk40_1_8,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel40_0 j i k) (mpower1_8 j i k) (quadraturePoint j.val (16*i.val+k.val)) 40 8 (kernel40_0_contains j i k) (mpower1_8_contains j i k)
noncomputable def ha40_1_8 : Fin 7 → CBox := ![⟨⟨(-3962),3962⟩,⟨(-3962),3962⟩⟩,⟨⟨(-28316),28316⟩,⟨(-28316),28316⟩⟩,⟨⟨(-8255),7868⟩,⟨(-7935),8188⟩⟩,⟨⟨(-686),748⟩,⟨(-755),679⟩⟩,⟨⟨(-31761),(-31594)⟩,⟨44284,44451⟩⟩,⟨⟨1506681296055313545,1506681296055313584⟩,⟨(-452111038342034514),(-452111038342034475)⟩⟩,⟨⟨281557186603028290420797546,281557186603028292405826935⟩,⟨318499213378149643897238281,318499213378149645890486172⟩⟩]
lemma ha40_1_8_eq (j : Fin 7) : ha40_1_8 j = ((ha40_1_7 j).mul (piI.mul (atomPoints j).z)).scale 1 8 := by fin_cases j <;> decide +kernel
lemma ha40_1_8_contains (j : Fin 7) : (ha40_1_8 j).Contains (fullFactor true 40 8 ((j.val:ℝ)/6)) := by
  rw [ha40_1_8_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha40_1_7 j) true 40 7 j (ha40_1_7_contains j)
noncomputable def hk40_1_9 (j : Fin 6) (i k : Fin 16) : CBox := (kernel40_0 j i k).mul (mpower1_9 j i k)
lemma hk40_1_9_contains (j : Fin 6) (i k : Fin 16) :
    (hk40_1_9 j i k).Contains (fullFactor true 40 9 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk40_1_9,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel40_0 j i k) (mpower1_9 j i k) (quadraturePoint j.val (16*i.val+k.val)) 40 9 (kernel40_0_contains j i k) (mpower1_9_contains j i k)
noncomputable def ha40_1_9 : Fin 7 → CBox := ![⟨⟨(-4057),4057⟩,⟨(-4057),4057⟩⟩,⟨⟨(-35817),35817⟩,⟨(-35817),35817⟩⟩,⟨⟨(-8845),9202⟩,⟨(-8982),9065⟩⟩,⟨⟨(-664),602⟩,⟨(-639),627⟩⟩,⟨⟨28051,28166⟩,⟨8733,8848⟩⟩,⟨⟨(-323130073323018360),(-323130073323018338)⟩,⟨(-648535005380141616),(-648535005380141594)⟩⟩,⟨⟨121915557279061779596669674,121915557279061780438251326⟩,⟨(-119612888636203860505051893),(-119612888636203859666640969)⟩⟩]
lemma ha40_1_9_eq (j : Fin 7) : ha40_1_9 j = ((ha40_1_8 j).mul (piI.mul (atomPoints j).z)).scale 1 9 := by fin_cases j <;> decide +kernel
lemma ha40_1_9_contains (j : Fin 7) : (ha40_1_9 j).Contains (fullFactor true 40 9 ((j.val:ℝ)/6)) := by
  rw [ha40_1_9_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha40_1_8 j) true 40 8 j (ha40_1_8_contains j)
noncomputable def hk40_1_10 (j : Fin 6) (i k : Fin 16) : CBox := (kernel40_0 j i k).mul (mpower1_10 j i k)
lemma hk40_1_10_contains (j : Fin 6) (i k : Fin 16) :
    (hk40_1_10 j i k).Contains (fullFactor true 40 10 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk40_1_10,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel40_0 j i k) (mpower1_10 j i k) (quadraturePoint j.val (16*i.val+k.val)) 40 10 (kernel40_0_contains j i k) (mpower1_10_contains j i k)
noncomputable def ha40_1_10 : Fin 7 → CBox := ![⟨⟨(-3739),3739⟩,⟨(-3739),3739⟩⟩,⟨⟨(-40775),40775⟩,⟨(-40775),40775⟩⟩,⟨⟨(-9157),9024⟩,⟨(-9203),8978⟩⟩,⟨⟨(-497),509⟩,⟨(-485),521⟩⟩,⟨⟨(-234),(-162)⟩,⟨(-14354),(-14282)⟩⟩,⟨⟨(-242187535003552317),(-242187535003552305)⟩,⟨177684847944160322,177684847944160334⟩⟩,⟨⟨(-45481774851456876984216890),(-45481774851456876665517088)⟩,⟨(-41778013856444853089006940),(-41778013856444852769219208)⟩⟩]
lemma ha40_1_10_eq (j : Fin 7) : ha40_1_10 j = ((ha40_1_9 j).mul (piI.mul (atomPoints j).z)).scale 1 10 := by fin_cases j <;> decide +kernel
lemma ha40_1_10_contains (j : Fin 7) : (ha40_1_10 j).Contains (fullFactor true 40 10 ((j.val:ℝ)/6)) := by
  rw [ha40_1_10_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha40_1_9 j) true 40 9 j (ha40_1_9_contains j)
noncomputable def hk40_1_11 (j : Fin 6) (i k : Fin 16) : CBox := (kernel40_0 j i k).mul (mpower1_11 j i k)
lemma hk40_1_11_contains (j : Fin 6) (i k : Fin 16) :
    (hk40_1_11 j i k).Contains (fullFactor true 40 11 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk40_1_11,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel40_0 j i k) (mpower1_11 j i k) (quadraturePoint j.val (16*i.val+k.val)) 40 11 (kernel40_0_contains j i k) (mpower1_11_contains j i k)
noncomputable def ha40_1_11 : Fin 7 → CBox := ![⟨⟨(-3133),3133⟩,⟨(-3133),3133⟩⟩,⟨⟨(-42199),42199⟩,⟨(-42199),42199⟩⟩,⟨⟨(-8348),8303⟩,⟨(-8244),8407⟩⟩,⟨⟨(-357),370⟩,⟨(-371),356⟩⟩,⟨⟨(-6007),(-5966)⟩,⟨2035,2076⟩⟩,⟨⟨81497191473969017,81497191473969023⟩,⟨78569403991563599,78569403991563605⟩⟩,⟨⟨(-12938293678809876355135207),(-12938293678809876244670428)⟩,⟨15643697368760384497823902,15643697368760384607953780⟩⟩]
lemma ha40_1_11_eq (j : Fin 7) : ha40_1_11 j = ((ha40_1_10 j).mul (piI.mul (atomPoints j).z)).scale 1 11 := by fin_cases j <;> decide +kernel
lemma ha40_1_11_contains (j : Fin 7) : (ha40_1_11 j).Contains (fullFactor true 40 11 ((j.val:ℝ)/6)) := by
  rw [ha40_1_11_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha40_1_10 j) true 40 10 j (ha40_1_10_contains j)
noncomputable def hk40_1_12 (j : Fin 6) (i k : Fin 16) : CBox := (kernel40_0 j i k).mul (mpower1_12 j i k)
lemma hk40_1_12_contains (j : Fin 6) (i k : Fin 16) :
    (hk40_1_12 j i k).Contains (fullFactor true 40 12 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk40_1_12,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel40_0 j i k) (mpower1_12 j i k) (quadraturePoint j.val (16*i.val+k.val)) 40 12 (kernel40_0_contains j i k) (mpower1_12_contains j i k)
noncomputable def ha40_1_12 : Fin 7 → CBox := ![⟨⟨(-2406),2406⟩,⟨(-2406),2406⟩⟩,⟨⟨(-40034),40034⟩,⟨(-40034),40034⟩⟩,⟨⟨(-6945),7034⟩,⟨(-7013),6966⟩⟩,⟨⟨(-246),236⟩,⟨(-242),240⟩⟩,⟨⟨1536,1558⟩,⟨2034,2056⟩⟩,⟨⟨21965032701093443,21965032701093447⟩,⟨(-32356415038641788),(-32356415038641784)⟩⟩,⟨⟨4909938778159874873450914,4909938778159874908335228⟩,⟨3648587153778259364987562,3648587153778259399964956⟩⟩]
lemma ha40_1_12_eq (j : Fin 7) : ha40_1_12 j = ((ha40_1_11 j).mul (piI.mul (atomPoints j).z)).scale 1 12 := by fin_cases j <;> decide +kernel
lemma ha40_1_12_contains (j : Fin 7) : (ha40_1_12 j).Contains (fullFactor true 40 12 ((j.val:ℝ)/6)) := by
  rw [ha40_1_12_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha40_1_11 j) true 40 11 j (ha40_1_11_contains j)
noncomputable def hk40_1_13 (j : Fin 6) (i k : Fin 16) : CBox := (kernel40_0 j i k).mul (mpower1_13 j i k)
lemma hk40_1_13_contains (j : Fin 6) (i k : Fin 16) :
    (hk40_1_13 j i k).Contains (fullFactor true 40 13 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk40_1_13,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel40_0 j i k) (mpower1_13 j i k) (quadraturePoint j.val (16*i.val+k.val)) 40 13 (kernel40_0_contains j i k) (mpower1_13_contains j i k)
noncomputable def ha40_1_13 : Fin 7 → CBox := ![⟨⟨(-1706),1706⟩,⟨(-1706),1706⟩⟩,⟨⟨(-35058),35058⟩,⟨(-35058),35058⟩⟩,⟨⟨(-5443),5390⟩,⟨(-5425),5408⟩⟩,⟨⟨(-147),148⟩,⟨(-145),150⟩⟩,⟨⟨541,552⟩,⟨(-794),(-782)⟩⟩,⟨⟨(-11358124411285479),(-11358124411285477)⟩,⟨(-5149605768211994),(-5149605768211992)⟩⟩,⟨⟨942552888006158443861305,942552888006158454084344⟩,⟨(-1416540324858875858334417),(-1416540324858875848134831)⟩⟩]
lemma ha40_1_13_eq (j : Fin 7) : ha40_1_13 j = ((ha40_1_12 j).mul (piI.mul (atomPoints j).z)).scale 1 13 := by fin_cases j <;> decide +kernel
lemma ha40_1_13_contains (j : Fin 7) : (ha40_1_13 j).Contains (fullFactor true 40 13 ((j.val:ℝ)/6)) := by
  rw [ha40_1_13_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha40_1_12 j) true 40 12 j (ha40_1_12_contains j)
noncomputable def hk40_1_14 (j : Fin 6) (i k : Fin 16) : CBox := (kernel40_0 j i k).mul (mpower1_14 j i k)
lemma hk40_1_14_contains (j : Fin 6) (i k : Fin 16) :
    (hk40_1_14 j i k).Contains (fullFactor true 40 14 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk40_1_14,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel40_0 j i k) (mpower1_14 j i k) (quadraturePoint j.val (16*i.val+k.val)) 40 14 (kernel40_0_contains j i k) (mpower1_14_contains j i k)
noncomputable def ha40_1_14 : Fin 7 → CBox := ![⟨⟨(-1123),1123⟩,⟨(-1123),1123⟩⟩,⟨⟨(-28508),28508⟩,⟨(-28508),28508⟩⟩,⟨⟨(-3892),3904⟩,⟨(-3885),3911⟩⟩,⟨⟨(-83),85⟩,⟨(-85),83⟩⟩,⟨⟨(-322),(-316)⟩,⟨(-98),(-92)⟩⟩,⟨⟨(-931291415034147),(-931291415034146)⟩,⟨3573442424518372,3573442424518374⟩⟩,⟨⟨(-378010736779680055172301),(-378010736779680052403198)⟩,⟨(-224113892390746525015629),(-224113892390746522241161)⟩⟩]
lemma ha40_1_14_eq (j : Fin 7) : ha40_1_14 j = ((ha40_1_13 j).mul (piI.mul (atomPoints j).z)).scale 1 14 := by fin_cases j <;> decide +kernel
lemma ha40_1_14_contains (j : Fin 7) : (ha40_1_14 j).Contains (fullFactor true 40 14 ((j.val:ℝ)/6)) := by
  rw [ha40_1_14_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha40_1_13 j) true 40 13 j (ha40_1_13_contains j)
noncomputable def hk40_1_15 (j : Fin 6) (i k : Fin 16) : CBox := (kernel40_0 j i k).mul (mpower1_15 j i k)
lemma hk40_1_15_contains (j : Fin 6) (i k : Fin 16) :
    (hk40_1_15 j i k).Contains (fullFactor true 40 15 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk40_1_15,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel40_0 j i k) (mpower1_15 j i k) (quadraturePoint j.val (16*i.val+k.val)) 40 15 (kernel40_0_contains j i k) (mpower1_15_contains j i k)
noncomputable def ha40_1_15 : Fin 7 → CBox := ![⟨⟨(-690),690⟩,⟨(-690),690⟩⟩,⟨⟨(-21636),21636⟩,⟨(-21636),21636⟩⟩,⟨⟨(-2616),2621⟩,⟨(-2625),2612⟩⟩,⟨⟨(-45),44⟩,⟨(-45),45⟩⟩,⟨⟨1,5⟩,⟨106,110⟩⟩,⟨⟨1016965561011323,1016965561011325⟩,⟨85853841957985,85853841957986⟩⟩,⟨⟨(-49220050476064148297996),(-49220050476064147595232)⟩,⟨93805948709273671364437,93805948709273672066088⟩⟩]
lemma ha40_1_15_eq (j : Fin 7) : ha40_1_15 j = ((ha40_1_14 j).mul (piI.mul (atomPoints j).z)).scale 1 15 := by fin_cases j <;> decide +kernel
lemma ha40_1_15_contains (j : Fin 7) : (ha40_1_15 j).Contains (fullFactor true 40 15 ((j.val:ℝ)/6)) := by
  rw [ha40_1_15_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha40_1_14 j) true 40 14 j (ha40_1_14_contains j)
noncomputable def hk40_1_16 (j : Fin 6) (i k : Fin 16) : CBox := (kernel40_0 j i k).mul (mpower1_16 j i k)
lemma hk40_1_16_contains (j : Fin 6) (i k : Fin 16) :
    (hk40_1_16 j i k).Contains (fullFactor true 40 16 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk40_1_16,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel40_0 j i k) (mpower1_16 j i k) (quadraturePoint j.val (16*i.val+k.val)) 40 16 (kernel40_0_contains j i k) (mpower1_16_contains j i k)
noncomputable def ha40_1_16 : Fin 7 → CBox := ![⟨⟨(-398),398⟩,⟨(-398),398⟩⟩,⟨⟨(-15395),15395⟩,⟨(-15395),15395⟩⟩,⟨⟨(-1652),1646⟩,⟨(-1648),1650⟩⟩,⟨⟨(-23),23⟩,⟨(-23),23⟩⟩,⟨⟨30,32⟩,⟨(-12),(-10)⟩⟩,⟨⟨(-22844725416934),(-22844725416933)⟩,⟨(-263442041938007),(-263442041938005)⟩⟩,⟨⟨21748621082995046956479,21748621082995047123152⟩,⟨10007539142231467342543,10007539142231467509424⟩⟩]
lemma ha40_1_16_eq (j : Fin 7) : ha40_1_16 j = ((ha40_1_15 j).mul (piI.mul (atomPoints j).z)).scale 1 16 := by fin_cases j <;> decide +kernel
lemma ha40_1_16_contains (j : Fin 7) : (ha40_1_16 j).Contains (fullFactor true 40 16 ((j.val:ℝ)/6)) := by
  rw [ha40_1_16_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha40_1_15 j) true 40 15 j (ha40_1_15_contains j)
noncomputable def hk40_1_17 (j : Fin 6) (i k : Fin 16) : CBox := (kernel40_0 j i k).mul (mpower1_17 j i k)
lemma hk40_1_17_contains (j : Fin 6) (i k : Fin 16) :
    (hk40_1_17 j i k).Contains (fullFactor true 40 17 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk40_1_17,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel40_0 j i k) (mpower1_17 j i k) (quadraturePoint j.val (16*i.val+k.val)) 40 17 (kernel40_0_contains j i k) (mpower1_17_contains j i k)
noncomputable def ha40_1_17 : Fin 7 → CBox := ![⟨⟨(-216),216⟩,⟨(-216),216⟩⟩,⟨⟨(-10310),10310⟩,⟨(-10310),10310⟩⟩,⟨⟨(-976),979⟩,⟨(-977),978⟩⟩,⟨⟨(-11),11⟩,⟨(-11),11⟩⟩,⟨⟨(-7),(-5)⟩,⟨(-8),(-7)⟩⟩,⟨⟨(-62361710301011),(-62361710301009)⟩,⟨16404177844075,16404177844077⟩⟩,⟨⟨1885510170541198203898,1885510170541198241196⟩,⟨(-4730234483802039233298),(-4730234483802039196035)⟩⟩]
lemma ha40_1_17_eq (j : Fin 7) : ha40_1_17 j = ((ha40_1_16 j).mul (piI.mul (atomPoints j).z)).scale 1 17 := by fin_cases j <;> decide +kernel
lemma ha40_1_17_contains (j : Fin 7) : (ha40_1_17 j).Contains (fullFactor true 40 17 ((j.val:ℝ)/6)) := by
  rw [ha40_1_17_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha40_1_16 j) true 40 16 j (ha40_1_16_contains j)
noncomputable def hk40_1_18 (j : Fin 6) (i k : Fin 16) : CBox := (kernel40_0 j i k).mul (mpower1_18 j i k)
lemma hk40_1_18_contains (j : Fin 6) (i k : Fin 16) :
    (hk40_1_18 j i k).Contains (fullFactor true 40 18 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk40_1_18,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel40_0 j i k) (mpower1_18 j i k) (quadraturePoint j.val (16*i.val+k.val)) 40 18 (kernel40_0_contains j i k) (mpower1_18_contains j i k)
noncomputable def ha40_1_18 : Fin 7 → CBox := ![⟨⟨(-111),111⟩,⟨(-111),111⟩⟩,⟨⟨(-6521),6521⟩,⟨(-6521),6521⟩⟩,⟨⟨(-548),547⟩,⟨(-548),547⟩⟩,⟨⟨(-5),5⟩,⟨(-5),5⟩⟩,⟨⟨(-2),(-1)⟩,⟨1,3⟩⟩,⟨⟨6163199413551,6163199413553⟩,⟨13511805720081,13511805720082⟩⟩,⟨⟨(-968613803248514031848),(-968613803248514023979)⟩,⟨(-328911907090003044810),(-328911907090003036936)⟩⟩]
lemma ha40_1_18_eq (j : Fin 7) : ha40_1_18 j = ((ha40_1_17 j).mul (piI.mul (atomPoints j).z)).scale 1 18 := by fin_cases j <;> decide +kernel
lemma ha40_1_18_contains (j : Fin 7) : (ha40_1_18 j).Contains (fullFactor true 40 18 ((j.val:ℝ)/6)) := by
  rw [ha40_1_18_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha40_1_17 j) true 40 17 j (ha40_1_17_contains j)
noncomputable def hk40_1_19 (j : Fin 6) (i k : Fin 16) : CBox := (kernel40_0 j i k).mul (mpower1_19 j i k)
lemma hk40_1_19_contains (j : Fin 6) (i k : Fin 16) :
    (hk40_1_19 j i k).Contains (fullFactor true 40 19 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk40_1_19,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel40_0 j i k) (mpower1_19 j i k) (quadraturePoint j.val (16*i.val+k.val)) 40 19 (kernel40_0_contains j i k) (mpower1_19_contains j i k)
noncomputable def ha40_1_19 : Fin 7 → CBox := ![⟨⟨(-54),54⟩,⟨(-54),54⟩⟩,⟨⟨(-3908),3908⟩,⟨(-3908),3908⟩⟩,⟨⟨(-291),291⟩,⟨(-291),291⟩⟩,⟨⟨(-3),3⟩,⟨(-3),3⟩⟩,⟨⟨0,1⟩,⟨0,1⟩⟩,⟨⟨2676787052090,2676787052092⟩,⟨(-1826048788243),(-1826048788242)⟩⟩,⟨⟨(-52938399912444025343),(-52938399912444023768)⟩,⟨187339502992304506687,187339502992304508262⟩⟩]
lemma ha40_1_19_eq (j : Fin 7) : ha40_1_19 j = ((ha40_1_18 j).mul (piI.mul (atomPoints j).z)).scale 1 19 := by fin_cases j <;> decide +kernel
lemma ha40_1_19_contains (j : Fin 7) : (ha40_1_19 j).Contains (fullFactor true 40 19 ((j.val:ℝ)/6)) := by
  rw [ha40_1_19_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha40_1_18 j) true 40 18 j (ha40_1_18_contains j)
noncomputable def hk40_1_20 (j : Fin 6) (i k : Fin 16) : CBox := (kernel40_0 j i k).mul (mpower1_20 j i k)
lemma hk40_1_20_contains (j : Fin 6) (i k : Fin 16) :
    (hk40_1_20 j i k).Contains (fullFactor true 40 20 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk40_1_20,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel40_0 j i k) (mpower1_20 j i k) (quadraturePoint j.val (16*i.val+k.val)) 40 20 (kernel40_0_contains j i k) (mpower1_20_contains j i k)
noncomputable def ha40_1_20 : Fin 7 → CBox := ![⟨⟨(-25),25⟩,⟨(-25),25⟩⟩,⟨⟨(-2225),2225⟩,⟨(-2225),2225⟩⟩,⟨⟨(-147),147⟩,⟨(-147),147⟩⟩,⟨⟨(-2),2⟩,⟨(-2),2⟩⟩,⟨⟨(-1),1⟩,⟨(-1),0⟩⟩,⟨⟨(-467261224227),(-467261224226)⟩,⟨(-482468609017),(-482468609016)⟩⟩,⟨⟨34321412213631553232,34321412213631553532⟩,⟨7799228685556768865,7799228685556769165⟩⟩]
lemma ha40_1_20_eq (j : Fin 7) : ha40_1_20 j = ((ha40_1_19 j).mul (piI.mul (atomPoints j).z)).scale 1 20 := by fin_cases j <;> decide +kernel
lemma ha40_1_20_contains (j : Fin 7) : (ha40_1_20 j).Contains (fullFactor true 40 20 ((j.val:ℝ)/6)) := by
  rw [ha40_1_20_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha40_1_19 j) true 40 19 j (ha40_1_19_contains j)
noncomputable def hk40_1_21 (j : Fin 6) (i k : Fin 16) : CBox := (kernel40_0 j i k).mul (mpower1_21 j i k)
lemma hk40_1_21_contains (j : Fin 6) (i k : Fin 16) :
    (hk40_1_21 j i k).Contains (fullFactor true 40 21 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk40_1_21,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel40_0 j i k) (mpower1_21 j i k) (quadraturePoint j.val (16*i.val+k.val)) 40 21 (kernel40_0_contains j i k) (mpower1_21_contains j i k)
noncomputable def ha40_1_21 : Fin 7 → CBox := ![⟨⟨(-11),11⟩,⟨(-11),11⟩⟩,⟨⟨(-1207),1207⟩,⟨(-1207),1207⟩⟩,⟨⟨(-71),71⟩,⟨(-71),71⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-78187269680),(-78187269679)⟩,⟨107081214276,107081214277⟩⟩,⟨⟨1034217675189435481,1034217675189435536⟩,⟨(-5971428595914992448),(-5971428595914992393)⟩⟩]
lemma ha40_1_21_eq (j : Fin 7) : ha40_1_21 j = ((ha40_1_20 j).mul (piI.mul (atomPoints j).z)).scale 1 21 := by fin_cases j <;> decide +kernel
lemma ha40_1_21_contains (j : Fin 7) : (ha40_1_21 j).Contains (fullFactor true 40 21 ((j.val:ℝ)/6)) := by
  rw [ha40_1_21_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha40_1_20 j) true 40 20 j (ha40_1_20_contains j)
noncomputable def hk40_1_22 (j : Fin 6) (i k : Fin 16) : CBox := (kernel40_0 j i k).mul (mpower1_22 j i k)
lemma hk40_1_22_contains (j : Fin 6) (i k : Fin 16) :
    (hk40_1_22 j i k).Contains (fullFactor true 40 22 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk40_1_22,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel40_0 j i k) (mpower1_22 j i k) (quadraturePoint j.val (16*i.val+k.val)) 40 22 (kernel40_0_contains j i k) (mpower1_22_contains j i k)
noncomputable def ha40_1_22 : Fin 7 → CBox := ![⟨⟨(-5),5⟩,⟨(-5),5⟩⟩,⟨⟨(-625),625⟩,⟨(-625),625⟩⟩,⟨⟨(-33),33⟩,⟨(-33),33⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨22387552197,22387552198⟩,⟨11090922931,11090922932⟩⟩,⟨⟨(-988962848599431676),(-988962848599431666)⟩,⟨(-118786899046655844),(-118786899046655833)⟩⟩]
lemma ha40_1_22_eq (j : Fin 7) : ha40_1_22 j = ((ha40_1_21 j).mul (piI.mul (atomPoints j).z)).scale 1 22 := by fin_cases j <;> decide +kernel
lemma ha40_1_22_contains (j : Fin 7) : (ha40_1_22 j).Contains (fullFactor true 40 22 ((j.val:ℝ)/6)) := by
  rw [ha40_1_22_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha40_1_21 j) true 40 21 j (ha40_1_21_contains j)
noncomputable def hk40_1_23 (j : Fin 6) (i k : Fin 16) : CBox := (kernel40_0 j i k).mul (mpower1_23 j i k)
lemma hk40_1_23_contains (j : Fin 6) (i k : Fin 16) :
    (hk40_1_23 j i k).Contains (fullFactor true 40 23 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk40_1_23,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel40_0 j i k) (mpower1_23 j i k) (quadraturePoint j.val (16*i.val+k.val)) 40 23 (kernel40_0_contains j i k) (mpower1_23_contains j i k)
noncomputable def ha40_1_23 : Fin 7 → CBox := ![⟨⟨(-3),3⟩,⟨(-3),3⟩⟩,⟨⟨(-310),310⟩,⟨(-310),310⟩⟩,⟨⟨(-15),15⟩,⟨(-15),15⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨1284436423,1284436424⟩,⟨(-4316137878),(-4316137877)⟩⟩,⟨⟨(-10575726714460746),(-10575726714460743)⟩,⟨156238070085025944,156238070085025947⟩⟩]
lemma ha40_1_23_eq (j : Fin 7) : ha40_1_23 j = ((ha40_1_22 j).mul (piI.mul (atomPoints j).z)).scale 1 23 := by fin_cases j <;> decide +kernel
lemma ha40_1_23_contains (j : Fin 7) : (ha40_1_23 j).Contains (fullFactor true 40 23 ((j.val:ℝ)/6)) := by
  rw [ha40_1_23_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha40_1_22 j) true 40 22 j (ha40_1_22_contains j)
noncomputable def hk40_1_24 (j : Fin 6) (i k : Fin 16) : CBox := (kernel40_0 j i k).mul (mpower1_24 j i k)
lemma hk40_1_24_contains (j : Fin 6) (i k : Fin 16) :
    (hk40_1_24 j i k).Contains (fullFactor true 40 24 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk40_1_24,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel40_0 j i k) (mpower1_24 j i k) (quadraturePoint j.val (16*i.val+k.val)) 40 24 (kernel40_0_contains j i k) (mpower1_24_contains j i k)
noncomputable def ha40_1_24 : Fin 7 → CBox := ![⟨⟨(-2),2⟩,⟨(-2),2⟩⟩,⟨⟨(-148),148⟩,⟨(-148),148⟩⟩,⟨⟨(-7),7⟩,⟨(-7),7⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-772389001),(-772389000)⟩,⟨(-91976058),(-91976057)⟩⟩,⟨⟨23590232457303446,23590232457303447⟩,⟨368828254149167,368828254149169⟩⟩]
lemma ha40_1_24_eq (j : Fin 7) : ha40_1_24 j = ((ha40_1_23 j).mul (piI.mul (atomPoints j).z)).scale 1 24 := by fin_cases j <;> decide +kernel
lemma ha40_1_24_contains (j : Fin 7) : (ha40_1_24 j).Contains (fullFactor true 40 24 ((j.val:ℝ)/6)) := by
  rw [ha40_1_24_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha40_1_23 j) true 40 23 j (ha40_1_23_contains j)
noncomputable def hk40_1_25 (j : Fin 6) (i k : Fin 16) : CBox := (kernel40_0 j i k).mul (mpower1_25 j i k)
lemma hk40_1_25_contains (j : Fin 6) (i k : Fin 16) :
    (hk40_1_25 j i k).Contains (fullFactor true 40 25 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk40_1_25,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel40_0 j i k) (mpower1_25 j i k) (quadraturePoint j.val (16*i.val+k.val)) 40 25 (kernel40_0_contains j i k) (mpower1_25_contains j i k)
noncomputable def ha40_1_25 : Fin 7 → CBox := ![⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-68),68⟩,⟨(-68),68⟩⟩,⟨⟨(-3),3⟩,⟨(-3),3⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨6729921,6729922⟩,⟨128808676,128808678⟩⟩,⟨⟨(-123910745632842),(-123910745632841)⟩,⟨(-3410167991139813),(-3410167991139812)⟩⟩]
lemma ha40_1_25_eq (j : Fin 7) : ha40_1_25 j = ((ha40_1_24 j).mul (piI.mul (atomPoints j).z)).scale 1 25 := by fin_cases j <;> decide +kernel
lemma ha40_1_25_contains (j : Fin 7) : (ha40_1_25 j).Contains (fullFactor true 40 25 ((j.val:ℝ)/6)) := by
  rw [ha40_1_25_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha40_1_24 j) true 40 24 j (ha40_1_24_contains j)
noncomputable def hk40_1_26 (j : Fin 6) (i k : Fin 16) : CBox := (kernel40_0 j i k).mul (mpower1_26 j i k)
lemma hk40_1_26_contains (j : Fin 6) (i k : Fin 16) :
    (hk40_1_26 j i k).Contains (fullFactor true 40 26 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk40_1_26,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel40_0 j i k) (mpower1_26 j i k) (quadraturePoint j.val (16*i.val+k.val)) 40 26 (kernel40_0_contains j i k) (mpower1_26_contains j i k)
noncomputable def ha40_1_26 : Fin 7 → CBox := ![⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-30),30⟩,⟨(-30),30⟩⟩,⟨⟨(-2),2⟩,⟨(-2),2⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨20056986,20056988⟩,⟨(-4546705),(-4546704)⟩⟩,⟨⟨(-472728395220447),(-472728395220445)⟩,⟨41837831168059,41837831168060⟩⟩]
lemma ha40_1_26_eq (j : Fin 7) : ha40_1_26 j = ((ha40_1_25 j).mul (piI.mul (atomPoints j).z)).scale 1 26 := by fin_cases j <;> decide +kernel
lemma ha40_1_26_contains (j : Fin 7) : (ha40_1_26 j).Contains (fullFactor true 40 26 ((j.val:ℝ)/6)) := by
  rw [ha40_1_26_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha40_1_25 j) true 40 25 j (ha40_1_25_contains j)
noncomputable def hk40_1_27 (j : Fin 6) (i k : Fin 16) : CBox := (kernel40_0 j i k).mul (mpower1_27 j i k)
lemma hk40_1_27_contains (j : Fin 6) (i k : Fin 16) :
    (hk40_1_27 j i k).Contains (fullFactor true 40 27 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk40_1_27,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel40_0 j i k) (mpower1_27 j i k) (quadraturePoint j.val (16*i.val+k.val)) 40 27 (kernel40_0_contains j i k) (mpower1_27_contains j i k)
noncomputable def ha40_1_27 : Fin 7 → CBox := ![⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-13),13⟩,⟨(-13),13⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1211144),(-1211143)⟩,⟨(-2916166),(-2916165)⟩⟩,⟨⟨8883084964888,8883084964889⟩,⟨62932537572148,62932537572150⟩⟩]
lemma ha40_1_27_eq (j : Fin 7) : ha40_1_27 j = ((ha40_1_26 j).mul (piI.mul (atomPoints j).z)).scale 1 27 := by fin_cases j <;> decide +kernel
lemma ha40_1_27_contains (j : Fin 7) : (ha40_1_27 j).Contains (fullFactor true 40 27 ((j.val:ℝ)/6)) := by
  rw [ha40_1_27_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha40_1_26 j) true 40 26 j (ha40_1_26_contains j)
noncomputable def hk40_1_28 (j : Fin 6) (i k : Fin 16) : CBox := (kernel40_0 j i k).mul (mpower1_28 j i k)
lemma hk40_1_28_contains (j : Fin 6) (i k : Fin 16) :
    (hk40_1_28 j i k).Contains (fullFactor true 40 28 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk40_1_28,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel40_0 j i k) (mpower1_28 j i k) (quadraturePoint j.val (16*i.val+k.val)) 40 28 (kernel40_0_contains j i k) (mpower1_28_contains j i k)
noncomputable def ha40_1_28 : Fin 7 → CBox := ![⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-6),6⟩,⟨(-6),6⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-395014),(-395013)⟩,⟨250062,250063⟩⟩,⟨⟨8056536613963,8056536613964⟩,⟨(-1567646598841),(-1567646598840)⟩⟩]
lemma ha40_1_28_eq (j : Fin 7) : ha40_1_28 j = ((ha40_1_27 j).mul (piI.mul (atomPoints j).z)).scale 1 28 := by fin_cases j <;> decide +kernel
lemma ha40_1_28_contains (j : Fin 7) : (ha40_1_28 j).Contains (fullFactor true 40 28 ((j.val:ℝ)/6)) := by
  rw [ha40_1_28_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha40_1_27 j) true 40 27 j (ha40_1_27_contains j)
noncomputable def hk40_1_29 (j : Fin 6) (i k : Fin 16) : CBox := (kernel40_0 j i k).mul (mpower1_29 j i k)
lemma hk40_1_29_contains (j : Fin 6) (i k : Fin 16) :
    (hk40_1_29 j i k).Contains (fullFactor true 40 29 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk40_1_29,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel40_0 j i k) (mpower1_29 j i k) (quadraturePoint j.val (16*i.val+k.val)) 40 29 (kernel40_0_contains j i k) (mpower1_29_contains j i k)
noncomputable def ha40_1_29 : Fin 7 → CBox := ![⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-3),3⟩,⟨(-3),3⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨44820,44821⟩,⟨49573,49574⟩⟩,⟨⟨(-247366054809),(-247366054808)⟩,⟨(-993034525320),(-993034525319)⟩⟩]
lemma ha40_1_29_eq (j : Fin 7) : ha40_1_29 j = ((ha40_1_28 j).mul (piI.mul (atomPoints j).z)).scale 1 29 := by fin_cases j <;> decide +kernel
lemma ha40_1_29_contains (j : Fin 7) : (ha40_1_29 j).Contains (fullFactor true 40 29 ((j.val:ℝ)/6)) := by
  rw [ha40_1_29_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha40_1_28 j) true 40 28 j (ha40_1_28_contains j)
noncomputable def hk40_1_30 (j : Fin 6) (i k : Fin 16) : CBox := (kernel40_0 j i k).mul (mpower1_30 j i k)
lemma hk40_1_30_contains (j : Fin 6) (i k : Fin 16) :
    (hk40_1_30 j i k).Contains (fullFactor true 40 30 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk40_1_30,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel40_0 j i k) (mpower1_30 j i k) (quadraturePoint j.val (16*i.val+k.val)) 40 30 (kernel40_0_contains j i k) (mpower1_30_contains j i k)
noncomputable def ha40_1_30 : Fin 7 → CBox := ![⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-2),2⟩,⟨(-2),2⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨5698,5699⟩,⟨(-7268),(-7267)⟩⟩,⟨⟨(-117980825813),(-117980825812)⟩,⟨35990356281,35990356282⟩⟩]
lemma ha40_1_30_eq (j : Fin 7) : ha40_1_30 j = ((ha40_1_29 j).mul (piI.mul (atomPoints j).z)).scale 1 30 := by fin_cases j <;> decide +kernel
lemma ha40_1_30_contains (j : Fin 7) : (ha40_1_30 j).Contains (fullFactor true 40 30 ((j.val:ℝ)/6)) := by
  rw [ha40_1_30_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha40_1_29 j) true 40 29 j (ha40_1_29_contains j)
end SharpPlanar.CachedData

end OAI
