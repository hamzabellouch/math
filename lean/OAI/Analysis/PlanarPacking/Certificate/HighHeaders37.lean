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
noncomputable def hk37_0_0 (j : Fin 6) (i k : Fin 16) : CBox := (power37 j i k).conj.mul (mpower0_0 j i k)
lemma hk37_0_0_contains (j : Fin 6) (i k : Fin 16) :
    (hk37_0_0 j i k).Contains (fullFactor false 37 0 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk37_0_0,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power37 j i k) (mpower0_0 j i k) (quadraturePoint j.val (16*i.val+k.val)) 37 0 (power37_contains j i k) (mpower0_0_contains j i k)
noncomputable def ha37_0_0 : Fin 7 → CBox := ![⟨⟨999999999999999999999999999557,1000000000000000000000000000591⟩,⟨(-591),591⟩⟩,⟨⟨866025403784438646652463972353,866025403784438646860449899485⟩,⟨499999999999999999908006033126,500000000000000000117164942813⟩⟩,⟨⟨499999999999999999690091657455,500000000000000000259566390561⟩,⟨866025403784438646493088998599,866025403784438647063422282455⟩⟩,⟨⟨(-164464382913),77269564347⟩,⟨999999999999999999879133026407,1000000000000000000120866973630⟩⟩,⟨⟨(-500000000000000000829749758478),(-499999999999999999270934145549)⟩,⟨866025403784438645955564246685,866025403784438647513752215628⟩⟩,⟨⟨(-866025403784438647780983075406),(-866025403784438645819125614846)⟩,⟨499999999999999998956455302613,500000000000000000917689817373⟩⟩,⟨⟨(-1000000000000000000242468318081),(-999999999999999999757531682067)⟩,⟨(-329663136721),155273499293⟩⟩]
lemma ha37_0_0_eq (j : Fin 7) : ha37_0_0 j = ((atomPoints j).direct.powBin 7 37).conj := by fin_cases j <;> decide +kernel
lemma ha37_0_0_contains (j : Fin 7) : (ha37_0_0 j).Contains (fullFactor false 37 0 ((j.val:ℝ)/6)) := by
  rw [ha37_0_0_eq]
  simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @direct_factor_zero_full ((atomPoints j).direct.powBin 7 37) ((j.val:ℝ)/6) 37 (@direct_power_bin_contains (atomPoints j) ((j.val:ℝ)/6) (atomPoints_contains j) 37 (by norm_num))
noncomputable def hk37_0_1 (j : Fin 6) (i k : Fin 16) : CBox := (power37 j i k).conj.mul (mpower0_1 j i k)
lemma hk37_0_1_contains (j : Fin 6) (i k : Fin 16) :
    (hk37_0_1 j i k).Contains (fullFactor false 37 1 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk37_0_1,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power37 j i k) (mpower0_1 j i k) (quadraturePoint j.val (16*i.val+k.val)) 37 1 (power37_contains j i k) (mpower0_1_contains j i k)
noncomputable def ha37_0_1 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-261799387799149436600514087268),(-261799387799149436490165404914)⟩,⟨453449841058554462589882844839,453449841058554462700227397305⟩⟩,⟨⟨(-906899682117108925613006977016),(-906899682117108925012868607446)⟩,⟨523598775598298872752131409257,523598775598298873350150621903⟩⟩,⟨⟨(-1570796326794896619424857398209),(-1570796326794896619040142601849)⟩,⟨(-258340048569),121374747850⟩⟩,⟨⟨(-1813799364234217852169182760527),(-1813799364234217848899948007068)⟩,⟨(-1047197551196597747894490497036),(-1047197551196597744626381378447)⟩⟩,⟨⟨(-1308996938995747185098339657113),(-1308996938995747179959673037496)⟩,⟨(-2267249205292772315911087205568),(-2267249205292772310767739505961)⟩⟩,⟨⟨(-487806084677),1035667288483⟩,⟨(-3141592653589793239231736686812),(-3141592653589793237698263313653)⟩⟩]
lemma ha37_0_1_eq (j : Fin 7) : ha37_0_1 j = ((ha37_0_0 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 1 := by fin_cases j <;> decide +kernel
lemma ha37_0_1_contains (j : Fin 7) : (ha37_0_1 j).Contains (fullFactor false 37 1 ((j.val:ℝ)/6)) := by
  rw [ha37_0_1_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha37_0_0 j) false 37 0 j (ha37_0_0_contains j)
noncomputable def hk37_0_2 (j : Fin 6) (i k : Fin 16) : CBox := (power37 j i k).conj.mul (mpower0_2 j i k)
lemma hk37_0_2_contains (j : Fin 6) (i k : Fin 16) :
    (hk37_0_2 j i k).Contains (fullFactor false 37 2 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk37_0_2,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power37 j i k) (mpower0_2 j i k) (quadraturePoint j.val (16*i.val+k.val)) 37 2 (power37_contains j i k) (mpower0_2_contains j i k)
noncomputable def ha37_0_2 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-118712890786751174421752378522),(-118712890786751174392486367370)⟩,⟨(-68538919452009434869399008726),(-68538919452009434840291625084)⟩⟩,⟨⟨(-274155677808037739555676365759),(-274155677808037739241681573606)⟩,⟨(-474851563147004697798301576545),(-474851563147004697482558361576)⟩⟩,⟨⟨(-95327504045),202899799679⟩,⟨(-1233700550136169827509202900107),(-1233700550136169827203121614796)⟩⟩,⟨⟨1096622711232150956047411000146,1096622711232150959473257524682⟩,⟨(-1899406252588018792180890370703),(-1899406252588018788751309744709)⟩⟩,⟨⟨2967822269668779356956353656225,2967822269668779363698426922895⟩,⟨(-1713472986300235874478330712978),(-1713472986300235867746377683463)⟩⟩,⟨⟨4934802200544679308212407877547,4934802200544679310636890182612⟩,⟨(-766244005999),1626822372531⟩⟩]
lemma ha37_0_2_eq (j : Fin 7) : ha37_0_2 j = ((ha37_0_1 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 2 := by fin_cases j <;> decide +kernel
lemma ha37_0_2_contains (j : Fin 7) : (ha37_0_2 j).Contains (fullFactor false 37 2 ((j.val:ℝ)/6)) := by
  rw [ha37_0_2_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha37_0_1 j) false 37 1 j (ha37_0_1_contains j)
noncomputable def hk37_0_3 (j : Fin 6) (i k : Fin 16) : CBox := (power37 j i k).conj.mul (mpower0_3 j i k)
lemma hk37_0_3_contains (j : Fin 6) (i k : Fin 16) :
    (hk37_0_3 j i k).Contains (fullFactor false 37 3 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk37_0_3,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power37 j i k) (mpower0_3 j i k) (quadraturePoint j.val (16*i.val+k.val)) 37 3 (power37_contains j i k) (mpower0_3_contains j i k)
noncomputable def ha37_0_3 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨11962298101967523213616229492,11962298101967523218734503483⟩,⟨(-20719308087892496644875122061),(-20719308087892496639701287918)⟩⟩,⟨⟨165754464703139973087106448216,165754464703139973197849234906⟩,⟨(-95698384815740185777131204948),(-95698384815740185667221728383)⟩⟩,⟨⟨645964097506246253576050266679,645964097506246253738370220486⟩,⟨(-49913364399),106238086682⟩⟩,⟨⟨1326035717625119783873807576824,1326035717625119786272327435059⟩,⟨765587078525921484695970677103,765587078525921487090099677310⟩⟩,⟨⟨1495287262745940398856345312229,1495287262745940404735842232149⟩,⟨2589913510986562077470500526821,2589913510986562083362313323278⟩⟩,⟨⟨(-1703604404747),802408846702⟩,⟨5167712780049970027980001312217,5167712780049970030535362585670⟩⟩]
lemma ha37_0_3_eq (j : Fin 7) : ha37_0_3 j = ((ha37_0_2 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 3 := by fin_cases j <;> decide +kernel
lemma ha37_0_3_contains (j : Fin 7) : (ha37_0_3 j).Contains (fullFactor false 37 3 ((j.val:ℝ)/6)) := by
  rw [ha37_0_3_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha37_0_2 j) false 37 2 j (ha37_0_2_contains j)
noncomputable def hk37_0_4 (j : Fin 6) (i k : Fin 16) : CBox := (power37 j i k).conj.mul (mpower0_4 j i k)
lemma hk37_0_4_contains (j : Fin 6) (i k : Fin 16) :
    (hk37_0_4 j i k).Contains (fullFactor false 37 4 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk37_0_4,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power37 j i k) (mpower0_4 j i k) (quadraturePoint j.val (16*i.val+k.val)) 37 4 (power37_contains j i k) (mpower0_4_contains j i k)
noncomputable def ha37_0_4 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2712151086516110563038389172,2712151086516110563724275524⟩,⟨1565861159883012429561959706,1565861159883012430236924496⟩⟩,⟨⟨25053778558128198862072198274,25053778558128198890926180607⟩,⟨43394417384257769000628336166,43394417384257769029758858647⟩⟩,⟨⟨(-41719599082),19600932364⟩,⟨253669507901048013605049335316,253669507901048013669599687240⟩⟩,⟨⟨(-400860456930051182711946820499),(-400860456930051181457107828900)⟩,⟨694310678148124303579108543342,694310678148124304837180663894⟩⟩,⟨⟨(-1695094429072569104129456135271),(-1695094429072569100267878024271)⟩,⟨978663224926882766613729403205,978663224926882770464966320510⟩⟩,⟨⟨(-4058712126416768219207139847142),(-4058712126416768217187244514204)⟩,⟨(-1338007770645),630210434494⟩⟩]
lemma ha37_0_4_eq (j : Fin 7) : ha37_0_4 j = ((ha37_0_3 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 4 := by fin_cases j <;> decide +kernel
lemma ha37_0_4_contains (j : Fin 7) : (ha37_0_4 j).Contains (fullFactor false 37 4 ((j.val:ℝ)/6)) := by
  rw [ha37_0_4_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha37_0_3 j) false 37 3 j (ha37_0_3_contains j)
noncomputable def hk37_0_5 (j : Fin 6) (i k : Fin 16) : CBox := (power37 j i k).conj.mul (mpower0_5 j i k)
lemma hk37_0_5_contains (j : Fin 6) (i k : Fin 16) :
    (hk37_0_5 j i k).Contains (fullFactor false 37 5 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk37_0_5,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power37 j i k) (mpower0_5 j i k) (quadraturePoint j.val (16*i.val+k.val)) 37 5 (power37_contains j i k) (mpower0_5_contains j i k)
noncomputable def ha37_0_5 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-163976597214335483827392980),(-163976597214335483756188878)⟩,⟨284015797627486289449541375,284015797627486289522271277⟩⟩,⟨⟨(-9088505524079561266842774979),(-9088505524079561260712763005)⟩,⟨5247251110858735477911141214,5247251110858735483971007662⟩⟩,⟨⟨(-79692626246167045131070830718),(-79692626246167045110538070070)⟩,⟨(-13106598599),6157814512⟩⟩,⟨⟨(-290832176770545960690200430805),(-290832176770545960162294665684)⟩,⟨(-167912035547479535678553545057),(-167912035547479535152393336787)⟩⟩,⟨⟨(-512426866294798387781023967428),(-512426866294798385762889927611)⟩,⟨(-887549367585894655700509601005),(-887549367585894653675766872824)⟩⟩,⟨⟨(-395972894245),840695076541⟩,⟨(-2550164039877345444504369958769),(-2550164039877345443227114866719)⟩⟩]
lemma ha37_0_5_eq (j : Fin 7) : ha37_0_5 j = ((ha37_0_4 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 5 := by fin_cases j <;> decide +kernel
lemma ha37_0_5_contains (j : Fin 7) : (ha37_0_5 j).Contains (fullFactor false 37 5 ((j.val:ℝ)/6)) := by
  rw [ha37_0_5_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha37_0_4 j) false 37 4 j (ha37_0_4_contains j)
noncomputable def hk37_0_6 (j : Fin 6) (i k : Fin 16) : CBox := (power37 j i k).conj.mul (mpower0_6 j i k)
lemma hk37_0_6_contains (j : Fin 6) (i k : Fin 16) :
    (hk37_0_6 j i k).Contains (fullFactor false 37 6 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk37_0_6,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power37 j i k) (mpower0_6 j i k) (quadraturePoint j.val (16*i.val+k.val)) 37 6 (power37_contains j i k) (mpower0_6_contains j i k)
noncomputable def ha37_0_6 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-24785053981387676530020934),(-24785053981387676523595158)⟩,⟨(-14309657588033580849268662),(-14309657588033580843009382)⟩⟩,⟨⟨(-915818085634149174614021974),(-915818085634149173553460616)⟩,⟨(-1586243454808811298293111300),(-1586243454808811297218173208)⟩⟩,⟨⟨(-1612112070),3431299490⟩,⟨(-20863480763352960875866477065),(-20863480763352960870424602375)⟩⟩,⟨⟨58612357480585547058285859593,58612357480585547242136989069⟩,⟨(-101519581107763923143548921198),(-101519581107763922958951899502)⟩⟩,⟨⟨387266468459182445308524779418,387266468459182446193218164689⟩,⟨(-223588399813024701127798986075),(-223588399813024700246510188558)⟩⟩,⟨⟨1335262768854589495544804804303,1335262768854589496217824280028⟩,⟨(-207330922597),440186912729⟩⟩]
lemma ha37_0_6_eq (j : Fin 7) : ha37_0_6 j = ((ha37_0_5 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 6 := by fin_cases j <;> decide +kernel
lemma ha37_0_6_contains (j : Fin 7) : (ha37_0_6 j).Contains (fullFactor false 37 6 ((j.val:ℝ)/6)) := by
  rw [ha37_0_6_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha37_0_5 j) false 37 5 j (ha37_0_5_contains j)
noncomputable def hk37_0_7 (j : Fin 6) (i k : Fin 16) : CBox := (power37 j i k).conj.mul (mpower0_7 j i k)
lemma hk37_0_7_contains (j : Fin 6) (i k : Fin 16) :
    (hk37_0_7 j i k).Contains (fullFactor false 37 7 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk37_0_7,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power37 j i k) (mpower0_7 j i k) (quadraturePoint j.val (16*i.val+k.val)) 37 7 (power37_contains j i k) (mpower0_7_contains j i k)
noncomputable def ha37_0_7 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1070359884617898513899520,1070359884617898514371121⟩,⟨(-1853917702541761442495017),(-1853917702541761442008468)⟩⟩,⟨⟨237301465925345464533413322,237301465925345464694979039⟩,⟨(-137006065231091009878523151),(-137006065231091009719427438)⟩⟩,⟨⟨4681754135318688100092019392,4681754135318688101328075704⟩,⟨(-361757103),769981806⟩⟩,⟨⟨30374587638444219441424002516,30374587638444219496751987569⟩,⟨17536776349579649229385369109,17536776349579649284449319709⟩⟩,⟨⟨83621865985773321239259142108,83621865985773321569126558296⟩,⟨144837320511075112517541003098,144837320511075112848876586972⟩⟩,⟨⟨(-197555424463),93049900471⟩,⟨599264529320792076738907109846,599264529320792077042865062469⟩⟩]
lemma ha37_0_7_eq (j : Fin 7) : ha37_0_7 j = ((ha37_0_6 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 7 := by fin_cases j <;> decide +kernel
lemma ha37_0_7_contains (j : Fin 7) : (ha37_0_7 j).Contains (fullFactor false 37 7 ((j.val:ℝ)/6)) := by
  rw [ha37_0_7_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha37_0_6 j) false 37 6 j (ha37_0_6_contains j)
noncomputable def hk37_0_8 (j : Fin 6) (i k : Fin 16) : CBox := (power37 j i k).conj.mul (mpower0_8 j i k)
lemma hk37_0_8_contains (j : Fin 6) (i k : Fin 16) :
    (hk37_0_8 j i k).Contains (fullFactor false 37 8 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk37_0_8,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power37 j i k) (mpower0_8 j i k) (quadraturePoint j.val (16*i.val+k.val)) 37 8 (power37_contains j i k) (mpower0_8_contains j i k)
noncomputable def ha37_0_8 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨121338629888859693698185,121338629888859693730417⟩,⟨70054890629433514713183,70054890629433514744273⟩⟩,⟨⟨17934052001134979758758833,17934052001134979779641500⟩,⟨31062689251548081581019091,31062689251548081602266871⟩⟩,⟨⟨(-151185575),71030842⟩,⟨919260274839426580124420179,919260274839426580370045365⟩⟩,⟨⟨(-4591117312290554828823781344),(-4591117312290554814393458806)⟩,⟨7952048448396308879805209161,7952048448396308894315353934⟩⟩,⟨⟨(-47397902300335817913825097005),(-47397902300335817805244908527)⟩,⟨27365191652122466632758619107,27365191652122466740794584734⟩⟩,⟨⟨(-235330630358893204603348134369),(-235330630358893204483235044836)⟩,⟨(-77579833772),36540610468⟩⟩]
lemma ha37_0_8_eq (j : Fin 7) : ha37_0_8 j = ((ha37_0_7 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 8 := by fin_cases j <;> decide +kernel
lemma ha37_0_8_contains (j : Fin 7) : (ha37_0_8 j).Contains (fullFactor false 37 8 ((j.val:ℝ)/6)) := by
  rw [ha37_0_8_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha37_0_7 j) false 37 7 j (ha37_0_7_contains j)
noncomputable def hk37_0_9 (j : Fin 6) (i k : Fin 16) : CBox := (power37 j i k).conj.mul (mpower0_9 j i k)
lemma hk37_0_9_contains (j : Fin 6) (i k : Fin 16) :
    (hk37_0_9 j i k).Contains (fullFactor false 37 9 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk37_0_9,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power37 j i k) (mpower0_9 j i k) (quadraturePoint j.val (16*i.val+k.val)) 37 9 (power37_contains j i k) (mpower0_9_contains j i k)
noncomputable def ha37_0_9 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-4075628328693792153474),(-4075628328693792151651)⟩,⟨7059195338064676365601,7059195338064676367500⟩⟩,⟨⟨(-3614308013089114301006811),(-3614308013089114298523013)⟩,⟨2086721704291221580736292,2086721704291221583172744⟩⟩,⟨⟨(-160441184787359821895434234),(-160441184787359821852053851)⟩,⟨(-26386861),12397221⟩⟩,⟨⟨(-1850525702701626523077753118),(-1850525702701626519695198694)⟩,⟨(-1068401512597105451802814280),(-1068401512597105448441324912)⟩⟩,⟨⟨(-7960211579480062812497652046),(-7960211579480062781045925392)⟩,⟨(-13787490894657571044927633009),(-13787490894657571013299049539)⟩⟩,⟨⟨(-12755079268),27080470650⟩,⟨(-82145886611128228820451377739),(-82145886611128228778262521518)⟩⟩]
lemma ha37_0_9_eq (j : Fin 7) : ha37_0_9 j = ((ha37_0_8 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 9 := by fin_cases j <;> decide +kernel
lemma ha37_0_9_contains (j : Fin 7) : (ha37_0_9 j).Contains (fullFactor false 37 9 ((j.val:ℝ)/6)) := by
  rw [ha37_0_9_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha37_0_8 j) false 37 8 j (ha37_0_8_contains j)
noncomputable def hk37_0_10 (j : Fin 6) (i k : Fin 16) : CBox := (power37 j i k).conj.mul (mpower0_10 j i k)
lemma hk37_0_10_contains (j : Fin 6) (i k : Fin 16) :
    (hk37_0_10 j i k).Contains (fullFactor false 37 10 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk37_0_10,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power37 j i k) (mpower0_10 j i k) (quadraturePoint j.val (16*i.val+k.val)) 37 10 (power37_contains j i k) (mpower0_10_contains j i k)
noncomputable def ha37_0_10 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-369618603571988403240),(-369618603571988403139)⟩,⟨(-213399400269781075781),(-213399400269781075684)⟩⟩,⟨⟨(-218520985876255821661670),(-218520985876255821405829)⟩,⟨(-378489450057716125006271),(-378489450057716124744963)⟩⟩,⟨⟨(-1947351),4144839⟩,⟨(-25202042373060605484689269),(-25202042373060605477794873)⟩⟩,⟨⟨223765489537285960931983063,223765489537285961636724019⟩,⟨(-387573196859101312207957926),(-387573196859101311498283699)⟩⟩,⟨⟨3609556675507699245933659237,3609556675507699254225492603⟩,⟨(-2083978518259580821507423358),(-2083978518259580813266747064)⟩⟩,⟨⟨25806891390014060006123797643,25806891390014060019459963607⟩,⟨(-4007126333),8507580765⟩⟩]
lemma ha37_0_10_eq (j : Fin 7) : ha37_0_10 j = ((ha37_0_9 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 10 := by fin_cases j <;> decide +kernel
lemma ha37_0_10_contains (j : Fin 7) : (ha37_0_10 j).Contains (fullFactor false 37 10 ((j.val:ℝ)/6)) := by
  rw [ha37_0_10_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha37_0_9 j) false 37 9 j (ha37_0_9_contains j)
noncomputable def hk37_0_11 (j : Fin 6) (i k : Fin 16) : CBox := (power37 j i k).conj.mul (mpower0_11 j i k)
lemma hk37_0_11_contains (j : Fin 6) (i k : Fin 16) :
    (hk37_0_11 j i k).Contains (fullFactor false 37 11 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk37_0_11,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power37 j i k) (mpower0_11 j i k) (quadraturePoint j.val (16*i.val+k.val)) 37 11 (power37_contains j i k) (mpower0_11_contains j i k)
noncomputable def ha37_0_11 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨10157787699515332858,10157787699515332864⟩,⟨(-17593804388058740567),(-17593804388058740562)⟩⟩,⟨⟨36032111386744300664572,36032111386744300689564⟩,⟨(-20803149208607401709528),(-20803149208607401685104)⟩⟩,⟨⟨3598843235212085339990249,3598843235212085340986223⟩,⟨(-278082),591882⟩⟩,⟨⟨73793764120052327715242239,73793764120052327850598790⟩,⟨42604849579227958615378554,42604849579227958749696535⟩⟩,⟨⟨495985727515397111286664236,495985727515397113249519380⟩,⟨859072479885680690682683430,859072479885680692658869670⟩⟩,⟨⟨(-2429759385),1144432605⟩,⟨7370430945714350775403776458,7370430945714350779236037362⟩⟩]
lemma ha37_0_11_eq (j : Fin 7) : ha37_0_11 j = ((ha37_0_10 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 11 := by fin_cases j <;> decide +kernel
lemma ha37_0_11_contains (j : Fin 7) : (ha37_0_11 j).Contains (fullFactor false 37 11 ((j.val:ℝ)/6)) := by
  rw [ha37_0_11_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha37_0_10 j) false 37 10 j (ha37_0_10_contains j)
noncomputable def hk37_0_12 (j : Fin 6) (i k : Fin 16) : CBox := (power37 j i k).conj.mul (mpower0_12 j i k)
lemma hk37_0_12_contains (j : Fin 6) (i k : Fin 16) :
    (hk37_0_12 j i k).Contains (fullFactor false 37 12 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk37_0_12,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power37 j i k) (mpower0_12 j i k) (quadraturePoint j.val (16*i.val+k.val)) 37 12 (power37_contains j i k) (mpower0_12_contains j i k)
noncomputable def ha37_0_12 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨767674536308627877,767674536308627878⟩,⟨443217100187807442,443217100187807443⟩⟩,⟨⟨1815417242369259284368,1815417242369259286506⟩,⟨3144394900720139783910,3144394900720139786102⟩⟩,⟨⟨(-77478),36401⟩,⟨471087477881817150305332,471087477881817150437205⟩⟩,⟨⟨(-7435949024744486046005210),(-7435949024744486022538630)⟩,⟨12879441513349692546904017,12879441513349692570569189⟩⟩,⟨⟨(-187420541090973603052311496),(-187420541090973602620577961)⟩,⟨108207299850538926226170342,108207299850538926654743340⟩⟩,⟨⟨(-1929574309403923048425427637),(-1929574309403923047416002052)⟩,⟨(-636109520),299611756⟩⟩]
lemma ha37_0_12_eq (j : Fin 7) : ha37_0_12 j = ((ha37_0_11 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 12 := by fin_cases j <;> decide +kernel
lemma ha37_0_12_contains (j : Fin 7) : (ha37_0_12 j).Contains (fullFactor false 37 12 ((j.val:ℝ)/6)) := by
  rw [ha37_0_12_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha37_0_11 j) false 37 11 j (ha37_0_11_contains j)
noncomputable def hk37_0_13 (j : Fin 6) (i k : Fin 16) : CBox := (power37 j i k).conj.mul (mpower0_13 j i k)
lemma hk37_0_13_contains (j : Fin 6) (i k : Fin 16) :
    (hk37_0_13 j i k).Contains (fullFactor false 37 13 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk37_0_13,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power37 j i k) (mpower0_13 j i k) (quadraturePoint j.val (16*i.val+k.val)) 37 13 (power37_contains j i k) (mpower0_13_contains j i k)
noncomputable def ha37_0_13 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-17851379306351119),(-17851379306351118)⟩,⟨30919495943783799,30919495943783800⟩⟩,⟨⟨(-253292510771476882377),(-253292510771476882198)⟩,⟨146238499277628361419,146238499277628361593⟩⟩,⟨⟨(-56921729219679268126366),(-56921729219679268110249)⟩,⟨(-9362),4399⟩⟩,⟨⟨(-2074972248239938621505248),(-2074972248239938617686010)⟩,⟨(-1197985786082331539527840),(-1197985786082331535743388)⟩⟩,⟨⟨(-21791234504823142556025080),(-21791234504823142469647909)⟩,⟨(-37743525322001707939225975),(-37743525322001707852161544)⟩⟩,⟨⟨(-72404469),153722846⟩,⟨(-466302805767612564547887711),(-466302805767612564302464652)⟩⟩]
lemma ha37_0_13_eq (j : Fin 7) : ha37_0_13 j = ((ha37_0_12 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 13 := by fin_cases j <;> decide +kernel
lemma ha37_0_13_contains (j : Fin 7) : (ha37_0_13 j).Contains (fullFactor false 37 13 ((j.val:ℝ)/6)) := by
  rw [ha37_0_13_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha37_0_12 j) false 37 12 j (ha37_0_12_contains j)
noncomputable def hk37_0_14 (j : Fin 6) (i k : Fin 16) : CBox := (power37 j i k).conj.mul (mpower0_14 j i k)
lemma hk37_0_14_contains (j : Fin 6) (i k : Fin 16) :
    (hk37_0_14 j i k).Contains (fullFactor false 37 14 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk37_0_14,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power37 j i k) (mpower0_14 j i k) (quadraturePoint j.val (16*i.val+k.val)) 37 14 (power37_contains j i k) (mpower0_14_contains j i k)
noncomputable def ha37_0_14 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1156386444162984),(-1156386444162983)⟩,⟨(-667640024824733),(-667640024824732)⟩⟩,⟨⟨(-10938614166728417765),(-10938614166728417751)⟩,⟨(-18946235501166317759),(-18946235501166317744)⟩⟩,⟨⟨(-494),1051⟩,⟨(-6386603083791852242072),(-6386603083791852240242)⟩⟩,⟨⟨179218254507678396295437,179218254507678396862161⟩,⟨(-310415122451108950310317),(-310415122451108949737971)⟩⟩,⟨⟨7058022730486958373354971,7058022730486958389658449⟩,⟨(-4074951323393142886145172),(-4074951323393142869979707)⟩⟩,⟨⟨104638104924845707091412685,104638104924845707146818565⟩,⟨(-16247525),34495326⟩⟩]
lemma ha37_0_14_eq (j : Fin 7) : ha37_0_14 j = ((ha37_0_13 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 14 := by fin_cases j <;> decide +kernel
lemma ha37_0_14_contains (j : Fin 7) : (ha37_0_14 j).Contains (fullFactor false 37 14 ((j.val:ℝ)/6)) := by
  rw [ha37_0_14_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha37_0_13 j) false 37 13 j (ha37_0_13_contains j)
noncomputable def hk37_0_15 (j : Fin 6) (i k : Fin 16) : CBox := (power37 j i k).conj.mul (mpower0_15 j i k)
lemma hk37_0_15_contains (j : Fin 6) (i k : Fin 16) :
    (hk37_0_15 j i k).Contains (fullFactor false 37 15 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk37_0_15,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power37 j i k) (mpower0_15 j i k) (quadraturePoint j.val (16*i.val+k.val)) 37 15 (power37_contains j i k) (mpower0_15_contains j i k)
noncomputable def ha37_0_15 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨23305033302576,23305033302577⟩,⟨(-40365501752148),(-40365501752147)⟩⟩,⟨⟨1322696761414360852,1322696761414360854⟩,⟨(-763659331258827444),(-763659331258827442)⟩⟩,⟨⟨668803510981146723158,668803510981146723353⟩,⟨(-52),111⟩⟩,⟨⟨43342127478025776379411,43342127478025776459464⟩,⟨25023588966689257626924,25023588966689257706134⟩⟩,⟨⟨711213174517105744916582,711213174517105747740253⟩,⟨1231857353275977867854833,1231857353275977870704249⟩⟩,⟨⟨(-7224685),3402874⟩,⟨21915353447830215821794274,21915353447830215833468214⟩⟩]
lemma ha37_0_15_eq (j : Fin 7) : ha37_0_15 j = ((ha37_0_14 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 15 := by fin_cases j <;> decide +kernel
lemma ha37_0_15_contains (j : Fin 7) : (ha37_0_15 j).Contains (fullFactor false 37 15 ((j.val:ℝ)/6)) := by
  rw [ha37_0_15_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha37_0_14 j) false 37 14 j (ha37_0_14_contains j)
noncomputable def hk37_0_16 (j : Fin 6) (i k : Fin 16) : CBox := (power37 j i k).conj.mul (mpower0_16 j i k)
lemma hk37_0_16_contains (j : Fin 6) (i k : Fin 16) :
    (hk37_0_16 j i k).Contains (fullFactor false 37 16 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk37_0_16,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power37 j i k) (mpower0_16 j i k) (quadraturePoint j.val (16*i.val+k.val)) 37 16 (power37_contains j i k) (mpower0_16_contains j i k)
noncomputable def ha37_0_16 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1320957955864,1320957955865⟩,⟨762655431406,762655431407⟩⟩,⟨⟨49981386352667221,49981386352667222⟩,⟨86570300595549323,86570300595549325⟩⟩,⟨⟨(-11),6⟩,⟨65659631149794723613,65659631149794723633⟩⟩,⟨⟨(-3275580136008399054935),(-3275580136008399044555)⟩,⟨5673471219829920489382,5673471219829920499880⟩⟩,⟨⟨(-201562188089707223839416),(-201562188089707223372539)⟩,⟨116371983552042445442077,116371983552042445904470⟩⟩,⟨⟨(-4303069587032947008502405),(-4303069587032947006196534)⟩,⟨(-1418564),668153⟩⟩]
lemma ha37_0_16_eq (j : Fin 7) : ha37_0_16 j = ((ha37_0_15 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 16 := by fin_cases j <;> decide +kernel
lemma ha37_0_16_contains (j : Fin 7) : (ha37_0_16 j).Contains (fullFactor false 37 16 ((j.val:ℝ)/6)) := by
  rw [ha37_0_16_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha37_0_15 j) false 37 15 j (ha37_0_15_contains j)
noncomputable def hk37_0_17 (j : Fin 6) (i k : Fin 16) : CBox := (power37 j i k).conj.mul (mpower0_17 j i k)
lemma hk37_0_17_contains (j : Fin 6) (i k : Fin 16) :
    (hk37_0_17 j i k).Contains (fullFactor false 37 17 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk37_0_17,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power37 j i k) (mpower0_17 j i k) (quadraturePoint j.val (16*i.val+k.val)) 37 17 (power37_contains j i k) (mpower0_17_contains j i k)
noncomputable def ha37_0_17 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-23489732359),(-23489732358)⟩,⟨40685409900,40685409901⟩⟩,⟨⟨(-5332718046471331),(-5332718046471330)⟩,⟨3078846199642597,3078846199642598⟩⟩,⟨⟨(-6066935731106195669),(-6066935731106195666)⟩,⟨(-2),1⟩⟩,⟨⟨(-698970019787090239848),(-698970019787090238551)⟩,⟨(-403550529079554597395),(-403550529079554596114)⟩⟩,⟨⟨(-17921243559351411776666),(-17921243559351411705399)⟩,⟨(-31040504379613153676543),(-31040504379613153604544)⟩⟩,⟨⟨(-123475),262151⟩,⟨(-795205400147551278702789),(-795205400147551278274133)⟩⟩]
lemma ha37_0_17_eq (j : Fin 7) : ha37_0_17 j = ((ha37_0_16 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 17 := by fin_cases j <;> decide +kernel
lemma ha37_0_17_contains (j : Fin 7) : (ha37_0_17 j).Contains (fullFactor false 37 17 ((j.val:ℝ)/6)) := by
  rw [ha37_0_17_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha37_0_16 j) false 37 16 j (ha37_0_16_contains j)
noncomputable def hk37_0_18 (j : Fin 6) (i k : Fin 16) : CBox := (power37 j i k).conj.mul (mpower0_18 j i k)
lemma hk37_0_18_contains (j : Fin 6) (i k : Fin 16) :
    (hk37_0_18 j i k).Contains (fullFactor false 37 18 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk37_0_18,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power37 j i k) (mpower0_18 j i k) (quadraturePoint j.val (16*i.val+k.val)) 37 18 (power37_contains j i k) (mpower0_18_contains j i k)
noncomputable def ha37_0_18 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1183490601),(-1183490600)⟩,⟨(-683288617),(-683288616)⟩⟩,⟨⟨(-179120011154260),(-179120011154259)⟩,⟨(-310244959971483),(-310244959971482)⟩⟩,⟨⟨(-1),1⟩,⟨(-529440020073462377),(-529440020073462376)⟩⟩,⟨⟨46955236204022331299,46955236204022331449⟩,⟨(-81328854786764263457),(-81328854786764263305)⟩⟩,⟨⟨4514658357533078053133,4514658357533078063620⟩,⟨(-2606539218020916340696),(-2606539218020916330322)⟩⟩,⟨⟨138789524622137721108926,138789524622137721184183⟩,⟨(-21551),45754⟩⟩]
lemma ha37_0_18_eq (j : Fin 7) : ha37_0_18 j = ((ha37_0_17 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 18 := by fin_cases j <;> decide +kernel
lemma ha37_0_18_contains (j : Fin 7) : (ha37_0_18 j).Contains (fullFactor false 37 18 ((j.val:ℝ)/6)) := by
  rw [ha37_0_18_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha37_0_17 j) false 37 17 j (ha37_0_17_contains j)
noncomputable def hk37_0_19 (j : Fin 6) (i k : Fin 16) : CBox := (power37 j i k).conj.mul (mpower0_19 j i k)
lemma hk37_0_19_contains (j : Fin 6) (i k : Fin 16) :
    (hk37_0_19 j i k).Contains (fullFactor false 37 19 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk37_0_19,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power37 j i k) (mpower0_19 j i k) (quadraturePoint j.val (16*i.val+k.val)) 37 19 (power37_contains j i k) (mpower0_19_contains j i k)
noncomputable def ha37_0_19 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨18829951,18829952⟩,⟨(-32614434),(-32614433)⟩⟩,⟨⟨17099355913327,17099355913328⟩,⟨(-9872317739529),(-9872317739528)⟩⟩,⟨⟨43770654673137422,43770654673137423⟩,⟨(-1),1⟩⟩,⟨⟨8964987113086656136,8964987113086656154⟩,⟨5175937723022106872,5175937723022106890⟩⟩,⟨⟨359152827132815576764,359152827132815578196⟩,⟨622070944276038604799,622070944276038606247⟩⟩,⟨⟨(-7566),3564⟩,⟨22948428997269873104272,22948428997269873116790⟩⟩]
lemma ha37_0_19_eq (j : Fin 7) : ha37_0_19 j = ((ha37_0_18 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 19 := by fin_cases j <;> decide +kernel
lemma ha37_0_19_contains (j : Fin 7) : (ha37_0_19 j).Contains (fullFactor false 37 19 ((j.val:ℝ)/6)) := by
  rw [ha37_0_19_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha37_0_18 j) false 37 18 j (ha37_0_18_contains j)
noncomputable def hk37_0_20 (j : Fin 6) (i k : Fin 16) : CBox := (power37 j i k).conj.mul (mpower0_20 j i k)
lemma hk37_0_20_contains (j : Fin 6) (i k : Fin 16) :
    (hk37_0_20 j i k).Contains (fullFactor false 37 20 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk37_0_20,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power37 j i k) (mpower0_20 j i k) (quadraturePoint j.val (16*i.val+k.val)) 37 20 (power37_contains j i k) (mpower0_20_contains j i k)
noncomputable def ha37_0_20 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨853843,853844⟩,⟨492966,492967⟩⟩,⟨⟨516913348073,516913348074⟩,⟨895320181973,895320181974⟩⟩,⟨⟨(-1),1⟩,⟨3437739179098606,3437739179098608⟩⟩,⟨⟨(-542022930869484435),(-542022930869484432)⟩,⟨938811255133340261,938811255133340264⟩⟩,⟨⟨(-81428896189552855255),(-81428896189552855064)⟩,⟨47012995134852432507,47012995134852432696⟩⟩,⟨⟨(-3604730797462500934903),(-3604730797462500932924)⟩,⟨(-1189),560⟩⟩]
lemma ha37_0_20_eq (j : Fin 7) : ha37_0_20 j = ((ha37_0_19 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 20 := by fin_cases j <;> decide +kernel
lemma ha37_0_20_contains (j : Fin 7) : (ha37_0_20 j).Contains (fullFactor false 37 20 ((j.val:ℝ)/6)) := by
  rw [ha37_0_20_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha37_0_19 j) false 37 19 j (ha37_0_19_contains j)
noncomputable def hk37_0_21 (j : Fin 6) (i k : Fin 16) : CBox := (power37 j i k).conj.mul (mpower0_21 j i k)
lemma hk37_0_21_contains (j : Fin 6) (i k : Fin 16) :
    (hk37_0_21 j i k).Contains (fullFactor false 37 21 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk37_0_21,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power37 j i k) (mpower0_21 j i k) (quadraturePoint j.val (16*i.val+k.val)) 37 21 (power37_contains j i k) (mpower0_21_contains j i k)
noncomputable def ha37_0_21 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-12292),(-12291)⟩,⟨21289,21290⟩⟩,⟨⟨(-44646528672),(-44646528671)⟩,⟨25776685346,25776685347⟩⟩,⟨⟨(-257142289286048),(-257142289286047)⟩,⟨(-1),1⟩⟩,⟨⟨(-93630556896327456),(-93630556896327454)⟩,⟨(-54057627228469228),(-54057627228469227)⟩⟩,⟨⟨(-5860939688051789423),(-5860939688051789398)⟩,⟨(-10151445319802585628),(-10151445319802585603)⟩⟩,⟨⟨(-84),178⟩,⟨(-539266466260812849093),(-539266466260812848794)⟩⟩]
lemma ha37_0_21_eq (j : Fin 7) : ha37_0_21 j = ((ha37_0_20 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 21 := by fin_cases j <;> decide +kernel
lemma ha37_0_21_contains (j : Fin 7) : (ha37_0_21 j).Contains (fullFactor false 37 21 ((j.val:ℝ)/6)) := by
  rw [ha37_0_21_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha37_0_20 j) false 37 20 j (ha37_0_20_contains j)
noncomputable def hk37_0_22 (j : Fin 6) (i k : Fin 16) : CBox := (power37 j i k).conj.mul (mpower0_22 j i k)
lemma hk37_0_22_contains (j : Fin 6) (i k : Fin 16) :
    (hk37_0_22 j i k).Contains (fullFactor false 37 22 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk37_0_22,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power37 j i k) (mpower0_22 j i k) (quadraturePoint j.val (16*i.val+k.val)) 37 22 (power37_contains j i k) (mpower0_22_contains j i k)
noncomputable def ha37_0_22 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-507),(-506)⟩,⟨(-293),(-292)⟩⟩,⟨⟨(-1226967354),(-1226967353)⟩,⟨(-2125169796),(-2125169795)⟩⟩,⟨⟨(-1),1⟩,⟨(-18359916521553),(-18359916521552)⟩⟩,⟨⟨5146274077922863,5146274077922864⟩,⟨(-8913608172637076),(-8913608172637075)⟩⟩,⟨⟨1208019168182208036,1208019168182208040⟩,⟨(-697450191936225612),(-697450191936225608)⟩⟩,⟨⟨77007071306013533777,77007071306013533821⟩,⟨(-12),26⟩⟩]
lemma ha37_0_22_eq (j : Fin 7) : ha37_0_22 j = ((ha37_0_21 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 22 := by fin_cases j <;> decide +kernel
lemma ha37_0_22_contains (j : Fin 7) : (ha37_0_22 j).Contains (fullFactor false 37 22 ((j.val:ℝ)/6)) := by
  rw [ha37_0_22_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha37_0_21 j) false 37 21 j (ha37_0_21_contains j)
noncomputable def hk37_0_23 (j : Fin 6) (i k : Fin 16) : CBox := (power37 j i k).conj.mul (mpower0_23 j i k)
lemma hk37_0_23_contains (j : Fin 6) (i k : Fin 16) :
    (hk37_0_23 j i k).Contains (fullFactor false 37 23 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk37_0_23,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power37 j i k) (mpower0_23 j i k) (quadraturePoint j.val (16*i.val+k.val)) 37 23 (power37_contains j i k) (mpower0_23_contains j i k)
noncomputable def ha37_0_23 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨6,7⟩,⟨(-12),(-11)⟩⟩,⟨⟨96759678,96759679⟩,⟨(-55864227),(-55864226)⟩⟩,⟨⟨1253899540535,1253899540536⟩,⟨(-1),1⟩⟩,⟨⟨811679013105350,811679013105351⟩,⟨468623096711943,468623096711944⟩⟩,⟨⟨79387840551870928,79387840551870929⟩,⟨137503773339017306,137503773339017308⟩⟩,⟨⟨(-4),2⟩,⟨10518471716932064452,10518471716932064459⟩⟩]
lemma ha37_0_23_eq (j : Fin 7) : ha37_0_23 j = ((ha37_0_22 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 23 := by fin_cases j <;> decide +kernel
lemma ha37_0_23_contains (j : Fin 7) : (ha37_0_23 j).Contains (fullFactor false 37 23 ((j.val:ℝ)/6)) := by
  rw [ha37_0_23_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha37_0_22 j) false 37 22 j (ha37_0_22_contains j)
noncomputable def hk37_0_24 (j : Fin 6) (i k : Fin 16) : CBox := (power37 j i k).conj.mul (mpower0_24 j i k)
lemma hk37_0_24_contains (j : Fin 6) (i k : Fin 16) :
    (hk37_0_24 j i k).Contains (fullFactor false 37 24 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk37_0_24,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power37 j i k) (mpower0_24 j i k) (quadraturePoint j.val (16*i.val+k.val)) 37 24 (power37_contains j i k) (mpower0_24_contains j i k)
noncomputable def ha37_0_24 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨0,1⟩,⟨0,1⟩⟩,⟨⟨2437536,2437537⟩,⟨4221937,4221938⟩⟩,⟨⟨(-1),1⟩,⟨82067533018,82067533019⟩⟩,⟨⟨(-40895079942577),(-40895079942576)⟩,⟨70832356240132,70832356240133⟩⟩,⟨⟨(-14999334866761558),(-14999334866761557)⟩,⟨8659870022990124,8659870022990125⟩⟩,⟨⟨(-1376864728037741371),(-1376864728037741370)⟩,⟨(-1),1⟩⟩]
lemma ha37_0_24_eq (j : Fin 7) : ha37_0_24 j = ((ha37_0_23 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 24 := by fin_cases j <;> decide +kernel
lemma ha37_0_24_contains (j : Fin 7) : (ha37_0_24 j).Contains (fullFactor false 37 24 ((j.val:ℝ)/6)) := by
  rw [ha37_0_24_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha37_0_23 j) false 37 23 j (ha37_0_23_contains j)
noncomputable def hk37_0_25 (j : Fin 6) (i k : Fin 16) : CBox := (power37 j i k).conj.mul (mpower0_25 j i k)
lemma hk37_0_25_contains (j : Fin 6) (i k : Fin 16) :
    (hk37_0_25 j i k).Contains (fullFactor false 37 25 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk37_0_25,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power37 j i k) (mpower0_25 j i k) (quadraturePoint j.val (16*i.val+k.val)) 37 25 (power37_contains j i k) (mpower0_25_contains j i k)
noncomputable def ha37_0_25 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),0⟩,⟨0,1⟩⟩,⟨⟨(-176849),(-176848)⟩,⟨102103,102104⟩⟩,⟨⟨(-5156455177),(-5156455176)⟩,⟨(-1),1⟩⟩,⟨⟨(-5934037600013),(-5934037600012)⟩,⟨(-3426018205749),(-3426018205748)⟩⟩,⟨⟨(-906859468175609),(-906859468175608)⟩,⟨(-1570726674205046),(-1570726674205044)⟩⟩,⟨⟨(-1),1⟩,⟨(-173021924583611077),(-173021924583611076)⟩⟩]
lemma ha37_0_25_eq (j : Fin 7) : ha37_0_25 j = ((ha37_0_24 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 25 := by fin_cases j <;> decide +kernel
lemma ha37_0_25_contains (j : Fin 7) : (ha37_0_25 j).Contains (fullFactor false 37 25 ((j.val:ℝ)/6)) := by
  rw [ha37_0_25_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha37_0_24 j) false 37 24 j (ha37_0_24_contains j)
noncomputable def hk37_0_26 (j : Fin 6) (i k : Fin 16) : CBox := (power37 j i k).conj.mul (mpower0_26 j i k)
lemma hk37_0_26_contains (j : Fin 6) (i k : Fin 16) :
    (hk37_0_26 j i k).Contains (fullFactor false 37 26 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk37_0_26,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power37 j i k) (mpower0_26 j i k) (quadraturePoint j.val (16*i.val+k.val)) 37 26 (power37_contains j i k) (mpower0_26_contains j i k)
noncomputable def ha37_0_26 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),0⟩,⟨(-1),0⟩⟩,⟨⟨(-4113),(-4112)⟩,⟨(-7123),(-7122)⟩⟩,⟨⟨(-1),1⟩,⟨(-311528495),(-311528494)⟩⟩,⟨⟨275978298108,275978298109⟩,⟨(-478008434111),(-478008434110)⟩⟩,⟨⟨158159723733336,158159723733337⟩,⟨(-91313559072399),(-91313559072398)⟩⟩,⟨⟨20906323353147684,20906323353147685⟩,⟨(-1),1⟩⟩]
lemma ha37_0_26_eq (j : Fin 7) : ha37_0_26 j = ((ha37_0_25 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 26 := by fin_cases j <;> decide +kernel
lemma ha37_0_26_contains (j : Fin 7) : (ha37_0_26 j).Contains (fullFactor false 37 26 ((j.val:ℝ)/6)) := by
  rw [ha37_0_26_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha37_0_25 j) false 37 25 j (ha37_0_25_contains j)
noncomputable def hk37_0_27 (j : Fin 6) (i k : Fin 16) : CBox := (power37 j i k).conj.mul (mpower0_27 j i k)
lemma hk37_0_27_contains (j : Fin 6) (i k : Fin 16) :
    (hk37_0_27 j i k).Contains (fullFactor false 37 27 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk37_0_27,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power37 j i k) (mpower0_27 j i k) (quadraturePoint j.val (16*i.val+k.val)) 37 27 (power37_contains j i k) (mpower0_27_contains j i k)
noncomputable def ha37_0_27 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨0,1⟩,⟨(-1),0⟩⟩,⟨⟨276,277⟩,⟨(-160),(-159)⟩⟩,⟨⟨18123993,18123994⟩,⟨(-1),1⟩⟩,⟨⟨37079204566,37079204567⟩,⟨21407688737,21407688739⟩⟩,⟨⟨8854012541820,8854012541821⟩,⟨15335599573285,15335599573286⟩⟩,⟨⟨(-1),1⟩,⟨2432561179993388,2432561179993389⟩⟩]
lemma ha37_0_27_eq (j : Fin 7) : ha37_0_27 j = ((ha37_0_26 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 27 := by fin_cases j <;> decide +kernel
lemma ha37_0_27_contains (j : Fin 7) : (ha37_0_27 j).Contains (fullFactor false 37 27 ((j.val:ℝ)/6)) := by
  rw [ha37_0_27_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha37_0_26 j) false 37 26 j (ha37_0_26_contains j)
noncomputable def hk37_0_28 (j : Fin 6) (i k : Fin 16) : CBox := (power37 j i k).conj.mul (mpower0_28 j i k)
lemma hk37_0_28_contains (j : Fin 6) (i k : Fin 16) :
    (hk37_0_28 j i k).Contains (fullFactor false 37 28 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk37_0_28,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power37 j i k) (mpower0_28 j i k) (quadraturePoint j.val (16*i.val+k.val)) 37 28 (power37_contains j i k) (mpower0_28_contains j i k)
noncomputable def ha37_0_28 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨0,1⟩,⟨0,1⟩⟩,⟨⟨5,6⟩,⟨10,11⟩⟩,⟨⟨(-1),1⟩,⟨1016753,1016754⟩⟩,⟨⟨(-1601291374),(-1601291373)⟩,⟨2773518015,2773518016⟩⟩,⟨⟨(-1433875207079),(-1433875207078)⟩,⟨827848236790,827848236791⟩⟩,⟨⟨(-272932726159820),(-272932726159819)⟩,⟨(-1),1⟩⟩]
lemma ha37_0_28_eq (j : Fin 7) : ha37_0_28 j = ((ha37_0_27 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 28 := by fin_cases j <;> decide +kernel
lemma ha37_0_28_contains (j : Fin 7) : (ha37_0_28 j).Contains (fullFactor false 37 28 ((j.val:ℝ)/6)) := by
  rw [ha37_0_28_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha37_0_27 j) false 37 27 j (ha37_0_27_contains j)
noncomputable def hk37_0_29 (j : Fin 6) (i k : Fin 16) : CBox := (power37 j i k).conj.mul (mpower0_29 j i k)
lemma hk37_0_29_contains (j : Fin 6) (i k : Fin 16) :
    (hk37_0_29 j i k).Contains (fullFactor false 37 29 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk37_0_29,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power37 j i k) (mpower0_29 j i k) (quadraturePoint j.val (16*i.val+k.val)) 37 29 (power37_contains j i k) (mpower0_29_contains j i k)
noncomputable def ha37_0_29 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),0⟩,⟨0,1⟩⟩,⟨⟨(-1),0⟩,⟨0,1⟩⟩,⟨⟨(-55073),(-55072)⟩,⟨(-1),1⟩⟩,⟨⟨(-200304916),(-200304915)⟩,⟨(-115646097),(-115646096)⟩⟩,⟨⟨(-74734538477),(-74734538476)⟩,⟨(-129444017722),(-129444017721)⟩⟩,⟨⟨(-1),1⟩,⟨(-29567015428550),(-29567015428549)⟩⟩]
lemma ha37_0_29_eq (j : Fin 7) : ha37_0_29 j = ((ha37_0_28 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 29 := by fin_cases j <;> decide +kernel
lemma ha37_0_29_contains (j : Fin 7) : (ha37_0_29 j).Contains (fullFactor false 37 29 ((j.val:ℝ)/6)) := by
  rw [ha37_0_29_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha37_0_28 j) false 37 28 j (ha37_0_28_contains j)
noncomputable def hk37_0_30 (j : Fin 6) (i k : Fin 16) : CBox := (power37 j i k).conj.mul (mpower0_30 j i k)
lemma hk37_0_30_contains (j : Fin 6) (i k : Fin 16) :
    (hk37_0_30 j i k).Contains (fullFactor false 37 30 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk37_0_30,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power37 j i k) (mpower0_30 j i k) (quadraturePoint j.val (16*i.val+k.val)) 37 30 (power37_contains j i k) (mpower0_30_contains j i k)
noncomputable def ha37_0_30 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),0⟩,⟨(-1),0⟩⟩,⟨⟨(-1),0⟩,⟨(-1),0⟩⟩,⟨⟨(-1),1⟩,⟨(-2884),(-2883)⟩⟩,⟨⟨8073620,8073621⟩,⟨(-13983922),(-13983921)⟩⟩,⟨⟨11296121531,11296121532⟩,⟨(-6521818807),(-6521818806)⟩⟩,⟨⟨3096250615296,3096250615297⟩,⟨(-1),1⟩⟩]
lemma ha37_0_30_eq (j : Fin 7) : ha37_0_30 j = ((ha37_0_29 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 30 := by fin_cases j <;> decide +kernel
lemma ha37_0_30_contains (j : Fin 7) : (ha37_0_30 j).Contains (fullFactor false 37 30 ((j.val:ℝ)/6)) := by
  rw [ha37_0_30_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha37_0_29 j) false 37 29 j (ha37_0_29_contains j)
noncomputable def hk37_1_0 (j : Fin 6) (i k : Fin 16) : CBox := (kernel37_0 j i k).mul (mpower1_0 j i k)
lemma hk37_1_0_contains (j : Fin 6) (i k : Fin 16) :
    (hk37_1_0 j i k).Contains (fullFactor true 37 0 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk37_1_0,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel37_0 j i k) (mpower1_0 j i k) (quadraturePoint j.val (16*i.val+k.val)) 37 0 (kernel37_0_contains j i k) (mpower1_0_contains j i k)
noncomputable def ha37_1_0 : Fin 7 → CBox := ![⟨⟨(-3),3⟩,⟨(-3),3⟩⟩,⟨⟨(-4),4⟩,⟨(-4),4⟩⟩,⟨⟨(-2),4⟩,⟨(-4),2⟩⟩,⟨⟨0,3⟩,⟨(-2),2⟩⟩,⟨⟨640417,640420⟩,⟨(-172576),(-172573)⟩⟩,⟨⟨4344109497548861007,4344109497548861053⟩,⟨4160151813898398136,4160151813898398182⟩⟩,⟨⟨918146183807522803526732868,918146183807522811268423752⟩,⟨(-467290594442411598540061168),(-467290594442411590816352397)⟩⟩]
lemma ha37_1_0_eq (j : Fin 7) : ha37_1_0 j = atomKernel37_0 j := by fin_cases j <;> decide +kernel
lemma ha37_1_0_contains (j : Fin 7) : (ha37_1_0 j).Contains (fullFactor true 37 0 ((j.val:ℝ)/6)) := by
  rw [ha37_1_0_eq]
  simpa only [fullFactor,ite_true] using atomKernel37_0_contains j
noncomputable def hk37_1_1 (j : Fin 6) (i k : Fin 16) : CBox := (kernel37_0 j i k).mul (mpower1_1 j i k)
lemma hk37_1_1_contains (j : Fin 6) (i k : Fin 16) :
    (hk37_1_1 j i k).Contains (fullFactor true 37 1 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk37_1_1,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel37_0 j i k) (mpower1_1 j i k) (quadraturePoint j.val (16*i.val+k.val)) 37 1 (kernel37_0_contains j i k) (mpower1_1_contains j i k)
noncomputable def ha37_1_1 : Fin 7 → CBox := ![⟨⟨(-28),28⟩,⟨(-28),28⟩⟩,⟨⟨(-46),46⟩,⟨(-46),46⟩⟩,⟨⟨(-41),21⟩,⟨(-31),30⟩⟩,⟨⟨(-19),11⟩,⟨(-21),6⟩⟩,⟨⟨(-1767764),(-1767745)⟩,⟨(-2697224),(-2697205)⟩⟩,⟨⟨13935873524237933494,13935873524237933716⟩,⟨(-20676989198405546918),(-20676989198405546696)⟩⟩,⟨⟨(-1859801892531483976917095203),(-1859801892531483947566978519)⟩,⟨(-3227705054763723539994758263),(-3227705054763723510578171492)⟩⟩]
lemma ha37_1_1_eq (j : Fin 7) : ha37_1_1 j = ((ha37_1_0 j).mul (piI.mul (atomPoints j).z)).scale 1 1 := by fin_cases j <;> decide +kernel
lemma ha37_1_1_contains (j : Fin 7) : (ha37_1_1 j).Contains (fullFactor true 37 1 ((j.val:ℝ)/6)) := by
  rw [ha37_1_1_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha37_1_0 j) true 37 0 j (ha37_1_0_contains j)
noncomputable def hk37_1_2 (j : Fin 6) (i k : Fin 16) : CBox := (kernel37_0 j i k).mul (mpower1_2 j i k)
lemma hk37_1_2_contains (j : Fin 6) (i k : Fin 16) :
    (hk37_1_2 j i k).Contains (fullFactor true 37 2 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk37_1_2,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel37_0 j i k) (mpower1_2 j i k) (quadraturePoint j.val (16*i.val+k.val)) 37 2 (kernel37_0_contains j i k) (mpower1_2_contains j i k)
noncomputable def ha37_1_2 : Fin 7 → CBox := ![⟨⟨(-130),130⟩,⟨(-130),130⟩⟩,⟨⟨(-262),262⟩,⟨(-262),262⟩⟩,⟨⟨(-132),179⟩,⟨(-128),182⟩⟩,⟨⟨(-70),43⟩,⟨(-37),79⟩⟩,⟨⟨(-4891191),(-4891132)⟩,⟨6127094,6127154⟩⟩,⟨⟨(-47143363989244490672),(-47143363989244490139)⟩,⟨(-21184630629088004693),(-21184630629088004160)⟩⟩,⟨⟨(-5653052879275558233852965209),(-5653052879275558177966244052)⟩,⟨3660935032232944014075610826,3660935032232944069841107317⟩⟩]
lemma ha37_1_2_eq (j : Fin 7) : ha37_1_2 j = ((ha37_1_1 j).mul (piI.mul (atomPoints j).z)).scale 1 2 := by fin_cases j <;> decide +kernel
lemma ha37_1_2_contains (j : Fin 7) : (ha37_1_2 j).Contains (fullFactor true 37 2 ((j.val:ℝ)/6)) := by
  rw [ha37_1_2_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha37_1_1 j) true 37 1 j (ha37_1_1_contains j)
noncomputable def hk37_1_3 (j : Fin 6) (i k : Fin 16) : CBox := (kernel37_0 j i k).mul (mpower1_3 j i k)
lemma hk37_1_3_contains (j : Fin 6) (i k : Fin 16) :
    (hk37_1_3 j i k).Contains (fullFactor true 37 3 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk37_1_3,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel37_0 j i k) (mpower1_3 j i k) (quadraturePoint j.val (16*i.val+k.val)) 37 3 (kernel37_0_contains j i k) (mpower1_3_contains j i k)
noncomputable def ha37_1_3 : Fin 7 → CBox := ![⟨⟨(-400),400⟩,⟨(-400),400⟩⟩,⟨⟨(-995),995⟩,⟨(-995),995⟩⟩,⟨⟨(-514),530⟩,⟨(-606),437⟩⟩,⟨⟨(-104),201⟩,⟨(-148),155⟩⟩,⟨⟨11906305,11906428⟩,⟨4437384,4437507⟩⟩,⟨⟨(-17780726288434282856),(-17780726288434282003)⟩,⟨69171680068521329164,69171680068521330016⟩⟩,⟨⟨4760408142191049565667575376,4760408142191049636304293880⟩,⟨6575298364963613156734701198,6575298364963613227516982995⟩⟩]
lemma ha37_1_3_eq (j : Fin 7) : ha37_1_3 j = ((ha37_1_2 j).mul (piI.mul (atomPoints j).z)).scale 1 3 := by fin_cases j <;> decide +kernel
lemma ha37_1_3_contains (j : Fin 7) : (ha37_1_3 j).Contains (fullFactor true 37 3 ((j.val:ℝ)/6)) := by
  rw [ha37_1_3_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha37_1_2 j) true 37 2 j (ha37_1_2_contains j)
noncomputable def hk37_1_4 (j : Fin 6) (i k : Fin 16) : CBox := (kernel37_0 j i k).mul (mpower1_4 j i k)
lemma hk37_1_4_contains (j : Fin 6) (i k : Fin 16) :
    (hk37_1_4 j i k).Contains (fullFactor true 37 4 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk37_1_4,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel37_0 j i k) (mpower1_4 j i k) (quadraturePoint j.val (16*i.val+k.val)) 37 4 (kernel37_0_contains j i k) (mpower1_4_contains j i k)
noncomputable def ha37_1_4 : Fin 7 → CBox := ![⟨⟨(-922),922⟩,⟨(-922),922⟩⟩,⟨⟨(-2832),2832⟩,⟨(-2832),2832⟩⟩,⟨⟨(-1433),1196⟩,⟨(-1221),1408⟩⟩,⟨⟨(-332),272⟩,⟨(-367),238⟩⟩,⟨⟨614545,614735⟩,⟨(-15432994),(-15432804)⟩⟩,⟨⟨73777461411469450171,73777461411469451192⟩,⟨5980391993766767191,5980391993766768213⟩⟩,⟨⟨5712423951050474562510354708,5712423951050474629745049618⟩,⟨(-4606155895862078175145584391),(-4606155895862078108040408476)⟩⟩]
lemma ha37_1_4_eq (j : Fin 7) : ha37_1_4 j = ((ha37_1_3 j).mul (piI.mul (atomPoints j).z)).scale 1 4 := by fin_cases j <;> decide +kernel
lemma ha37_1_4_contains (j : Fin 7) : (ha37_1_4 j).Contains (fullFactor true 37 4 ((j.val:ℝ)/6)) := by
  rw [ha37_1_4_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha37_1_3 j) true 37 3 j (ha37_1_3_contains j)
noncomputable def hk37_1_5 (j : Fin 6) (i k : Fin 16) : CBox := (kernel37_0 j i k).mul (mpower1_5 j i k)
lemma hk37_1_5_contains (j : Fin 6) (i k : Fin 16) :
    (hk37_1_5 j i k).Contains (fullFactor true 37 5 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk37_1_5,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel37_0 j i k) (mpower1_5 j i k) (quadraturePoint j.val (16*i.val+k.val)) 37 5 (kernel37_0_contains j i k) (mpower1_5_contains j i k)
noncomputable def ha37_1_5 : Fin 7 → CBox := ![⟨⟨(-1700),1700⟩,⟨(-1700),1700⟩⟩,⟨⟨(-6448),6448⟩,⟨(-6448),6448⟩⟩,⟨⟨(-2436),2862⟩,⟨(-2619),2679⟩⟩,⟨⟨(-529),432⟩,⟨(-413),547⟩⟩,⟨⟨(-14446362),(-14446128)⟩,⟨4109226,4109460⟩⟩,⟨⟨(-5506033194194289397),(-5506033194194288417)⟩,⟨(-61122958207581120856),(-61122958207581119876)⟩⟩,⟨⟨(-3541117976530520963240694540),(-3541117976530520912240738465)⟩,⟨(-3952559657833703827951031511),(-3952559657833703776859989286)⟩⟩]
lemma ha37_1_5_eq (j : Fin 7) : ha37_1_5 j = ((ha37_1_4 j).mul (piI.mul (atomPoints j).z)).scale 1 5 := by fin_cases j <;> decide +kernel
lemma ha37_1_5_contains (j : Fin 7) : (ha37_1_5 j).Contains (fullFactor true 37 5 ((j.val:ℝ)/6)) := by
  rw [ha37_1_5_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha37_1_4 j) true 37 4 j (ha37_1_4_contains j)
noncomputable def hk37_1_6 (j : Fin 6) (i k : Fin 16) : CBox := (kernel37_0 j i k).mul (mpower1_6 j i k)
lemma hk37_1_6_contains (j : Fin 6) (i k : Fin 16) :
    (hk37_1_6 j i k).Contains (fullFactor true 37 6 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk37_1_6,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel37_0 j i k) (mpower1_6 j i k) (quadraturePoint j.val (16*i.val+k.val)) 37 6 (kernel37_0_contains j i k) (mpower1_6_contains j i k)
noncomputable def ha37_1_6 : Fin 7 → CBox := ![⟨⟨(-2612),2612⟩,⟨(-2612),2612⟩⟩,⟨⟨(-12235),12235⟩,⟨(-12235),12235⟩⟩,⟨⟨(-4597),4299⟩,⟨(-4655),4241⟩⟩,⟨⟨(-556),716⟩,⟨(-626),646⟩⟩,⟨⟨6812602,6812842⟩,⟨10085609,10085850⟩⟩,⟨⟨(-40971242018793126507),(-40971242018793125723)⟩,⟨10923830489994791299,10923830489994792083⟩⟩,⟨⟨(-2267978040700473717894383236),(-2267978040700473685541872423)⟩,⟨2254875767150800268330887484,2254875767150800300630682597⟩⟩]
lemma ha37_1_6_eq (j : Fin 7) : ha37_1_6 j = ((ha37_1_5 j).mul (piI.mul (atomPoints j).z)).scale 1 6 := by fin_cases j <;> decide +kernel
lemma ha37_1_6_contains (j : Fin 7) : (ha37_1_6 j).Contains (fullFactor true 37 6 ((j.val:ℝ)/6)) := by
  rw [ha37_1_6_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha37_1_5 j) true 37 5 j (ha37_1_5_contains j)
noncomputable def hk37_1_7 (j : Fin 6) (i k : Fin 16) : CBox := (kernel37_0 j i k).mul (mpower1_7 j i k)
lemma hk37_1_7_contains (j : Fin 6) (i k : Fin 16) :
    (hk37_1_7 j i k).Contains (fullFactor true 37 7 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk37_1_7,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel37_0 j i k) (mpower1_7 j i k) (quadraturePoint j.val (16*i.val+k.val)) 37 7 (kernel37_0_contains j i k) (mpower1_7_contains j i k)
noncomputable def ha37_1_7 : Fin 7 → CBox := ![⟨⟨(-3439),3439⟩,⟨(-3439),3439⟩⟩,⟨⟨(-19898),19898⟩,⟨(-19898),19898⟩⟩,⟨⟨(-6449),6354⟩,⟨(-6146),6657⟩⟩,⟨⟨(-747),697⟩,⟨(-784),659⟩⟩,⟨⟨5181645,5181857⟩,⟨(-6679845),(-6679634)⟩⟩,⟨⟨10497619079020689615,10497619079020690152⟩,⟨22812277696157862769,22812277696157863307⟩⟩,⟨⟨1224040136075421604335228910,1224040136075421621869173817⟩,⟨1109474596327746114642455815,1109474596327746132202200999⟩⟩]
lemma ha37_1_7_eq (j : Fin 7) : ha37_1_7 j = ((ha37_1_6 j).mul (piI.mul (atomPoints j).z)).scale 1 7 := by fin_cases j <;> decide +kernel
lemma ha37_1_7_contains (j : Fin 7) : (ha37_1_7 j).Contains (fullFactor true 37 7 ((j.val:ℝ)/6)) := by
  rw [ha37_1_7_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha37_1_6 j) true 37 6 j (ha37_1_6_contains j)
noncomputable def hk37_1_8 (j : Fin 6) (i k : Fin 16) : CBox := (kernel37_0 j i k).mul (mpower1_8 j i k)
lemma hk37_1_8_contains (j : Fin 6) (i k : Fin 16) :
    (hk37_1_8 j i k).Contains (fullFactor true 37 8 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk37_1_8,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel37_0 j i k) (mpower1_8 j i k) (quadraturePoint j.val (16*i.val+k.val)) 37 8 (kernel37_0_contains j i k) (mpower1_8_contains j i k)
noncomputable def ha37_1_8 : Fin 7 → CBox := ![⟨⟨(-3962),3962⟩,⟨(-3962),3962⟩⟩,⟨⟨(-28316),28316⟩,⟨(-28316),28316⟩⟩,⟨⟨(-7868),8255⟩,⟨(-8188),7935⟩⟩,⟨⟨(-748),686⟩,⟨(-679),755⟩⟩,⟨⟨(-4839147),(-4838984)⟩,⟨(-1727263),(-1727099)⟩⟩,⟨⟨10725172713320644233,10725172713320644556⟩,⟨(-7369085465573956964),(-7369085465573956641)⟩⟩,⟨⟨472062441840471498172774701,472062441840471506512098317⟩,⟨(-578546321226195164728478133),(-578546321226195156400038578)⟩⟩]
lemma ha37_1_8_eq (j : Fin 7) : ha37_1_8 j = ((ha37_1_7 j).mul (piI.mul (atomPoints j).z)).scale 1 8 := by fin_cases j <;> decide +kernel
lemma ha37_1_8_contains (j : Fin 7) : (ha37_1_8 j).Contains (fullFactor true 37 8 ((j.val:ℝ)/6)) := by
  rw [ha37_1_8_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha37_1_7 j) true 37 7 j (ha37_1_7_contains j)
noncomputable def hk37_1_9 (j : Fin 6) (i k : Fin 16) : CBox := (kernel37_0 j i k).mul (mpower1_9 j i k)
lemma hk37_1_9_contains (j : Fin 6) (i k : Fin 16) :
    (hk37_1_9 j i k).Contains (fullFactor true 37 9 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk37_1_9,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel37_0 j i k) (mpower1_9 j i k) (quadraturePoint j.val (16*i.val+k.val)) 37 9 (kernel37_0_contains j i k) (mpower1_9_contains j i k)
noncomputable def ha37_1_9 : Fin 7 → CBox := ![⟨⟨(-4057),4057⟩,⟨(-4057),4057⟩⟩,⟨⟨(-35817),35817⟩,⟨(-35817),35817⟩⟩,⟨⟨(-9202),8845⟩,⟨(-9065),8982⟩⟩,⟨⟨(-602),664⟩,⟨(-627),639⟩⟩,⟨⟨(-71906),(-71794)⟩,⟨2774802,2774914⟩⟩,⟨⟨(-4184298758307195196),(-4184298758307195023)⟩,⟨(-4291713509554320739),(-4291713509554320566)⟩⟩,⟨⟨(-241976286499405232906370225),(-241976286499405229390031672)⟩,⟨(-177332687349981139256365634),(-177332687349981135736016127)⟩⟩]
lemma ha37_1_9_eq (j : Fin 7) : ha37_1_9 j = ((ha37_1_8 j).mul (piI.mul (atomPoints j).z)).scale 1 9 := by fin_cases j <;> decide +kernel
lemma ha37_1_9_contains (j : Fin 7) : (ha37_1_9 j).Contains (fullFactor true 37 9 ((j.val:ℝ)/6)) := by
  rw [ha37_1_9_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha37_1_8 j) true 37 8 j (ha37_1_8_contains j)
noncomputable def hk37_1_10 (j : Fin 6) (i k : Fin 16) : CBox := (kernel37_0 j i k).mul (mpower1_10 j i k)
lemma hk37_1_10_contains (j : Fin 6) (i k : Fin 16) :
    (hk37_1_10 j i k).Contains (fullFactor true 37 10 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk37_1_10,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel37_0 j i k) (mpower1_10 j i k) (quadraturePoint j.val (16*i.val+k.val)) 37 10 (kernel37_0_contains j i k) (mpower1_10_contains j i k)
noncomputable def ha37_1_10 : Fin 7 → CBox := ![⟨⟨(-3739),3739⟩,⟨(-3739),3739⟩⟩,⟨⟨(-40775),40775⟩,⟨(-40775),40775⟩⟩,⟨⟨(-9024),9157⟩,⟨(-8978),9203⟩⟩,⟨⟨(-509),497⟩,⟨(-521),485⟩⟩,⟨⟨1292834,1292904⟩,⟨(-387330),(-387260)⟩⟩,⟨⟨(-1458589750693653586),(-1458589750693653502)⟩,⟨2011677458340643893,2011677458340643977⟩⟩,⟨⟨(-59491625261097004472004932),(-59491625261097003134551796)⟩,⟨90708102475415221579488621,90708102475415222915639146⟩⟩]
lemma ha37_1_10_eq (j : Fin 7) : ha37_1_10 j = ((ha37_1_9 j).mul (piI.mul (atomPoints j).z)).scale 1 10 := by fin_cases j <;> decide +kernel
lemma ha37_1_10_contains (j : Fin 7) : (ha37_1_10 j).Contains (fullFactor true 37 10 ((j.val:ℝ)/6)) := by
  rw [ha37_1_10_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha37_1_9 j) true 37 9 j (ha37_1_9_contains j)
noncomputable def hk37_1_11 (j : Fin 6) (i k : Fin 16) : CBox := (kernel37_0 j i k).mul (mpower1_11 j i k)
lemma hk37_1_11_contains (j : Fin 6) (i k : Fin 16) :
    (hk37_1_11 j i k).Contains (fullFactor true 37 11 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk37_1_11,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel37_0 j i k) (mpower1_11 j i k) (quadraturePoint j.val (16*i.val+k.val)) 37 11 (kernel37_0_contains j i k) (mpower1_11_contains j i k)
noncomputable def ha37_1_11 : Fin 7 → CBox := ![⟨⟨(-3133),3133⟩,⟨(-3133),3133⟩⟩,⟨⟨(-42199),42199⟩,⟨(-42199),42199⟩⟩,⟨⟨(-8303),8348⟩,⟨(-8407),8244⟩⟩,⟨⟨(-370),357⟩,⟨(-356),371⟩⟩,⟨⟨(-340789),(-340749)⟩,⟨(-489670),(-489630)⟩⟩,⟨⟨840508187239479960,840508187239479998⟩,⟨412903305770674694,412903305770674732⟩⟩,⟨⟨30792751087470671147001011,30792751087470671608554701⟩,⟨17981203932682540307041509,17981203932682540768969655⟩⟩]
lemma ha37_1_11_eq (j : Fin 7) : ha37_1_11 j = ((ha37_1_10 j).mul (piI.mul (atomPoints j).z)).scale 1 11 := by fin_cases j <;> decide +kernel
lemma ha37_1_11_contains (j : Fin 7) : (ha37_1_11 j).Contains (fullFactor true 37 11 ((j.val:ℝ)/6)) := by
  rw [ha37_1_11_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha37_1_10 j) true 37 10 j (ha37_1_10_contains j)
noncomputable def hk37_1_12 (j : Fin 6) (i k : Fin 16) : CBox := (kernel37_0 j i k).mul (mpower1_12 j i k)
lemma hk37_1_12_contains (j : Fin 6) (i k : Fin 16) :
    (hk37_1_12 j i k).Contains (fullFactor true 37 12 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk37_1_12,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel37_0 j i k) (mpower1_12 j i k) (quadraturePoint j.val (16*i.val+k.val)) 37 12 (kernel37_0_contains j i k) (mpower1_12_contains j i k)
noncomputable def ha37_1_12 : Fin 7 → CBox := ![⟨⟨(-2406),2406⟩,⟨(-2406),2406⟩⟩,⟨⟨(-40034),40034⟩,⟨(-40034),40034⟩⟩,⟨⟨(-7034),6945⟩,⟨(-6966),7013⟩⟩,⟨⟨(-236),246⟩,⟨(-240),242⟩⟩,⟨⟨(-145493),(-145472)⟩,⟨193018,193039⟩⟩,⟨⟨91238174116560770,91238174116560786⟩,⟨(-310377887141678088),(-310377887141678072)⟩⟩,⟨⟨4929044787969739925127639,4929044787969740071371568⟩,⟨(-9547484745733043856323969),(-9547484745733043710175228)⟩⟩]
lemma ha37_1_12_eq (j : Fin 7) : ha37_1_12 j = ((ha37_1_11 j).mul (piI.mul (atomPoints j).z)).scale 1 12 := by fin_cases j <;> decide +kernel
lemma ha37_1_12_contains (j : Fin 7) : (ha37_1_12 j).Contains (fullFactor true 37 12 ((j.val:ℝ)/6)) := by
  rw [ha37_1_12_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha37_1_11 j) true 37 11 j (ha37_1_11_contains j)
noncomputable def hk37_1_13 (j : Fin 6) (i k : Fin 16) : CBox := (kernel37_0 j i k).mul (mpower1_13 j i k)
lemma hk37_1_13_contains (j : Fin 6) (i k : Fin 16) :
    (hk37_1_13 j i k).Contains (fullFactor true 37 13 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk37_1_13,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel37_0 j i k) (mpower1_13 j i k) (quadraturePoint j.val (16*i.val+k.val)) 37 13 (kernel37_0_contains j i k) (mpower1_13_contains j i k)
noncomputable def ha37_1_13 : Fin 7 → CBox := ![⟨⟨(-1706),1706⟩,⟨(-1706),1706⟩⟩,⟨⟨(-35058),35058⟩,⟨(-35058),35058⟩⟩,⟨⟨(-5390),5443⟩,⟨(-5408),5425⟩⟩,⟨⟨(-148),147⟩,⟨(-150),145⟩⟩,⟨⟨85552,85563⟩,⟨29196,29207⟩⟩,⟨⟨(-102480389105477069),(-102480389105477062)⟩,⟨(-11856480152202294),(-11856480152202287)⟩⟩,⟨⟨(-2723212253227302121209394),(-2723212253227302078492446)⟩,⟨(-1231241987829629277978823),(-1231241987829629235240681)⟩⟩]
lemma ha37_1_13_eq (j : Fin 7) : ha37_1_13 j = ((ha37_1_12 j).mul (piI.mul (atomPoints j).z)).scale 1 13 := by fin_cases j <;> decide +kernel
lemma ha37_1_13_contains (j : Fin 7) : (ha37_1_13 j).Contains (fullFactor true 37 13 ((j.val:ℝ)/6)) := by
  rw [ha37_1_13_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha37_1_12 j) true 37 12 j (ha37_1_12_contains j)
noncomputable def hk37_1_14 (j : Fin 6) (i k : Fin 16) : CBox := (kernel37_0 j i k).mul (mpower1_14 j i k)
lemma hk37_1_14_contains (j : Fin 6) (i k : Fin 16) :
    (hk37_1_14 j i k).Contains (fullFactor true 37 14 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk37_1_14,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel37_0 j i k) (mpower1_14 j i k) (quadraturePoint j.val (16*i.val+k.val)) 37 14 (kernel37_0_contains j i k) (mpower1_14_contains j i k)
noncomputable def ha37_1_14 : Fin 7 → CBox := ![⟨⟨(-1123),1123⟩,⟨(-1123),1123⟩⟩,⟨⟨(-28508),28508⟩,⟨(-28508),28508⟩⟩,⟨⟨(-3904),3892⟩,⟨(-3911),3885⟩⟩,⟨⟨(-85),83⟩,⟨(-83),85⟩⟩,⟨⟨373,379⟩,⟨(-31398),(-31392)⟩⟩,⟨⟨1695730203433430,1695730203433433⟩,⟨30500950451928800,30500950451928803⟩⟩,⟨⟨(-281050012815584380851932),(-281050012815584369254400)⟩,⟨718913199479470975148861,718913199479470986742372⟩⟩]
lemma ha37_1_14_eq (j : Fin 7) : ha37_1_14 j = ((ha37_1_13 j).mul (piI.mul (atomPoints j).z)).scale 1 14 := by fin_cases j <;> decide +kernel
lemma ha37_1_14_contains (j : Fin 7) : (ha37_1_14 j).Contains (fullFactor true 37 14 ((j.val:ℝ)/6)) := by
  rw [ha37_1_14_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha37_1_13 j) true 37 13 j (ha37_1_13_contains j)
noncomputable def hk37_1_15 (j : Fin 6) (i k : Fin 16) : CBox := (kernel37_0 j i k).mul (mpower1_15 j i k)
lemma hk37_1_15_contains (j : Fin 6) (i k : Fin 16) :
    (hk37_1_15 j i k).Contains (fullFactor true 37 15 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk37_1_15,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel37_0 j i k) (mpower1_15 j i k) (quadraturePoint j.val (16*i.val+k.val)) 37 15 (kernel37_0_contains j i k) (mpower1_15_contains j i k)
noncomputable def ha37_1_15 : Fin 7 → CBox := ![⟨⟨(-690),690⟩,⟨(-690),690⟩⟩,⟨⟨(-21636),21636⟩,⟨(-21636),21636⟩⟩,⟨⟨(-2621),2616⟩,⟨(-2612),2625⟩⟩,⟨⟨(-44),45⟩,⟨(-45),45⟩⟩,⟨⟨(-9709),(-9706)⟩,⟨3054,3058⟩⟩,⟨⟨8227406715157239,8227406715157241⟩,⟨(-1893968861334797),(-1893968861334795)⟩⟩,⟨⟨176585865758021682215873,176585865758021685152581⟩,⟨58659078114787604239036,58659078114787607176343⟩⟩]
lemma ha37_1_15_eq (j : Fin 7) : ha37_1_15 j = ((ha37_1_14 j).mul (piI.mul (atomPoints j).z)).scale 1 15 := by fin_cases j <;> decide +kernel
lemma ha37_1_15_contains (j : Fin 7) : (ha37_1_15 j).Contains (fullFactor true 37 15 ((j.val:ℝ)/6)) := by
  rw [ha37_1_15_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha37_1_14 j) true 37 14 j (ha37_1_14_contains j)
noncomputable def hk37_1_16 (j : Fin 6) (i k : Fin 16) : CBox := (kernel37_0 j i k).mul (mpower1_16 j i k)
lemma hk37_1_16_contains (j : Fin 6) (i k : Fin 16) :
    (hk37_1_16 j i k).Contains (fullFactor true 37 16 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk37_1_16,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel37_0 j i k) (mpower1_16 j i k) (quadraturePoint j.val (16*i.val+k.val)) 37 16 (kernel37_0_contains j i k) (mpower1_16_contains j i k)
noncomputable def ha37_1_16 : Fin 7 → CBox := ![⟨⟨(-398),398⟩,⟨(-398),398⟩⟩,⟨⟨(-15395),15395⟩,⟨(-15395),15395⟩⟩,⟨⟨(-1646),1652⟩,⟨(-1650),1648⟩⟩,⟨⟨(-23),23⟩,⟨(-23),23⟩⟩,⟨⟨1801,1803⟩,⟨2512,2515⟩⟩,⟨⟨(-845751717338876),(-845751717338875)⟩,⟨(-2017341265709903),(-2017341265709901)⟩⟩,⟨⟨11166333636847733441092,11166333636847734138525⟩,⟨(-40541923196445848628153),(-40541923196445847930768)⟩⟩]
lemma ha37_1_16_eq (j : Fin 7) : ha37_1_16 j = ((ha37_1_15 j).mul (piI.mul (atomPoints j).z)).scale 1 16 := by fin_cases j <;> decide +kernel
lemma ha37_1_16_contains (j : Fin 7) : (ha37_1_16 j).Contains (fullFactor true 37 16 ((j.val:ℝ)/6)) := by
  rw [ha37_1_16_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha37_1_15 j) true 37 15 j (ha37_1_15_contains j)
noncomputable def hk37_1_17 (j : Fin 6) (i k : Fin 16) : CBox := (kernel37_0 j i k).mul (mpower1_17 j i k)
lemma hk37_1_17_contains (j : Fin 6) (i k : Fin 16) :
    (hk37_1_17 j i k).Contains (fullFactor true 37 17 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk37_1_17,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel37_0 j i k) (mpower1_17 j i k) (quadraturePoint j.val (16*i.val+k.val)) 37 17 (kernel37_0_contains j i k) (mpower1_17_contains j i k)
noncomputable def ha37_1_17 : Fin 7 → CBox := ![⟨⟨(-216),216⟩,⟨(-216),216⟩⟩,⟨⟨(-10310),10310⟩,⟨(-10310),10310⟩⟩,⟨⟨(-979),976⟩,⟨(-978),977⟩⟩,⟨⟨(-11),11⟩,⟨(-11),11⟩⟩,⟨⟨521,523⟩,⟨(-715),(-713)⟩⟩,⟨⟨(-449751122733046),(-449751122733045)⟩,⟨286821750308002,286821750308003⟩⟩,⟨⟨(-8734981190388822501974),(-8734981190388822346108)⟩,⟨(-1924072271878494437590),(-1924072271878494281733)⟩⟩]
lemma ha37_1_17_eq (j : Fin 7) : ha37_1_17 j = ((ha37_1_16 j).mul (piI.mul (atomPoints j).z)).scale 1 17 := by fin_cases j <;> decide +kernel
lemma ha37_1_17_contains (j : Fin 7) : (ha37_1_17 j).Contains (fullFactor true 37 17 ((j.val:ℝ)/6)) := by
  rw [ha37_1_17_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha37_1_16 j) true 37 16 j (ha37_1_16_contains j)
noncomputable def hk37_1_18 (j : Fin 6) (i k : Fin 16) : CBox := (kernel37_0 j i k).mul (mpower1_18 j i k)
lemma hk37_1_18_contains (j : Fin 6) (i k : Fin 16) :
    (hk37_1_18 j i k).Contains (fullFactor true 37 18 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk37_1_18,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel37_0 j i k) (mpower1_18 j i k) (quadraturePoint j.val (16*i.val+k.val)) 37 18 (kernel37_0_contains j i k) (mpower1_18_contains j i k)
noncomputable def ha37_1_18 : Fin 7 → CBox := ![⟨⟨(-111),111⟩,⟨(-111),111⟩⟩,⟨⟨(-6521),6521⟩,⟨(-6521),6521⟩⟩,⟨⟨(-547),548⟩,⟨(-547),548⟩⟩,⟨⟨(-5),5⟩,⟨(-5),5⟩⟩,⟨⟨(-228),(-226)⟩,⟨(-75),(-73)⟩⟩,⟨⟨82695207857506,82695207857507⟩,⟨90853137584984,90853137584986⟩⟩,⟨⟨(-294871019922530828892),(-294871019922530795996)⟩,⟨1772418557172071199870,1772418557172071232771⟩⟩]
lemma ha37_1_18_eq (j : Fin 7) : ha37_1_18 j = ((ha37_1_17 j).mul (piI.mul (atomPoints j).z)).scale 1 18 := by fin_cases j <;> decide +kernel
lemma ha37_1_18_contains (j : Fin 7) : (ha37_1_18 j).Contains (fullFactor true 37 18 ((j.val:ℝ)/6)) := by
  rw [ha37_1_18_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha37_1_17 j) true 37 17 j (ha37_1_17_contains j)
noncomputable def hk37_1_19 (j : Fin 6) (i k : Fin 16) : CBox := (kernel37_0 j i k).mul (mpower1_19 j i k)
lemma hk37_1_19_contains (j : Fin 6) (i k : Fin 16) :
    (hk37_1_19 j i k).Contains (fullFactor true 37 19 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk37_1_19,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel37_0 j i k) (mpower1_19 j i k) (quadraturePoint j.val (16*i.val+k.val)) 37 19 (kernel37_0_contains j i k) (mpower1_19_contains j i k)
noncomputable def ha37_1_19 : Fin 7 → CBox := ![⟨⟨(-54),54⟩,⟨(-54),54⟩⟩,⟨⟨(-3908),3908⟩,⟨(-3908),3908⟩⟩,⟨⟨(-291),291⟩,⟨(-291),291⟩⟩,⟨⟨(-3),3⟩,⟨(-3),3⟩⟩,⟨⟨(-1),1⟩,⟨60,62⟩⟩,⟨⟨16469437454035,16469437454036⟩,⟨(-21148564604886),(-21148564604885)⟩⟩,⟨⟨339769393772241242543,339769393772241249124⟩,⟨38524944936095360899,38524944936095367477⟩⟩]
lemma ha37_1_19_eq (j : Fin 7) : ha37_1_19 j = ((ha37_1_18 j).mul (piI.mul (atomPoints j).z)).scale 1 19 := by fin_cases j <;> decide +kernel
lemma ha37_1_19_contains (j : Fin 7) : (ha37_1_19 j).Contains (fullFactor true 37 19 ((j.val:ℝ)/6)) := by
  rw [ha37_1_19_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha37_1_18 j) true 37 18 j (ha37_1_18_contains j)
noncomputable def hk37_1_20 (j : Fin 6) (i k : Fin 16) : CBox := (kernel37_0 j i k).mul (mpower1_20 j i k)
lemma hk37_1_20_contains (j : Fin 6) (i k : Fin 16) :
    (hk37_1_20 j i k).Contains (fullFactor true 37 20 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk37_1_20,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel37_0 j i k) (mpower1_20 j i k) (quadraturePoint j.val (16*i.val+k.val)) 37 20 (kernel37_0_contains j i k) (mpower1_20_contains j i k)
noncomputable def ha37_1_20 : Fin 7 → CBox := ![⟨⟨(-25),25⟩,⟨(-25),25⟩⟩,⟨⟨(-2225),2225⟩,⟨(-2225),2225⟩⟩,⟨⟨(-147),147⟩,⟨(-147),147⟩⟩,⟨⟨(-2),2⟩,⟨(-2),2⟩⟩,⟨⟨13,15⟩,⟨(-5),(-4)⟩⟩,⟨⟨(-4899882747792),(-4899882747791)⟩,⟨(-2619374350485),(-2619374350484)⟩⟩,⟨⟨3765747032122580063,3765747032122581313⟩,⟨(-61707504307877733182),(-61707504307877731931)⟩⟩]
lemma ha37_1_20_eq (j : Fin 7) : ha37_1_20 j = ((ha37_1_19 j).mul (piI.mul (atomPoints j).z)).scale 1 20 := by fin_cases j <;> decide +kernel
lemma ha37_1_20_contains (j : Fin 7) : (ha37_1_20 j).Contains (fullFactor true 37 20 ((j.val:ℝ)/6)) := by
  rw [ha37_1_20_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha37_1_19 j) true 37 19 j (ha37_1_19_contains j)
noncomputable def hk37_1_21 (j : Fin 6) (i k : Fin 16) : CBox := (kernel37_0 j i k).mul (mpower1_21 j i k)
lemma hk37_1_21_contains (j : Fin 6) (i k : Fin 16) :
    (hk37_1_21 j i k).Contains (fullFactor true 37 21 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk37_1_21,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel37_0 j i k) (mpower1_21 j i k) (quadraturePoint j.val (16*i.val+k.val)) 37 21 (kernel37_0_contains j i k) (mpower1_21_contains j i k)
noncomputable def ha37_1_21 : Fin 7 → CBox := ![⟨⟨(-11),11⟩,⟨(-11),11⟩⟩,⟨⟨(-1207),1207⟩,⟨(-1207),1207⟩⟩,⟨⟨(-71),71⟩,⟨(-71),71⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-3),(-1)⟩,⟨(-4),(-2)⟩⟩,⟨⟨(-345233693200),(-345233693199)⟩,⟨1041062387022,1041062387024⟩⟩,⟨⟨(-10644500561137476003),(-10644500561137475775)⟩,⟨(-95770739832207450),(-95770739832207223)⟩⟩]
lemma ha37_1_21_eq (j : Fin 7) : ha37_1_21 j = ((ha37_1_20 j).mul (piI.mul (atomPoints j).z)).scale 1 21 := by fin_cases j <;> decide +kernel
lemma ha37_1_21_contains (j : Fin 7) : (ha37_1_21 j).Contains (fullFactor true 37 21 ((j.val:ℝ)/6)) := by
  rw [ha37_1_21_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha37_1_20 j) true 37 20 j (ha37_1_20_contains j)
noncomputable def hk37_1_22 (j : Fin 6) (i k : Fin 16) : CBox := (kernel37_0 j i k).mul (mpower1_22 j i k)
lemma hk37_1_22_contains (j : Fin 6) (i k : Fin 16) :
    (hk37_1_22 j i k).Contains (fullFactor true 37 22 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk37_1_22,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel37_0 j i k) (mpower1_22 j i k) (quadraturePoint j.val (16*i.val+k.val)) 37 22 (kernel37_0_contains j i k) (mpower1_22_contains j i k)
noncomputable def ha37_1_22 : Fin 7 → CBox := ![⟨⟨(-5),5⟩,⟨(-5),5⟩⟩,⟨⟨(-625),625⟩,⟨(-625),625⟩⟩,⟨⟨(-33),33⟩,⟨(-33),33⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),0⟩,⟨0,1⟩⟩,⟨⟨204372630662,204372630664⟩,⟨30779834369,30779834370⟩⟩,⟨⟨75132860765014515,75132860765014555⟩,⟨1747979631240417095,1747979631240417135⟩⟩]
lemma ha37_1_22_eq (j : Fin 7) : ha37_1_22 j = ((ha37_1_21 j).mul (piI.mul (atomPoints j).z)).scale 1 22 := by fin_cases j <;> decide +kernel
lemma ha37_1_22_contains (j : Fin 7) : (ha37_1_22 j).Contains (fullFactor true 37 22 ((j.val:ℝ)/6)) := by
  rw [ha37_1_22_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha37_1_21 j) true 37 21 j (ha37_1_21_contains j)
noncomputable def hk37_1_23 (j : Fin 6) (i k : Fin 16) : CBox := (kernel37_0 j i k).mul (mpower1_23 j i k)
lemma hk37_1_23_contains (j : Fin 6) (i k : Fin 16) :
    (hk37_1_23 j i k).Contains (fullFactor true 37 23 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk37_1_23,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel37_0 j i k) (mpower1_23 j i k) (quadraturePoint j.val (16*i.val+k.val)) 37 23 (kernel37_0_contains j i k) (mpower1_23_contains j i k)
noncomputable def ha37_1_23 : Fin 7 → CBox := ![⟨⟨(-3),3⟩,⟨(-3),3⟩⟩,⟨⟨(-310),310⟩,⟨(-310),310⟩⟩,⟨⟨(-15),15⟩,⟨(-15),15⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨0,1⟩,⟨(-1),1⟩⟩,⟨⟨(-791127731),(-791127730)⟩,⟨(-37243525688),(-37243525687)⟩⟩,⟨⟨273821391917617059,273821391917617066⟩,⟨(-26066552811858473),(-26066552811858465)⟩⟩]
lemma ha37_1_23_eq (j : Fin 7) : ha37_1_23 j = ((ha37_1_22 j).mul (piI.mul (atomPoints j).z)).scale 1 23 := by fin_cases j <;> decide +kernel
lemma ha37_1_23_contains (j : Fin 7) : (ha37_1_23 j).Contains (fullFactor true 37 23 ((j.val:ℝ)/6)) := by
  rw [ha37_1_23_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha37_1_22 j) true 37 22 j (ha37_1_22_contains j)
noncomputable def hk37_1_24 (j : Fin 6) (i k : Fin 16) : CBox := (kernel37_0 j i k).mul (mpower1_24 j i k)
lemma hk37_1_24_contains (j : Fin 6) (i k : Fin 16) :
    (hk37_1_24 j i k).Contains (fullFactor true 37 24 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk37_1_24,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel37_0 j i k) (mpower1_24 j i k) (quadraturePoint j.val (16*i.val+k.val)) 37 24 (kernel37_0_contains j i k) (mpower1_24_contains j i k)
noncomputable def ha37_1_24 : Fin 7 → CBox := ![⟨⟨(-2),2⟩,⟨(-2),2⟩⟩,⟨⟨(-148),148⟩,⟨(-148),148⟩⟩,⟨⟨(-7),7⟩,⟨(-7),7⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-6316401363),(-6316401362)⟩,⟨1227616404,1227616406⟩⟩,⟨⟨(-6064306754158959),(-6064306754158957)⟩,⟨(-40995065503906793),(-40995065503906791)⟩⟩]
lemma ha37_1_24_eq (j : Fin 7) : ha37_1_24 j = ((ha37_1_23 j).mul (piI.mul (atomPoints j).z)).scale 1 24 := by fin_cases j <;> decide +kernel
lemma ha37_1_24_contains (j : Fin 7) : (ha37_1_24 j).Contains (fullFactor true 37 24 ((j.val:ℝ)/6)) := by
  rw [ha37_1_24_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha37_1_23 j) true 37 23 j (ha37_1_23_contains j)
noncomputable def hk37_1_25 (j : Fin 6) (i k : Fin 16) : CBox := (kernel37_0 j i k).mul (mpower1_25 j i k)
lemma hk37_1_25_contains (j : Fin 6) (i k : Fin 16) :
    (hk37_1_25 j i k).Contains (fullFactor true 37 25 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk37_1_25,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel37_0 j i k) (mpower1_25 j i k) (quadraturePoint j.val (16*i.val+k.val)) 37 25 (kernel37_0_contains j i k) (mpower1_25_contains j i k)
noncomputable def ha37_1_25 : Fin 7 → CBox := ![⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-68),68⟩,⟨(-68),68⟩⟩,⟨⟨(-3),3⟩,⟨(-3),3⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨378553989,378553990⟩,⟨997590121,997590122⟩⟩,⟨⟨(-5875821350805101),(-5875821350805100)⟩,⟨1183846021712508,1183846021712509⟩⟩]
lemma ha37_1_25_eq (j : Fin 7) : ha37_1_25 j = ((ha37_1_24 j).mul (piI.mul (atomPoints j).z)).scale 1 25 := by fin_cases j <;> decide +kernel
lemma ha37_1_25_contains (j : Fin 7) : (ha37_1_25 j).Contains (fullFactor true 37 25 ((j.val:ℝ)/6)) := by
  rw [ha37_1_25_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha37_1_24 j) true 37 24 j (ha37_1_24_contains j)
noncomputable def hk37_1_26 (j : Fin 6) (i k : Fin 16) : CBox := (kernel37_0 j i k).mul (mpower1_26 j i k)
lemma hk37_1_26_contains (j : Fin 6) (i k : Fin 16) :
    (hk37_1_26 j i k).Contains (fullFactor true 37 26 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk37_1_26,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel37_0 j i k) (mpower1_26 j i k) (quadraturePoint j.val (16*i.val+k.val)) 37 26 (kernel37_0_contains j i k) (mpower1_26_contains j i k)
noncomputable def ha37_1_26 : Fin 7 → CBox := ![⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-30),30⟩,⟨(-30),30⟩⟩,⟨⟨(-2),2⟩,⟨(-2),2⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨146493595,146493596⟩,⟨(-86504341),(-86504340)⟩⟩,⟨⟨206854672796077,206854672796078⟩,⟨807517275301772,807517275301773⟩⟩]
lemma ha37_1_26_eq (j : Fin 7) : ha37_1_26 j = ((ha37_1_25 j).mul (piI.mul (atomPoints j).z)).scale 1 26 := by fin_cases j <;> decide +kernel
lemma ha37_1_26_contains (j : Fin 7) : (ha37_1_26 j).Contains (fullFactor true 37 26 ((j.val:ℝ)/6)) := by
  rw [ha37_1_26_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha37_1_25 j) true 37 25 j (ha37_1_25_contains j)
noncomputable def hk37_1_27 (j : Fin 6) (i k : Fin 16) : CBox := (kernel37_0 j i k).mul (mpower1_27 j i k)
lemma hk37_1_27_contains (j : Fin 6) (i k : Fin 16) :
    (hk37_1_27 j i k).Contains (fullFactor true 37 27 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk37_1_27,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel37_0 j i k) (mpower1_27 j i k) (quadraturePoint j.val (16*i.val+k.val)) 37 27 (kernel37_0_contains j i k) (mpower1_27_contains j i k)
noncomputable def ha37_1_27 : Fin 7 → CBox := ![⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-13),13⟩,⟨(-13),13⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-16910075),(-16910074)⟩,⟨(-19909047),(-19909046)⟩⟩,⟨⟨106560152297710,106560152297711⟩,⟨(-33281030995449),(-33281030995448)⟩⟩]
lemma ha37_1_27_eq (j : Fin 7) : ha37_1_27 j = ((ha37_1_26 j).mul (piI.mul (atomPoints j).z)).scale 1 27 := by fin_cases j <;> decide +kernel
lemma ha37_1_27_contains (j : Fin 7) : (ha37_1_27 j).Contains (fullFactor true 37 27 ((j.val:ℝ)/6)) := by
  rw [ha37_1_27_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha37_1_26 j) true 37 26 j (ha37_1_26_contains j)
noncomputable def hk37_1_28 (j : Fin 6) (i k : Fin 16) : CBox := (kernel37_0 j i k).mul (mpower1_28 j i k)
lemma hk37_1_28_contains (j : Fin 6) (i k : Fin 16) :
    (hk37_1_28 j i k).Contains (fullFactor true 37 28 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk37_1_28,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel37_0 j i k) (mpower1_28 j i k) (quadraturePoint j.val (16*i.val+k.val)) 37 28 (kernel37_0_contains j i k) (mpower1_28_contains j i k)
noncomputable def ha37_1_28 : Fin 7 → CBox := ![⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-6),6⟩,⟨(-6),6⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-2479447),(-2479446)⟩,⟨2968024,2968026⟩⟩,⟨⟨(-5006708097030),(-5006708097029)⟩,⟨(-13519364064655),(-13519364064654)⟩⟩]
lemma ha37_1_28_eq (j : Fin 7) : ha37_1_28 j = ((ha37_1_27 j).mul (piI.mul (atomPoints j).z)).scale 1 28 := by fin_cases j <;> decide +kernel
lemma ha37_1_28_contains (j : Fin 7) : (ha37_1_28 j).Contains (fullFactor true 37 28 ((j.val:ℝ)/6)) := by
  rw [ha37_1_28_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha37_1_27 j) true 37 27 j (ha37_1_27_contains j)
noncomputable def hk37_1_29 (j : Fin 6) (i k : Fin 16) : CBox := (kernel37_0 j i k).mul (mpower1_29 j i k)
lemma hk37_1_29_contains (j : Fin 6) (i k : Fin 16) :
    (hk37_1_29 j i k).Contains (fullFactor true 37 29 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk37_1_29,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel37_0 j i k) (mpower1_29 j i k) (quadraturePoint j.val (16*i.val+k.val)) 37 29 (kernel37_0_contains j i k) (mpower1_29_contains j i k)
noncomputable def ha37_1_29 : Fin 7 → CBox := ![⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-3),3⟩,⟨(-3),3⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨478329,478330⟩,⟨277202,277203⟩⟩,⟨⟨(-1650987906586),(-1650987906585)⟩,⟨710963091053,710963091054⟩⟩]
lemma ha37_1_29_eq (j : Fin 7) : ha37_1_29 j = ((ha37_1_28 j).mul (piI.mul (atomPoints j).z)).scale 1 29 := by fin_cases j <;> decide +kernel
lemma ha37_1_29_contains (j : Fin 7) : (ha37_1_29 j).Contains (fullFactor true 37 29 ((j.val:ℝ)/6)) := by
  rw [ha37_1_29_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha37_1_28 j) true 37 28 j (ha37_1_28_contains j)
noncomputable def hk37_1_30 (j : Fin 6) (i k : Fin 16) : CBox := (kernel37_0 j i k).mul (mpower1_30 j i k)
lemma hk37_1_30_contains (j : Fin 6) (i k : Fin 16) :
    (hk37_1_30 j i k).Contains (fullFactor true 37 30 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk37_1_30,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel37_0 j i k) (mpower1_30 j i k) (quadraturePoint j.val (16*i.val+k.val)) 37 30 (kernel37_0_contains j i k) (mpower1_30_contains j i k)
noncomputable def ha37_1_30 : Fin 7 → CBox := ![⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-2),2⟩,⟨(-2),2⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨26518,26519⟩,⟨(-71646),(-71645)⟩⟩,⟨⟨95910592364,95910592365⟩,⟨194275346530,194275346531⟩⟩]
lemma ha37_1_30_eq (j : Fin 7) : ha37_1_30 j = ((ha37_1_29 j).mul (piI.mul (atomPoints j).z)).scale 1 30 := by fin_cases j <;> decide +kernel
lemma ha37_1_30_contains (j : Fin 7) : (ha37_1_30 j).Contains (fullFactor true 37 30 ((j.val:ℝ)/6)) := by
  rw [ha37_1_30_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha37_1_29 j) true 37 29 j (ha37_1_29_contains j)
end SharpPlanar.CachedData

end OAI
