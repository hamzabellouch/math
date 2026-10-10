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
noncomputable def hk15_0_0 (j : Fin 6) (i k : Fin 16) : CBox := (power15 j i k).conj.mul (mpower0_0 j i k)
lemma hk15_0_0_contains (j : Fin 6) (i k : Fin 16) :
    (hk15_0_0 j i k).Contains (fullFactor false 15 0 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk15_0_0,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power15 j i k) (mpower0_0 j i k) (quadraturePoint j.val (16*i.val+k.val)) 15 0 (power15_contains j i k) (mpower0_0_contains j i k)
noncomputable def ha15_0_0 : Fin 7 → CBox := ![⟨⟨999999999999999999999999999821,1000000000000000000000000000239⟩,⟨(-239),239⟩⟩,⟨⟨(-42956189891),31173106335⟩,⟨999999999999999999962970231043,1000000000000000000037029768974⟩⟩,⟨⟨(-1000000000000000000101240687395),(-999999999999999999898759312614)⟩,⟨(-112998241606),89432074414⟩⟩,⟨⟨(-31325499059),66674749829⟩,⟨(-1000000000000000000049000124444),(-999999999999999999950999875571)⟩⟩,⟨⟨999999999999999999723183942652,1000000000000000000276816057312⟩,⟨(-253268553387),300400887807⟩⟩,⟨⟨(-377863658631),318948240660⟩,⟨999999999999999999651575526767,1000000000000000000348424473187⟩⟩,⟨⟨(-1000000000000000000098297966789),(-999999999999999999901702033271)⟩,⟨(-133647217589),62948715929⟩⟩]
lemma ha15_0_0_eq (j : Fin 7) : ha15_0_0 j = ((atomPoints j).direct.powBin 7 15).conj := by fin_cases j <;> decide +kernel
lemma ha15_0_0_contains (j : Fin 7) : (ha15_0_0 j).Contains (fullFactor false 15 0 ((j.val:ℝ)/6)) := by
  rw [ha15_0_0_eq]
  simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @direct_factor_zero_full ((atomPoints j).direct.powBin 7 15) ((j.val:ℝ)/6) 15 (@direct_power_bin_contains (atomPoints j) ((j.val:ℝ)/6) (atomPoints_contains j) 15 (by norm_num))
noncomputable def hk15_0_1 (j : Fin 6) (i k : Fin 16) : CBox := (power15 j i k).conj.mul (mpower0_1 j i k)
lemma hk15_0_1_contains (j : Fin 6) (i k : Fin 16) :
    (hk15_0_1 j i k).Contains (fullFactor false 15 1 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk15_0_1,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power15 j i k) (mpower0_1 j i k) (quadraturePoint j.val (16*i.val+k.val)) 15 1 (power15_contains j i k) (mpower0_1_contains j i k)
noncomputable def ha15_0_1 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-523598775598298873097722075031),(-523598775598298873057277924977)⟩,⟨(-22491808432),16322200309⟩⟩,⟨⟨(-93653049325),118331481900⟩,⟨(-1047197551196597746262685666591),(-1047197551196597746047314333419)⟩⟩,⟨⟨1570796326794896619153030784534,1570796326794896619311969215490⟩,⟨(-49205978857),104732452122⟩⟩,⟨⟨(-629158148178),530444417804⟩,⟨2094395102393195491726904471890,2094395102393195492893095528034⟩⟩,⟨⟨(-2617993877991494366303839804415),(-2617993877991494364471160195465)⟩,⟨(-989244745012),835004541445⟩⟩,⟨⟨(-197759223516),419865116951⟩,⟨(-3141592653589793238778812170328),(-3141592653589793238151187829861)⟩⟩]
lemma ha15_0_1_eq (j : Fin 7) : ha15_0_1 j = ((ha15_0_0 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 1 := by fin_cases j <;> decide +kernel
lemma ha15_0_1_contains (j : Fin 7) : (ha15_0_1 j).Contains (fullFactor false 15 1 ((j.val:ℝ)/6)) := by
  rw [ha15_0_1_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha15_0_0 j) false 15 0 j (ha15_0_0_contains j)
noncomputable def hk15_0_2 (j : Fin 6) (i k : Fin 16) : CBox := (power15 j i k).conj.mul (mpower0_2 j i k)
lemma hk15_0_2_contains (j : Fin 6) (i k : Fin 16) :
    (hk15_0_2 j i k).Contains (fullFactor false 15 2 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk15_0_2,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power15 j i k) (mpower0_2 j i k) (quadraturePoint j.val (16*i.val+k.val)) 15 2 (power15_contains j i k) (mpower0_2_contains j i k)
noncomputable def ha15_0_2 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-4273142049),5888341678⟩,⟨(-137077838904018869711752543846),(-137077838904018869700727957807)⟩⟩,⟨⟨548311355616075478767704255503,548311355616075478882217751106⟩,⟨(-49036621958),61958219038⟩⟩,⟨⟨(-82256675545),38646285423⟩,⟨1233700550136169827291783786146,1233700550136169827420540728730⟩⟩,⟨⟨(-2193245422464301915913950880784),(-2193245422464301914685737145549)⟩,⟨(-658852872088),555480095371⟩⟩,⟨⟨(-1093018388800),1294918343139⟩,⟨(-3426945972600471743860946423610),(-3426945972600471741451066117504)⟩⟩,⟨⟨4934802200544679308923860043922,4934802200544679309925438015804⟩,⟨(-310639461889),659522583456⟩⟩]
lemma ha15_0_2_eq (j : Fin 7) : ha15_0_2 j = ((ha15_0_1 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 2 := by fin_cases j <;> decide +kernel
lemma ha15_0_2_contains (j : Fin 7) : (ha15_0_2 j).Contains (fullFactor false 15 2 ((j.val:ℝ)/6)) := by
  rw [ha15_0_2_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha15_0_1 j) false 15 1 j (ha15_0_1_contains j)
noncomputable def hk15_0_3 (j : Fin 6) (i k : Fin 16) : CBox := (power15 j i k).conj.mul (mpower0_3 j i k)
lemma hk15_0_3_contains (j : Fin 6) (i k : Fin 16) :
    (hk15_0_3 j i k).Contains (fullFactor false 15 3 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk15_0_3,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power15 j i k) (mpower0_3 j i k) (quadraturePoint j.val (16*i.val+k.val)) 15 3 (power15_contains j i k) (mpower0_3_contains j i k)
noncomputable def ha15_0_3 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨23924596203935046430748373736,23924596203935046432748681343⟩,⟨(-745803982),1027709498⟩⟩,⟨⟨(-21627498418),17117010145⟩,⟨191396769631480371433697227535,191396769631480371474279213101⟩⟩,⟨⟨(-645964097506246253691946816111),(-645964097506246253622473671039)⟩,⟨(-43069494601),20235147729⟩⟩,⟨⟨(-387798263741),459966076167⟩,⟨(-1531174157051842972063070173830),(-1531174157051842971200741351187)⟩⟩,⟨⟨2990574525491880802912297647187,2990574525491880805024834237587⟩,⟨(-953838483471),1130029431613⟩⟩,⟨⟨(-690650434354),325300883796⟩,⟨5167712780049970028725032278639,5167712780049970029790331618796⟩⟩]
lemma ha15_0_3_eq (j : Fin 7) : ha15_0_3 j = ((ha15_0_2 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 3 := by fin_cases j <;> decide +kernel
lemma ha15_0_3_contains (j : Fin 7) : (ha15_0_3 j).Contains (fullFactor false 15 3 ((j.val:ℝ)/6)) := by
  rw [ha15_0_3_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha15_0_2 j) false 15 2 j (ha15_0_2_contains j)
noncomputable def hk15_0_4 (j : Fin 6) (i k : Fin 16) : CBox := (power15 j i k).conj.mul (mpower0_4 j i k)
lemma hk15_0_4_contains (j : Fin 6) (i k : Fin 16) :
    (hk15_0_4 j i k).Contains (fullFactor false 15 4 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk15_0_4,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power15 j i k) (mpower0_4 j i k) (quadraturePoint j.val (16*i.val+k.val)) 15 4 (power15_contains j i k) (mpower0_4_contains j i k)
noncomputable def ha15_0_4 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-134526859),97625513⟩,⟨3131722319766024859584151577,3131722319766024859855959813⟩⟩,⟨⟨(-50107557116256397760912809259),(-50107557116256397750128972973)⟩,⟨(-5662065846),4481222777⟩⟩,⟨⟨(-7946323932),16913350980⟩,⟨(-253669507901048013651369258973),(-253669507901048013623279763578)⟩⟩,⟨⟨801720913860102363861301121522,801720913860102364315367394152⟩,⟨(-203050696074),240837674298⟩⟩,⟨⟨(-739602533479),624285827580⟩,⟨1957326449853765536630593644777,1957326449853765538019475973551⟩⟩,⟨⟨(-4058712126416768218621993894085),(-4058712126416768217772390466906)⟩,⟨(-542435582692),255490716685⟩⟩]
lemma ha15_0_4_eq (j : Fin 7) : ha15_0_4 j = ((ha15_0_3 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 4 := by fin_cases j <;> decide +kernel
lemma ha15_0_4_contains (j : Fin 7) : (ha15_0_4 j).Contains (fullFactor false 15 4 ((j.val:ℝ)/6)) := by
  rw [ha15_0_4_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha15_0_3 j) false 15 3 j (ha15_0_3_contains j)
noncomputable def hk15_0_5 (j : Fin 6) (i k : Fin 16) : CBox := (power15 j i k).conj.mul (mpower0_5 j i k)
lemma hk15_0_5_contains (j : Fin 6) (i k : Fin 16) :
    (hk15_0_5 j i k).Contains (fullFactor false 15 5 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk15_0_5,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power15 j i k) (mpower0_5 j i k) (quadraturePoint j.val (16*i.val+k.val)) 15 5 (power15_contains j i k) (mpower0_5_contains j i k)
noncomputable def ha15_0_5 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-327953194428670967590080757),(-327953194428670967560573156)⟩,⟨(-14087620),10223320⟩⟩,⟨⟨(-938545104),1185860298⟩,⟨(-10494502221717470963556445818),(-10494502221717470961264479388)⟩⟩,⟨⟨79692626246167045116265328020,79692626246167045125343572766⟩,⟨(-2496411289),5313485919⟩⟩,⟨⟨(-100881849105),85053676679⟩,⟨335824071094959070701500904927,335824071094959070892768701659⟩⟩,⟨⟨(-1024853732589596774038136387336),(-1024853732589596773307657089788)⟩,⟨(-387254980960),326875294945⟩⟩,⟨⟨(-160529551720),340822328327⟩,⟨(-2550164039877345444136711913289),(-2550164039877345443594772911977)⟩⟩]
lemma ha15_0_5_eq (j : Fin 7) : ha15_0_5 j = ((ha15_0_4 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 5 := by fin_cases j <;> decide +kernel
lemma ha15_0_5_contains (j : Fin 7) : (ha15_0_5 j).Contains (fullFactor false 15 5 ((j.val:ℝ)/6)) := by
  rw [ha15_0_5_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha15_0_4 j) false 15 4 j (ha15_0_4_contains j)
noncomputable def hk15_0_6 (j : Fin 6) (i k : Fin 16) : CBox := (power15 j i k).conj.mul (mpower0_6 j i k)
lemma hk15_0_6_contains (j : Fin 6) (i k : Fin 16) :
    (hk15_0_6 j i k).Contains (fullFactor false 15 6 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk15_0_6,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power15 j i k) (mpower0_6 j i k) (quadraturePoint j.val (16*i.val+k.val)) 15 6 (power15_contains j i k) (mpower0_6_contains j i k)
noncomputable def ha15_0_6 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-892153),1229377⟩,⟨(-28619315176067161692890729),(-28619315176067161690224606)⟩⟩,⟨⟨1831636171268298348056763787,1831636171268298348462617673⟩,⟨(-163807023),206971667⟩⟩,⟨⟨(-1391067361),653558948⟩,⟨20863480763352960871923995000,20863480763352960874367084440⟩⟩,⟨⟨(-117224714961171094322189303698),(-117224714961171094255051109720)⟩,⟨(-35214408448),29689333980⟩⟩,⟨⟨(-142626253506),168971861563⟩,⟨(-447176799626049401590666121815),(-447176799626049401270510992354)⟩⟩,⟨⟨1335262768854589495737310106639,1335262768854589496025318977576⟩,⟨(-84053076728),178454153809⟩⟩]
lemma ha15_0_6_eq (j : Fin 7) : ha15_0_6 j = ((ha15_0_5 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 6 := by fin_cases j <;> decide +kernel
lemma ha15_0_6_contains (j : Fin 7) : (ha15_0_6 j).Contains (fullFactor false 15 6 ((j.val:ℝ)/6)) := by
  rw [ha15_0_6_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha15_0_5 j) false 15 5 j (ha15_0_5_contains j)
noncomputable def hk15_0_7 (j : Fin 6) (i k : Fin 16) : CBox := (power15 j i k).conj.mul (mpower0_7 j i k)
lemma hk15_0_7_contains (j : Fin 6) (i k : Fin 16) :
    (hk15_0_7 j i k).Contains (fullFactor false 15 7 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk15_0_7,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power15 j i k) (mpower0_7 j i k) (quadraturePoint j.val (16*i.val+k.val)) 15 7 (power15_contains j i k) (mpower0_7_contains j i k)
noncomputable def ha15_0_7 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨2140719769235797028113637,2140719769235797028319877⟩,⟨(-66733),91958⟩⟩,⟨⟨(-30962889),24505474⟩,⟨274012130462182019580950991,274012130462182019642538799⟩⟩,⟨⟨(-4681754135318688100991612786),(-4681754135318688100428482310)⟩,⟨(-312154786),146658285⟩⟩,⟨⟨(-8883027955),10536126370⟩,⟨(-35073552699159298520403018229),(-35073552699159298500203674978)⟩⟩,⟨⟨167243731971546642769299094343,167243731971546642889569186097⟩,⟨(-53342094075),63195328447⟩⟩,⟨⟨(-80090036945),37722932623⟩,⟨599264529320792076825303287503,599264529320792076956468884760⟩⟩]
lemma ha15_0_7_eq (j : Fin 7) : ha15_0_7 j = ((ha15_0_6 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 7 := by fin_cases j <;> decide +kernel
lemma ha15_0_7_contains (j : Fin 7) : (ha15_0_7 j).Contains (fullFactor false 15 7 ((j.val:ℝ)/6)) := by
  rw [ha15_0_7_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha15_0_6 j) false 15 6 j (ha15_0_6_contains j)
noncomputable def hk15_0_8 (j : Fin 6) (i k : Fin 16) : CBox := (power15 j i k).conj.mul (mpower0_8 j i k)
lemma hk15_0_8_contains (j : Fin 6) (i k : Fin 16) :
    (hk15_0_8 j i k).Contains (fullFactor false 15 8 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk15_0_8,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power15 j i k) (mpower0_8 j i k) (quadraturePoint j.val (16*i.val+k.val)) 15 8 (power15_contains j i k) (mpower0_8_contains j i k)
noncomputable def ha15_0_8 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-6019),4368⟩,⟨140109781258867029446957,140109781258867029460902⟩⟩,⟨⟨(-35868104002269959544294003),(-35868104002269959536118005)⟩,⟨(-4053033),3207760⟩⟩,⟨⟨(-28796287),61291449⟩,⟨(-919260274839426580303981026),(-919260274839426580190484518)⟩⟩,⟨⟨9182234624581109639634035091,9182234624581109644951438750⟩,⟨(-2325571281),2758351434⟩⟩,⟨⟨(-20680622874),17456159466⟩,⟨54730383304244933360675035808,54730383304244933400207543520⟩⟩,⟨⟨(-235330630358893204569420434720),(-235330630358893204517162744464)⟩,⟨(-31451283962),14813761001⟩⟩]
lemma ha15_0_8_eq (j : Fin 7) : ha15_0_8 j = ((ha15_0_7 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 8 := by fin_cases j <;> decide +kernel
lemma ha15_0_8_contains (j : Fin 7) : (ha15_0_8 j).Contains (fullFactor false 15 8 ((j.val:ℝ)/6)) := by
  rw [ha15_0_8_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha15_0_7 j) false 15 7 j (ha15_0_7_contains j)
noncomputable def hk15_0_9 (j : Fin 6) (i k : Fin 16) : CBox := (power15 j i k).conj.mul (mpower0_9 j i k)
lemma hk15_0_9_contains (j : Fin 6) (i k : Fin 16) :
    (hk15_0_9 j i k).Contains (fullFactor false 15 9 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk15_0_9,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power15 j i k) (mpower0_9 j i k) (quadraturePoint j.val (16*i.val+k.val)) 15 9 (power15_contains j i k) (mpower0_9_contains j i k)
noncomputable def ha15_0_9 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-8151256657387584305339),(-8151256657387584304501)⟩,⟨(-351),255⟩⟩,⟨⟨(-373240),471592⟩,⟨(-4173443408582443164601439),(-4173443408582443163636833)⟩⟩,⟨⟨160441184787359821863584253,160441184787359821883903832⟩,⟨(-5025901),10697376⟩⟩,⟨⟨(-641897527),541185012⟩,⟨2136803025194210899406888683,2136803025194210900651106359⟩⟩,⟨⟨(-15920423158960125601322348701),(-15920423158960125589772132067)⟩,⟨(-6015749342),5077790958⟩⟩,⟨⟨(-5170978082),10978569183⟩,⟨(-82145886611128228808608376409),(-82145886611128228790105522840)⟩⟩]
lemma ha15_0_9_eq (j : Fin 7) : ha15_0_9 j = ((ha15_0_8 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 9 := by fin_cases j <;> decide +kernel
lemma ha15_0_9_contains (j : Fin 7) : (ha15_0_9 j).Contains (fullFactor false 15 9 ((j.val:ℝ)/6)) := by
  rw [ha15_0_9_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha15_0_8 j) false 15 8 j (ha15_0_8_contains j)
noncomputable def hk15_0_10 (j : Fin 6) (i k : Fin 16) : CBox := (power15 j i k).conj.mul (mpower0_10 j i k)
lemma hk15_0_10_contains (j : Fin 6) (i k : Fin 16) :
    (hk15_0_10 j i k).Contains (fullFactor false 15 10 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk15_0_10,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power15 j i k) (mpower0_10 j i k) (quadraturePoint j.val (16*i.val+k.val)) 15 10 (power15_contains j i k) (mpower0_10_contains j i k)
noncomputable def ha15_0_10 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-14),19⟩,⟨(-426798800539562151478),(-426798800539562151431)⟩⟩,⟨⟨437041971752511643038297,437041971752511643140703⟩,⟨(-39086),49385⟩⟩,⟨⟨(-1680340),789467⟩,⟨25202042373060605479606064,25202042373060605482878078⟩⟩,⟨⟨(-447530979074571922654654354),(-447530979074571922392641477)⟩,⟨(-134438704),113345524⟩⟩,⟨⟨(-1329362565),1574919495⟩,⟨(-4167957036519161636817281487),(-4167957036519161633780174823)⟩⟩,⟨⟨25806891390014060009844386238,25806891390014060015739375010⟩,⟨(-1624510676),3449019230⟩⟩]
lemma ha15_0_10_eq (j : Fin 7) : ha15_0_10 j = ((ha15_0_9 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 10 := by fin_cases j <;> decide +kernel
lemma ha15_0_10_contains (j : Fin 7) : (ha15_0_10 j).Contains (fullFactor false 15 10 ((j.val:ℝ)/6)) := by
  rw [ha15_0_10_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha15_0_9 j) false 15 9 j (ha15_0_9_contains j)
noncomputable def hk15_0_11 (j : Fin 6) (i k : Fin 16) : CBox := (power15 j i k).conj.mul (mpower0_11 j i k)
lemma hk15_0_11_contains (j : Fin 6) (i k : Fin 16) :
    (hk15_0_11 j i k).Contains (fullFactor false 15 11 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk15_0_11,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power15 j i k) (mpower0_11 j i k) (quadraturePoint j.val (16*i.val+k.val)) 15 11 (power15_contains j i k) (mpower0_11_contains j i k)
noncomputable def ha15_0_11 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨20315575399030665719,20315575399030665723⟩,⟨(-1),1⟩⟩,⟨⟨(-4702),3721⟩,⟨41606298417214803391785,41606298417214803401668⟩⟩,⟨⟨(-3598843235212085340727585),(-3598843235212085340248886)⟩,⟨(-239952),112736⟩⟩,⟨⟨(-21580938),25597070⟩,⟨(-85209699158455917381575028),(-85209699158455917331416661)⟩⟩,⟨⟨991971455030794224298034444,991971455030794225024021684⟩,⟨(-316387551),374829964⟩⟩,⟨⟨(-985037589),463959165⟩,⟨7370430945714350776466374076,7370430945714350778173439743⟩⟩]
lemma ha15_0_11_eq (j : Fin 7) : ha15_0_11 j = ((ha15_0_10 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 11 := by fin_cases j <;> decide +kernel
lemma ha15_0_11_contains (j : Fin 7) : (ha15_0_11 j).Contains (fullFactor false 15 11 ((j.val:ℝ)/6)) := by
  rw [ha15_0_11_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha15_0_10 j) false 15 10 j (ha15_0_10_contains j)
noncomputable def hk15_0_12 (j : Fin 6) (i k : Fin 16) : CBox := (power15 j i k).conj.mul (mpower0_12 j i k)
lemma hk15_0_12_contains (j : Fin 6) (i k : Fin 16) :
    (hk15_0_12 j i k).Contains (fullFactor false 15 12 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk15_0_12,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power15 j i k) (mpower0_12 j i k) (quadraturePoint j.val (16*i.val+k.val)) 15 12 (power15_contains j i k) (mpower0_12_contains j i k)
noncomputable def ha15_0_12 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),1⟩,⟨886434200375614885,886434200375614886⟩⟩,⟨⟨(-3630834484738518571494),(-3630834484738518570619)⟩,⟨(-411),325⟩⟩,⟨⟨(-14758),31410⟩,⟨(-471087477881817150403349),(-471087477881817150339187)⟩⟩,⟨⟨14871898049488972062645666,14871898049488972071447292⟩,⟨(-3766585),4467532⟩⟩,⟨⟨(-81775213),69025056⟩,⟨216414599701077852828613158,216414599701077852987687873⟩⟩,⟨⟨(-1929574309403923048147240231),(-1929574309403923047694189458)⟩,⟨(-257882238),121464226⟩⟩]
lemma ha15_0_12_eq (j : Fin 7) : ha15_0_12 j = ((ha15_0_11 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 12 := by fin_cases j <;> decide +kernel
lemma ha15_0_12_contains (j : Fin 7) : (ha15_0_12 j).Contains (fullFactor false 15 12 ((j.val:ℝ)/6)) := by
  rw [ha15_0_12_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha15_0_11 j) false 15 11 j (ha15_0_11_contains j)
noncomputable def hk15_0_13 (j : Fin 6) (i k : Fin 16) : CBox := (power15 j i k).conj.mul (mpower0_13 j i k)
lemma hk15_0_13_contains (j : Fin 6) (i k : Fin 16) :
    (hk15_0_13 j i k).Contains (fullFactor false 15 13 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk15_0_13,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power15 j i k) (mpower0_13 j i k) (quadraturePoint j.val (16*i.val+k.val)) 15 13 (power15_contains j i k) (mpower0_13_contains j i k)
noncomputable def ha15_0_13 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-35702758612702237),(-35702758612702236)⟩,⟨(-1),1⟩⟩,⟨⟨(-27),34⟩,⟨(-292476998555256723062),(-292476998555256722990)⟩⟩,⟨⟨56921729219679268114340,56921729219679268122275⟩,⟨(-1784),3796⟩⟩,⟨⟨(-719753),606825⟩,⟨2395971572164663074317176,2395971572164663075742810⟩⟩,⟨⟨(-43582469009646285047244983),(-43582469009646285015071129)⟩,⟨(-16468232),13900552⟩⟩,⟨⟨(-29353164),62320073⟩,⟨(-466302805767612564480660671),(-466302805767612564369691692)⟩⟩]
lemma ha15_0_13_eq (j : Fin 7) : ha15_0_13 j = ((ha15_0_12 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 13 := by fin_cases j <;> decide +kernel
lemma ha15_0_13_contains (j : Fin 7) : (ha15_0_13 j).Contains (fullFactor false 15 13 ((j.val:ℝ)/6)) := by
  rw [ha15_0_13_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha15_0_12 j) false 15 12 j (ha15_0_12_contains j)
noncomputable def hk15_0_14 (j : Fin 6) (i k : Fin 16) : CBox := (power15 j i k).conj.mul (mpower0_14 j i k)
lemma hk15_0_14_contains (j : Fin 6) (i k : Fin 16) :
    (hk15_0_14 j i k).Contains (fullFactor false 15 14 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk15_0_14,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power15 j i k) (mpower0_14 j i k) (quadraturePoint j.val (16*i.val+k.val)) 15 14 (power15_contains j i k) (mpower0_14_contains j i k)
noncomputable def ha15_0_14 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),1⟩,⟨(-1335280049649466),(-1335280049649465)⟩⟩,⟨⟨21877228333456835514,21877228333456835521⟩,⟨(-3),3⟩⟩,⟨⟨(-426),201⟩,⟨6386603083791852240701,6386603083791852241613⟩⟩,⟨⟨(-358436509015356793228717),(-358436509015356793014301)⟩,⟨(-107675),90781⟩⟩,⟨⟨(-2599398),3079553⟩,⟨(-8149902646786285760171804),(-8149902646786285754129364)⟩⟩,⟨⟨104638104924845707106498398,104638104924845707131732853⟩,⟨(-6586835),13984592⟩⟩]
lemma ha15_0_14_eq (j : Fin 7) : ha15_0_14 j = ((ha15_0_13 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 14 := by fin_cases j <;> decide +kernel
lemma ha15_0_14_contains (j : Fin 7) : (ha15_0_14 j).Contains (fullFactor false 15 14 ((j.val:ℝ)/6)) := by
  rw [ha15_0_14_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha15_0_13 j) false 15 13 j (ha15_0_13_contains j)
noncomputable def hk15_0_15 (j : Fin 6) (i k : Fin 16) : CBox := (power15 j i k).conj.mul (mpower0_15 j i k)
lemma hk15_0_15_contains (j : Fin 6) (i k : Fin 16) :
    (hk15_0_15 j i k).Contains (fullFactor false 15 15 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk15_0_15,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power15 j i k) (mpower0_15 j i k) (quadraturePoint j.val (16*i.val+k.val)) 15 15 (power15_contains j i k) (mpower0_15_contains j i k)
noncomputable def ha15_0_15 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨46610066605153,46610066605154⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨1527318662517654886,1527318662517654887⟩⟩,⟨⟨(-668803510981146723305),(-668803510981146723206)⟩,⟨(-45),22⟩⟩,⟨⟨(-12676),15035⟩,⟨(-50047177933378515343068),(-50047177933378515312970)⟩⟩,⟨⟨1422426349034211492306287,1422426349034211493365421⟩,⟨(-453681),537484⟩⟩,⟨⟨(-2928927),1379544⟩,⟨21915353447830215824953818,21915353447830215830308670⟩⟩]
lemma ha15_0_15_eq (j : Fin 7) : ha15_0_15 j = ((ha15_0_14 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 15 := by fin_cases j <;> decide +kernel
lemma ha15_0_15_contains (j : Fin 7) : (ha15_0_15 j).Contains (fullFactor false 15 15 ((j.val:ℝ)/6)) := by
  rw [ha15_0_15_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha15_0_14 j) false 15 14 j (ha15_0_14_contains j)
noncomputable def hk15_0_16 (j : Fin 6) (i k : Fin 16) : CBox := (power15 j i k).conj.mul (mpower0_16 j i k)
lemma hk15_0_16_contains (j : Fin 6) (i k : Fin 16) :
    (hk15_0_16 j i k).Contains (fullFactor false 15 16 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk15_0_16,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power15 j i k) (mpower0_16 j i k) (quadraturePoint j.val (16*i.val+k.val)) 15 16 (power15_contains j i k) (mpower0_16_contains j i k)
noncomputable def ha15_0_16 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),1⟩,⟨1525310862813,1525310862814⟩⟩,⟨⟨(-99962772705334444),(-99962772705334443)⟩,⟨(-1),1⟩⟩,⟨⟨(-3),5⟩,⟨(-65659631149794723628),(-65659631149794723617)⟩⟩,⟨⟨6551160272016798096849,6551160272016798100811⟩,⟨(-1660),1969⟩⟩,⟨⟨(-87946),74234⟩,⟨232743967104084891288818,232743967104084891462860⟩⟩,⟨⟨(-4303069587032947007882030),(-4303069587032947006816909)⟩,⟨(-575094),270873⟩⟩]
lemma ha15_0_16_eq (j : Fin 7) : ha15_0_16 j = ((ha15_0_15 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 16 := by fin_cases j <;> decide +kernel
lemma ha15_0_16_contains (j : Fin 7) : (ha15_0_16 j).Contains (fullFactor false 15 16 ((j.val:ℝ)/6)) := by
  rw [ha15_0_16_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha15_0_15 j) false 15 15 j (ha15_0_15_contains j)
noncomputable def hk15_0_17 (j : Fin 6) (i k : Fin 16) : CBox := (power15 j i k).conj.mul (mpower0_17 j i k)
lemma hk15_0_17_contains (j : Fin 6) (i k : Fin 16) :
    (hk15_0_17 j i k).Contains (fullFactor false 15 17 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk15_0_17,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power15 j i k) (mpower0_17 j i k) (quadraturePoint j.val (16*i.val+k.val)) 15 17 (power15_contains j i k) (mpower0_17_contains j i k)
noncomputable def ha15_0_17 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-46979464717),(-46979464716)⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-6157692399285196),(-6157692399285195)⟩⟩,⟨⟨6066935731106195666,6066935731106195668⟩,⟨(-1),1⟩⟩,⟨⟨(-243),205⟩,⟨807101058159109193182,807101058159109193673⟩⟩,⟨⟨(-35842487118702823500035),(-35842487118702823473117)⟩,⟨(-13544),11433⟩⟩,⟨⟨(-50058),106278⟩,⟨(-795205400147551278588144),(-795205400147551278388778)⟩⟩]
lemma ha15_0_17_eq (j : Fin 7) : ha15_0_17 j = ((ha15_0_16 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 17 := by fin_cases j <;> decide +kernel
lemma ha15_0_17_contains (j : Fin 7) : (ha15_0_17 j).Contains (fullFactor false 15 17 ((j.val:ℝ)/6)) := by
  rw [ha15_0_17_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha15_0_16 j) false 15 16 j (ha15_0_16_contains j)
noncomputable def hk15_0_18 (j : Fin 6) (i k : Fin 16) : CBox := (power15 j i k).conj.mul (mpower0_18 j i k)
lemma hk15_0_18_contains (j : Fin 6) (i k : Fin 16) :
    (hk15_0_18 j i k).Contains (fullFactor false 15 18 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk15_0_18,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power15 j i k) (mpower0_18 j i k) (quadraturePoint j.val (16*i.val+k.val)) 15 18 (power15_contains j i k) (mpower0_18_contains j i k)
noncomputable def ha15_0_18 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),1⟩,⟨(-1366577234),(-1366577233)⟩⟩,⟨⟨358240022308519,358240022308520⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨529440020073462376,529440020073462377⟩⟩,⟨⟨(-93910472408044662768),(-93910472408044662710)⟩,⟨(-29),24⟩⟩,⟨⟨(-1663),1970⟩,⟨(-5213078436041832673641),(-5213078436041832669708)⟩⟩,⟨⟨138789524622137721128935,138789524622137721164174⟩,⟨(-8737),18550⟩⟩]
lemma ha15_0_18_eq (j : Fin 7) : ha15_0_18 j = ((ha15_0_17 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 18 := by fin_cases j <;> decide +kernel
lemma ha15_0_18_contains (j : Fin 7) : (ha15_0_18 j).Contains (fullFactor false 15 18 ((j.val:ℝ)/6)) := by
  rw [ha15_0_18_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha15_0_17 j) false 15 17 j (ha15_0_17_contains j)
noncomputable def hk15_0_19 (j : Fin 6) (i k : Fin 16) : CBox := (power15 j i k).conj.mul (mpower0_19 j i k)
lemma hk15_0_19_contains (j : Fin 6) (i k : Fin 16) :
    (hk15_0_19 j i k).Contains (fullFactor false 15 19 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk15_0_19,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power15 j i k) (mpower0_19 j i k) (quadraturePoint j.val (16*i.val+k.val)) 15 19 (power15_contains j i k) (mpower0_19_contains j i k)
noncomputable def ha15_0_19 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨37659903,37659904⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨19744635479057,19744635479058⟩⟩,⟨⟨(-43770654673137423),(-43770654673137422)⟩,⟨(-1),1⟩⟩,⟨⟨(-3),4⟩,⟨(-10351875446044213765),(-10351875446044213758)⟩⟩,⟨⟨718305654265631154778,718305654265631155323⟩,⟨(-230),272⟩⟩,⟨⟨(-3068),1445⟩,⟨22948428997269873107581,22948428997269873113481⟩⟩]
lemma ha15_0_19_eq (j : Fin 7) : ha15_0_19 j = ((ha15_0_18 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 19 := by fin_cases j <;> decide +kernel
lemma ha15_0_19_contains (j : Fin 7) : (ha15_0_19 j).Contains (fullFactor false 15 19 ((j.val:ℝ)/6)) := by
  rw [ha15_0_19_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha15_0_18 j) false 15 18 j (ha15_0_18_contains j)
noncomputable def hk15_0_20 (j : Fin 6) (i k : Fin 16) : CBox := (power15 j i k).conj.mul (mpower0_20 j i k)
lemma hk15_0_20_contains (j : Fin 6) (i k : Fin 16) :
    (hk15_0_20 j i k).Contains (fullFactor false 15 20 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk15_0_20,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power15 j i k) (mpower0_20 j i k) (quadraturePoint j.val (16*i.val+k.val)) 15 20 (power15_contains j i k) (mpower0_20_contains j i k)
noncomputable def ha15_0_20 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),1⟩,⟨985933,985934⟩⟩,⟨⟨(-1033826696147),(-1033826696146)⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-3437739179098608),(-3437739179098606)⟩⟩,⟨⟨1084045861738968866,1084045861738968868⟩,⟨(-1),1⟩⟩,⟨⟨(-36),31⟩,⟨94025990269704865178,94025990269704865251⟩⟩,⟨⟨(-3604730797462500934383),(-3604730797462500933444)⟩,⟨(-482),227⟩⟩]
lemma ha15_0_20_eq (j : Fin 7) : ha15_0_20 j = ((ha15_0_19 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 20 := by fin_cases j <;> decide +kernel
lemma ha15_0_20_contains (j : Fin 7) : (ha15_0_20 j).Contains (fullFactor false 15 20 ((j.val:ℝ)/6)) := by
  rw [ha15_0_20_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha15_0_19 j) false 15 19 j (ha15_0_19_contains j)
noncomputable def hk15_0_21 (j : Fin 6) (i k : Fin 16) : CBox := (power15 j i k).conj.mul (mpower0_21 j i k)
lemma hk15_0_21_contains (j : Fin 6) (i k : Fin 16) :
    (hk15_0_21 j i k).Contains (fullFactor false 15 21 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk15_0_21,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power15 j i k) (mpower0_21 j i k) (quadraturePoint j.val (16*i.val+k.val)) 15 21 (power15_contains j i k) (mpower0_21_contains j i k)
noncomputable def ha15_0_21 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-24583),(-24582)⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-51553370694),(-51553370693)⟩⟩,⟨⟨257142289286047,257142289286048⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨108115254456938454,108115254456938455⟩⟩,⟨⟨(-11721879376103578828),(-11721879376103578818)⟩,⟨(-5),4⟩⟩,⟨⟨(-34),73⟩,⟨(-539266466260812849015),(-539266466260812848872)⟩⟩]
lemma ha15_0_21_eq (j : Fin 7) : ha15_0_21 j = ((ha15_0_20 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 21 := by fin_cases j <;> decide +kernel
lemma ha15_0_21_contains (j : Fin 7) : (ha15_0_21 j).Contains (fullFactor false 15 21 ((j.val:ℝ)/6)) := by
  rw [ha15_0_21_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha15_0_20 j) false 15 20 j (ha15_0_20_contains j)
noncomputable def hk15_0_22 (j : Fin 6) (i k : Fin 16) : CBox := (power15 j i k).conj.mul (mpower0_22 j i k)
lemma hk15_0_22_contains (j : Fin 6) (i k : Fin 16) :
    (hk15_0_22 j i k).Contains (fullFactor false 15 22 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk15_0_22,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power15 j i k) (mpower0_22 j i k) (quadraturePoint j.val (16*i.val+k.val)) 15 22 (power15_contains j i k) (mpower0_22_contains j i k)
noncomputable def ha15_0_22 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),1⟩,⟨(-586),(-585)⟩⟩,⟨⟨2453934706,2453934707⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨18359916521552,18359916521553⟩⟩,⟨⟨(-10292548155845728),(-10292548155845727)⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1394900383872451221),(-1394900383872451218)⟩⟩,⟨⟨77007071306013533788,77007071306013533810⟩,⟨(-5),11⟩⟩]
lemma ha15_0_22_eq (j : Fin 7) : ha15_0_22 j = ((ha15_0_21 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 22 := by fin_cases j <;> decide +kernel
lemma ha15_0_22_contains (j : Fin 7) : (ha15_0_22 j).Contains (fullFactor false 15 22 ((j.val:ℝ)/6)) := by
  rw [ha15_0_22_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha15_0_21 j) false 15 21 j (ha15_0_21_contains j)
noncomputable def hk15_0_23 (j : Fin 6) (i k : Fin 16) : CBox := (power15 j i k).conj.mul (mpower0_23 j i k)
lemma hk15_0_23_contains (j : Fin 6) (i k : Fin 16) :
    (hk15_0_23 j i k).Contains (fullFactor false 15 23 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk15_0_23,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power15 j i k) (mpower0_23 j i k) (quadraturePoint j.val (16*i.val+k.val)) 15 23 (power15_contains j i k) (mpower0_23_contains j i k)
noncomputable def ha15_0_23 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨13,14⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨111728452,111728453⟩⟩,⟨⟨(-1253899540536),(-1253899540535)⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-937246193423888),(-937246193423887)⟩⟩,⟨⟨158775681103741856,158775681103741858⟩,⟨(-1),1⟩⟩,⟨⟨(-2),1⟩,⟨10518471716932064453,10518471716932064457⟩⟩]
lemma ha15_0_23_eq (j : Fin 7) : ha15_0_23 j = ((ha15_0_22 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 23 := by fin_cases j <;> decide +kernel
lemma ha15_0_23_contains (j : Fin 7) : (ha15_0_23 j).Contains (fullFactor false 15 23 ((j.val:ℝ)/6)) := by
  rw [ha15_0_23_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha15_0_22 j) false 15 22 j (ha15_0_22_contains j)
noncomputable def hk15_0_24 (j : Fin 6) (i k : Fin 16) : CBox := (power15 j i k).conj.mul (mpower0_24 j i k)
lemma hk15_0_24_contains (j : Fin 6) (i k : Fin 16) :
    (hk15_0_24 j i k).Contains (fullFactor false 15 24 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk15_0_24,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power15 j i k) (mpower0_24 j i k) (quadraturePoint j.val (16*i.val+k.val)) 15 24 (power15_contains j i k) (mpower0_24_contains j i k)
noncomputable def ha15_0_24 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),1⟩,⟨0,1⟩⟩,⟨⟨(-4875074),(-4875073)⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-82067533019),(-82067533018)⟩⟩,⟨⟨81790159885152,81790159885153⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨17319740045980248,17319740045980250⟩⟩,⟨⟨(-1376864728037741371),(-1376864728037741370)⟩,⟨(-1),1⟩⟩]
lemma ha15_0_24_eq (j : Fin 7) : ha15_0_24 j = ((ha15_0_23 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 24 := by fin_cases j <;> decide +kernel
lemma ha15_0_24_contains (j : Fin 7) : (ha15_0_24 j).Contains (fullFactor false 15 24 ((j.val:ℝ)/6)) := by
  rw [ha15_0_24_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha15_0_23 j) false 15 23 j (ha15_0_23_contains j)
noncomputable def hk15_0_25 (j : Fin 6) (i k : Fin 16) : CBox := (power15 j i k).conj.mul (mpower0_25 j i k)
lemma hk15_0_25_contains (j : Fin 6) (i k : Fin 16) :
    (hk15_0_25 j i k).Contains (fullFactor false 15 25 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk15_0_25,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power15 j i k) (mpower0_25 j i k) (quadraturePoint j.val (16*i.val+k.val)) 15 25 (power15_contains j i k) (mpower0_25_contains j i k)
noncomputable def ha15_0_25 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),0⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-204207),(-204206)⟩⟩,⟨⟨5156455176,5156455177⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨6852036411496,6852036411497⟩⟩,⟨⟨(-1813718936351217),(-1813718936351216)⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-173021924583611077),(-173021924583611076)⟩⟩]
lemma ha15_0_25_eq (j : Fin 7) : ha15_0_25 j = ((ha15_0_24 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 25 := by fin_cases j <;> decide +kernel
lemma ha15_0_25_contains (j : Fin 7) : (ha15_0_25 j).Contains (fullFactor false 15 25 ((j.val:ℝ)/6)) := by
  rw [ha15_0_25_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha15_0_24 j) false 15 24 j (ha15_0_24_contains j)
noncomputable def hk15_0_26 (j : Fin 6) (i k : Fin 16) : CBox := (power15 j i k).conj.mul (mpower0_26 j i k)
lemma hk15_0_26_contains (j : Fin 6) (i k : Fin 16) :
    (hk15_0_26 j i k).Contains (fullFactor false 15 26 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk15_0_26,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power15 j i k) (mpower0_26 j i k) (quadraturePoint j.val (16*i.val+k.val)) 15 26 (power15_contains j i k) (mpower0_26_contains j i k)
noncomputable def ha15_0_26 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),1⟩,⟨(-1),0⟩⟩,⟨⟨8224,8225⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨311528494,311528495⟩⟩,⟨⟨(-551956596218),(-551956596217)⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-182627118144798),(-182627118144797)⟩⟩,⟨⟨20906323353147684,20906323353147685⟩,⟨(-1),1⟩⟩]
lemma ha15_0_26_eq (j : Fin 7) : ha15_0_26 j = ((ha15_0_25 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 26 := by fin_cases j <;> decide +kernel
lemma ha15_0_26_contains (j : Fin 7) : (ha15_0_26 j).Contains (fullFactor false 15 26 ((j.val:ℝ)/6)) := by
  rw [ha15_0_26_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha15_0_25 j) false 15 25 j (ha15_0_25_contains j)
noncomputable def hk15_0_27 (j : Fin 6) (i k : Fin 16) : CBox := (power15 j i k).conj.mul (mpower0_27 j i k)
lemma hk15_0_27_contains (j : Fin 6) (i k : Fin 16) :
    (hk15_0_27 j i k).Contains (fullFactor false 15 27 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk15_0_27,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power15 j i k) (mpower0_27 j i k) (quadraturePoint j.val (16*i.val+k.val)) 15 27 (power15_contains j i k) (mpower0_27_contains j i k)
noncomputable def ha15_0_27 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨0,1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨318,320⟩⟩,⟨⟨(-18123994),(-18123993)⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-42815377477),(-42815377475)⟩⟩,⟨⟨17708025083641,17708025083642⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨2432561179993388,2432561179993389⟩⟩]
lemma ha15_0_27_eq (j : Fin 7) : ha15_0_27 j = ((ha15_0_26 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 27 := by fin_cases j <;> decide +kernel
lemma ha15_0_27_contains (j : Fin 7) : (ha15_0_27 j).Contains (fullFactor false 15 27 ((j.val:ℝ)/6)) := by
  rw [ha15_0_27_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha15_0_26 j) false 15 26 j (ha15_0_26_contains j)
noncomputable def hk15_0_28 (j : Fin 6) (i k : Fin 16) : CBox := (power15 j i k).conj.mul (mpower0_28 j i k)
lemma hk15_0_28_contains (j : Fin 6) (i k : Fin 16) :
    (hk15_0_28 j i k).Contains (fullFactor false 15 28 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk15_0_28,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power15 j i k) (mpower0_28 j i k) (quadraturePoint j.val (16*i.val+k.val)) 15 28 (power15_contains j i k) (mpower0_28_contains j i k)
noncomputable def ha15_0_28 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),1⟩,⟨0,1⟩⟩,⟨⟨(-12),(-11)⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1016754),(-1016753)⟩⟩,⟨⟨3202582746,3202582747⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨1655696473581,1655696473582⟩⟩,⟨⟨(-272932726159820),(-272932726159819)⟩,⟨(-1),1⟩⟩]
lemma ha15_0_28_eq (j : Fin 7) : ha15_0_28 j = ((ha15_0_27 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 28 := by fin_cases j <;> decide +kernel
lemma ha15_0_28_contains (j : Fin 7) : (ha15_0_28 j).Contains (fullFactor false 15 28 ((j.val:ℝ)/6)) := by
  rw [ha15_0_28_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha15_0_27 j) false 15 27 j (ha15_0_27_contains j)
noncomputable def hk15_0_29 (j : Fin 6) (i k : Fin 16) : CBox := (power15 j i k).conj.mul (mpower0_29 j i k)
lemma hk15_0_29_contains (j : Fin 6) (i k : Fin 16) :
    (hk15_0_29 j i k).Contains (fullFactor false 15 29 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk15_0_29,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power15 j i k) (mpower0_29 j i k) (quadraturePoint j.val (16*i.val+k.val)) 15 29 (power15_contains j i k) (mpower0_29_contains j i k)
noncomputable def ha15_0_29 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),0⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),0⟩⟩,⟨⟨55072,55073⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨231292193,231292194⟩⟩,⟨⟨(-149469076954),(-149469076953)⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-29567015428550),(-29567015428549)⟩⟩]
lemma ha15_0_29_eq (j : Fin 7) : ha15_0_29 j = ((ha15_0_28 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 29 := by fin_cases j <;> decide +kernel
lemma ha15_0_29_contains (j : Fin 7) : (ha15_0_29 j).Contains (fullFactor false 15 29 ((j.val:ℝ)/6)) := by
  rw [ha15_0_29_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha15_0_28 j) false 15 28 j (ha15_0_28_contains j)
noncomputable def hk15_0_30 (j : Fin 6) (i k : Fin 16) : CBox := (power15 j i k).conj.mul (mpower0_30 j i k)
lemma hk15_0_30_contains (j : Fin 6) (i k : Fin 16) :
    (hk15_0_30 j i k).Contains (fullFactor false 15 30 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk15_0_30,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power15 j i k) (mpower0_30 j i k) (quadraturePoint j.val (16*i.val+k.val)) 15 30 (power15_contains j i k) (mpower0_30_contains j i k)
noncomputable def ha15_0_30 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),1⟩,⟨(-1),0⟩⟩,⟨⟨0,1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨2883,2884⟩⟩,⟨⟨(-16147242),(-16147241)⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-13043637614),(-13043637613)⟩⟩,⟨⟨3096250615296,3096250615297⟩,⟨(-1),1⟩⟩]
lemma ha15_0_30_eq (j : Fin 7) : ha15_0_30 j = ((ha15_0_29 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 30 := by fin_cases j <;> decide +kernel
lemma ha15_0_30_contains (j : Fin 7) : (ha15_0_30 j).Contains (fullFactor false 15 30 ((j.val:ℝ)/6)) := by
  rw [ha15_0_30_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha15_0_29 j) false 15 29 j (ha15_0_29_contains j)
noncomputable def hk15_1_0 (j : Fin 6) (i k : Fin 16) : CBox := (kernel15_0 j i k).mul (mpower1_0 j i k)
lemma hk15_1_0_contains (j : Fin 6) (i k : Fin 16) :
    (hk15_1_0 j i k).Contains (fullFactor true 15 0 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk15_1_0,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel15_0 j i k) (mpower1_0 j i k) (quadraturePoint j.val (16*i.val+k.val)) 15 0 (kernel15_0_contains j i k) (mpower1_0_contains j i k)
noncomputable def ha15_1_0 : Fin 7 → CBox := ![⟨⟨(-3),3⟩,⟨(-3),3⟩⟩,⟨⟨(-2),3⟩,⟨0,4⟩⟩,⟨⟨(-2),2⟩,⟨(-4),0⟩⟩,⟨⟨625573895434,625573895437⟩,⟨(-214227081645),(-214227081642)⟩⟩,⟨⟨132384326353275230385,132384326353275230804⟩,⟨149359938803361118801,149359938803361119222⟩⟩,⟨⟨(-28810067062832780021385073),(-28810067062832779936816669)⟩,⟨14486376964375100047519274,14486376964375100131573904⟩⟩,⟨⟨(-58231720871487424966415309699),(-58231720871487424854159620381)⟩,⟨(-26845578778470410410385226492),(-26845578778470410298096885403)⟩⟩]
lemma ha15_1_0_eq (j : Fin 7) : ha15_1_0 j = atomKernel15_0 j := by fin_cases j <;> decide +kernel
lemma ha15_1_0_contains (j : Fin 7) : (ha15_1_0 j).Contains (fullFactor true 15 0 ((j.val:ℝ)/6)) := by
  rw [ha15_1_0_eq]
  simpa only [fullFactor,ite_true] using atomKernel15_0_contains j
noncomputable def hk15_1_1 (j : Fin 6) (i k : Fin 16) : CBox := (kernel15_0 j i k).mul (mpower1_1 j i k)
lemma hk15_1_1_contains (j : Fin 6) (i k : Fin 16) :
    (hk15_1_1 j i k).Contains (fullFactor true 15 1 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk15_1_1,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel15_0 j i k) (mpower1_1 j i k) (quadraturePoint j.val (16*i.val+k.val)) 15 1 (kernel15_0_contains j i k) (mpower1_1_contains j i k)
noncomputable def ha15_1_1 : Fin 7 → CBox := ![⟨⟨(-28),28⟩,⟨(-28),28⟩⟩,⟨⟨(-23),31⟩,⟨(-42),8⟩⟩,⟨⟨(-31),10⟩,⟨(-11),30⟩⟩,⟨⟨(-2864698396932),(-2864698396907)⟩,⟨(-2589347110637),(-2589347110612)⟩⟩,⟨⟨489431859984239291916,489431859984239294500⟩,⟨(-837947705130953727508),(-837947705130953724930)⟩⟩,⟨⟨79472213774095043298203588,79472213774095043701406556⟩,⟨107494824575706493716140980,107494824575706494121235166⟩⟩,⟨⟨(-86005718452907319310299713598),(-86005718452907318883401587765)⟩,⟨215317144707460205231342483657,215317144707460205658470834949⟩⟩]
lemma ha15_1_1_eq (j : Fin 7) : ha15_1_1 j = ((ha15_1_0 j).mul (piI.mul (atomPoints j).z)).scale 1 1 := by fin_cases j <;> decide +kernel
lemma ha15_1_1_contains (j : Fin 7) : (ha15_1_1 j).Contains (fullFactor true 15 1 ((j.val:ℝ)/6)) := by
  rw [ha15_1_1_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha15_1_0 j) true 15 0 j (ha15_1_0_contains j)
noncomputable def hk15_1_2 (j : Fin 6) (i k : Fin 16) : CBox := (kernel15_0 j i k).mul (mpower1_2 j i k)
lemma hk15_1_2_contains (j : Fin 6) (i k : Fin 16) :
    (hk15_1_2 j i k).Contains (fullFactor true 15 2 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk15_1_2,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel15_0 j i k) (mpower1_2 j i k) (quadraturePoint j.val (16*i.val+k.val)) 15 2 (kernel15_0_contains j i k) (mpower1_2_contains j i k)
noncomputable def ha15_1_2 : Fin 7 → CBox := ![⟨⟨(-130),130⟩,⟨(-130),130⟩⟩,⟨⟨(-197),104⟩,⟨(-89),204⟩⟩,⟨⟨(-53),154⟩,⟨(-100),107⟩⟩,⟨⟨(-2560025615819),(-2560025615719)⟩,⟨10980751835020,10980751835121⟩⟩,⟨⟨(-2306486536956523932688),(-2306486536956523924766)⟩,⟨(-495690220200613276416),(-495690220200613268488)⟩⟩,⟨⟨191587750265370151223355066,191587750265370152193596853⟩,⟨(-200188333252064110004307444),(-200188333252064109037413542)⟩⟩,⟨⟨396832699157656569054233384096,396832699157656569866762387436⟩,⟨135069033182822761642779371455,135069033182822762454209790513⟩⟩]
lemma ha15_1_2_eq (j : Fin 7) : ha15_1_2 j = ((ha15_1_1 j).mul (piI.mul (atomPoints j).z)).scale 1 2 := by fin_cases j <;> decide +kernel
lemma ha15_1_2_contains (j : Fin 7) : (ha15_1_2 j).Contains (fullFactor true 15 2 ((j.val:ℝ)/6)) := by
  rw [ha15_1_2_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha15_1_1 j) true 15 1 j (ha15_1_1_contains j)
noncomputable def hk15_1_3 (j : Fin 6) (i k : Fin 16) : CBox := (kernel15_0 j i k).mul (mpower1_3 j i k)
lemma hk15_1_3_contains (j : Fin 6) (i k : Fin 16) :
    (hk15_1_3 j i k).Contains (fullFactor true 15 3 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk15_1_3,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel15_0 j i k) (mpower1_3 j i k) (quadraturePoint j.val (16*i.val+k.val)) 15 3 (kernel15_0_contains j i k) (mpower1_3_contains j i k)
noncomputable def ha15_1_3 : Fin 7 → CBox := ![⟨⟨(-400),400⟩,⟨(-400),400⟩⟩,⟨⟨(-377),757⟩,⟨(-651),472⟩⟩,⟨⟨(-425),271⟩,⟨(-440),256⟩⟩,⟨⟨21112534549322,21112534549589⟩,⟨(-5999353735881),(-5999353735615)⟩⟩,⟨⟨401688601115852264813,401688601115852281030⟩,⟨3802363419361090332217,3802363419361090348434⟩⟩,⟨⟨(-317588274110024087716860362),(-317588274110024086171384778)⟩,⟨(-213899675238427037127015273),(-213899675238427035577797486)⟩⟩,⟨⟨137741062977387383480494090471,137741062977387384508646548109⟩,⟨(-486111858337694741492911411797),(-486111858337694740462554603186)⟩⟩]
lemma ha15_1_3_eq (j : Fin 7) : ha15_1_3 j = ((ha15_1_2 j).mul (piI.mul (atomPoints j).z)).scale 1 3 := by fin_cases j <;> decide +kernel
lemma ha15_1_3_contains (j : Fin 7) : (ha15_1_3 j).Contains (fullFactor true 15 3 ((j.val:ℝ)/6)) := by
  rw [ha15_1_3_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha15_1_2 j) true 15 2 j (ha15_1_2_contains j)
noncomputable def hk15_1_4 (j : Fin 6) (i k : Fin 16) : CBox := (kernel15_0 j i k).mul (mpower1_4 j i k)
lemma hk15_1_4_contains (j : Fin 6) (i k : Fin 16) :
    (hk15_1_4 j i k).Contains (fullFactor true 15 4 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk15_1_4,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel15_0 j i k) (mpower1_4 j i k) (quadraturePoint j.val (16*i.val+k.val)) 15 4 (kernel15_0_contains j i k) (mpower1_4_contains j i k)
noncomputable def ha15_1_4 : Fin 7 → CBox := ![⟨⟨(-922),922⟩,⟨(-922),922⟩⟩,⟨⟨(-2056),1162⟩,⟨(-1609),1599⟩⟩,⟨⟨(-901),853⟩,⟨(-665),1089⟩⟩,⟨⟨(-22598648149796),(-22598648149266)⟩,⟨(-22717664327240),(-22717664326710)⟩⟩,⟨⟨4239544125816975678769,4239544125816975703659⟩,⟨(-1904433238686230489227),(-1904433238686230464346)⟩⟩,⟨⟨(-162541118681205133191023302),(-162541118681205131335775039)⟩,⟨362023184194780211338230350,362023184194780213190594499⟩⟩,⟨⟨(-445306669878462460210889292884),(-445306669878462459231045612640)⟩,⟨(-101526927733513473539826172242),(-101526927733513472562818014691)⟩⟩]
lemma ha15_1_4_eq (j : Fin 7) : ha15_1_4 j = ((ha15_1_3 j).mul (piI.mul (atomPoints j).z)).scale 1 4 := by fin_cases j <;> decide +kernel
lemma ha15_1_4_contains (j : Fin 7) : (ha15_1_4 j).Contains (fullFactor true 15 4 ((j.val:ℝ)/6)) := by
  rw [ha15_1_4_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha15_1_3 j) true 15 3 j (ha15_1_3_contains j)
noncomputable def hk15_1_5 (j : Fin 6) (i k : Fin 16) : CBox := (kernel15_0 j i k).mul (mpower1_5 j i k)
lemma hk15_1_5_contains (j : Fin 6) (i k : Fin 16) :
    (hk15_1_5 j i k).Contains (fullFactor true 15 5 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk15_1_5,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel15_0 j i k) (mpower1_5 j i k) (quadraturePoint j.val (16*i.val+k.val)) 15 5 (kernel15_0_contains j i k) (mpower1_5_contains j i k)
noncomputable def ha15_1_5 : Fin 7 → CBox := ![⟨⟨(-1700),1700⟩,⟨(-1700),1700⟩⟩,⟨⟨(-2979),4342⟩,⟨(-3316),3996⟩⟩,⟨⟨(-1525),2009⟩,⟨(-1951),1583⟩⟩,⟨⟨(-10418862931842),(-10418862930999)⟩,⟨35946189151787,35946189152630⟩⟩,⟨⟨(-3044576310301885074431),(-3044576310301885043887)⟩,⟨(-3340150571014782556265),(-3340150571014782525711)⟩⟩,⟨⟨318690081768096833058830388,318690081768096834834668134⟩,⟨81810767217361637703150258,81810767217361639480508871⟩⟩,⟨⟨(-56599930540124757150322128673),(-56599930540124756407637415155)⟩,⟨325415606367997381944026281898,325415606367997382689401540299⟩⟩]
lemma ha15_1_5_eq (j : Fin 7) : ha15_1_5 j = ((ha15_1_4 j).mul (piI.mul (atomPoints j).z)).scale 1 5 := by fin_cases j <;> decide +kernel
lemma ha15_1_5_contains (j : Fin 7) : (ha15_1_5 j).Contains (fullFactor true 15 5 ((j.val:ℝ)/6)) := by
  rw [ha15_1_5_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha15_1_4 j) true 15 4 j (ha15_1_4_contains j)
noncomputable def hk15_1_6 (j : Fin 6) (i k : Fin 16) : CBox := (kernel15_0 j i k).mul (mpower1_6 j i k)
lemma hk15_1_6_contains (j : Fin 6) (i k : Fin 16) :
    (hk15_1_6 j i k).Contains (fullFactor true 15 6 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk15_1_6,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel15_0 j i k) (mpower1_6 j i k) (quadraturePoint j.val (16*i.val+k.val)) 15 6 (kernel15_0_contains j i k) (mpower1_6_contains j i k)
noncomputable def ha15_1_6 : Fin 7 → CBox := ![⟨⟨(-2612),2612⟩,⟨(-2612),2612⟩⟩,⟨⟨(-7603),6283⟩,⟨(-7797),6083⟩⟩,⟨⟨(-3324),2611⟩,⟨(-3024),2910⟩⟩,⟨⟨35518079631519,35518079632635⟩,⟨(-8084131697515),(-8084131696399)⟩⟩,⟨⟨(-1802973530615136234569),(-1802973530615136203317)⟩,⟨3187904732439952240391,3187904732439952271638⟩⟩,⟨⟨18294362229336327109471060,18294362229336328528395377⟩,⟨(-226593843997383169441327698),(-226593843997383168022835504)⟩⟩,⟨⟨197618697793113608511014677922,197618697793113608983481362151⟩,⟨23879907184948611096909296487,23879907184948611567352717564⟩⟩]
lemma ha15_1_6_eq (j : Fin 7) : ha15_1_6 j = ((ha15_1_5 j).mul (piI.mul (atomPoints j).z)).scale 1 6 := by fin_cases j <;> decide +kernel
lemma ha15_1_6_contains (j : Fin 7) : (ha15_1_6 j).Contains (fullFactor true 15 6 ((j.val:ℝ)/6)) := by
  rw [ha15_1_6_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha15_1_5 j) true 15 5 j (ha15_1_5_contains j)
noncomputable def hk15_1_7 (j : Fin 6) (i k : Fin 16) : CBox := (kernel15_0 j i k).mul (mpower1_7 j i k)
lemma hk15_1_7_contains (j : Fin 6) (i k : Fin 16) :
    (hk15_1_7 j i k).Contains (fullFactor true 15 7 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk15_1_7,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel15_0 j i k) (mpower1_7 j i k) (quadraturePoint j.val (16*i.val+k.val)) 15 7 (kernel15_0_contains j i k) (mpower1_7_contains j i k)
noncomputable def ha15_1_7 : Fin 7 → CBox := ![⟨⟨(-3439),3439⟩,⟨(-3439),3439⟩⟩,⟨⟨(-11023),11558⟩,⟨(-9999),12578⟩⟩,⟨⟨(-4062),4479⟩,⟨(-3968),4573⟩⟩,⟨⟨(-20258819518622),(-20258819517356)⟩,⟨(-22651190020228),(-22651190018961)⟩⟩,⟨⟨2494319000515089241861,2494319000515089269258⟩,⟨499843744875283091634,499843744875283119031⟩⟩,⟨⟨(-134083963527644779933418743),(-134083963527644778962375356)⟩,⟨12121900020882973530682592,12121900020882974501614447⟩⟩,⟨⟨7017634420739189197267071111,7017634420739189452680313366⟩,⟨(-102584324816062481936021609509),(-102584324816062481679348468007)⟩⟩]
lemma ha15_1_7_eq (j : Fin 7) : ha15_1_7 j = ((ha15_1_6 j).mul (piI.mul (atomPoints j).z)).scale 1 7 := by fin_cases j <;> decide +kernel
lemma ha15_1_7_contains (j : Fin 7) : (ha15_1_7 j).Contains (fullFactor true 15 7 ((j.val:ℝ)/6)) := by
  rw [ha15_1_7_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha15_1_6 j) true 15 6 j (ha15_1_6_contains j)
noncomputable def hk15_1_8 (j : Fin 6) (i k : Fin 16) : CBox := (kernel15_0 j i k).mul (mpower1_8 j i k)
lemma hk15_1_8_contains (j : Fin 6) (i k : Fin 16) :
    (hk15_1_8 j i k).Contains (fullFactor true 15 8 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk15_1_8,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel15_0 j i k) (mpower1_8 j i k) (quadraturePoint j.val (16*i.val+k.val)) 15 8 (kernel15_0_contains j i k) (mpower1_8_contains j i k)
noncomputable def ha15_1_8 : Fin 7 → CBox := ![⟨⟨(-3962),3962⟩,⟨(-3962),3962⟩⟩,⟨⟨(-15723),16409⟩,⟨(-17425),14705⟩⟩,⟨⟨(-5312),5444⟩,⟨(-5698),5058⟩⟩,⟨⟨(-7297053885566),(-7297053884308)⟩,⟨20948790345937,20948790347194⟩⟩,⟨⟨(-183813712575673850108),(-183813712575673829093)⟩,⟨(-1535146035112526515883),(-1535146035112526494866)⟩⟩,⟨⟨17994695129012496248721797,17994695129012496830085929⟩,⟨67404396222478305509399851,67404396222478306090975188⟩⟩,⟨⟨(-46469049102037817827503005770),(-46469049102037817705503440376)⟩,⟨(-759782235425478337082612924),(-759782235425478215752335137)⟩⟩]
lemma ha15_1_8_eq (j : Fin 7) : ha15_1_8 j = ((ha15_1_7 j).mul (piI.mul (atomPoints j).z)).scale 1 8 := by fin_cases j <;> decide +kernel
lemma ha15_1_8_contains (j : Fin 7) : (ha15_1_8 j).Contains (fullFactor true 15 8 ((j.val:ℝ)/6)) := by
  rw [ha15_1_8_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha15_1_7 j) true 15 7 j (ha15_1_7_contains j)
noncomputable def hk15_1_9 (j : Fin 6) (i k : Fin 16) : CBox := (kernel15_0 j i k).mul (mpower1_9 j i k)
lemma hk15_1_9_contains (j : Fin 6) (i k : Fin 16) :
    (hk15_1_9 j i k).Contains (fullFactor true 15 9 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk15_1_9,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel15_0 j i k) (mpower1_9 j i k) (quadraturePoint j.val (16*i.val+k.val)) 15 9 (kernel15_0_contains j i k) (mpower1_9_contains j i k)
noncomputable def ha15_1_9 : Fin 7 → CBox := ![⟨⟨(-4057),4057⟩,⟨(-4057),4057⟩⟩,⟨⟨(-21176),19468⟩,⟨(-19305),21338⟩⟩,⟨⟨(-6239),5801⟩,⟨(-5883),6157⟩⟩,⟨⟨14184763743012,14184763744122⟩,⟨(-2445490624864),(-2445490623754)⟩⟩,⟨⟨(-757090533452023006356),(-757090533452022992025)⟩,⟨352834535793565789884,352834535793565804213⟩⟩,⟨⟨29188128716051348340310780,29188128716051348649897667⟩,⟨(-13442990277986974236270631),(-13442990277986973926822170)⟩⟩,⟨⟨664672863515847585481122140,664672863515847636711296327⟩,⟨18660401461724227774186828652,18660401461724227825726915504⟩⟩]
lemma ha15_1_9_eq (j : Fin 7) : ha15_1_9 j = ((ha15_1_8 j).mul (piI.mul (atomPoints j).z)).scale 1 9 := by fin_cases j <;> decide +kernel
lemma ha15_1_9_contains (j : Fin 7) : (ha15_1_9 j).Contains (fullFactor true 15 9 ((j.val:ℝ)/6)) := by
  rw [ha15_1_9_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha15_1_8 j) true 15 8 j (ha15_1_8_contains j)
noncomputable def hk15_1_10 (j : Fin 6) (i k : Fin 16) : CBox := (kernel15_0 j i k).mul (mpower1_10 j i k)
lemma hk15_1_10_contains (j : Fin 6) (i k : Fin 16) :
    (hk15_1_10 j i k).Contains (fullFactor true 15 10 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk15_1_10,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel15_0 j i k) (mpower1_10 j i k) (quadraturePoint j.val (16*i.val+k.val)) 15 10 (kernel15_0_contains j i k) (mpower1_10_contains j i k)
noncomputable def ha15_1_10 : Fin 7 → CBox := ![⟨⟨(-3739),3739⟩,⟨(-3739),3739⟩⟩,⟨⟨(-22102),24168⟩,⟨(-23597),22673⟩⟩,⟨⟨(-5886),6243⟩,⟨(-6020),6110⟩⟩,⟨⟨(-5263495714484),(-5263495713602)⟩,⟨(-6553904743419),(-6553904742537)⟩⟩,⟨⟨277735377147687386750,277735377147687395543⟩,⟨296307999341825349684,296307999341825358478⟩⟩,⟨⟨(-7547594100426376764901197),(-7547594100426376616653954)⟩,⟨(-10977418084869787108871500),(-10977418084869786960560510)⟩⟩,⟨⟨6725838771628259267563751076,6725838771628259287158465271⟩,⟨(-590407718691001156908759945),(-590407718691001137439745825)⟩⟩]
lemma ha15_1_10_eq (j : Fin 7) : ha15_1_10 j = ((ha15_1_9 j).mul (piI.mul (atomPoints j).z)).scale 1 10 := by fin_cases j <;> decide +kernel
lemma ha15_1_10_contains (j : Fin 7) : (ha15_1_10 j).Contains (fullFactor true 15 10 ((j.val:ℝ)/6)) := by
  rw [ha15_1_10_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha15_1_9 j) true 15 9 j (ha15_1_9_contains j)
noncomputable def hk15_1_11 (j : Fin 6) (i k : Fin 16) : CBox := (kernel15_0 j i k).mul (mpower1_11 j i k)
lemma hk15_1_11_contains (j : Fin 6) (i k : Fin 16) :
    (hk15_1_11 j i k).Contains (fullFactor true 15 11 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk15_1_11,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel15_0 j i k) (mpower1_11 j i k) (quadraturePoint j.val (16*i.val+k.val)) 15 11 (kernel15_0_contains j i k) (mpower1_11_contains j i k)
noncomputable def ha15_1_11 : Fin 7 → CBox := ![⟨⟨(-3133),3133⟩,⟨(-3133),3133⟩⟩,⟨⟨(-24819),23067⟩,⟨(-23970),23916⟩⟩,⟨⟨(-5613),5496⟩,⟨(-5658),5451⟩⟩,⟨⟨(-1689414375471),(-1689414374834)⟩,⟨4130443859177,4130443859814⟩⟩,⟨⟨86188332621887914661,86188332621887919568⟩,⟨(-157467880162956726687),(-157467880162956721781)⟩⟩,⟨⟨(-3593654006583865313223255),(-3593654006583865248635504)⟩,⟨3505964284482908939751413,3505964284482909004316215⟩⟩,⟨⟨(-308628268204759549822896842),(-308628268204759543096234252)⟩,⟨(-2197846918024064348573568131),(-2197846918024064341801709344)⟩⟩]
lemma ha15_1_11_eq (j : Fin 7) : ha15_1_11 j = ((ha15_1_10 j).mul (piI.mul (atomPoints j).z)).scale 1 11 := by fin_cases j <;> decide +kernel
lemma ha15_1_11_contains (j : Fin 7) : (ha15_1_11 j).Contains (fullFactor true 15 11 ((j.val:ℝ)/6)) := by
  rw [ha15_1_11_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha15_1_10 j) true 15 10 j (ha15_1_10_contains j)
noncomputable def hk15_1_12 (j : Fin 6) (i k : Fin 16) : CBox := (kernel15_0 j i k).mul (mpower1_12 j i k)
lemma hk15_1_12_contains (j : Fin 6) (i k : Fin 16) :
    (hk15_1_12 j i k).Contains (fullFactor true 15 12 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk15_1_12,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel15_0 j i k) (mpower1_12 j i k) (quadraturePoint j.val (16*i.val+k.val)) 15 12 (kernel15_0_contains j i k) (mpower1_12_contains j i k)
noncomputable def ha15_1_12 : Fin 7 → CBox := ![⟨⟨(-2406),2406⟩,⟨(-2406),2406⟩⟩,⟨⟨(-22163),23266⟩,⟨(-22426),23003⟩⟩,⟨⟨(-4684),4643⟩,⟨(-4596),4731⟩⟩,⟨⟨2156707367896,2156707368319⟩,⟨(-254925141847),(-254925141425)⟩⟩,⟨⟨(-71508829287481362095),(-71508829287481359586)⟩,⟨(-13297433057265845842),(-13297433057265843332)⟩⟩,⟨⟨1404494218386461420922392,1404494218386461446698181⟩,⟨1017656014294769912723169,1017656014294769938505503⟩⟩,⟨⟨(-656544190399913219629145732),(-656544190399913217483987941)⟩,⟨127263483344247139595633642,127263483344247141726182768⟩⟩]
lemma ha15_1_12_eq (j : Fin 7) : ha15_1_12 j = ((ha15_1_11 j).mul (piI.mul (atomPoints j).z)).scale 1 12 := by fin_cases j <;> decide +kernel
lemma ha15_1_12_contains (j : Fin 7) : (ha15_1_12 j).Contains (fullFactor true 15 12 ((j.val:ℝ)/6)) := by
  rw [ha15_1_12_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha15_1_11 j) true 15 11 j (ha15_1_11_contains j)
noncomputable def hk15_1_13 (j : Fin 6) (i k : Fin 16) : CBox := (kernel15_0 j i k).mul (mpower1_13 j i k)
lemma hk15_1_13_contains (j : Fin 6) (i k : Fin 16) :
    (hk15_1_13 j i k).Contains (fullFactor true 15 13 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk15_1_13,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel15_0 j i k) (mpower1_13 j i k) (quadraturePoint j.val (16*i.val+k.val)) 15 13 (kernel15_0_contains j i k) (mpower1_13_contains j i k)
noncomputable def ha15_1_13 : Fin 7 → CBox := ![⟨⟨(-1706),1706⟩,⟨(-1706),1706⟩⟩,⟨⟨(-20134),19649⟩,⟨(-20219),19564⟩⟩,⟨⟨(-3580),3649⟩,⟨(-3632),3597⟩⟩,⟨⟨(-569668011292),(-569668011033)⟩,⟨(-791971671935),(-791971671676)⟩⟩,⟨⟨3609797622146720276,3609797622146721461⟩,⟨26963105368978648840,26963105368978650025⟩⟩,⟨⟨243710287018291043505728,243710287018291053005642⟩,⟨(-496501147944250074930468),(-496501147944250065431937)⟩⟩,⟨⟨44833327446599466684009381,44833327446599467306942232⟩,⟨180530882763175071693781929,180530882763175072321005279⟩⟩]
lemma ha15_1_13_eq (j : Fin 7) : ha15_1_13 j = ((ha15_1_12 j).mul (piI.mul (atomPoints j).z)).scale 1 13 := by fin_cases j <;> decide +kernel
lemma ha15_1_13_contains (j : Fin 7) : (ha15_1_13 j).Contains (fullFactor true 15 13 ((j.val:ℝ)/6)) := by
  rw [ha15_1_13_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha15_1_12 j) true 15 12 j (ha15_1_12_contains j)
noncomputable def hk15_1_14 (j : Fin 6) (i k : Fin 16) : CBox := (kernel15_0 j i k).mul (mpower1_14 j i k)
lemma hk15_1_14_contains (j : Fin 6) (i k : Fin 16) :
    (hk15_1_14 j i k).Contains (fullFactor true 15 14 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk15_1_14,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel15_0 j i k) (mpower1_14 j i k) (quadraturePoint j.val (16*i.val+k.val)) 15 14 (kernel15_0_contains j i k) (mpower1_14_contains j i k)
noncomputable def ha15_1_14 : Fin 7 → CBox := ![⟨⟨(-1123),1123⟩,⟨(-1123),1123⟩⟩,⟨⟨(-16129),16221⟩,⟨(-15932),16419⟩⟩,⟨⟨(-2620),2583⟩,⟨(-2608),2595⟩⟩,⟨⟨(-173818590698),(-173818590550)⟩,⟨367949577243,367949577390⟩⟩,⟨⟨8507080383887302937,8507080383887303457⟩,⟨(-4109710130156672208),(-4109710130156671687)⟩⟩,⟨⟨(-157142896822890047951179),(-157142896822890044701024)⟩,⟨(-46138600764435763749781),(-46138600764435760499487)⟩⟩,⟨⟨45963086726065309246952429,45963086726065309417237566⟩,⟨(-13985228726111315582829828),(-13985228726111315413699412)⟩⟩]
lemma ha15_1_14_eq (j : Fin 7) : ha15_1_14 j = ((ha15_1_13 j).mul (piI.mul (atomPoints j).z)).scale 1 14 := by fin_cases j <;> decide +kernel
lemma ha15_1_14_contains (j : Fin 7) : (ha15_1_14 j).Contains (fullFactor true 15 14 ((j.val:ℝ)/6)) := by
  rw [ha15_1_14_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha15_1_13 j) true 15 13 j (ha15_1_13_contains j)
noncomputable def hk15_1_15 (j : Fin 6) (i k : Fin 16) : CBox := (kernel15_0 j i k).mul (mpower1_15 j i k)
lemma hk15_1_15_contains (j : Fin 6) (i k : Fin 16) :
    (hk15_1_15 j i k).Contains (fullFactor true 15 15 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk15_1_15,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel15_0 j i k) (mpower1_15 j i k) (quadraturePoint j.val (16*i.val+k.val)) 15 15 (kernel15_0_contains j i k) (mpower1_15_contains j i k)
noncomputable def ha15_1_15 : Fin 7 → CBox := ![⟨⟨(-690),690⟩,⟨(-690),690⟩⟩,⟨⟨(-12240),12313⟩,⟨(-12412),12141⟩⟩,⟨⟨(-1744),1751⟩,⟨(-1739),1756⟩⟩,⟨⟨158099612087,158099612166⟩,⟨(-10225237149),(-10225237070)⟩⟩,⟨⟨(-2125205039136247149),(-2125205039136246935)⟩,⟨(-2204996245807952913),(-2204996245807952699)⟩⟩,⟨⟨(-5187553943830586139198),(-5187553943830585101299)⟩,⟨44964726852375325914609,44964726852375326952556⟩⟩,⟨⟨(-3942111202732563382593650),(-3942111202732563339733811)⟩,⟨(-10889856645213153745299472),(-10889856645213153702152876)⟩⟩]
lemma ha15_1_15_eq (j : Fin 7) : ha15_1_15 j = ((ha15_1_14 j).mul (piI.mul (atomPoints j).z)).scale 1 15 := by fin_cases j <;> decide +kernel
lemma ha15_1_15_contains (j : Fin 7) : (ha15_1_15 j).Contains (fullFactor true 15 15 ((j.val:ℝ)/6)) := by
  rw [ha15_1_15_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha15_1_14 j) true 15 14 j (ha15_1_14_contains j)
noncomputable def hk15_1_16 (j : Fin 6) (i k : Fin 16) : CBox := (kernel15_0 j i k).mul (mpower1_16 j i k)
lemma hk15_1_16_contains (j : Fin 6) (i k : Fin 16) :
    (hk15_1_16 j i k).Contains (fullFactor true 15 16 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk15_1_16,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel15_0 j i k) (mpower1_16 j i k) (quadraturePoint j.val (16*i.val+k.val)) 15 16 (kernel15_0_contains j i k) (mpower1_16_contains j i k)
noncomputable def ha15_1_16 : Fin 7 → CBox := ![⟨⟨(-398),398⟩,⟨(-398),398⟩⟩,⟨⟨(-8784),8686⟩,⟨(-8679),8792⟩⟩,⟨⟨(-1099),1102⟩,⟨(-1104),1097⟩⟩,⟨⟨(-31228332042),(-31228332002)⟩,⟨(-48667494379),(-48667494339)⟩⟩,⟨⟨(-435413478534336185),(-435413478534336102)⟩,⟨822486226160486884,822486226160486967⟩⟩,⟨⟨11709240053361893858973,11709240053361894169719⟩,⟨(-654761877177932907779),(-654761877177932597070)⟩⟩,⟨⟨(-2411458278760950122135610),(-2411458278760950111886925)⟩,⟨1017493194193356470556535,1017493194193356480739136⟩⟩]
lemma ha15_1_16_eq (j : Fin 7) : ha15_1_16 j = ((ha15_1_15 j).mul (piI.mul (atomPoints j).z)).scale 1 16 := by fin_cases j <;> decide +kernel
lemma ha15_1_16_contains (j : Fin 7) : (ha15_1_16 j).Contains (fullFactor true 15 16 ((j.val:ℝ)/6)) := by
  rw [ha15_1_16_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha15_1_15 j) true 15 15 j (ha15_1_15_contains j)
noncomputable def hk15_1_17 (j : Fin 6) (i k : Fin 16) : CBox := (kernel15_0 j i k).mul (mpower1_17 j i k)
lemma hk15_1_17_contains (j : Fin 6) (i k : Fin 16) :
    (hk15_1_17 j i k).Contains (fullFactor true 15 17 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk15_1_17,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel15_0 j i k) (mpower1_17 j i k) (quadraturePoint j.val (16*i.val+k.val)) 15 17 (kernel15_0_contains j i k) (mpower1_17_contains j i k)
noncomputable def ha15_1_17 : Fin 7 → CBox := ![⟨⟨(-216),216⟩,⟨(-216),216⟩⟩,⟨⟨(-5816),5884⟩,⟨(-5865),5835⟩⟩,⟨⟨(-654),651⟩,⟨(-652),653⟩⟩,⟨⟨(-9425378470),(-9425378450)⟩,⟨17485381697,17485381717⟩⟩,⟨⟨262334359118344426,262334359118344457⟩,⟨45014456098625043,45014456098625073⟩⟩,⟨⟨(-642457226611800476393),(-642457226611800388849)⟩,⟨(-2786738818555085824850),(-2786738818555085737292)⟩⟩,⟨⟨242764825140712194912229,242764825140712197189124⟩,⟨500987089757133509120961,500987089757133511412057⟩⟩]
lemma ha15_1_17_eq (j : Fin 7) : ha15_1_17 j = ((ha15_1_16 j).mul (piI.mul (atomPoints j).z)).scale 1 17 := by fin_cases j <;> decide +kernel
lemma ha15_1_17_contains (j : Fin 7) : (ha15_1_17 j).Contains (fullFactor true 15 17 ((j.val:ℝ)/6)) := by
  rw [ha15_1_17_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha15_1_16 j) true 15 16 j (ha15_1_16_contains j)
noncomputable def hk15_1_18 (j : Fin 6) (i k : Fin 16) : CBox := (kernel15_0 j i k).mul (mpower1_18 j i k)
lemma hk15_1_18_contains (j : Fin 6) (i k : Fin 16) :
    (hk15_1_18 j i k).Contains (fullFactor true 15 18 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk15_1_18,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel15_0 j i k) (mpower1_18 j i k) (quadraturePoint j.val (16*i.val+k.val)) 15 18 (kernel15_0_contains j i k) (mpower1_18_contains j i k)
noncomputable def ha15_1_18 : Fin 7 → CBox := ![⟨⟨(-111),111⟩,⟨(-111),111⟩⟩,⟨⟨(-3718),3683⟩,⟨(-3701),3700⟩⟩,⟨⟨(-365),366⟩,⟨(-365),366⟩⟩,⟨⟨6444107887,6444107897⟩,⟨(-74218501),(-74218491)⟩⟩,⟨⟨(-10531320220854831),(-10531320220854820)⟩,⟨(-71121936203773337),(-71121936203773325)⟩⟩,⟨⟨(-607342621940853143638),(-607342621940853120337)⟩,⟨254852341643027207340,254852341643027230637⟩⟩,⟨⟨97971814481565340434885,97971814481565340918589⟩,⟨(-53927896166649930642501),(-53927896166649930161654)⟩⟩]
lemma ha15_1_18_eq (j : Fin 7) : ha15_1_18 j = ((ha15_1_17 j).mul (piI.mul (atomPoints j).z)).scale 1 18 := by fin_cases j <;> decide +kernel
lemma ha15_1_18_contains (j : Fin 7) : (ha15_1_18 j).Contains (fullFactor true 15 18 ((j.val:ℝ)/6)) := by
  rw [ha15_1_18_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha15_1_17 j) true 15 17 j (ha15_1_17_contains j)
noncomputable def hk15_1_19 (j : Fin 6) (i k : Fin 16) : CBox := (kernel15_0 j i k).mul (mpower1_19 j i k)
lemma hk15_1_19_contains (j : Fin 6) (i k : Fin 16) :
    (hk15_1_19 j i k).Contains (fullFactor true 15 19 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk15_1_19,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel15_0 j i k) (mpower1_19 j i k) (quadraturePoint j.val (16*i.val+k.val)) 15 19 (kernel15_0_contains j i k) (mpower1_19_contains j i k)
noncomputable def ha15_1_19 : Fin 7 → CBox := ![⟨⟨(-54),54⟩,⟨(-54),54⟩⟩,⟨⟨(-2211),2225⟩,⟨(-2214),2221⟩⟩,⟨⟨(-194),194⟩,⟨(-195),194⟩⟩,⟨⟨(-979782838),(-979782833)⟩,⟨(-1721488150),(-1721488145)⟩⟩,⟨⟨(-16453888042155436),(-16453888042155431)⟩,⟨8233140571867490,8233140571867495⟩⟩,⟨⟨77310617344702121125,77310617344702126999⟩,⟨121141085236577360601,121141085236577366476⟩⟩,⟨⟨(-11217449129925969720171),(-11217449129925969623967)⟩,⟨(-18086976379205769019271),(-18086976379205768922527)⟩⟩]
lemma ha15_1_19_eq (j : Fin 7) : ha15_1_19 j = ((ha15_1_18 j).mul (piI.mul (atomPoints j).z)).scale 1 19 := by fin_cases j <;> decide +kernel
lemma ha15_1_19_contains (j : Fin 7) : (ha15_1_19 j).Contains (fullFactor true 15 19 ((j.val:ℝ)/6)) := by
  rw [ha15_1_19_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha15_1_18 j) true 15 18 j (ha15_1_18_contains j)
noncomputable def hk15_1_20 (j : Fin 6) (i k : Fin 16) : CBox := (kernel15_0 j i k).mul (mpower1_20 j i k)
lemma hk15_1_20_contains (j : Fin 6) (i k : Fin 16) :
    (hk15_1_20 j i k).Contains (fullFactor true 15 20 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk15_1_20,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel15_0 j i k) (mpower1_20 j i k) (quadraturePoint j.val (16*i.val+k.val)) 15 20 (kernel15_0_contains j i k) (mpower1_20_contains j i k)
noncomputable def ha15_1_20 : Fin 7 → CBox := ![⟨⟨(-25),25⟩,⟨(-25),25⟩⟩,⟨⟨(-1265),1261⟩,⟨(-1265),1260⟩⟩,⟨⟨(-98),98⟩,⟨(-98),98⟩⟩,⟨⟨(-301053578),(-301053575)⟩,⟨493839787,493839790⟩⟩,⟨⟨3148526298655337,3148526298655340⟩,⟨3177032113605567,3177032113605570⟩⟩,⟨⟨22022346920094668566,22022346920094669974⟩,⟨(-20057851764723305843),(-20057851764723304435)⟩⟩,⟨⟨(-3160310230924031310217),(-3160310230924031291835)⟩,⟨2195137655675748406775,2195137655675748425061⟩⟩]
lemma ha15_1_20_eq (j : Fin 7) : ha15_1_20 j = ((ha15_1_19 j).mul (piI.mul (atomPoints j).z)).scale 1 20 := by fin_cases j <;> decide +kernel
lemma ha15_1_20_contains (j : Fin 7) : (ha15_1_20 j).Contains (fullFactor true 15 20 ((j.val:ℝ)/6)) := by
  rw [ha15_1_20_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha15_1_19 j) true 15 19 j (ha15_1_19_contains j)
noncomputable def hk15_1_21 (j : Fin 6) (i k : Fin 16) : CBox := (kernel15_0 j i k).mul (mpower1_21 j i k)
lemma hk15_1_21_contains (j : Fin 6) (i k : Fin 16) :
    (hk15_1_21 j i k).Contains (fullFactor true 15 21 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk15_1_21,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel15_0 j i k) (mpower1_21 j i k) (quadraturePoint j.val (16*i.val+k.val)) 15 21 (kernel15_0_contains j i k) (mpower1_21_contains j i k)
noncomputable def ha15_1_21 : Fin 7 → CBox := ![⟨⟨(-11),11⟩,⟨(-11),11⟩⟩,⟨⟨(-685),685⟩,⟨(-684),686⟩⟩,⟨⟨(-48),48⟩,⟨(-48),48⟩⟩,⟨⟨160697625,160697627⟩,⟨6681225,6681227⟩⟩,⟨⟨471748304129511,471748304129513⟩,⟨(-921928267152629),(-921928267152627)⟩⟩,⟨⟨(-4640605343711136063),(-4640605343711135741)⟩,⟨(-3611474314318475652),(-3611474314318475330)⟩⟩,⟨⟨405720061178166583300,405720061178166586611⟩,⟨523798770182581203669,523798770182581206996⟩⟩]
lemma ha15_1_21_eq (j : Fin 7) : ha15_1_21 j = ((ha15_1_20 j).mul (piI.mul (atomPoints j).z)).scale 1 21 := by fin_cases j <;> decide +kernel
lemma ha15_1_21_contains (j : Fin 7) : (ha15_1_21 j).Contains (fullFactor true 15 21 ((j.val:ℝ)/6)) := by
  rw [ha15_1_21_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha15_1_20 j) true 15 20 j (ha15_1_20_contains j)
noncomputable def hk15_1_22 (j : Fin 6) (i k : Fin 16) : CBox := (kernel15_0 j i k).mul (mpower1_22 j i k)
lemma hk15_1_22_contains (j : Fin 6) (i k : Fin 16) :
    (hk15_1_22 j i k).Contains (fullFactor true 15 22 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk15_1_22,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel15_0 j i k) (mpower1_22 j i k) (quadraturePoint j.val (16*i.val+k.val)) 15 22 (kernel15_0_contains j i k) (mpower1_22_contains j i k)
noncomputable def ha15_1_22 : Fin 7 → CBox := ![⟨⟨(-5),5⟩,⟨(-5),5⟩⟩,⟨⟨(-355),355⟩,⟨(-355),355⟩⟩,⟨⟨(-22),22⟩,⟨(-22),22⟩⟩,⟨⟨(-19120124),(-19120122)⟩,⟨(-38172563),(-38172562)⟩⟩,⟨⟨(-226098430574011),(-226098430574009)⟩,⟨(-35564641660123),(-35564641660121)⟩⟩,⟨⟨(-522069999585921152),(-522069999585921081)⟩,⟨977355735340744596,977355735340744667⟩⟩,⟨⟨82512162792955925322,82512162792955925898⟩,⟨(-71064598054666030852),(-71064598054666030279)⟩⟩]
lemma ha15_1_22_eq (j : Fin 7) : ha15_1_22 j = ((ha15_1_21 j).mul (piI.mul (atomPoints j).z)).scale 1 22 := by fin_cases j <;> decide +kernel
lemma ha15_1_22_contains (j : Fin 7) : (ha15_1_22 j).Contains (fullFactor true 15 22 ((j.val:ℝ)/6)) := by
  rw [ha15_1_22_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha15_1_21 j) true 15 21 j (ha15_1_21_contains j)
noncomputable def hk15_1_23 (j : Fin 6) (i k : Fin 16) : CBox := (kernel15_0 j i k).mul (mpower1_23 j i k)
lemma hk15_1_23_contains (j : Fin 6) (i k : Fin 16) :
    (hk15_1_23 j i k).Contains (fullFactor true 15 23 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk15_1_23,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel15_0 j i k) (mpower1_23 j i k) (quadraturePoint j.val (16*i.val+k.val)) 15 23 (kernel15_0_contains j i k) (mpower1_23_contains j i k)
noncomputable def ha15_1_23 : Fin 7 → CBox := ![⟨⟨(-3),3⟩,⟨(-3),3⟩⟩,⟨⟨(-176),176⟩,⟨(-176),176⟩⟩,⟨⟨(-10),10⟩,⟨(-10),10⟩⟩,⟨⟨(-6125499),(-6125497)⟩,⟨8943427,8943428⟩⟩,⟨⟨7752672013700,7752672013702⟩,⟨47759365910783,47759365910785⟩⟩,⟨⟨189586262789742919,189586262789742935⟩,⟨62802344945326088,62802344945326104⟩⟩,⟨⟨(-11830856502292973303),(-11830856502292973207)⟩,⟨(-12374327409537990826),(-12374327409537990729)⟩⟩]
lemma ha15_1_23_eq (j : Fin 7) : ha15_1_23 j = ((ha15_1_22 j).mul (piI.mul (atomPoints j).z)).scale 1 23 := by fin_cases j <;> decide +kernel
lemma ha15_1_23_contains (j : Fin 7) : (ha15_1_23 j).Contains (fullFactor true 15 23 ((j.val:ℝ)/6)) := by
  rw [ha15_1_23_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha15_1_22 j) true 15 22 j (ha15_1_22_contains j)
noncomputable def hk15_1_24 (j : Fin 6) (i k : Fin 16) : CBox := (kernel15_0 j i k).mul (mpower1_24 j i k)
lemma hk15_1_24_contains (j : Fin 6) (i k : Fin 16) :
    (hk15_1_24 j i k).Contains (fullFactor true 15 24 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk15_1_24,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel15_0 j i k) (mpower1_24 j i k) (quadraturePoint j.val (16*i.val+k.val)) 15 24 (kernel15_0_contains j i k) (mpower1_24_contains j i k)
noncomputable def ha15_1_24 : Fin 7 → CBox := ![⟨⟨(-2),2⟩,⟨(-2),2⟩⟩,⟨⟨(-84),84⟩,⟨(-84),84⟩⟩,⟨⟨(-5),5⟩,⟨(-5),5⟩⟩,⟨⟨2625858,2625860⟩,⟨249207,249208⟩⟩,⟨⟨8704153872782,8704153872784⟩,⟨(-4507905184802),(-4507905184800)⟩⟩,⟨⟨5126650465711862,5126650465711866⟩,⟨(-34114500675306509),(-34114500675306505)⟩⟩,⟨⟨(-1769270786662302653),(-1769270786662302637)⟩,⟨1876879160420998496,1876879160420998512⟩⟩]
lemma ha15_1_24_eq (j : Fin 7) : ha15_1_24 j = ((ha15_1_23 j).mul (piI.mul (atomPoints j).z)).scale 1 24 := by fin_cases j <;> decide +kernel
lemma ha15_1_24_contains (j : Fin 7) : (ha15_1_24 j).Contains (fullFactor true 15 24 ((j.val:ℝ)/6)) := by
  rw [ha15_1_24_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha15_1_23 j) true 15 23 j (ha15_1_23_contains j)
noncomputable def hk15_1_25 (j : Fin 6) (i k : Fin 16) : CBox := (kernel15_0 j i k).mul (mpower1_25 j i k)
lemma hk15_1_25_contains (j : Fin 6) (i k : Fin 16) :
    (hk15_1_25 j i k).Contains (fullFactor true 15 25 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk15_1_25,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel15_0 j i k) (mpower1_25 j i k) (quadraturePoint j.val (16*i.val+k.val)) 15 25 (kernel15_0_contains j i k) (mpower1_25_contains j i k)
noncomputable def ha15_1_25 : Fin 7 → CBox := ![⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-39),39⟩,⟨(-39),39⟩⟩,⟨⟨(-3),3⟩,⟨(-3),3⟩⟩,⟨⟨(-246326),(-246324)⟩,⟨(-564756),(-564754)⟩⟩,⟨⟨(-1360654760856),(-1360654760854)⟩,⟨(-1335280545191),(-1335280545189)⟩⟩,⟨⟨(-5719142408384237),(-5719142408384235)⟩,⟨123325192930835,123325192930837⟩⟩,⟨⟨284387257174484265,284387257174484268⟩,⟨241458199398735454,241458199398735457⟩⟩]
lemma ha15_1_25_eq (j : Fin 7) : ha15_1_25 j = ((ha15_1_24 j).mul (piI.mul (atomPoints j).z)).scale 1 25 := by fin_cases j <;> decide +kernel
lemma ha15_1_25_contains (j : Fin 7) : (ha15_1_25 j).Contains (fullFactor true 15 25 ((j.val:ℝ)/6)) := by
  rw [ha15_1_25_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha15_1_24 j) true 15 24 j (ha15_1_24_contains j)
noncomputable def hk15_1_26 (j : Fin 6) (i k : Fin 16) : CBox := (kernel15_0 j i k).mul (mpower1_26 j i k)
lemma hk15_1_26_contains (j : Fin 6) (i k : Fin 16) :
    (hk15_1_26 j i k).Contains (fullFactor true 15 26 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk15_1_26,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel15_0 j i k) (mpower1_26 j i k) (quadraturePoint j.val (16*i.val+k.val)) 15 26 (kernel15_0_contains j i k) (mpower1_26_contains j i k)
noncomputable def ha15_1_26 : Fin 7 → CBox := ![⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-18),18⟩,⟨(-18),18⟩⟩,⟨⟨(-2),2⟩,⟨(-2),2⟩⟩,⟨⟨(-84148),(-84147)⟩,⟨109866,109868⟩⟩,⟨⟨(-157965566007),(-157965566006)⟩,⟨319601395790,319601395792⟩⟩,⟨⟨174301566456258,174301566456259⟩,⟨895289664226572,895289664226573⟩⟩,⟨⟨31481211390298999,31481211390299000⟩,⟨(-41241123333053736),(-41241123333053735)⟩⟩]
lemma ha15_1_26_eq (j : Fin 7) : ha15_1_26 j = ((ha15_1_25 j).mul (piI.mul (atomPoints j).z)).scale 1 26 := by fin_cases j <;> decide +kernel
lemma ha15_1_26_contains (j : Fin 7) : (ha15_1_26 j).Contains (fullFactor true 15 26 ((j.val:ℝ)/6)) := by
  rw [ha15_1_26_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha15_1_25 j) true 15 25 j (ha15_1_25_contains j)
noncomputable def hk15_1_27 (j : Fin 6) (i k : Fin 16) : CBox := (kernel15_0 j i k).mul (mpower1_27 j i k)
lemma hk15_1_27_contains (j : Fin 6) (i k : Fin 16) :
    (hk15_1_27 j i k).Contains (fullFactor true 15 27 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk15_1_27,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel15_0 j i k) (mpower1_27 j i k) (quadraturePoint j.val (16*i.val+k.val)) 15 27 (kernel15_0_contains j i k) (mpower1_27_contains j i k)
noncomputable def ha15_1_27 : Fin 7 → CBox := ![⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-8),8⟩,⟨(-8),8⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨29605,29607⟩,⟨4404,4405⟩⟩,⟨⟨63552930965,63552930966⟩,⟨9092191472,9092191473⟩⟩,⟨⟨130917105456939,130917105456940⟩,⟨(-49727056261603),(-49727056261601)⟩⟩,⟨⟨(-5734596402523010),(-5734596402523009)⟩,⟨(-3923536666890048),(-3923536666890047)⟩⟩]
lemma ha15_1_27_eq (j : Fin 7) : ha15_1_27 j = ((ha15_1_26 j).mul (piI.mul (atomPoints j).z)).scale 1 27 := by fin_cases j <;> decide +kernel
lemma ha15_1_27_contains (j : Fin 7) : (ha15_1_27 j).Contains (fullFactor true 15 27 ((j.val:ℝ)/6)) := by
  rw [ha15_1_27_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha15_1_26 j) true 15 26 j (ha15_1_26_contains j)
noncomputable def hk15_1_28 (j : Fin 6) (i k : Fin 16) : CBox := (kernel15_0 j i k).mul (mpower1_28 j i k)
lemma hk15_1_28_contains (j : Fin 6) (i k : Fin 16) :
    (hk15_1_28 j i k).Contains (fullFactor true 15 28 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk15_1_28,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel15_0 j i k) (mpower1_28 j i k) (quadraturePoint j.val (16*i.val+k.val)) 15 28 (kernel15_0_contains j i k) (mpower1_28_contains j i k)
noncomputable def ha15_1_28 : Fin 7 → CBox := ![⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-4),4⟩,⟨(-4),4⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-2189),(-2188)⟩,⟨(-5847),(-5846)⟩⟩,⟨⟨(-1939268497),(-1939268495)⟩,⟨(-10978277340),(-10978277339)⟩⟩,⟨⟨(-10548404384211),(-10548404384210)⟩,⟨(-17850432717514),(-17850432717513)⟩⟩,⟨⟨(-467542452399819),(-467542452399818)⟩,⟨765875448926351,765875448926352⟩⟩]
lemma ha15_1_28_eq (j : Fin 7) : ha15_1_28 j = ((ha15_1_27 j).mul (piI.mul (atomPoints j).z)).scale 1 28 := by fin_cases j <;> decide +kernel
lemma ha15_1_28_contains (j : Fin 7) : (ha15_1_28 j).Contains (fullFactor true 15 28 ((j.val:ℝ)/6)) := by
  rw [ha15_1_28_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha15_1_27 j) true 15 27 j (ha15_1_27_contains j)
noncomputable def hk15_1_29 (j : Fin 6) (i k : Fin 16) : CBox := (kernel15_0 j i k).mul (mpower1_29 j i k)
lemma hk15_1_29_contains (j : Fin 6) (i k : Fin 16) :
    (hk15_1_29 j i k).Contains (fullFactor true 15 29 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk15_1_29,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel15_0 j i k) (mpower1_29 j i k) (quadraturePoint j.val (16*i.val+k.val)) 15 29 (kernel15_0_contains j i k) (mpower1_29_contains j i k)
noncomputable def ha15_1_29 : Fin 7 → CBox := ![⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-2),2⟩,⟨(-2),2⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-817),(-816)⟩,⟨955,957⟩⟩,⟨⟨(-1647615162),(-1647615160)⟩,⟨882600101,882600102⟩⟩,⟨⟨(-2258448542260),(-2258448542259)⟩,⟨1919500148939,1919500148940⟩⟩,⟨⟨98392696649395,98392696649396⟩,⟨53258516137027,53258516137028⟩⟩]
lemma ha15_1_29_eq (j : Fin 7) : ha15_1_29 j = ((ha15_1_28 j).mul (piI.mul (atomPoints j).z)).scale 1 29 := by fin_cases j <;> decide +kernel
lemma ha15_1_29_contains (j : Fin 7) : (ha15_1_29 j).Contains (fullFactor true 15 29 ((j.val:ℝ)/6)) := by
  rw [ha15_1_29_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha15_1_28 j) true 15 28 j (ha15_1_28_contains j)
noncomputable def hk15_1_30 (j : Fin 6) (i k : Fin 16) : CBox := (kernel15_0 j i k).mul (mpower1_30 j i k)
lemma hk15_1_30_contains (j : Fin 6) (i k : Fin 16) :
    (hk15_1_30 j i k).Contains (fullFactor true 15 30 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk15_1_30,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel15_0 j i k) (mpower1_30 j i k) (quadraturePoint j.val (16*i.val+k.val)) 15 30 (kernel15_0_contains j i k) (mpower1_30_contains j i k)
noncomputable def ha15_1_30 : Fin 7 → CBox := ![⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨239,241⟩,⟨48,50⟩⟩,⟨⟨219144240,219144241⟩,⟨209150349,209150350⟩⟩,⟨⟨314412101283,314412101284⟩,⟨262483908643,262483908644⟩⟩,⟨⟨5794745396292,5794745396293⟩,⟨(-12176637327149),(-12176637327147)⟩⟩]
lemma ha15_1_30_eq (j : Fin 7) : ha15_1_30 j = ((ha15_1_29 j).mul (piI.mul (atomPoints j).z)).scale 1 30 := by fin_cases j <;> decide +kernel
lemma ha15_1_30_contains (j : Fin 7) : (ha15_1_30 j).Contains (fullFactor true 15 30 ((j.val:ℝ)/6)) := by
  rw [ha15_1_30_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha15_1_29 j) true 15 29 j (ha15_1_29_contains j)
end SharpPlanar.CachedData

end OAI
