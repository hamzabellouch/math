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
noncomputable def hk21_0_0 (j : Fin 6) (i k : Fin 16) : CBox := (power21 j i k).conj.mul (mpower0_0 j i k)
lemma hk21_0_0_contains (j : Fin 6) (i k : Fin 16) :
    (hk21_0_0 j i k).Contains (fullFactor false 21 0 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk21_0_0,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power21 j i k) (mpower0_0 j i k) (quadraturePoint j.val (16*i.val+k.val)) 21 0 (power21_contains j i k) (mpower0_0_contains j i k)
noncomputable def ha21_0_0 : Fin 7 → CBox := ![⟨⟨999999999999999999999999999749,1000000000000000000000000000335⟩,⟨(-335),335⟩⟩,⟨⟨(-69211756054),85708073036⟩,⟨(-1000000000000000000077346766017),(-999999999999999999922653234016)⟩⟩,⟨⟨(-1000000000000000000211538567651),(-999999999999999999788461432360)⟩,⟨(-227952066935),194959432869⟩⟩,⟨⟨(-93344649761),43855698683⟩,⟨999999999999999999931399825799,1000000000000000000068600174222⟩⟩,⟨⟨999999999999999999421654447563,1000000000000000000578345552390⟩,⟨(-545413462277),611398730460⟩⟩,⟨⟨(-686678776404),769160361558⟩,⟨(-1000000000000000000727979659711),(-999999999999999999272020340233)⟩⟩,⟨⟨(-1000000000000000000137617153505),(-999999999999999999862382846579)⟩,⟨(-187106104625),88128202301⟩⟩]
lemma ha21_0_0_eq (j : Fin 7) : ha21_0_0 j = ((atomPoints j).direct.powBin 7 21).conj := by fin_cases j <;> decide +kernel
lemma ha21_0_0_contains (j : Fin 7) : (ha21_0_0 j).Contains (fullFactor false 21 0 ((j.val:ℝ)/6)) := by
  rw [ha21_0_0_eq]
  simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @direct_factor_zero_full ((atomPoints j).direct.powBin 7 21) ((j.val:ℝ)/6) 21 (@direct_power_bin_contains (atomPoints j) ((j.val:ℝ)/6) (atomPoints_contains j) 21 (by norm_num))
noncomputable def hk21_0_1 (j : Fin 6) (i k : Fin 16) : CBox := (power21 j i k).conj.mul (mpower0_1 j i k)
lemma hk21_0_1_contains (j : Fin 6) (i k : Fin 16) :
    (hk21_0_1 j i k).Contains (fullFactor false 21 1 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk21_0_1,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power21 j i k) (mpower0_1 j i k) (quadraturePoint j.val (16*i.val+k.val)) 21 1 (power21_contains j i k) (mpower0_1_contains j i k)
noncomputable def ha21_0_1 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨523598775598298873036167994698,523598775598298873118832005318⟩,⟨(-36239190727),44876642101⟩⟩,⟨⟨(-204161040684),238710846285⟩,⟨(-1047197551196597746378189336697),(-1047197551196597745931810663315)⟩⟩,⟨⟨(-1570796326794896619342756901686),(-1570796326794896619122243098347)⟩,⟨(-146625432971),68888370401⟩⟩,⟨⟨(-1280510506685),1142311284173⟩,⟨2094395102393195491095382574149,2094395102393195493524617425752⟩⟩,⟨⟨2617993877991494363477487040759,2617993877991494367297512959095⟩,⟨(-1797720832773),2013657117753⟩⟩,⟨⟨(-276862912923),587811163732⟩,⟨(-3141592653589793238902337038460),(-3141592653589793238027662961804)⟩⟩]
lemma ha21_0_1_eq (j : Fin 7) : ha21_0_1 j = ((ha21_0_0 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 1 := by fin_cases j <;> decide +kernel
lemma ha21_0_1_contains (j : Fin 7) : (ha21_0_1 j).Contains (fullFactor false 21 1 ((j.val:ℝ)/6)) := by
  rw [ha21_0_1_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha21_0_0 j) false 21 0 j (ha21_0_0_contains j)
noncomputable def hk21_0_2 (j : Fin 6) (i k : Fin 16) : CBox := (power21 j i k).conj.mul (mpower0_2 j i k)
lemma hk21_0_2_contains (j : Fin 6) (i k : Fin 16) :
    (hk21_0_2 j i k).Contains (fullFactor false 21 2 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk21_0_2,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power21 j i k) (mpower0_2 j i k) (quadraturePoint j.val (16*i.val+k.val)) 21 2 (power21_contains j i k) (mpower0_2_contains j i k)
noncomputable def ha21_0_2 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-11748677429),9487397947⟩,⟨137077838904018869695201390983,137077838904018869717279110672⟩⟩,⟨⟨548311355616075478707226675260,548311355616075478942695331350⟩,⟨(-106898470928),124988706837⟩⟩,⟨⟨(-54104799593),115159345763⟩,⟨(-1233700550136169827444721320924),(-1233700550136169827267603193959)⟩⟩,⟨⟨(-2193245422464301916575279065601),(-2193245422464301914024408960707)⟩,⟨(-1340947466883),1196225579491⟩⟩,⟨⟨(-2635871003326),2353211067269⟩,⟨3426945972600471740150350999632,3426945972600471745161661541449⟩⟩,⟨⟨4934802200544679308729827634910,4934802200544679310119470424933⟩,⟨(-434895246646),923331616840⟩⟩]
lemma ha21_0_2_eq (j : Fin 7) : ha21_0_2 j = ((ha21_0_1 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 2 := by fin_cases j <;> decide +kernel
lemma ha21_0_2_contains (j : Fin 7) : (ha21_0_2 j).Contains (fullFactor false 21 2 ((j.val:ℝ)/6)) := by
  rw [ha21_0_2_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha21_0_1 j) false 21 1 j (ha21_0_1_contains j)
noncomputable def hk21_0_3 (j : Fin 6) (i k : Fin 16) : CBox := (power21 j i k).conj.mul (mpower0_3 j i k)
lemma hk21_0_3_contains (j : Fin 6) (i k : Fin 16) :
    (hk21_0_3 j i k).Contains (fullFactor false 21 3 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk21_0_3,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power21 j i k) (mpower0_3 j i k) (quadraturePoint j.val (16*i.val+k.val)) 21 3 (power21_contains j i k) (mpower0_3_contains j i k)
noncomputable def ha21_0_3 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-23924596203935046433713249218),(-23924596203935046429783805862)⟩,⟨(-2050531039),1655863317⟩⟩,⟨⟨(-43629289243),37314605661⟩,⟨191396769631480371412586569558,191396769631480371495389871079⟩⟩,⟨⟨645964097506246253609812742577,645964097506246253704607744577⟩,⟨(-28329206821),60297292441⟩⟩,⟨⟨(-835122998348),936157935736⟩,⟨(-1531174157051842972524764344282),(-1531174157051842970739047180718)⟩⟩,⟨⟨(-2990574525491880806159922309425),(-2990574525491880801777209575321)⟩,⟨(-2300231383295),2053564055911⟩⟩,⟨⟨(-966910608098),455421237315⟩,⟨5167712780049970028521842015069,5167712780049970029993521882488⟩⟩]
lemma ha21_0_3_eq (j : Fin 7) : ha21_0_3 j = ((ha21_0_2 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 3 := by fin_cases j <;> decide +kernel
lemma ha21_0_3_contains (j : Fin 7) : (ha21_0_3 j).Contains (fullFactor false 21 3 ((j.val:ℝ)/6)) := by
  rw [ha21_0_3_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha21_0_2 j) false 21 2 j (ha21_0_2_contains j)
noncomputable def hk21_0_4 (j : Fin 6) (i k : Fin 16) : CBox := (power21 j i k).conj.mul (mpower0_4 j i k)
lemma hk21_0_4_contains (j : Fin 6) (i k : Fin 16) :
    (hk21_0_4 j i k).Contains (fullFactor false 21 4 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk21_0_4,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power21 j i k) (mpower0_4 j i k) (quadraturePoint j.val (16*i.val+k.val)) 21 4 (power21_contains j i k) (mpower0_4_contains j i k)
noncomputable def ha21_0_4 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-216752002),268413886⟩,⟨(-3131722319766024859982221452),(-3131722319766024859457889937)⟩⟩,⟨⟨(-50107557116256397766439566594),(-50107557116256397744602215639)⟩,⟨(-11422121214),9768940919⟩⟩,⟨⟨(-23678691371),11124853504⟩,⟨253669507901048013618307828597,253669507901048013656341193955⟩⟩,⟨⟨801720913860102363619558619163,801720913860102364557109896501⟩,⟨(-437269379409),490171148919⟩⟩,⟨⟨(-1344054531610),1505497919858⟩,⟨(-1957326449853765538762389379314),(-1957326449853765535887680238996)⟩⟩,⟨⟨(-4058712126416768218781579154009),(-4058712126416768217612805207078)⟩,⟨(-759409815770),357687003360⟩⟩]
lemma ha21_0_4_eq (j : Fin 7) : ha21_0_4 j = ((ha21_0_3 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 4 := by fin_cases j <;> decide +kernel
lemma ha21_0_4_contains (j : Fin 7) : (ha21_0_4 j).Contains (fullFactor false 21 4 ((j.val:ℝ)/6)) := by
  rw [ha21_0_4_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha21_0_3 j) false 21 3 j (ha21_0_3_contains j)
noncomputable def hk21_0_5 (j : Fin 6) (i k : Fin 16) : CBox := (power21 j i k).conj.mul (mpower0_5 j i k)
lemma hk21_0_5_contains (j : Fin 6) (i k : Fin 16) :
    (hk21_0_5 j i k).Contains (fullFactor false 21 5 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk21_0_5,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power21 j i k) (mpower0_5 j i k) (quadraturePoint j.val (16*i.val+k.val)) 21 5 (power21_contains j i k) (mpower0_5_contains j i k)
noncomputable def ha21_0_5 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨327953194428670967547351068,327953194428670967603302844⟩,⟨(-22698217),28108237⟩⟩,⟨⟨(-2046002202),2392243473⟩,⟨(-10494502221717470964713967167),(-10494502221717470960106958039)⟩⟩,⟨⟨(-79692626246167045126905552208),(-79692626246167045114703348579)⟩,⟨(-7438880286),3494975805⟩⟩,⟨⟨(-205322410727),183162969333⟩,⟨335824071094959070600240042331,335824071094959070994029564251⟩⟩,⟨⟨1024853732589596772918668540146,1024853732589596774427124936970⟩,⟨(-703745307089),788276867504⟩⟩,⟨⟨(-224741372409),477151259658⟩,⟨(-2550164039877345444236982289328),(-2550164039877345443494502535997)⟩⟩]
lemma ha21_0_5_eq (j : Fin 7) : ha21_0_5 j = ((ha21_0_4 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 5 := by fin_cases j <;> decide +kernel
lemma ha21_0_5_contains (j : Fin 7) : (ha21_0_5 j).Contains (fullFactor false 21 5 ((j.val:ℝ)/6)) := by
  rw [ha21_0_5_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha21_0_4 j) false 21 4 j (ha21_0_4_contains j)
noncomputable def hk21_0_6 (j : Fin 6) (i k : Fin 16) : CBox := (power21 j i k).conj.mul (mpower0_6 j i k)
lemma hk21_0_6_contains (j : Fin 6) (i k : Fin 16) :
    (hk21_0_6 j i k).Contains (fullFactor false 21 6 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk21_0_6,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power21 j i k) (mpower0_6 j i k) (quadraturePoint j.val (16*i.val+k.val)) 21 6 (power21_contains j i k) (mpower0_6_contains j i k)
noncomputable def ha21_0_6 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-2452907),1980794⟩,⟨28619315176067161689070761,28619315176067161694044574⟩⟩,⟨⟨1831636171268298347854738200,1831636171268298348664643260⟩,⟨(-357094750),417525252⟩⟩,⟨⟨(-914982527),1947494305⟩,⟨(-20863480763352960874776009701),(-20863480763352960871515069739)⟩⟩,⟨⟨(-117224714961171094357536012811),(-117224714961171094219704400605)⟩,⟨(-71671041907),63935937652⟩⟩,⟨⟨(-343950668882),307066817605⟩,⟨447176799626049401100782718759,447176799626049401760394395406⟩⟩,⟨⟨1335262768854589495684808660547,1335262768854589496077820423698⟩,⟨(-117674307420),249835815333⟩⟩]
lemma ha21_0_6_eq (j : Fin 7) : ha21_0_6 j = ((ha21_0_5 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 6 := by fin_cases j <;> decide +kernel
lemma ha21_0_6_contains (j : Fin 7) : (ha21_0_6 j).Contains (fullFactor false 21 6 ((j.val:ℝ)/6)) := by
  rw [ha21_0_6_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha21_0_5 j) false 21 5 j (ha21_0_5_contains j)
noncomputable def hk21_0_7 (j : Fin 6) (i k : Fin 16) : CBox := (power21 j i k).conj.mul (mpower0_7 j i k)
lemma hk21_0_7_contains (j : Fin 6) (i k : Fin 16) :
    (hk21_0_7 j i k).Contains (fullFactor false 21 7 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk21_0_7,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power21 j i k) (mpower0_7 j i k) (quadraturePoint j.val (16*i.val+k.val)) 21 7 (power21_contains j i k) (mpower0_7_contains j i k)
noncomputable def ha21_0_7 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-2140719769235797028406185),(-2140719769235797028027329)⟩,⟨(-183478),148164⟩⟩,⟨⟨(-62461632),53421250⟩,⟨274012130462182019550728034,274012130462182019672761757⟩⟩,⟨⟨4681754135318688100336719696,4681754135318688101083375400⟩,⟨(-205321599),437016701⟩⟩,⟨⟨(-19129587813),21443925594⟩,⟨(-35073552699159298530978728865),(-35073552699159298489627964341)⟩⟩,⟨⟨(-167243731971546642953047411980),(-167243731971546642705820868458)⟩,⟨(-128637249353),114842721233⟩⟩,⟨⟨(-112126051722),52812105673⟩,⟨599264529320792076801740693597,599264529320792076980031478680⟩⟩]
lemma ha21_0_7_eq (j : Fin 7) : ha21_0_7 j = ((ha21_0_6 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 7 := by fin_cases j <;> decide +kernel
lemma ha21_0_7_contains (j : Fin 7) : (ha21_0_7 j).Contains (fullFactor false 21 7 ((j.val:ℝ)/6)) := by
  rw [ha21_0_7_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha21_0_6 j) false 21 6 j (ha21_0_6_contains j)
noncomputable def hk21_0_8 (j : Fin 6) (i k : Fin 16) : CBox := (power21 j i k).conj.mul (mpower0_8 j i k)
lemma hk21_0_8_contains (j : Fin 6) (i k : Fin 16) :
    (hk21_0_8 j i k).Contains (fullFactor false 21 8 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk21_0_8,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power21 j i k) (mpower0_8 j i k) (quadraturePoint j.val (16*i.val+k.val)) 21 8 (power21_contains j i k) (mpower0_8_contains j i k)
noncomputable def ha21_0_8 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-9698),12009⟩,⟨(-140109781258867029466551),(-140109781258867029441308)⟩⟩,⟨⟨(-35868104002269959548250178),(-35868104002269959532161829)⟩,⟨(-8176209),6992826⟩⟩,⟨⟨(-85808029),40314802⟩,⟨919260274839426580172466971,919260274839426580321998573⟩⟩,⟨⟨9182234624581109636865320521,9182234624581109647720153320⟩,⟨(-5008114379),5614006593⟩⟩,⟨⟨(-37582192640),42096441411⟩,⟨(-54730383304244933420980744363),(-54730383304244933339901834964)⟩⟩,⟨⟨(-235330630358893204578673443715),(-235330630358893204507909735475)⟩,⟨(-44031797546),20739265401⟩⟩]
lemma ha21_0_8_eq (j : Fin 7) : ha21_0_8 j = ((ha21_0_7 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 8 := by fin_cases j <;> decide +kernel
lemma ha21_0_8_contains (j : Fin 7) : (ha21_0_8 j).Contains (fullFactor false 21 8 ((j.val:ℝ)/6)) := by
  rw [ha21_0_8_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha21_0_7 j) false 21 7 j (ha21_0_7_contains j)
noncomputable def hk21_0_9 (j : Fin 6) (i k : Fin 16) : CBox := (power21 j i k).conj.mul (mpower0_9 j i k)
lemma hk21_0_9_contains (j : Fin 6) (i k : Fin 16) :
    (hk21_0_9 j i k).Contains (fullFactor false 21 9 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk21_0_9,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power21 j i k) (mpower0_9 j i k) (quadraturePoint j.val (16*i.val+k.val)) 21 9 (power21_contains j i k) (mpower0_9_contains j i k)
noncomputable def ha21_0_9 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨8151256657387584304172,8151256657387584305668⟩,⟨(-565),699⟩⟩,⟨⟨(-813653),951346⟩,⟨(-4173443408582443165061761),(-4173443408582443163176511)⟩⟩,⟨⟨(-160441184787359821887048487),(-160441184787359821860439598)⟩,⟨(-14976327),7036261⟩⟩,⟨⟨(-1306438658),1165441137⟩,⟨2136803025194210898762579546,2136803025194210901295415497⟩⟩,⟨⟨15920423158960125583729452885,15920423158960125607365027883⟩,⟨(-10932216695),12245358434⟩⟩,⟨⟨(-7239369314),15369996855⟩,⟨(-82145886611128228811838285862),(-82145886611128228786875613389)⟩⟩]
lemma ha21_0_9_eq (j : Fin 7) : ha21_0_9 j = ((ha21_0_8 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 9 := by fin_cases j <;> decide +kernel
lemma ha21_0_9_contains (j : Fin 7) : (ha21_0_9 j).Contains (fullFactor false 21 9 ((j.val:ℝ)/6)) := by
  rw [ha21_0_9_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha21_0_8 j) false 21 8 j (ha21_0_8_contains j)
noncomputable def hk21_0_10 (j : Fin 6) (i k : Fin 16) : CBox := (power21 j i k).conj.mul (mpower0_10 j i k)
lemma hk21_0_10_contains (j : Fin 6) (i k : Fin 16) :
    (hk21_0_10 j i k).Contains (fullFactor false 21 10 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk21_0_10,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power21 j i k) (mpower0_10 j i k) (quadraturePoint j.val (16*i.val+k.val)) 21 10 (power21_contains j i k) (mpower0_10_contains j i k)
noncomputable def ha21_0_10 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-37),30⟩,⟨426798800539562151414,426798800539562151495⟩⟩,⟨⟨437041971752511642990092,437041971752511643188907⟩,⟨(-85206),99625⟩⟩,⟨⟨(-1105254),2352476⟩,⟨(-25202042373060605483372039),(-25202042373060605479112103)⟩⟩,⟨⟨(-447530979074571922789598144),(-447530979074571922257697687)⟩,⟨(-273619873),244089421⟩⟩,⟨⟨(-3205827342),2862047639⟩,⟨4167957036519161632198205113,4167957036519161638399251198⟩⟩,⟨⟨25806891390014060008829680257,25806891390014060016754080990⟩,⟨(-2274314946),4828626921⟩⟩]
lemma ha21_0_10_eq (j : Fin 7) : ha21_0_10 j = ((ha21_0_9 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 10 := by fin_cases j <;> decide +kernel
lemma ha21_0_10_contains (j : Fin 7) : (ha21_0_10 j).Contains (fullFactor false 21 10 ((j.val:ℝ)/6)) := by
  rw [ha21_0_10_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha21_0_9 j) false 21 9 j (ha21_0_9_contains j)
noncomputable def hk21_0_11 (j : Fin 6) (i k : Fin 16) : CBox := (power21 j i k).conj.mul (mpower0_11 j i k)
lemma hk21_0_11_contains (j : Fin 6) (i k : Fin 16) :
    (hk21_0_11 j i k).Contains (fullFactor false 21 11 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk21_0_11,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power21 j i k) (mpower0_11 j i k) (quadraturePoint j.val (16*i.val+k.val)) 21 11 (power21_contains j i k) (mpower0_11_contains j i k)
noncomputable def ha21_0_11 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-20315575399030665724),(-20315575399030665719)⟩,⟨(-2),2⟩⟩,⟨⟨(-9485),8112⟩,⟨41606298417214803387196,41606298417214803406257⟩⟩,⟨⟨3598843235212085340178349,3598843235212085340798123⟩,⟨(-157830),335933⟩⟩,⟨⟨(-46474518),52097102⟩,⟨(-85209699158455917407268265),(-85209699158455917305723423)⟩⟩,⟨⟨(-991971455030794225400529595),(-991971455030794223921526533)⟩,⟨(-762985124),681165746⟩⟩,⟨⟨(-1379052624),649542830⟩,⟨7370430945714350776176574725,7370430945714350778463239093⟩⟩]
lemma ha21_0_11_eq (j : Fin 7) : ha21_0_11 j = ((ha21_0_10 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 11 := by fin_cases j <;> decide +kernel
lemma ha21_0_11_contains (j : Fin 7) : (ha21_0_11 j).Contains (fullFactor false 21 11 ((j.val:ℝ)/6)) := by
  rw [ha21_0_11_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha21_0_10 j) false 21 10 j (ha21_0_10_contains j)
noncomputable def hk21_0_12 (j : Fin 6) (i k : Fin 16) : CBox := (power21 j i k).conj.mul (mpower0_12 j i k)
lemma hk21_0_12_contains (j : Fin 6) (i k : Fin 16) :
    (hk21_0_12 j i k).Contains (fullFactor false 21 12 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk21_0_12,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power21 j i k) (mpower0_12 j i k) (quadraturePoint j.val (16*i.val+k.val)) 21 12 (power21_contains j i k) (mpower0_12_contains j i k)
noncomputable def ha21_0_12 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),1⟩,⟨(-886434200375614886),(-886434200375614885)⟩⟩,⟨⟨(-3630834484738518571894),(-3630834484738518570218)⟩,⟨(-828),708⟩⟩,⟨⟨(-43974),20660⟩,⟨471087477881817150329954,471087477881817150412583⟩⟩,⟨⟨14871898049488972058161350,14871898049488972075931608⟩,⟨(-8111334),9092660⟩⟩,⟨⟨(-148607313),166457532⟩,⟨(-216414599701077853069829157),(-216414599701077852746471874)⟩⟩,⟨⟨(-1929574309403923048223109524),(-1929574309403923047618320165)⟩,⟨(-361035133),170049916⟩⟩]
lemma ha21_0_12_eq (j : Fin 7) : ha21_0_12 j = ((ha21_0_11 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 12 := by fin_cases j <;> decide +kernel
lemma ha21_0_12_contains (j : Fin 7) : (ha21_0_12 j).Contains (fullFactor false 21 12 ((j.val:ℝ)/6)) := by
  rw [ha21_0_12_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha21_0_11 j) false 21 11 j (ha21_0_11_contains j)
noncomputable def hk21_0_13 (j : Fin 6) (i k : Fin 16) : CBox := (power21 j i k).conj.mul (mpower0_13 j i k)
lemma hk21_0_13_contains (j : Fin 6) (i k : Fin 16) :
    (hk21_0_13 j i k).Contains (fullFactor false 21 13 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk21_0_13,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power21 j i k) (mpower0_13 j i k) (quadraturePoint j.val (16*i.val+k.val)) 21 13 (power21_contains j i k) (mpower0_13_contains j i k)
noncomputable def ha21_0_13 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨35702758612702236,35702758612702237⟩,⟨(-1),1⟩⟩,⟨⟨(-58),67⟩,⟨(-292476998555256723095),(-292476998555256722958)⟩⟩,⟨⟨(-56921729219679268123391),(-56921729219679268113225)⟩,⟨(-5314),2497⟩⟩,⟨⟨(-1464895),1306796⟩,⟨2395971572164663073594720,2395971572164663076465266⟩⟩,⟨⟨43582469009646284998529177,43582469009646285063786935⟩,⟨(-29927157),33521908⟩⟩,⟨⟨(-41094429),87248102⟩,⟨(-466302805767612564498995319),(-466302805767612564351357045)⟩⟩]
lemma ha21_0_13_eq (j : Fin 7) : ha21_0_13 j = ((ha21_0_12 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 13 := by fin_cases j <;> decide +kernel
lemma ha21_0_13_contains (j : Fin 7) : (ha21_0_13 j).Contains (fullFactor false 21 13 ((j.val:ℝ)/6)) := by
  rw [ha21_0_13_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha21_0_12 j) false 21 12 j (ha21_0_12_contains j)
noncomputable def hk21_0_14 (j : Fin 6) (i k : Fin 16) : CBox := (power21 j i k).conj.mul (mpower0_14 j i k)
lemma hk21_0_14_contains (j : Fin 6) (i k : Fin 16) :
    (hk21_0_14 j i k).Contains (fullFactor false 21 14 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk21_0_14,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power21 j i k) (mpower0_14 j i k) (quadraturePoint j.val (16*i.val+k.val)) 21 14 (power21_contains j i k) (mpower0_14_contains j i k)
noncomputable def ha21_0_14 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),1⟩,⟨1335280049649465,1335280049649466⟩⟩,⟨⟨21877228333456835512,21877228333456835523⟩,⟨(-5),6⟩⟩,⟨⟨(-281),597⟩,⟨(-6386603083791852241738),(-6386603083791852240576)⟩⟩,⟨⟨(-358436509015356793336796),(-358436509015356792906222)⟩,⟨(-219148),195497⟩⟩,⟨⟨(-6268583),5596366⟩,⟨8149902646786285751036026,8149902646786285763265141⟩⟩,⟨⟨104638104924845707102384113,104638104924845707135847138⟩,⟨(-9221569),19578429⟩⟩]
lemma ha21_0_14_eq (j : Fin 7) : ha21_0_14 j = ((ha21_0_13 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 14 := by fin_cases j <;> decide +kernel
lemma ha21_0_14_contains (j : Fin 7) : (ha21_0_14 j).Contains (fullFactor false 21 14 ((j.val:ℝ)/6)) := by
  rw [ha21_0_14_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha21_0_13 j) false 21 13 j (ha21_0_13_contains j)
noncomputable def hk21_0_15 (j : Fin 6) (i k : Fin 16) : CBox := (power21 j i k).conj.mul (mpower0_15 j i k)
lemma hk21_0_15_contains (j : Fin 6) (i k : Fin 16) :
    (hk21_0_15 j i k).Contains (fullFactor false 21 15 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk21_0_15,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power21 j i k) (mpower0_15 j i k) (quadraturePoint j.val (16*i.val+k.val)) 21 15 (power21_contains j i k) (mpower0_15_contains j i k)
noncomputable def ha21_0_15 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-46610066605154),(-46610066605153)⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨1527318662517654886,1527318662517654888⟩⟩,⟨⟨668803510981146723193,668803510981146723318⟩,⟨(-30),63⟩⟩,⟨⟨(-27297),30599⟩,⟨(-50047177933378515358159),(-50047177933378515297879)⟩⟩,⟨⟨(-1422426349034211493905310),(-1422426349034211491766398)⟩,⟨(-1094075),976751⟩⟩,⟨⟨(-4100497),1931361⟩,⟨21915353447830215824092124,21915353447830215831170364⟩⟩]
lemma ha21_0_15_eq (j : Fin 7) : ha21_0_15 j = ((ha21_0_14 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 15 := by fin_cases j <;> decide +kernel
lemma ha21_0_15_contains (j : Fin 7) : (ha21_0_15 j).Contains (fullFactor false 21 15 ((j.val:ℝ)/6)) := by
  rw [ha21_0_15_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha21_0_14 j) false 21 14 j (ha21_0_14_contains j)
noncomputable def hk21_0_16 (j : Fin 6) (i k : Fin 16) : CBox := (power21 j i k).conj.mul (mpower0_16 j i k)
lemma hk21_0_16_contains (j : Fin 6) (i k : Fin 16) :
    (hk21_0_16 j i k).Contains (fullFactor false 21 16 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk21_0_16,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power21 j i k) (mpower0_16 j i k) (quadraturePoint j.val (16*i.val+k.val)) 21 16 (power21_contains j i k) (mpower0_16_contains j i k)
noncomputable def ha21_0_16 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),1⟩,⟨(-1525310862814),(-1525310862813)⟩⟩,⟨⟨(-99962772705334444),(-99962772705334443)⟩,⟨(-1),1⟩⟩,⟨⟨(-7),3⟩,⟨65659631149794723616,65659631149794723630⟩⟩,⟨⟨6551160272016798094873,6551160272016798102786⟩,⟨(-3574),4006⟩⟩,⟨⟨(-159821),179018⟩,⟨(-232743967104084891551200),(-232743967104084891200479)⟩⟩,⟨⟨(-4303069587032947008051223),(-4303069587032947006647716)⟩,⟨(-805131),379222⟩⟩]
lemma ha21_0_16_eq (j : Fin 7) : ha21_0_16 j = ((ha21_0_15 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 16 := by fin_cases j <;> decide +kernel
lemma ha21_0_16_contains (j : Fin 7) : (ha21_0_16 j).Contains (fullFactor false 21 16 ((j.val:ℝ)/6)) := by
  rw [ha21_0_16_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha21_0_15 j) false 21 15 j (ha21_0_15_contains j)
noncomputable def hk21_0_17 (j : Fin 6) (i k : Fin 16) : CBox := (power21 j i k).conj.mul (mpower0_17 j i k)
lemma hk21_0_17_contains (j : Fin 6) (i k : Fin 16) :
    (hk21_0_17 j i k).Contains (fullFactor false 21 17 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk21_0_17,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power21 j i k) (mpower0_17 j i k) (quadraturePoint j.val (16*i.val+k.val)) 21 17 (power21_contains j i k) (mpower0_17_contains j i k)
noncomputable def ha21_0_17 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨46979464716,46979464717⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-6157692399285196),(-6157692399285195)⟩⟩,⟨⟨(-6066935731106195668),(-6066935731106195666)⟩,⟨(-1),1⟩⟩,⟨⟨(-494),441⟩,⟨807101058159109192938,807101058159109193917⟩⟩,⟨⟨35842487118702823459513,35842487118702823513639⟩,⟨(-24613),27569⟩⟩,⟨⟨(-70081),148788⟩,⟨(-795205400147551278619411),(-795205400147551278357511)⟩⟩]
lemma ha21_0_17_eq (j : Fin 7) : ha21_0_17 j = ((ha21_0_16 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 17 := by fin_cases j <;> decide +kernel
lemma ha21_0_17_contains (j : Fin 7) : (ha21_0_17 j).Contains (fullFactor false 21 17 ((j.val:ℝ)/6)) := by
  rw [ha21_0_17_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha21_0_16 j) false 21 16 j (ha21_0_16_contains j)
noncomputable def hk21_0_18 (j : Fin 6) (i k : Fin 16) : CBox := (power21 j i k).conj.mul (mpower0_18 j i k)
lemma hk21_0_18_contains (j : Fin 6) (i k : Fin 16) :
    (hk21_0_18 j i k).Contains (fullFactor false 21 18 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk21_0_18,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power21 j i k) (mpower0_18 j i k) (quadraturePoint j.val (16*i.val+k.val)) 21 18 (power21_contains j i k) (mpower0_18_contains j i k)
noncomputable def ha21_0_18 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),1⟩,⟨1366577233,1366577234⟩⟩,⟨⟨358240022308519,358240022308520⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-529440020073462377),(-529440020073462376)⟩⟩,⟨⟨(-93910472408044662797),(-93910472408044662682)⟩,⟨(-58),52⟩⟩,⟨⟨(-4010),3580⟩,⟨5213078436041832667729,5213078436041832675619⟩⟩,⟨⟨138789524622137721123478,138789524622137721169631⟩,⟨(-12232),25969⟩⟩]
lemma ha21_0_18_eq (j : Fin 7) : ha21_0_18 j = ((ha21_0_17 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 18 := by fin_cases j <;> decide +kernel
lemma ha21_0_18_contains (j : Fin 7) : (ha21_0_18 j).Contains (fullFactor false 21 18 ((j.val:ℝ)/6)) := by
  rw [ha21_0_18_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha21_0_17 j) false 21 17 j (ha21_0_17_contains j)
noncomputable def hk21_0_19 (j : Fin 6) (i k : Fin 16) : CBox := (power21 j i k).conj.mul (mpower0_19 j i k)
lemma hk21_0_19_contains (j : Fin 6) (i k : Fin 16) :
    (hk21_0_19 j i k).Contains (fullFactor false 21 19 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk21_0_19,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power21 j i k) (mpower0_19 j i k) (quadraturePoint j.val (16*i.val+k.val)) 21 19 (power21_contains j i k) (mpower0_19_contains j i k)
noncomputable def ha21_0_19 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-37659904),(-37659903)⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨19744635479057,19744635479058⟩⟩,⟨⟨43770654673137422,43770654673137423⟩,⟨(-1),1⟩⟩,⟨⟨(-6),7⟩,⟨(-10351875446044213768),(-10351875446044213755)⟩⟩,⟨⟨(-718305654265631155596),(-718305654265631154505)⟩,⟨(-553),494⟩⟩,⟨⟨(-4294),2023⟩,⟨22948428997269873106678,22948428997269873114384⟩⟩]
lemma ha21_0_19_eq (j : Fin 7) : ha21_0_19 j = ((ha21_0_18 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 19 := by fin_cases j <;> decide +kernel
lemma ha21_0_19_contains (j : Fin 7) : (ha21_0_19 j).Contains (fullFactor false 21 19 ((j.val:ℝ)/6)) := by
  rw [ha21_0_19_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha21_0_18 j) false 21 18 j (ha21_0_18_contains j)
noncomputable def hk21_0_20 (j : Fin 6) (i k : Fin 16) : CBox := (power21 j i k).conj.mul (mpower0_20 j i k)
lemma hk21_0_20_contains (j : Fin 6) (i k : Fin 16) :
    (hk21_0_20 j i k).Contains (fullFactor false 21 20 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk21_0_20,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power21 j i k) (mpower0_20 j i k) (quadraturePoint j.val (16*i.val+k.val)) 21 20 (power21_contains j i k) (mpower0_20_contains j i k)
noncomputable def ha21_0_20 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),1⟩,⟨(-985934),(-985933)⟩⟩,⟨⟨(-1033826696147),(-1033826696146)⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨3437739179098606,3437739179098608⟩⟩,⟨⟨1084045861738968866,1084045861738968868⟩,⟨(-1),1⟩⟩,⟨⟨(-65),73⟩,⟨(-94025990269704865287),(-94025990269704865143)⟩⟩,⟨⟨(-3604730797462500934525),(-3604730797462500933302)⟩,⟨(-675),318⟩⟩]
lemma ha21_0_20_eq (j : Fin 7) : ha21_0_20 j = ((ha21_0_19 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 20 := by fin_cases j <;> decide +kernel
lemma ha21_0_20_contains (j : Fin 7) : (ha21_0_20 j).Contains (fullFactor false 21 20 ((j.val:ℝ)/6)) := by
  rw [ha21_0_20_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha21_0_19 j) false 21 19 j (ha21_0_19_contains j)
noncomputable def hk21_0_21 (j : Fin 6) (i k : Fin 16) : CBox := (power21 j i k).conj.mul (mpower0_21 j i k)
lemma hk21_0_21_contains (j : Fin 6) (i k : Fin 16) :
    (hk21_0_21 j i k).Contains (fullFactor false 21 21 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk21_0_21,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power21 j i k) (mpower0_21 j i k) (quadraturePoint j.val (16*i.val+k.val)) 21 21 (power21_contains j i k) (mpower0_21_contains j i k)
noncomputable def ha21_0_21 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨24582,24583⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-51553370694),(-51553370693)⟩⟩,⟨⟨(-257142289286048),(-257142289286047)⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨108115254456938454,108115254456938455⟩⟩,⟨⟨11721879376103578813,11721879376103578832⟩,⟨(-9),10⟩⟩,⟨⟨(-48),101⟩,⟨(-539266466260812849037),(-539266466260812848851)⟩⟩]
lemma ha21_0_21_eq (j : Fin 7) : ha21_0_21 j = ((ha21_0_20 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 21 := by fin_cases j <;> decide +kernel
lemma ha21_0_21_contains (j : Fin 7) : (ha21_0_21 j).Contains (fullFactor false 21 21 ((j.val:ℝ)/6)) := by
  rw [ha21_0_21_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha21_0_20 j) false 21 20 j (ha21_0_20_contains j)
noncomputable def hk21_0_22 (j : Fin 6) (i k : Fin 16) : CBox := (power21 j i k).conj.mul (mpower0_22 j i k)
lemma hk21_0_22_contains (j : Fin 6) (i k : Fin 16) :
    (hk21_0_22 j i k).Contains (fullFactor false 21 22 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk21_0_22,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power21 j i k) (mpower0_22 j i k) (quadraturePoint j.val (16*i.val+k.val)) 21 22 (power21_contains j i k) (mpower0_22_contains j i k)
noncomputable def ha21_0_22 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),1⟩,⟨585,586⟩⟩,⟨⟨2453934706,2453934707⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-18359916521553),(-18359916521552)⟩⟩,⟨⟨(-10292548155845728),(-10292548155845727)⟩,⟨(-1),1⟩⟩,⟨⟨(-2),2⟩,⟨1394900383872451218,1394900383872451221⟩⟩,⟨⟨77007071306013533785,77007071306013533813⟩,⟨(-7),15⟩⟩]
lemma ha21_0_22_eq (j : Fin 7) : ha21_0_22 j = ((ha21_0_21 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 22 := by fin_cases j <;> decide +kernel
lemma ha21_0_22_contains (j : Fin 7) : (ha21_0_22 j).Contains (fullFactor false 21 22 ((j.val:ℝ)/6)) := by
  rw [ha21_0_22_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha21_0_21 j) false 21 21 j (ha21_0_21_contains j)
noncomputable def hk21_0_23 (j : Fin 6) (i k : Fin 16) : CBox := (power21 j i k).conj.mul (mpower0_23 j i k)
lemma hk21_0_23_contains (j : Fin 6) (i k : Fin 16) :
    (hk21_0_23 j i k).Contains (fullFactor false 21 23 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk21_0_23,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power21 j i k) (mpower0_23 j i k) (quadraturePoint j.val (16*i.val+k.val)) 21 23 (power21_contains j i k) (mpower0_23_contains j i k)
noncomputable def ha21_0_23 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-14),(-13)⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨111728452,111728453⟩⟩,⟨⟨1253899540535,1253899540536⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-937246193423888),(-937246193423887)⟩⟩,⟨⟨(-158775681103741858),(-158775681103741856)⟩,⟨(-1),1⟩⟩,⟨⟨(-3),1⟩,⟨10518471716932064453,10518471716932064458⟩⟩]
lemma ha21_0_23_eq (j : Fin 7) : ha21_0_23 j = ((ha21_0_22 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 23 := by fin_cases j <;> decide +kernel
lemma ha21_0_23_contains (j : Fin 7) : (ha21_0_23 j).Contains (fullFactor false 21 23 ((j.val:ℝ)/6)) := by
  rw [ha21_0_23_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha21_0_22 j) false 21 22 j (ha21_0_22_contains j)
noncomputable def hk21_0_24 (j : Fin 6) (i k : Fin 16) : CBox := (power21 j i k).conj.mul (mpower0_24 j i k)
lemma hk21_0_24_contains (j : Fin 6) (i k : Fin 16) :
    (hk21_0_24 j i k).Contains (fullFactor false 21 24 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk21_0_24,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power21 j i k) (mpower0_24 j i k) (quadraturePoint j.val (16*i.val+k.val)) 21 24 (power21_contains j i k) (mpower0_24_contains j i k)
noncomputable def ha21_0_24 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),1⟩,⟨(-1),0⟩⟩,⟨⟨(-4875074),(-4875073)⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨82067533018,82067533019⟩⟩,⟨⟨81790159885152,81790159885153⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-17319740045980250),(-17319740045980248)⟩⟩,⟨⟨(-1376864728037741371),(-1376864728037741370)⟩,⟨(-1),1⟩⟩]
lemma ha21_0_24_eq (j : Fin 7) : ha21_0_24 j = ((ha21_0_23 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 24 := by fin_cases j <;> decide +kernel
lemma ha21_0_24_contains (j : Fin 7) : (ha21_0_24 j).Contains (fullFactor false 21 24 ((j.val:ℝ)/6)) := by
  rw [ha21_0_24_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha21_0_23 j) false 21 23 j (ha21_0_23_contains j)
noncomputable def hk21_0_25 (j : Fin 6) (i k : Fin 16) : CBox := (power21 j i k).conj.mul (mpower0_25 j i k)
lemma hk21_0_25_contains (j : Fin 6) (i k : Fin 16) :
    (hk21_0_25 j i k).Contains (fullFactor false 21 25 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk21_0_25,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power21 j i k) (mpower0_25 j i k) (quadraturePoint j.val (16*i.val+k.val)) 21 25 (power21_contains j i k) (mpower0_25_contains j i k)
noncomputable def ha21_0_25 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨0,1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-204207),(-204206)⟩⟩,⟨⟨(-5156455177),(-5156455176)⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨6852036411496,6852036411497⟩⟩,⟨⟨1813718936351216,1813718936351217⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-173021924583611077),(-173021924583611076)⟩⟩]
lemma ha21_0_25_eq (j : Fin 7) : ha21_0_25 j = ((ha21_0_24 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 25 := by fin_cases j <;> decide +kernel
lemma ha21_0_25_contains (j : Fin 7) : (ha21_0_25 j).Contains (fullFactor false 21 25 ((j.val:ℝ)/6)) := by
  rw [ha21_0_25_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha21_0_24 j) false 21 24 j (ha21_0_24_contains j)
noncomputable def hk21_0_26 (j : Fin 6) (i k : Fin 16) : CBox := (power21 j i k).conj.mul (mpower0_26 j i k)
lemma hk21_0_26_contains (j : Fin 6) (i k : Fin 16) :
    (hk21_0_26 j i k).Contains (fullFactor false 21 26 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk21_0_26,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power21 j i k) (mpower0_26 j i k) (quadraturePoint j.val (16*i.val+k.val)) 21 26 (power21_contains j i k) (mpower0_26_contains j i k)
noncomputable def ha21_0_26 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),1⟩,⟨0,1⟩⟩,⟨⟨8224,8225⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-311528495),(-311528494)⟩⟩,⟨⟨(-551956596218),(-551956596217)⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨182627118144797,182627118144798⟩⟩,⟨⟨20906323353147684,20906323353147685⟩,⟨(-1),1⟩⟩]
lemma ha21_0_26_eq (j : Fin 7) : ha21_0_26 j = ((ha21_0_25 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 26 := by fin_cases j <;> decide +kernel
lemma ha21_0_26_contains (j : Fin 7) : (ha21_0_26 j).Contains (fullFactor false 21 26 ((j.val:ℝ)/6)) := by
  rw [ha21_0_26_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha21_0_25 j) false 21 25 j (ha21_0_25_contains j)
noncomputable def hk21_0_27 (j : Fin 6) (i k : Fin 16) : CBox := (power21 j i k).conj.mul (mpower0_27 j i k)
lemma hk21_0_27_contains (j : Fin 6) (i k : Fin 16) :
    (hk21_0_27 j i k).Contains (fullFactor false 21 27 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk21_0_27,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power21 j i k) (mpower0_27 j i k) (quadraturePoint j.val (16*i.val+k.val)) 21 27 (power21_contains j i k) (mpower0_27_contains j i k)
noncomputable def ha21_0_27 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),0⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨318,320⟩⟩,⟨⟨18123993,18123994⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-42815377477),(-42815377475)⟩⟩,⟨⟨(-17708025083642),(-17708025083641)⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨2432561179993388,2432561179993389⟩⟩]
lemma ha21_0_27_eq (j : Fin 7) : ha21_0_27 j = ((ha21_0_26 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 27 := by fin_cases j <;> decide +kernel
lemma ha21_0_27_contains (j : Fin 7) : (ha21_0_27 j).Contains (fullFactor false 21 27 ((j.val:ℝ)/6)) := by
  rw [ha21_0_27_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha21_0_26 j) false 21 26 j (ha21_0_26_contains j)
noncomputable def hk21_0_28 (j : Fin 6) (i k : Fin 16) : CBox := (power21 j i k).conj.mul (mpower0_28 j i k)
lemma hk21_0_28_contains (j : Fin 6) (i k : Fin 16) :
    (hk21_0_28 j i k).Contains (fullFactor false 21 28 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk21_0_28,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power21 j i k) (mpower0_28 j i k) (quadraturePoint j.val (16*i.val+k.val)) 21 28 (power21_contains j i k) (mpower0_28_contains j i k)
noncomputable def ha21_0_28 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),1⟩,⟨(-1),0⟩⟩,⟨⟨(-12),(-11)⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨1016753,1016754⟩⟩,⟨⟨3202582746,3202582747⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1655696473582),(-1655696473581)⟩⟩,⟨⟨(-272932726159820),(-272932726159819)⟩,⟨(-1),1⟩⟩]
lemma ha21_0_28_eq (j : Fin 7) : ha21_0_28 j = ((ha21_0_27 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 28 := by fin_cases j <;> decide +kernel
lemma ha21_0_28_contains (j : Fin 7) : (ha21_0_28 j).Contains (fullFactor false 21 28 ((j.val:ℝ)/6)) := by
  rw [ha21_0_28_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha21_0_27 j) false 21 27 j (ha21_0_27_contains j)
noncomputable def hk21_0_29 (j : Fin 6) (i k : Fin 16) : CBox := (power21 j i k).conj.mul (mpower0_29 j i k)
lemma hk21_0_29_contains (j : Fin 6) (i k : Fin 16) :
    (hk21_0_29 j i k).Contains (fullFactor false 21 29 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk21_0_29,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power21 j i k) (mpower0_29 j i k) (quadraturePoint j.val (16*i.val+k.val)) 21 29 (power21_contains j i k) (mpower0_29_contains j i k)
noncomputable def ha21_0_29 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨0,1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),0⟩⟩,⟨⟨(-55073),(-55072)⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨231292193,231292194⟩⟩,⟨⟨149469076953,149469076954⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-29567015428550),(-29567015428549)⟩⟩]
lemma ha21_0_29_eq (j : Fin 7) : ha21_0_29 j = ((ha21_0_28 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 29 := by fin_cases j <;> decide +kernel
lemma ha21_0_29_contains (j : Fin 7) : (ha21_0_29 j).Contains (fullFactor false 21 29 ((j.val:ℝ)/6)) := by
  rw [ha21_0_29_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha21_0_28 j) false 21 28 j (ha21_0_28_contains j)
noncomputable def hk21_0_30 (j : Fin 6) (i k : Fin 16) : CBox := (power21 j i k).conj.mul (mpower0_30 j i k)
lemma hk21_0_30_contains (j : Fin 6) (i k : Fin 16) :
    (hk21_0_30 j i k).Contains (fullFactor false 21 30 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk21_0_30,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power21 j i k) (mpower0_30 j i k) (quadraturePoint j.val (16*i.val+k.val)) 21 30 (power21_contains j i k) (mpower0_30_contains j i k)
noncomputable def ha21_0_30 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),1⟩,⟨0,1⟩⟩,⟨⟨0,1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-2884),(-2883)⟩⟩,⟨⟨(-16147242),(-16147241)⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨13043637613,13043637614⟩⟩,⟨⟨3096250615296,3096250615297⟩,⟨(-1),1⟩⟩]
lemma ha21_0_30_eq (j : Fin 7) : ha21_0_30 j = ((ha21_0_29 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 30 := by fin_cases j <;> decide +kernel
lemma ha21_0_30_contains (j : Fin 7) : (ha21_0_30 j).Contains (fullFactor false 21 30 ((j.val:ℝ)/6)) := by
  rw [ha21_0_30_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha21_0_29 j) false 21 29 j (ha21_0_29_contains j)
noncomputable def hk21_1_0 (j : Fin 6) (i k : Fin 16) : CBox := (kernel21_0 j i k).mul (mpower1_0 j i k)
lemma hk21_1_0_contains (j : Fin 6) (i k : Fin 16) :
    (hk21_1_0 j i k).Contains (fullFactor true 21 0 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk21_1_0,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel21_0 j i k) (mpower1_0 j i k) (quadraturePoint j.val (16*i.val+k.val)) 21 0 (kernel21_0_contains j i k) (mpower1_0_contains j i k)
noncomputable def ha21_1_0 : Fin 7 → CBox := ![⟨⟨(-3),3⟩,⟨(-3),3⟩⟩,⟨⟨(-3),4⟩,⟨(-4),2⟩⟩,⟨⟨0,4⟩,⟨(-2),2⟩⟩,⟨⟨25312,25315⟩,⟨11801,11804⟩⟩,⟨⟨(-3818447111475508),(-3818447111475505)⟩,⟨(-22135735523014202),(-22135735523014199)⟩⟩,⟨⟨(-465579338219423601664417),(-465579338219423599382689)⟩,⟨(-72777510407062961050706),(-72777510407062958771017)⟩⟩,⟨⟨15107785144520704772910159032,15107785144520704814094127433⟩,⟨14272246381970123218210380229,14272246381970123259587922189⟩⟩]
lemma ha21_1_0_eq (j : Fin 7) : ha21_1_0 j = atomKernel21_0 j := by fin_cases j <;> decide +kernel
lemma ha21_1_0_contains (j : Fin 7) : (ha21_1_0 j).Contains (fullFactor true 21 0 ((j.val:ℝ)/6)) := by
  rw [ha21_1_0_eq]
  simpa only [fullFactor,ite_true] using atomKernel21_0_contains j
noncomputable def hk21_1_1 (j : Fin 6) (i k : Fin 16) : CBox := (kernel21_0 j i k).mul (mpower1_1 j i k)
lemma hk21_1_1_contains (j : Fin 6) (i k : Fin 16) :
    (hk21_1_1 j i k).Contains (fullFactor true 21 1 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk21_1_1,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel21_0 j i k) (mpower1_1 j i k) (quadraturePoint j.val (16*i.val+k.val)) 21 1 (kernel21_0_contains j i k) (mpower1_1_contains j i k)
noncomputable def ha21_1_1 : Fin 7 → CBox := ![⟨⟨(-28),28⟩,⟨(-28),28⟩⟩,⟨⟨(-46),31⟩,⟨(-31),42⟩⟩,⟨⟨(-30),11⟩,⟨(-31),10⟩⟩,⟨⟨(-11359),(-11334)⟩,⟨(-162722),(-162697)⟩⟩,⟨⟨(-96480550487984323),(-96480550487984304)⟩,⟨51184714145044773,51184714145044792⟩⟩,⟨⟨30592198090449795242469,30592198090449806164697⟩,⟨1953286993187611677087887,1953286993187611688021236⟩⟩,⟨⟨48700613826522762890528929747,48700613826522763047850641807⟩,⟨(-57234553114940164290854633226),(-57234553114940164134186467881)⟩⟩]
lemma ha21_1_1_eq (j : Fin 7) : ha21_1_1 j = ((ha21_1_0 j).mul (piI.mul (atomPoints j).z)).scale 1 1 := by fin_cases j <;> decide +kernel
lemma ha21_1_1_contains (j : Fin 7) : (ha21_1_1 j).Contains (fullFactor true 21 1 ((j.val:ℝ)/6)) := by
  rw [ha21_1_1_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha21_1_0 j) true 21 0 j (ha21_1_0_contains j)
noncomputable def hk21_1_2 (j : Fin 6) (i k : Fin 16) : CBox := (kernel21_0 j i k).mul (mpower1_2 j i k)
lemma hk21_1_2_contains (j : Fin 6) (i k : Fin 16) :
    (hk21_1_2 j i k).Contains (fullFactor true 21 2 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk21_1_2,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel21_0 j i k) (mpower1_2 j i k) (quadraturePoint j.val (16*i.val+k.val)) 21 2 (kernel21_0_contains j i k) (mpower1_2_contains j i k)
noncomputable def ha21_1_2 : Fin 7 → CBox := ![⟨⟨(-130),130⟩,⟨(-130),130⟩⟩,⟨⟨(-177),255⟩,⟨(-219),205⟩⟩,⟨⟨(-107),100⟩,⟨(-53),154⟩⟩,⟨⟨(-399578),(-399478)⟩,⟨259163,259264⟩⟩,⟨⟨191337625738189147,191337625738189206⟩,⟨184088006935988298,184088006935988358⟩⟩,⟨⟨3979104688035727781992774,3979104688035727808184783⟩,⟨(-750344026870806919582443),(-750344026870806893419580)⟩⟩,⟨⟨(-107910069603317323581483525279),(-107910069603317323283503211851)⟩,⟨(-82556030310145458717691266524),(-82556030310145458418638820578)⟩⟩]
lemma ha21_1_2_eq (j : Fin 7) : ha21_1_2 j = ((ha21_1_1 j).mul (piI.mul (atomPoints j).z)).scale 1 2 := by fin_cases j <;> decide +kernel
lemma ha21_1_2_contains (j : Fin 7) : (ha21_1_2 j).Contains (fullFactor true 21 2 ((j.val:ℝ)/6)) := by
  rw [ha21_1_2_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha21_1_1 j) true 21 1 j (ha21_1_1_contains j)
noncomputable def hk21_1_3 (j : Fin 6) (i k : Fin 16) : CBox := (kernel21_0 j i k).mul (mpower1_3 j i k)
lemma hk21_1_3_contains (j : Fin 6) (i k : Fin 16) :
    (hk21_1_3 j i k).Contains (fullFactor true 21 3 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk21_1_3,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel21_0 j i k) (mpower1_3 j i k) (quadraturePoint j.val (16*i.val+k.val)) 21 3 (kernel21_0_contains j i k) (mpower1_3_contains j i k)
noncomputable def ha21_1_3 : Fin 7 → CBox := ![⟨⟨(-400),400⟩,⟨(-400),400⟩⟩,⟨⟨(-924),707⟩,⟨(-840),779⟩⟩,⟨⟨(-256),440⟩,⟨(-425),271⟩⟩,⟨⟨818131,818399⟩,⟨435643,435910⟩⟩,⟨⟨186846632239843988,186846632239844111⟩,⟨(-387645571216347740),(-387645571216347618)⟩⟩,⟨⟨(-1955960318379645113927833),(-1955960318379645072144871)⟩,⟨(-5242449847029821582968734),(-5242449847029821541141342)⟩⟩,⟨⟨(-92616446464503346817578897168),(-92616446464503346438628113846)⟩,⟨135055964623526129813364557477,135055964623526130191184037826⟩⟩]
lemma ha21_1_3_eq (j : Fin 7) : ha21_1_3 j = ((ha21_1_2 j).mul (piI.mul (atomPoints j).z)).scale 1 3 := by fin_cases j <;> decide +kernel
lemma ha21_1_3_contains (j : Fin 7) : (ha21_1_3 j).Contains (fullFactor true 21 3 ((j.val:ℝ)/6)) := by
  rw [ha21_1_3_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha21_1_2 j) true 21 2 j (ha21_1_2_contains j)
noncomputable def hk21_1_4 (j : Fin 6) (i k : Fin 16) : CBox := (kernel21_0 j i k).mul (mpower1_4 j i k)
lemma hk21_1_4_contains (j : Fin 6) (i k : Fin 16) :
    (hk21_1_4 j i k).Contains (fullFactor true 21 4 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk21_1_4,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel21_0 j i k) (mpower1_4 j i k) (quadraturePoint j.val (16*i.val+k.val)) 21 4 (kernel21_0_contains j i k) (mpower1_4_contains j i k)
noncomputable def ha21_1_4 : Fin 7 → CBox := ![⟨⟨(-922),922⟩,⟨(-922),922⟩⟩,⟨⟨(-2136),2495⟩,⟨(-2151),2469⟩⟩,⟨⟨(-1089),665⟩,⟨(-901),853⟩⟩,⟨⟨(-22669),(-22137)⟩,⟨(-1353558),(-1353026)⟩⟩,⟨⟨(-518514400400403956),(-518514400400403767)⟩,⟨(-68952050797530133),(-68952050797529944)⟩⟩,⟨⟨(-5009841721879808147076639),(-5009841721879808096982191)⟩,⟨2920740193439121010097645,2920740193439121060145696⟩⟩,⟨⟨126270376428478578139822751975,126270376428478578499092893323⟩,⟨77270122082663491997768083490,77270122082663492357890797722⟩⟩]
lemma ha21_1_4_eq (j : Fin 7) : ha21_1_4 j = ((ha21_1_3 j).mul (piI.mul (atomPoints j).z)).scale 1 4 := by fin_cases j <;> decide +kernel
lemma ha21_1_4_contains (j : Fin 7) : (ha21_1_4 j).Contains (fullFactor true 21 4 ((j.val:ℝ)/6)) := by
  rw [ha21_1_4_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha21_1_3 j) true 21 3 j (ha21_1_3_contains j)
noncomputable def hk21_1_5 (j : Fin 6) (i k : Fin 16) : CBox := (kernel21_0 j i k).mul (mpower1_5 j i k)
lemma hk21_1_5_contains (j : Fin 6) (i k : Fin 16) :
    (hk21_1_5 j i k).Contains (fullFactor true 21 5 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk21_1_5,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel21_0 j i k) (mpower1_5 j i k) (quadraturePoint j.val (16*i.val+k.val)) 21 5 (kernel21_0_contains j i k) (mpower1_5_contains j i k)
noncomputable def ha21_1_5 : Fin 7 → CBox := ![⟨⟨(-1700),1700⟩,⟨(-1700),1700⟩⟩,⟨⟨(-5425),5111⟩,⟨(-5641),4887⟩⟩,⟨⟨(-1583),1951⟩,⟨(-1525),2009⟩⟩,⟨⟨(-1370342),(-1369496)⟩,⟨788425,789271⟩⟩,⟨⟨93435282928897793,93435282928898026⟩,⟨500003572683429201,500003572683429433⟩⟩,⟨⟨3092109020228483345861991,3092109020228483393820410⟩,⟨3681918901938586981315658,3681918901938587029309947⟩⟩,⟨⟨51062842150640993944172671928,51062842150640994217940170308⟩,⟨(-94094977435246888430107396874),(-94094977435246888156816826215)⟩⟩]
lemma ha21_1_5_eq (j : Fin 7) : ha21_1_5 j = ((ha21_1_4 j).mul (piI.mul (atomPoints j).z)).scale 1 5 := by fin_cases j <;> decide +kernel
lemma ha21_1_5_contains (j : Fin 7) : (ha21_1_5 j).Contains (fullFactor true 21 5 ((j.val:ℝ)/6)) := by
  rw [ha21_1_5_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha21_1_4 j) true 21 4 j (ha21_1_4_contains j)
noncomputable def hk21_1_6 (j : Fin 6) (i k : Fin 16) : CBox := (kernel21_0 j i k).mul (mpower1_6 j i k)
lemma hk21_1_6_contains (j : Fin 6) (i k : Fin 16) :
    (hk21_1_6 j i k).Contains (fullFactor true 21 6 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk21_1_6,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel21_0 j i k) (mpower1_6 j i k) (quadraturePoint j.val (16*i.val+k.val)) 21 6 (kernel21_0_contains j i k) (mpower1_6_contains j i k)
noncomputable def ha21_1_6 : Fin 7 → CBox := ![⟨⟨(-2612),2612⟩,⟨(-2612),2612⟩⟩,⟨⟨(-10026),9960⟩,⟨(-9412),10570⟩⟩,⟨⟨(-2910),3024⟩,⟨(-3324),2611⟩⟩,⟨⟨1317192,1318312⟩,⟨793690,794810⟩⟩,⟨⟨361403890790211805,361403890790212043⟩,⟨(-198225606634482607),(-198225606634482368)⟩⟩,⟨⟨2143990124347311540008031,2143990124347311578325206⟩,⟨(-2537562459911188635493223),(-2537562459911188597197319)⟩⟩,⟨⟨(-58227942459464784799907780503),(-58227942459464784626678167181)⟩,⟨(-27786787183841953699076873125),(-27786787183841953525653302766)⟩⟩]
lemma ha21_1_6_eq (j : Fin 7) : ha21_1_6 j = ((ha21_1_5 j).mul (piI.mul (atomPoints j).z)).scale 1 6 := by fin_cases j <;> decide +kernel
lemma ha21_1_6_contains (j : Fin 7) : (ha21_1_6 j).Contains (fullFactor true 21 6 ((j.val:ℝ)/6)) := by
  rw [ha21_1_6_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha21_1_5 j) true 21 5 j (ha21_1_5_contains j)
noncomputable def hk21_1_7 (j : Fin 6) (i k : Fin 16) : CBox := (kernel21_0 j i k).mul (mpower1_7 j i k)
lemma hk21_1_7_contains (j : Fin 6) (i k : Fin 16) :
    (hk21_1_7 j i k).Contains (fullFactor true 21 7 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk21_1_7,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel21_0 j i k) (mpower1_7 j i k) (quadraturePoint j.val (16*i.val+k.val)) 21 7 (kernel21_0_contains j i k) (mpower1_7_contains j i k)
noncomputable def ha21_1_7 : Fin 7 → CBox := ![⟨⟨(-3439),3439⟩,⟨(-3439),3439⟩⟩,⟨⟨(-15907),16595⟩,⟨(-16866),15633⟩⟩,⟨⟨(-4573),3968⟩,⟨(-4062),4479⟩⟩,⟨⟨46226,47497⟩,⟨(-1283373),(-1282102)⟩⟩,⟨⟨(-209065125771816914),(-209065125771816704)⟩,⟨(-195614231166143180),(-195614231166142970)⟩⟩,⟨⟨(-1696673844113512512752951),(-1696673844113512486542251)⟩,⟨(-995945191318522043159649),(-995945191318522016939281)⟩⟩,⟨⟨(-12772165142508555911782359212),(-12772165142508555817622484204)⟩,⟨30782890660336954233874125728,30782890660336954327986534975⟩⟩]
lemma ha21_1_7_eq (j : Fin 7) : ha21_1_7 j = ((ha21_1_6 j).mul (piI.mul (atomPoints j).z)).scale 1 7 := by fin_cases j <;> decide +kernel
lemma ha21_1_7_contains (j : Fin 7) : (ha21_1_7 j).Contains (fullFactor true 21 7 ((j.val:ℝ)/6)) := by
  rw [ha21_1_7_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha21_1_6 j) true 21 6 j (ha21_1_6_contains j)
noncomputable def hk21_1_8 (j : Fin 6) (i k : Fin 16) : CBox := (kernel21_0 j i k).mul (mpower1_8 j i k)
lemma hk21_1_8_contains (j : Fin 6) (i k : Fin 16) :
    (hk21_1_8 j i k).Contains (fullFactor true 21 8 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk21_1_8,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel21_0 j i k) (mpower1_8 j i k) (quadraturePoint j.val (16*i.val+k.val)) 21 8 (kernel21_0_contains j i k) (mpower1_8_contains j i k)
noncomputable def ha21_1_8 : Fin 7 → CBox := ![⟨⟨(-3962),3962⟩,⟨(-3962),3962⟩⟩,⟨⟨(-23741),22509⟩,⟨(-22694),23555⟩⟩,⟨⟨(-5058),5698⟩,⟨(-5312),5444⟩⟩,⟨⟨(-836281),(-835019)⟩,⟨423213,424475⟩⟩,⟨⟨(-73365930813289982),(-73365930813289820)⟩,⟨157787988823759811,157787988823759973⟩⟩,⟨⟨(-359219376252830628549745),(-359219376252830612850363)⟩,⟨954108018600215020818439,954108018600215036514678⟩⟩,⟨⟨14194511500609732960319473904,14194511500609733005055040925⟩,⟨5042551784208670541405379837,5042551784208670586136725919⟩⟩]
lemma ha21_1_8_eq (j : Fin 7) : ha21_1_8 j = ((ha21_1_7 j).mul (piI.mul (atomPoints j).z)).scale 1 8 := by fin_cases j <;> decide +kernel
lemma ha21_1_8_contains (j : Fin 7) : (ha21_1_8 j).Contains (fullFactor true 21 8 ((j.val:ℝ)/6)) := by
  rw [ha21_1_8_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha21_1_7 j) true 21 7 j (ha21_1_7_contains j)
noncomputable def hk21_1_9 (j : Fin 6) (i k : Fin 16) : CBox := (kernel21_0 j i k).mul (mpower1_9 j i k)
lemma hk21_1_9_contains (j : Fin 6) (i k : Fin 16) :
    (hk21_1_9 j i k).Contains (fullFactor true 21 9 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk21_1_9,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel21_0 j i k) (mpower1_9 j i k) (quadraturePoint j.val (16*i.val+k.val)) 21 9 (kernel21_0_contains j i k) (mpower1_9_contains j i k)
noncomputable def ha21_1_9 : Fin 7 → CBox := ![⟨⟨(-4057),4057⟩,⟨(-4057),4057⟩⟩,⟨⟨(-28549),29954⟩,⟨(-29363),29139⟩⟩,⟨⟨(-6157),5883⟩,⟨(-6239),5801⟩⟩,⟨⟨502776,503890⟩,⟨340472,341586⟩⟩,⟨⟨93350482292964928,93350482292965039⟩,⟨11093862236993857,11093862236993968⟩⟩,⟨⟨461201524973641178301879,461201524973641186656785⟩,⟨88392712375110500386156,88392712375110508741531⟩⟩,⟨⟨1727048306760188064322564848,1727048306760188083210636776⟩,⟨(-5800400832812695332967893443),(-5800400832812695314067135498)⟩⟩]
lemma ha21_1_9_eq (j : Fin 7) : ha21_1_9 j = ((ha21_1_8 j).mul (piI.mul (atomPoints j).z)).scale 1 9 := by fin_cases j <;> decide +kernel
lemma ha21_1_9_contains (j : Fin 7) : (ha21_1_9 j).Contains (fullFactor true 21 9 ((j.val:ℝ)/6)) := by
  rw [ha21_1_9_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha21_1_8 j) true 21 8 j (ha21_1_8_contains j)
noncomputable def hk21_1_10 (j : Fin 6) (i k : Fin 16) : CBox := (kernel21_0 j i k).mul (mpower1_10 j i k)
lemma hk21_1_10_contains (j : Fin 6) (i k : Fin 16) :
    (hk21_1_10 j i k).Contains (fullFactor true 21 10 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk21_1_10,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel21_0 j i k) (mpower1_10 j i k) (quadraturePoint j.val (16*i.val+k.val)) 21 10 (kernel21_0_contains j i k) (mpower1_10_contains j i k)
noncomputable def ha21_1_10 : Fin 7 → CBox := ![⟨⟨(-3739),3739⟩,⟨(-3739),3739⟩⟩,⟨⟨(-33881),32720⟩,⟨(-33476),33125⟩⟩,⟨⟨(-6110),6020⟩,⟨(-5886),6243⟩⟩,⟨⟨31322,32207⟩,⟨(-354070),(-353185)⟩⟩,⟨⟨(-9020573237231440),(-9020573237231371)⟩,⟨(-44808937544507244),(-44808937544507175)⟩⟩,⟨⟨3628384056985018137058,3628384056985022139136⟩,⟨(-194640019547781279409532),(-194640019547781275407212)⟩⟩,⟨⟨(-2126969209474934723941776402),(-2126969209474934716755225477)⟩,⟨(-514725568668045225166969124),(-514725568668045217989199493)⟩⟩]
lemma ha21_1_10_eq (j : Fin 7) : ha21_1_10 j = ((ha21_1_9 j).mul (piI.mul (atomPoints j).z)).scale 1 10 := by fin_cases j <;> decide +kernel
lemma ha21_1_10_contains (j : Fin 7) : (ha21_1_10 j).Contains (fullFactor true 21 10 ((j.val:ℝ)/6)) := by
  rw [ha21_1_10_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha21_1_9 j) true 21 9 j (ha21_1_9_contains j)
noncomputable def hk21_1_11 (j : Fin 6) (i k : Fin 16) : CBox := (kernel21_0 j i k).mul (mpower1_11 j i k)
lemma hk21_1_11_contains (j : Fin 6) (i k : Fin 16) :
    (hk21_1_11 j i k).Contains (fullFactor true 21 11 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk21_1_11,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel21_0 j i k) (mpower1_11 j i k) (quadraturePoint j.val (16*i.val+k.val)) 21 11 (kernel21_0_contains j i k) (mpower1_11_contains j i k)
noncomputable def ha21_1_11 : Fin 7 → CBox := ![⟨⟨(-3133),3133⟩,⟨(-3133),3133⟩⟩,⟨⟨(-34119),34809⟩,⟨(-34145),34782⟩⟩,⟨⟨(-5451),5658⟩,⟨(-5613),5496⟩⟩,⟨⟨(-172713),(-172073)⟩,⟨75907,76547⟩⟩,⟨⟨(-17577038496770089),(-17577038496770049)⟩,⟨9961496701455977,9961496701456016⟩⟩,⟨⟨(-72519780905046542338913),(-72519780905046540596013)⟩,⟨11114811196522972421005,11114811196522974163643⟩⟩,⟨⟨(-132663571714906582844480992),(-132663571714906580364867946)⟩,⟨707017540468709262971556584,707017540468709265455499491⟩⟩]
lemma ha21_1_11_eq (j : Fin 7) : ha21_1_11 j = ((ha21_1_10 j).mul (piI.mul (atomPoints j).z)).scale 1 11 := by fin_cases j <;> decide +kernel
lemma ha21_1_11_contains (j : Fin 7) : (ha21_1_11 j).Contains (fullFactor true 21 11 ((j.val:ℝ)/6)) := by
  rw [ha21_1_11_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha21_1_10 j) true 21 10 j (ha21_1_10_contains j)
noncomputable def hk21_1_12 (j : Fin 6) (i k : Fin 16) : CBox := (kernel21_0 j i k).mul (mpower1_12 j i k)
lemma hk21_1_12_contains (j : Fin 6) (i k : Fin 16) :
    (hk21_1_12 j i k).Contains (fullFactor true 21 12 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk21_1_12,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel21_0 j i k) (mpower1_12 j i k) (quadraturePoint j.val (16*i.val+k.val)) 21 12 (kernel21_0_contains j i k) (mpower1_12_contains j i k)
noncomputable def ha21_1_12 : Fin 7 → CBox := ![⟨⟨(-2406),2406⟩,⟨(-2406),2406⟩⟩,⟨⟨(-32817),32574⟩,⟨(-33006),32385⟩⟩,⟨⟨(-4731),4596⟩,⟨(-4684),4643⟩⟩,⟨⟨72893,73317⟩,⟨55197,55621⟩⟩,⟨⟨6054790492698686,6054790492698707⟩,⟨5509209134869157,5509209134869178⟩⟩,⟨⟨8040278427132549156070,8040278427132549851658⟩,⟨24036379677609155897654,24036379677609156593370⟩⟩,⟨⟨214830786016776349448255625,214830786016776350235205102⟩,⟨28857713076777863009964384,28857713076777863795157137⟩⟩]
lemma ha21_1_12_eq (j : Fin 7) : ha21_1_12 j = ((ha21_1_11 j).mul (piI.mul (atomPoints j).z)).scale 1 12 := by fin_cases j <;> decide +kernel
lemma ha21_1_12_contains (j : Fin 7) : (ha21_1_12 j).Contains (fullFactor true 21 12 ((j.val:ℝ)/6)) := by
  rw [ha21_1_12_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha21_1_11 j) true 21 11 j (ha21_1_11_contains j)
noncomputable def hk21_1_13 (j : Fin 6) (i k : Fin 16) : CBox := (kernel21_0 j i k).mul (mpower1_13 j i k)
lemma hk21_1_13_contains (j : Fin 6) (i k : Fin 16) :
    (hk21_1_13 j i k).Contains (fullFactor true 21 13 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk21_1_13,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel21_0 j i k) (mpower1_13 j i k) (quadraturePoint j.val (16*i.val+k.val)) 21 13 (kernel21_0_contains j i k) (mpower1_13_contains j i k)
noncomputable def ha21_1_13 : Fin 7 → CBox := ![⟨⟨(-1706),1706⟩,⟨(-1706),1706⟩⟩,⟨⟨(-28649),28615⟩,⟨(-28414),28850⟩⟩,⟨⟨(-3597),3632⟩,⟨(-3580),3649⟩⟩,⟨⟨5728,5988⟩,⟨(-40918),(-40658)⟩⟩,⟨⟨1252101601432533,1252101601432544⟩,⟨(-2793960176573697),(-2793960176573686)⟩⟩,⟨⟨7117916775454916127883,7117916775454916384226⟩,⟨(-3828912375816956778218),(-3828912375816956521922)⟩⟩,⟨⟨4912804315421372182970529,4912804315421372412476662⟩,⟨(-60090636290371233318815600),(-60090636290371233088690992)⟩⟩]
lemma ha21_1_13_eq (j : Fin 7) : ha21_1_13 j = ((ha21_1_12 j).mul (piI.mul (atomPoints j).z)).scale 1 13 := by fin_cases j <;> decide +kernel
lemma ha21_1_13_contains (j : Fin 7) : (ha21_1_13 j).Contains (fullFactor true 21 13 ((j.val:ℝ)/6)) := by
  rw [ha21_1_13_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha21_1_12 j) true 21 12 j (ha21_1_12_contains j)
noncomputable def hk21_1_14 (j : Fin 6) (i k : Fin 16) : CBox := (kernel21_0 j i k).mul (mpower1_14 j i k)
lemma hk21_1_14_contains (j : Fin 6) (i k : Fin 16) :
    (hk21_1_14 j i k).Contains (fullFactor true 21 14 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk21_1_14,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel21_0 j i k) (mpower1_14 j i k) (quadraturePoint j.val (16*i.val+k.val)) 21 14 (kernel21_0_contains j i k) (mpower1_14_contains j i k)
noncomputable def ha21_1_14 : Fin 7 → CBox := ![⟨⟨(-1123),1123⟩,⟨(-1123),1123⟩⟩,⟨⟨(-23215),23350⟩,⟨(-23397),23168⟩⟩,⟨⟨(-2595),2608⟩,⟨(-2620),2583⟩⟩,⟨⟨(-16141),(-15993)⟩,⟨6033,6182⟩⟩,⟨⟨(-1057531862638861),(-1057531862638855)⟩,⟨(-110775019920221),(-110775019920215)⟩⟩,⟨⟨(-1475387514196049881400),(-1475387514196049793709)⟩,⟨(-1884433923738260370747),(-1884433923738260283043)⟩⟩,⟨⟨(-15565096147500065443112018),(-15565096147500065380628108)⟩,⟨(-461203141777090261063187),(-461203141777090198773452)⟩⟩]
lemma ha21_1_14_eq (j : Fin 7) : ha21_1_14 j = ((ha21_1_13 j).mul (piI.mul (atomPoints j).z)).scale 1 14 := by fin_cases j <;> decide +kernel
lemma ha21_1_14_contains (j : Fin 7) : (ha21_1_14 j).Contains (fullFactor true 21 14 ((j.val:ℝ)/6)) := by
  rw [ha21_1_14_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha21_1_13 j) true 21 13 j (ha21_1_13_contains j)
noncomputable def hk21_1_15 (j : Fin 6) (i k : Fin 16) : CBox := (kernel21_0 j i k).mul (mpower1_15 j i k)
lemma hk21_1_15_contains (j : Fin 6) (i k : Fin 16) :
    (hk21_1_15 j i k).Contains (fullFactor true 21 15 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk21_1_15,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel21_0 j i k) (mpower1_15 j i k) (quadraturePoint j.val (16*i.val+k.val)) 21 15 (kernel21_0_contains j i k) (mpower1_15_contains j i k)
noncomputable def ha21_1_15 : Fin 7 → CBox := ![⟨⟨(-690),690⟩,⟨(-690),690⟩⟩,⟨⟨(-17733),17608⟩,⟨(-17629),17712⟩⟩,⟨⟨(-1756),1739⟩,⟨(-1744),1751⟩⟩,⟨⟨5071,5151⟩,⟨4280,4359⟩⟩,⟨⟨72717222711301,72717222711304⟩,⟨336909961463142,336909961463145⟩⟩,⟨⟨(-443956505706476393902),(-443956505706476365895)⟩,⟨490307404760758790855,490307404760758818858⟩⟩,⟨⟨83819583668170213251705,83819583668170229030191⟩,⟨3752837942859004519445812,3752837942859004535279584⟩⟩]
lemma ha21_1_15_eq (j : Fin 7) : ha21_1_15 j = ((ha21_1_14 j).mul (piI.mul (atomPoints j).z)).scale 1 15 := by fin_cases j <;> decide +kernel
lemma ha21_1_15_contains (j : Fin 7) : (ha21_1_15 j).Contains (fullFactor true 21 15 ((j.val:ℝ)/6)) := by
  rw [ha21_1_15_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha21_1_14 j) true 21 14 j (ha21_1_14_contains j)
noncomputable def hk21_1_16 (j : Fin 6) (i k : Fin 16) : CBox := (kernel21_0 j i k).mul (mpower1_16 j i k)
lemma hk21_1_16_contains (j : Fin 6) (i k : Fin 16) :
    (hk21_1_16 j i k).Contains (fullFactor true 21 16 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk21_1_16,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel21_0 j i k) (mpower1_16 j i k) (quadraturePoint j.val (16*i.val+k.val)) 21 16 (kernel21_0_contains j i k) (mpower1_16_contains j i k)
noncomputable def ha21_1_16 : Fin 7 → CBox := ![⟨⟨(-398),398⟩,⟨(-398),398⟩⟩,⟨⟨(-12534),12613⟩,⟨(-12579),12568⟩⟩,⟨⟨(-1097),1104⟩,⟨(-1099),1102⟩⟩,⟨⟨455,495⟩,⟨(-2416),(-2376)⟩⟩,⟨⟨90395491825513,90395491825515⟩,⟨(-52905716791484),(-52905716791482)⟩⟩,⟨⟨144733231343663972305,144733231343663980689⟩,⟨91772986196964009699,91772986196964018084⟩⟩,⟨⟨845991027874165170219117,845991027874165173980501⟩,⟨(-62959854171811811230017),(-62959854171811807482960)⟩⟩]
lemma ha21_1_16_eq (j : Fin 7) : ha21_1_16 j = ((ha21_1_15 j).mul (piI.mul (atomPoints j).z)).scale 1 16 := by fin_cases j <;> decide +kernel
lemma ha21_1_16_contains (j : Fin 7) : (ha21_1_16 j).Contains (fullFactor true 21 16 ((j.val:ℝ)/6)) := by
  rw [ha21_1_16_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha21_1_15 j) true 21 15 j (ha21_1_15_contains j)
noncomputable def hk21_1_17 (j : Fin 6) (i k : Fin 16) : CBox := (kernel21_0 j i k).mul (mpower1_17 j i k)
lemma hk21_1_17_contains (j : Fin 6) (i k : Fin 16) :
    (hk21_1_17 j i k).Contains (fullFactor true 21 17 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk21_1_17,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel21_0 j i k) (mpower1_17 j i k) (quadraturePoint j.val (16*i.val+k.val)) 21 17 (kernel21_0_contains j i k) (mpower1_17_contains j i k)
noncomputable def ha21_1_17 : Fin 7 → CBox := ![⟨⟨(-216),216⟩,⟨(-216),216⟩⟩,⟨⟨(-8439),8401⟩,⟨(-8427),8414⟩⟩,⟨⟨(-653),652⟩,⟨(-654),651⟩⟩,⟨⟨(-809),(-789)⟩,⟨246,266⟩⟩,⟨⟨(-22435601892826),(-22435601892824)⟩,⟨(-19850304477633),(-19850304477631)⟩⟩,⟨⟨16057851358134041222,16057851358134043585⟩,⟨(-38583192534504231157),(-38583192534504228793)⟩⟩,⟨⟨(-22717896797985879520981),(-22717896797985878683437)⟩,⟨(-179004320417499552148258),(-179004320417499551307327)⟩⟩]
lemma ha21_1_17_eq (j : Fin 7) : ha21_1_17 j = ((ha21_1_16 j).mul (piI.mul (atomPoints j).z)).scale 1 17 := by fin_cases j <;> decide +kernel
lemma ha21_1_17_contains (j : Fin 7) : (ha21_1_17 j).Contains (fullFactor true 21 17 ((j.val:ℝ)/6)) := by
  rw [ha21_1_17_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha21_1_16 j) true 21 16 j (ha21_1_16_contains j)
noncomputable def hk21_1_18 (j : Fin 6) (i k : Fin 16) : CBox := (kernel21_0 j i k).mul (mpower1_18 j i k)
lemma hk21_1_18_contains (j : Fin 6) (i k : Fin 16) :
    (hk21_1_18 j i k).Contains (fullFactor true 21 18 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk21_1_18,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel21_0 j i k) (mpower1_18 j i k) (quadraturePoint j.val (16*i.val+k.val)) 21 18 (kernel21_0_contains j i k) (mpower1_18_contains j i k)
noncomputable def ha21_1_18 : Fin 7 → CBox := ![⟨⟨(-111),111⟩,⟨(-111),111⟩⟩,⟨⟨(-5319),5333⟩,⟨(-5319),5333⟩⟩,⟨⟨(-366),365⟩,⟨(-365),366⟩⟩,⟨⟨193,203⟩,⟨182,191⟩⟩,⟨⟨(-3206125447260),(-3206125447258)⟩,⟨7429584745180,7429584745182⟩⟩,⟨⟨(-9385188289362566449),(-9385188289362565819)⟩,⟨(-2134818871831520354),(-2134818871831519724)⟩⟩,⟨⟨(-35673524798518564512904),(-35673524798518564335350)⟩,⟨6424842139256380886180,6424842139256381062996⟩⟩]
lemma ha21_1_18_eq (j : Fin 7) : ha21_1_18 j = ((ha21_1_17 j).mul (piI.mul (atomPoints j).z)).scale 1 18 := by fin_cases j <;> decide +kernel
lemma ha21_1_18_contains (j : Fin 7) : (ha21_1_18 j).Contains (fullFactor true 21 18 ((j.val:ℝ)/6)) := by
  rw [ha21_1_18_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha21_1_17 j) true 21 17 j (ha21_1_17_contains j)
noncomputable def hk21_1_19 (j : Fin 6) (i k : Fin 16) : CBox := (kernel21_0 j i k).mul (mpower1_19 j i k)
lemma hk21_1_19_contains (j : Fin 6) (i k : Fin 16) :
    (hk21_1_19 j i k).Contains (fullFactor true 21 19 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk21_1_19,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel21_0 j i k) (mpower1_19 j i k) (quadraturePoint j.val (16*i.val+k.val)) 21 19 (kernel21_0_contains j i k) (mpower1_19_contains j i k)
noncomputable def ha21_1_19 : Fin 7 → CBox := ![⟨⟨(-54),54⟩,⟨(-54),54⟩⟩,⟨⟨(-3193),3190⟩,⟨(-3196),3187⟩⟩,⟨⟨(-194),195⟩,⟨(-194),194⟩⟩,⟨⟨18,23⟩,⟨(-84),(-78)⟩⟩,⟨⟨2062264429133,2062264429134⟩,⟨187041879818,187041879820⟩⟩,⟨⟨(-111122720750244567),(-111122720750244407)⟩,⟨2097096643341633098,2097096643341633258⟩⟩,⟨⟨1573621561026333788544,1573621561026333823910⟩,⟨6716400672576576397939,6716400672576576433454⟩⟩]
lemma ha21_1_19_eq (j : Fin 7) : ha21_1_19 j = ((ha21_1_18 j).mul (piI.mul (atomPoints j).z)).scale 1 19 := by fin_cases j <;> decide +kernel
lemma ha21_1_19_contains (j : Fin 7) : (ha21_1_19 j).Contains (fullFactor true 21 19 ((j.val:ℝ)/6)) := by
  rw [ha21_1_19_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha21_1_18 j) true 21 18 j (ha21_1_18_contains j)
noncomputable def hk21_1_20 (j : Fin 6) (i k : Fin 16) : CBox := (kernel21_0 j i k).mul (mpower1_20 j i k)
lemma hk21_1_20_contains (j : Fin 6) (i k : Fin 16) :
    (hk21_1_20 j i k).Contains (fullFactor true 21 20 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk21_1_20,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel21_0 j i k) (mpower1_20 j i k) (quadraturePoint j.val (16*i.val+k.val)) 21 20 (kernel21_0_contains j i k) (mpower1_20_contains j i k)
noncomputable def ha21_1_20 : Fin 7 → CBox := ![⟨⟨(-25),25⟩,⟨(-25),25⟩⟩,⟨⟨(-1817),1817⟩,⟨(-1815),1819⟩⟩,⟨⟨(-98),98⟩,⟨(-98),98⟩⟩,⟨⟨(-25),(-22)⟩,⟨5,8⟩⟩,⟨⟨(-113046712677),(-113046712675)⟩,⟨(-490553725153),(-490553725151)⟩⟩,⟨⟨432276245065147118,432276245065147157⟩,⟨(-51151325909299032),(-51151325909298992)⟩⟩,⟨⟨1197880675797602033769,1197880675797602040518⟩,⟨(-347177475646580633062),(-347177475646580626341)⟩⟩]
lemma ha21_1_20_eq (j : Fin 7) : ha21_1_20 j = ((ha21_1_19 j).mul (piI.mul (atomPoints j).z)).scale 1 20 := by fin_cases j <;> decide +kernel
lemma ha21_1_20_contains (j : Fin 7) : (ha21_1_20 j).Contains (fullFactor true 21 20 ((j.val:ℝ)/6)) := by
  rw [ha21_1_20_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha21_1_19 j) true 21 19 j (ha21_1_19_contains j)
noncomputable def hk21_1_21 (j : Fin 6) (i k : Fin 16) : CBox := (kernel21_0 j i k).mul (mpower1_21 j i k)
lemma hk21_1_21_contains (j : Fin 6) (i k : Fin 16) :
    (hk21_1_21 j i k).Contains (fullFactor true 21 21 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk21_1_21,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel21_0 j i k) (mpower1_21 j i k) (quadraturePoint j.val (16*i.val+k.val)) 21 21 (kernel21_0_contains j i k) (mpower1_21_contains j i k)
noncomputable def ha21_1_21 : Fin 7 → CBox := ![⟨⟨(-11),11⟩,⟨(-11),11⟩⟩,⟨⟨(-985),986⟩,⟨(-986),985⟩⟩,⟨⟨(-48),48⟩,⟨(-48),48⟩⟩,⟨⟨4,6⟩,⟨4,6⟩⟩,⟨⟨(-99764135456),(-99764135454)⟩,⟨60268492661,60268492663⟩⟩,⟨⟨(-24448697423311813),(-24448697423311803)⟩,⟨(-82378585476382865),(-82378585476382855)⟩⟩,⟨⟨(-70409379846372144846),(-70409379846372143629)⟩,⟨(-202875601543502997378),(-202875601543502996156)⟩⟩]
lemma ha21_1_21_eq (j : Fin 7) : ha21_1_21 j = ((ha21_1_20 j).mul (piI.mul (atomPoints j).z)).scale 1 21 := by fin_cases j <;> decide +kernel
lemma ha21_1_21_contains (j : Fin 7) : (ha21_1_21 j).Contains (fullFactor true 21 21 ((j.val:ℝ)/6)) := by
  rw [ha21_1_21_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha21_1_20 j) true 21 20 j (ha21_1_20_contains j)
noncomputable def hk21_1_22 (j : Fin 6) (i k : Fin 16) : CBox := (kernel21_0 j i k).mul (mpower1_22 j i k)
lemma hk21_1_22_contains (j : Fin 6) (i k : Fin 16) :
    (hk21_1_22 j i k).Contains (fullFactor true 21 22 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk21_1_22,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel21_0 j i k) (mpower1_22 j i k) (quadraturePoint j.val (16*i.val+k.val)) 21 22 (kernel21_0_contains j i k) (mpower1_22_contains j i k)
noncomputable def ha21_1_22 : Fin 7 → CBox := ![⟨⟨(-5),5⟩,⟨(-5),5⟩⟩,⟨⟨(-511),510⟩,⟨(-510),511⟩⟩,⟨⟨(-22),22⟩,⟨(-22),22⟩⟩,⟨⟨0,1⟩,⟨(-3),(-1)⟩⟩,⟨⟨19528091443,19528091445⟩,⟨16799135387,16799135388⟩⟩,⟨⟨(-14514616734452756),(-14514616734452753)⟩,⟨7177264519278800,7177264519278803⟩⟩,⟨⟨(-32698548834758724346),(-32698548834758724134)⟩,⟨13288397097077496660,13288397097077496871⟩⟩]
lemma ha21_1_22_eq (j : Fin 7) : ha21_1_22 j = ((ha21_1_21 j).mul (piI.mul (atomPoints j).z)).scale 1 22 := by fin_cases j <;> decide +kernel
lemma ha21_1_22_contains (j : Fin 7) : (ha21_1_22 j).Contains (fullFactor true 21 22 ((j.val:ℝ)/6)) := by
  rw [ha21_1_22_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha21_1_21 j) true 21 21 j (ha21_1_21_contains j)
noncomputable def hk21_1_23 (j : Fin 6) (i k : Fin 16) : CBox := (kernel21_0 j i k).mul (mpower1_23 j i k)
lemma hk21_1_23_contains (j : Fin 6) (i k : Fin 16) :
    (hk21_1_23 j i k).Contains (fullFactor true 21 23 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk21_1_23,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel21_0 j i k) (mpower1_23 j i k) (quadraturePoint j.val (16*i.val+k.val)) 21 23 (kernel21_0_contains j i k) (mpower1_23_contains j i k)
noncomputable def ha21_1_23 : Fin 7 → CBox := ![⟨⟨(-3),3⟩,⟨(-3),3⟩⟩,⟨⟨(-253),253⟩,⟨(-253),253⟩⟩,⟨⟨(-10),10⟩,⟨(-10),10⟩⟩,⟨⟨(-1),0⟩,⟨(-1),1⟩⟩,⟨⟨2087817588,2087817590⟩,⟨(-5029402165),(-5029402163)⟩⟩,⟨⟨1719302955843843,1719302955843845⟩,⟨2358327073575622,2358327073575623⟩⟩,⟨⟨2353246265861244544,2353246265861244580⟩,⟨5025221929336364150,5025221929336364186⟩⟩]
lemma ha21_1_23_eq (j : Fin 7) : ha21_1_23 j = ((ha21_1_22 j).mul (piI.mul (atomPoints j).z)).scale 1 23 := by fin_cases j <;> decide +kernel
lemma ha21_1_23_contains (j : Fin 7) : (ha21_1_23 j).Contains (fullFactor true 21 23 ((j.val:ℝ)/6)) := by
  rw [ha21_1_23_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha21_1_22 j) true 21 22 j (ha21_1_22_contains j)
noncomputable def hk21_1_24 (j : Fin 6) (i k : Fin 16) : CBox := (kernel21_0 j i k).mul (mpower1_24 j i k)
lemma hk21_1_24_contains (j : Fin 6) (i k : Fin 16) :
    (hk21_1_24 j i k).Contains (fullFactor true 21 24 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk21_1_24,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel21_0 j i k) (mpower1_24 j i k) (quadraturePoint j.val (16*i.val+k.val)) 21 24 (kernel21_0_contains j i k) (mpower1_24_contains j i k)
noncomputable def ha21_1_24 : Fin 7 → CBox := ![⟨⟨(-2),2⟩,⟨(-2),2⟩⟩,⟨⟨(-121),121⟩,⟨(-121),121⟩⟩,⟨⟨(-5),5⟩,⟨(-5),5⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1099982148),(-1099982146)⟩,⟨(-84348237),(-84348235)⟩⟩,⟨⟨350981271630286,350981271630287⟩,⟨(-361868466306042),(-361868466306041)⟩⟩,⟨⟨737680428853148904,737680428853148911⟩,⟨(-393384846566192278),(-393384846566192272)⟩⟩]
lemma ha21_1_24_eq (j : Fin 7) : ha21_1_24 j = ((ha21_1_23 j).mul (piI.mul (atomPoints j).z)).scale 1 24 := by fin_cases j <;> decide +kernel
lemma ha21_1_24_contains (j : Fin 7) : (ha21_1_24 j).Contains (fullFactor true 21 24 ((j.val:ℝ)/6)) := by
  rw [ha21_1_24_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha21_1_23 j) true 21 23 j (ha21_1_23_contains j)
noncomputable def hk21_1_25 (j : Fin 6) (i k : Fin 16) : CBox := (kernel21_0 j i k).mul (mpower1_25 j i k)
lemma hk21_1_25_contains (j : Fin 6) (i k : Fin 16) :
    (hk21_1_25 j i k).Contains (fullFactor true 21 25 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk21_1_25,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel21_0 j i k) (mpower1_25 j i k) (quadraturePoint j.val (16*i.val+k.val)) 21 25 (kernel21_0_contains j i k) (mpower1_25_contains j i k)
noncomputable def ha21_1_25 : Fin 7 → CBox := ![⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-56),56⟩,⟨(-56),56⟩⟩,⟨⟨(-3),3⟩,⟨(-3),3⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨51087084,51087085⟩,⟨208388930,208388932⟩⟩,⟨⟨(-69021507574559),(-69021507574558)⟩,⟨(-47159864600332),(-47159864600331)⟩⟩,⟨⟨(-62361586098251161),(-62361586098251159)⟩,⟨(-103596641788216740),(-103596641788216738)⟩⟩]
lemma ha21_1_25_eq (j : Fin 7) : ha21_1_25 j = ((ha21_1_24 j).mul (piI.mul (atomPoints j).z)).scale 1 25 := by fin_cases j <;> decide +kernel
lemma ha21_1_25_contains (j : Fin 7) : (ha21_1_25 j).Contains (fullFactor true 21 25 ((j.val:ℝ)/6)) := by
  rw [ha21_1_25_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha21_1_24 j) true 21 24 j (ha21_1_24_contains j)
noncomputable def hk21_1_26 (j : Fin 6) (i k : Fin 16) : CBox := (kernel21_0 j i k).mul (mpower1_26 j i k)
lemma hk21_1_26_contains (j : Fin 6) (i k : Fin 16) :
    (hk21_1_26 j i k).Contains (fullFactor true 21 26 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk21_1_26,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel21_0 j i k) (mpower1_26 j i k) (quadraturePoint j.val (16*i.val+k.val)) 21 26 (kernel21_0_contains j i k) (mpower1_26_contains j i k)
noncomputable def ha21_1_26 : Fin 7 → CBox := ![⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-25),25⟩,⟨(-25),25⟩⟩,⟨⟨(-2),2⟩,⟨(-2),2⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨34051517,34051519⟩,⟨(-21223281),(-21223280)⟩⟩,⟨⟨(-5540377406866),(-5540377406864)⟩,⟨12122623909537,12122623909538⟩⟩,⟨⟨(-13937704877953426),(-13937704877953425)⟩,⟨9409307696240134,9409307696240135⟩⟩]
lemma ha21_1_26_eq (j : Fin 7) : ha21_1_26 j = ((ha21_1_25 j).mul (piI.mul (atomPoints j).z)).scale 1 26 := by fin_cases j <;> decide +kernel
lemma ha21_1_26_contains (j : Fin 7) : (ha21_1_26 j).Contains (fullFactor true 21 26 ((j.val:ℝ)/6)) := by
  rw [ha21_1_26_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha21_1_25 j) true 21 25 j (ha21_1_25_contains j)
noncomputable def hk21_1_27 (j : Fin 6) (i k : Fin 16) : CBox := (kernel21_0 j i k).mul (mpower1_27 j i k)
lemma hk21_1_27_contains (j : Fin 6) (i k : Fin 16) :
    (hk21_1_27 j i k).Contains (fullFactor true 21 27 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk21_1_27,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel21_0 j i k) (mpower1_27 j i k) (quadraturePoint j.val (16*i.val+k.val)) 21 27 (kernel21_0_contains j i k) (mpower1_27_contains j i k)
noncomputable def ha21_1_27 : Fin 7 → CBox := ![⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-11),11⟩,⟨(-11),11⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-5542649),(-5542648)⟩,⟨(-4635438),(-4635437)⟩⟩,⟨⟨1978763820307,1978763820309⟩,⟨522076177421,522076177422⟩⟩,⟨⟨1355347581055892,1355347581055894⟩,⟨1798614739545324,1798614739545325⟩⟩]
lemma ha21_1_27_eq (j : Fin 7) : ha21_1_27 j = ((ha21_1_26 j).mul (piI.mul (atomPoints j).z)).scale 1 27 := by fin_cases j <;> decide +kernel
lemma ha21_1_27_contains (j : Fin 7) : (ha21_1_27 j).Contains (fullFactor true 21 27 ((j.val:ℝ)/6)) := by
  rw [ha21_1_27_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha21_1_26 j) true 21 26 j (ha21_1_26_contains j)
noncomputable def hk21_1_28 (j : Fin 6) (i k : Fin 16) : CBox := (kernel21_0 j i k).mul (mpower1_28 j i k)
lemma hk21_1_28_contains (j : Fin 6) (i k : Fin 16) :
    (hk21_1_28 j i k).Contains (fullFactor true 21 28 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk21_1_28,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel21_0 j i k) (mpower1_28 j i k) (quadraturePoint j.val (16*i.val+k.val)) 21 28 (kernel21_0_contains j i k) (mpower1_28_contains j i k)
noncomputable def ha21_1_28 : Fin 7 → CBox := ![⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-5),5⟩,⟨(-5),5⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-464879),(-464877)⟩,⟨1165404,1165405⟩⟩,⟨⟨26399371916,26399371917⟩,⟨(-301840602774),(-301840602773)⟩⟩,⟨⟨222869517742249,222869517742250⟩,⟨(-186854547456092),(-186854547456090)⟩⟩]
lemma ha21_1_28_eq (j : Fin 7) : ha21_1_28 j = ((ha21_1_27 j).mul (piI.mul (atomPoints j).z)).scale 1 28 := by fin_cases j <;> decide +kernel
lemma ha21_1_28_contains (j : Fin 7) : (ha21_1_28 j).Contains (fullFactor true 21 28 ((j.val:ℝ)/6)) := by
  rw [ha21_1_28_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha21_1_27 j) true 21 27 j (ha21_1_27_contains j)
noncomputable def hk21_1_29 (j : Fin 6) (i k : Fin 16) : CBox := (kernel21_0 j i k).mul (mpower1_29 j i k)
lemma hk21_1_29_contains (j : Fin 6) (i k : Fin 16) :
    (hk21_1_29 j i k).Contains (fullFactor true 21 29 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk21_1_29,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel21_0 j i k) (mpower1_29 j i k) (quadraturePoint j.val (16*i.val+k.val)) 21 29 (kernel21_0_contains j i k) (mpower1_29_contains j i k)
noncomputable def ha21_1_29 : Fin 7 → CBox := ![⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-2),2⟩,⟨(-2),2⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨209952,209953⟩,⟨13162,13164⟩⟩,⟨⟨(-43162118255),(-43162118254)⟩,⟨3611676117,3611676118⟩⟩,⟨⟨(-24709848039620),(-24709848039619)⟩,⟨(-26541425058348),(-26541425058347)⟩⟩]
lemma ha21_1_29_eq (j : Fin 7) : ha21_1_29 j = ((ha21_1_28 j).mul (piI.mul (atomPoints j).z)).scale 1 29 := by fin_cases j <;> decide +kernel
lemma ha21_1_29_contains (j : Fin 7) : (ha21_1_29 j).Contains (fullFactor true 21 29 ((j.val:ℝ)/6)) := by
  rw [ha21_1_29_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha21_1_28 j) true 21 28 j (ha21_1_28_contains j)
noncomputable def hk21_1_30 (j : Fin 6) (i k : Fin 16) : CBox := (kernel21_0 j i k).mul (mpower1_30 j i k)
lemma hk21_1_30_contains (j : Fin 6) (i k : Fin 16) :
    (hk21_1_30 j i k).Contains (fullFactor true 21 30 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk21_1_30,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel21_0 j i k) (mpower1_30 j i k) (quadraturePoint j.val (16*i.val+k.val)) 21 30 (kernel21_0_contains j i k) (mpower1_30_contains j i k)
noncomputable def ha21_1_30 : Fin 7 → CBox := ![⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-1),1⟩,⟨(-1),1⟩⟩,⟨⟨(-8579),(-8577)⟩,⟨(-32998),(-32997)⟩⟩,⟨⟨1505135447,1505135448⟩,⟨5792876967,5792876968⟩⟩,⟨⟨(-3040064198136),(-3040064198135)⟩,⟨3140389236149,3140389236150⟩⟩]
lemma ha21_1_30_eq (j : Fin 7) : ha21_1_30 j = ((ha21_1_29 j).mul (piI.mul (atomPoints j).z)).scale 1 30 := by fin_cases j <;> decide +kernel
lemma ha21_1_30_contains (j : Fin 7) : (ha21_1_30 j).Contains (fullFactor true 21 30 ((j.val:ℝ)/6)) := by
  rw [ha21_1_30_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha21_1_29 j) true 21 29 j (ha21_1_29_contains j)
end SharpPlanar.CachedData

end OAI
