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
noncomputable def hk0_0_0 (j : Fin 6) (i k : Fin 16) : CBox := (power0 j i k).conj.mul (mpower0_0 j i k)
lemma hk0_0_0_contains (j : Fin 6) (i k : Fin 16) :
    (hk0_0_0 j i k).Contains (fullFactor false 0 0 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk0_0_0,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power0 j i k) (mpower0_0 j i k) (quadraturePoint j.val (16*i.val+k.val)) 0 0 (power0_contains j i k) (mpower0_0_contains j i k)
noncomputable def ha0_0_0 : Fin 7 → CBox := ![⟨⟨1000000000000000000000000000000,1000000000000000000000000000000⟩,⟨0,0⟩⟩,⟨⟨1000000000000000000000000000000,1000000000000000000000000000000⟩,⟨0,0⟩⟩,⟨⟨1000000000000000000000000000000,1000000000000000000000000000000⟩,⟨0,0⟩⟩,⟨⟨1000000000000000000000000000000,1000000000000000000000000000000⟩,⟨0,0⟩⟩,⟨⟨1000000000000000000000000000000,1000000000000000000000000000000⟩,⟨0,0⟩⟩,⟨⟨1000000000000000000000000000000,1000000000000000000000000000000⟩,⟨0,0⟩⟩,⟨⟨1000000000000000000000000000000,1000000000000000000000000000000⟩,⟨0,0⟩⟩]
lemma ha0_0_0_eq (j : Fin 7) : ha0_0_0 j = ((atomPoints j).direct.powBin 7 0).conj := by fin_cases j <;> decide +kernel
lemma ha0_0_0_contains (j : Fin 7) : (ha0_0_0 j).Contains (fullFactor false 0 0 ((j.val:ℝ)/6)) := by
  rw [ha0_0_0_eq]
  simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @direct_factor_zero_full ((atomPoints j).direct.powBin 7 0) ((j.val:ℝ)/6) 0 (@direct_power_bin_contains (atomPoints j) ((j.val:ℝ)/6) (atomPoints_contains j) 0 (by norm_num))
noncomputable def hk0_0_1 (j : Fin 6) (i k : Fin 16) : CBox := (power0 j i k).conj.mul (mpower0_1 j i k)
lemma hk0_0_1_contains (j : Fin 6) (i k : Fin 16) :
    (hk0_0_1 j i k).Contains (fullFactor false 0 1 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk0_0_1,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power0 j i k) (mpower0_1 j i k) (quadraturePoint j.val (16*i.val+k.val)) 0 1 (power0_contains j i k) (mpower0_1_contains j i k)
noncomputable def ha0_0_1 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨0,0⟩,⟨523598775598298873076666666664,523598775598298873078333333335⟩⟩,⟨⟨0,0⟩,⟨1047197551196597746153333333332,1047197551196597746156666666669⟩⟩,⟨⟨0,0⟩,⟨1570796326794896619230000000000,1570796326794896619235000000000⟩⟩,⟨⟨0,0⟩,⟨2094395102393195492306666666664,2094395102393195492313333333335⟩⟩,⟨⟨0,0⟩,⟨2617993877991494365383333333332,2617993877991494365391666666669⟩⟩,⟨⟨0,0⟩,⟨3141592653589793238460000000000,3141592653589793238470000000000⟩⟩]
lemma ha0_0_1_eq (j : Fin 7) : ha0_0_1 j = ((ha0_0_0 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 1 := by fin_cases j <;> decide +kernel
lemma ha0_0_1_contains (j : Fin 7) : (ha0_0_1 j).Contains (fullFactor false 0 1 ((j.val:ℝ)/6)) := by
  rw [ha0_0_1_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha0_0_0 j) false 0 0 j (ha0_0_0_contains j)
noncomputable def hk0_0_2 (j : Fin 6) (i k : Fin 16) : CBox := (power0 j i k).conj.mul (mpower0_2 j i k)
lemma hk0_0_2_contains (j : Fin 6) (i k : Fin 16) :
    (hk0_0_2 j i k).Contains (fullFactor false 0 2 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk0_0_2,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power0 j i k) (mpower0_2 j i k) (quadraturePoint j.val (16*i.val+k.val)) 0 2 (power0_contains j i k) (mpower0_2_contains j i k)
noncomputable def ha0_0_2 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-137077838904018869706676583140),(-137077838904018869705803918511)⟩,⟨0,0⟩⟩,⟨⟨(-548311355616075478826706332557),(-548311355616075478823215674048)⟩,⟨0,0⟩⟩,⟨⟨(-1233700550136169827360089248246),(-1233700550136169827352235266611)⟩,⟨0,0⟩⟩,⟨⟨(-2193245422464301915306825330218),(-2193245422464301915292862696192)⟩,⟨0,0⟩⟩,⟨⟨(-3426945972600471742666914578467),(-3426945972600471742645097962806)⟩,⟨0,0⟩⟩,⟨⟨(-4934802200544679309440356992983),(-4934802200544679309408941066446)⟩,⟨0,0⟩⟩]
lemma ha0_0_2_eq (j : Fin 7) : ha0_0_2 j = ((ha0_0_1 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 2 := by fin_cases j <;> decide +kernel
lemma ha0_0_2_contains (j : Fin 7) : (ha0_0_2 j).Contains (fullFactor false 0 2 ((j.val:ℝ)/6)) := by
  rw [ha0_0_2_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha0_0_1 j) false 0 1 j (ha0_0_1_contains j)
noncomputable def hk0_0_3 (j : Fin 6) (i k : Fin 16) : CBox := (power0 j i k).conj.mul (mpower0_3 j i k)
lemma hk0_0_3_contains (j : Fin 6) (i k : Fin 16) :
    (hk0_0_3 j i k).Contains (fullFactor false 0 3 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk0_0_3,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power0 j i k) (mpower0_3 j i k) (quadraturePoint j.val (16*i.val+k.val)) 0 3 (power0_contains j i k) (mpower0_3_contains j i k)
noncomputable def ha0_0_3 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨0,0⟩,⟨(-23924596203935046431862759073),(-23924596203935046431634296006)⟩⟩,⟨⟨0,0⟩,⟨(-191396769631480371454902072579),(-191396769631480371453074368056)⟩⟩,⟨⟨0,0⟩,⟨(-645964097506246253660294494946),(-645964097506246253654125992194)⟩⟩,⟨⟨0,0⟩,⟨(-1531174157051842971639216580616),(-1531174157051842971624594944455)⟩⟩,⟨⟨0,0⟩,⟨(-2990574525491880803982844884016),(-2990574525491880803954287000897)⟩⟩,⟨⟨0,0⟩,⟨(-5167712780049970029282355959565),(-5167712780049970029233007937558)⟩⟩]
lemma ha0_0_3_eq (j : Fin 7) : ha0_0_3 j = ((ha0_0_2 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 3 := by fin_cases j <;> decide +kernel
lemma ha0_0_3_contains (j : Fin 7) : (ha0_0_3 j).Contains (fullFactor false 0 3 ((j.val:ℝ)/6)) := by
  rw [ha0_0_3_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha0_0_2 j) false 0 2 j (ha0_0_2_contains j)
noncomputable def hk0_0_4 (j : Fin 6) (i k : Fin 16) : CBox := (power0 j i k).conj.mul (mpower0_4 j i k)
lemma hk0_0_4_contains (j : Fin 6) (i k : Fin 16) :
    (hk0_0_4 j i k).Contains (fullFactor false 0 4 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk0_0_4,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power0 j i k) (mpower0_4 j i k) (quadraturePoint j.val (16*i.val+k.val)) 0 4 (power0_contains j i k) (mpower0_4_contains j i k)
noncomputable def ha0_0_4 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨3131722319766024859700118531,3131722319766024859739992859⟩,⟨0,0⟩⟩,⟨⟨50107557116256397755201896499,50107557116256397755839885733⟩,⟨0,0⟩⟩,⟨⟨253669507901048013635709601029,253669507901048013638939421518⟩,⟨0,0⟩⟩,⟨⟨801720913860102364083230343990,801720913860102364093438171712⟩,⟨0,0⟩⟩,⟨⟨1957326449853765537312574082013,1957326449853765537337495536405⟩,⟨0,0⟩⟩,⟨⟨4058712126416768218171353616472,4058712126416768218223030744275⟩,⟨0,0⟩⟩]
lemma ha0_0_4_eq (j : Fin 7) : ha0_0_4 j = ((ha0_0_3 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 4 := by fin_cases j <;> decide +kernel
lemma ha0_0_4_contains (j : Fin 7) : (ha0_0_4 j).Contains (fullFactor false 0 4 ((j.val:ℝ)/6)) := by
  rw [ha0_0_4_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha0_0_3 j) false 0 3 j (ha0_0_3_contains j)
noncomputable def hk0_0_5 (j : Fin 6) (i k : Fin 16) : CBox := (power0 j i k).conj.mul (mpower0_5 j i k)
lemma hk0_0_5_contains (j : Fin 6) (i k : Fin 16) :
    (hk0_0_5 j i k).Contains (fullFactor false 0 5 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk0_0_5,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power0 j i k) (mpower0_5 j i k) (quadraturePoint j.val (16*i.val+k.val)) 0 5 (power0_contains j i k) (mpower0_5_contains j i k)
noncomputable def ha0_0_5 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨0,0⟩,⟨327953194428670967572717187,327953194428670967577936726⟩⟩,⟨⟨0,0⟩,⟨10494502221717470962326950007,10494502221717470962493975199⟩⟩,⟨⟨0,0⟩,⟨79692626246167045120170276622,79692626246167045121438624163⟩⟩,⟨⟨0,0⟩,⟨335824071094959070794462400250,335824071094959070799807206348⟩⟩,⟨⟨0,0⟩,⟨1024853732589596773664741211707,1024853732589596773681052265465⟩⟩,⟨⟨0,0⟩,⟨2550164039877345443845448851923,2550164039877345443886035973189⟩⟩]
lemma ha0_0_5_eq (j : Fin 7) : ha0_0_5 j = ((ha0_0_4 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 5 := by fin_cases j <;> decide +kernel
lemma ha0_0_5_contains (j : Fin 7) : (ha0_0_5 j).Contains (fullFactor false 0 5 ((j.val:ℝ)/6)) := by
  rw [ha0_0_5_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha0_0_4 j) false 0 4 j (ha0_0_4_contains j)
noncomputable def hk0_0_6 (j : Fin 6) (i k : Fin 16) : CBox := (power0 j i k).conj.mul (mpower0_6 j i k)
lemma hk0_0_6_contains (j : Fin 6) (i k : Fin 16) :
    (hk0_0_6 j i k).Contains (fullFactor false 0 6 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk0_0_6,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power0 j i k) (mpower0_6 j i k) (quadraturePoint j.val (16*i.val+k.val)) 0 6 (power0_contains j i k) (mpower0_6_contains j i k)
noncomputable def ha0_0_6 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-28619315176067161691830963),(-28619315176067161691284373)⟩,⟨0,0⟩⟩,⟨⟨(-1831636171268298348277181568),(-1831636171268298348242199892)⟩,⟨0,0⟩⟩,⟨⟨(-20863480763352960873344771286),(-20863480763352960872946308154)⟩,⟨0,0⟩⟩,⟨⟨(-117224714961171094289739620283),(-117224714961171094287500793139)⟩,⟨0,0⟩⟩,⟨⟨(-447176799626049401434858780983),(-447176799626049401426318333206)⟩,⟨0,0⟩⟩,⟨⟨(-1335262768854589495894065362267),(-1335262768854589495868563721867)⟩,⟨0,0⟩⟩]
lemma ha0_0_6_eq (j : Fin 7) : ha0_0_6 j = ((ha0_0_5 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 6 := by fin_cases j <;> decide +kernel
lemma ha0_0_6_contains (j : Fin 7) : (ha0_0_6 j).Contains (fullFactor false 0 6 ((j.val:ℝ)/6)) := by
  rw [ha0_0_6_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha0_0_5 j) false 0 5 j (ha0_0_5_contains j)
noncomputable def hk0_0_7 (j : Fin 6) (i k : Fin 16) : CBox := (power0 j i k).conj.mul (mpower0_7 j i k)
lemma hk0_0_7_contains (j : Fin 6) (i k : Fin 16) :
    (hk0_0_7 j i k).Contains (fullFactor false 0 7 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk0_0_7,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power0 j i k) (mpower0_7 j i k) (quadraturePoint j.val (16*i.val+k.val)) 0 7 (power0_contains j i k) (mpower0_7_contains j i k)
noncomputable def ha0_0_7 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨0,0⟩,⟨(-2140719769235797028240607),(-2140719769235797028192907)⟩⟩,⟨⟨0,0⟩,⟨(-274012130462182019614797623),(-274012130462182019608692168)⟩⟩,⟨⟨0,0⟩,⟨(-4681754135318688100762206250),(-4681754135318688100657888845)⟩⟩,⟨⟨0,0⟩,⟨(-35073552699159298510694095655),(-35073552699159298509912597553)⟩⟩,⟨⟨0,0⟩,⟨(-167243731971546642831297376890),(-167243731971546642827570903557)⟩⟩,⟨⟨0,0⟩,⟨(-599264529320792076897562399958),(-599264529320792076884209772268)⟩⟩]
lemma ha0_0_7_eq (j : Fin 7) : ha0_0_7 j = ((ha0_0_6 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 7 := by fin_cases j <;> decide +kernel
lemma ha0_0_7_contains (j : Fin 7) : (ha0_0_7 j).Contains (fullFactor false 0 7 ((j.val:ℝ)/6)) := by
  rw [ha0_0_7_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha0_0_6 j) false 0 6 j (ha0_0_6_contains j)
noncomputable def hk0_0_8 (j : Fin 6) (i k : Fin 16) : CBox := (power0 j i k).conj.mul (mpower0_8 j i k)
lemma hk0_0_8_contains (j : Fin 6) (i k : Fin 16) :
    (hk0_0_8 j i k).Contains (fullFactor false 0 8 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk0_0_8,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power0 j i k) (mpower0_8 j i k) (quadraturePoint j.val (16*i.val+k.val)) 0 8 (power0_contains j i k) (mpower0_8_contains j i k)
noncomputable def ha0_0_8 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨140109781258867029452145,140109781258867029455714⟩,⟨0,0⟩⟩,⟨⟨35868104002269959539749316,35868104002269959540662691⟩,⟨0,0⟩⟩,⟨⟨919260274839426580235528386,919260274839426580258937158⟩,⟨0,0⟩⟩,⟨⟨9182234624581109642175825077,9182234624581109642409648763⟩,⟨0,0⟩⟩,⟨⟨54730383304244933379744440781,54730383304244933381138138549⟩,⟨0,0⟩⟩,⟨⟨235330630358893204540295266938,235330630358893204546287912233⟩,⟨0,0⟩⟩]
lemma ha0_0_8_eq (j : Fin 7) : ha0_0_8 j = ((ha0_0_7 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 8 := by fin_cases j <;> decide +kernel
lemma ha0_0_8_contains (j : Fin 7) : (ha0_0_8 j).Contains (fullFactor false 0 8 ((j.val:ℝ)/6)) := by
  rw [ha0_0_8_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha0_0_7 j) false 0 7 j (ha0_0_7_contains j)
noncomputable def hk0_0_9 (j : Fin 6) (i k : Fin 16) : CBox := (power0 j i k).conj.mul (mpower0_9 j i k)
lemma hk0_0_9_contains (j : Fin 6) (i k : Fin 16) :
    (hk0_0_9 j i k).Contains (fullFactor false 0 9 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk0_0_9,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power0 j i k) (mpower0_9 j i k) (quadraturePoint j.val (16*i.val+k.val)) 0 9 (power0_contains j i k) (mpower0_9_contains j i k)
noncomputable def ha0_0_9 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨0,0⟩,⟨8151256657387584304803,8151256657387584305037⟩⟩,⟨⟨0,0⟩,⟨4173443408582443164059355,4173443408582443164178917⟩⟩,⟨⟨0,0⟩,⟨160441184787359821871445891,160441184787359821876042194⟩⟩,⟨⟨0,0⟩,⟨2136803025194210899998390072,2136803025194210900059604970⟩⟩,⟨⟨0,0⟩,⟨15920423158960125595319197120,15920423158960125595775283649⟩⟩,⟨⟨0,0⟩,⟨82145886611128228798180296470,82145886611128228800533602775⟩⟩]
lemma ha0_0_9_eq (j : Fin 7) : ha0_0_9 j = ((ha0_0_8 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 9 := by fin_cases j <;> decide +kernel
lemma ha0_0_9_contains (j : Fin 7) : (ha0_0_9 j).Contains (fullFactor false 0 9 ((j.val:ℝ)/6)) := by
  rw [ha0_0_9_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha0_0_8 j) false 0 8 j (ha0_0_8_contains j)
noncomputable def hk0_0_10 (j : Fin 6) (i k : Fin 16) : CBox := (power0 j i k).conj.mul (mpower0_10 j i k)
lemma hk0_0_10_contains (j : Fin 6) (i k : Fin 16) :
    (hk0_0_10 j i k).Contains (fullFactor false 0 10 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk0_0_10,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power0 j i k) (mpower0_10 j i k) (quadraturePoint j.val (16*i.val+k.val)) 0 10 (power0_contains j i k) (mpower0_10_contains j i k)
noncomputable def ha0_0_10 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-426798800539562151462),(-426798800539562151447)⟩,⟨0,0⟩⟩,⟨⟨(-437041971752511643096456),(-437041971752511643082544)⟩,⟨0,0⟩⟩,⟨⟨(-25202042373060605481643175),(-25202042373060605480840967)⟩,⟨0,0⟩⟩,⟨⟨(-447530979074571922530770593),(-447530979074571922516525238)⟩,⟨0,0⟩⟩,⟨⟨(-4167957036519161635365063252),(-4167957036519161635232393058)⟩,⟨0,0⟩⟩,⟨⟨(-25806891390014060013202610057),(-25806891390014060012381151189)⟩,⟨0,0⟩⟩]
lemma ha0_0_10_eq (j : Fin 7) : ha0_0_10 j = ((ha0_0_9 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 10 := by fin_cases j <;> decide +kernel
lemma ha0_0_10_contains (j : Fin 7) : (ha0_0_10 j).Contains (fullFactor false 0 10 ((j.val:ℝ)/6)) := by
  rw [ha0_0_10_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha0_0_9 j) false 0 9 j (ha0_0_9_contains j)
noncomputable def hk0_0_11 (j : Fin 6) (i k : Fin 16) : CBox := (power0 j i k).conj.mul (mpower0_11 j i k)
lemma hk0_0_11_contains (j : Fin 6) (i k : Fin 16) :
    (hk0_0_11 j i k).Contains (fullFactor false 0 11 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk0_0_11,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power0 j i k) (mpower0_11 j i k) (quadraturePoint j.val (16*i.val+k.val)) 0 11 (power0_contains j i k) (mpower0_11_contains j i k)
noncomputable def ha0_0_11 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨0,0⟩,⟨(-20315575399030665722),(-20315575399030665720)⟩⟩,⟨⟨0,0⟩,⟨(-41606298417214803397455),(-41606298417214803395998)⟩⟩,⟨⟨0,0⟩,⟨(-3598843235212085340551242),(-3598843235212085340425230)⟩⟩,⟨⟨0,0⟩,⟨(-85209699158455917357987615),(-85209699158455917355004074)⟩⟩,⟨⟨0,0⟩,⟨(-991971455030794224678394552),(-991971455030794224643661576)⟩⟩,⟨⟨0,0⟩,⟨(-7370430945714350777448941367),(-7370430945714350777190872451)⟩⟩]
lemma ha0_0_11_eq (j : Fin 7) : ha0_0_11 j = ((ha0_0_10 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 11 := by fin_cases j <;> decide +kernel
lemma ha0_0_11_contains (j : Fin 7) : (ha0_0_11 j).Contains (fullFactor false 0 11 ((j.val:ℝ)/6)) := by
  rw [ha0_0_11_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha0_0_10 j) false 0 10 j (ha0_0_10_contains j)
noncomputable def hk0_0_12 (j : Fin 6) (i k : Fin 16) : CBox := (power0 j i k).conj.mul (mpower0_12 j i k)
lemma hk0_0_12_contains (j : Fin 6) (i k : Fin 16) :
    (hk0_0_12 j i k).Contains (fullFactor false 0 12 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk0_0_12,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power0 j i k) (mpower0_12 j i k) (quadraturePoint j.val (16*i.val+k.val)) 0 12 (power0_contains j i k) (mpower0_12_contains j i k)
noncomputable def ha0_0_12 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨886434200375614885,886434200375614886⟩,⟨0,0⟩⟩,⟨⟨3630834484738518570986,3630834484738518571126⟩,⟨0,0⟩⟩,⟨⟨471087477881817150362271,471087477881817150380266⟩,⟨0,0⟩⟩,⟨⟨14871898049488972066762446,14871898049488972067330512⟩,⟨0,0⟩⟩,⟨⟨216414599701077852904017301,216414599701077852912283730⟩,⟨0,0⟩⟩,⟨⟨1929574309403923047883862689,1929574309403923047957567000⟩,⟨0,0⟩⟩]
lemma ha0_0_12_eq (j : Fin 7) : ha0_0_12 j = ((ha0_0_11 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 12 := by fin_cases j <;> decide +kernel
lemma ha0_0_12_contains (j : Fin 7) : (ha0_0_12 j).Contains (fullFactor false 0 12 ((j.val:ℝ)/6)) := by
  rw [ha0_0_12_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha0_0_11 j) false 0 11 j (ha0_0_11_contains j)
noncomputable def hk0_0_13 (j : Fin 6) (i k : Fin 16) : CBox := (power0 j i k).conj.mul (mpower0_13 j i k)
lemma hk0_0_13_contains (j : Fin 6) (i k : Fin 16) :
    (hk0_0_13 j i k).Contains (fullFactor false 0 13 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk0_0_13,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power0 j i k) (mpower0_13 j i k) (quadraturePoint j.val (16*i.val+k.val)) 0 13 (power0_contains j i k) (mpower0_13_contains j i k)
noncomputable def ha0_0_13 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨0,0⟩,⟨35702758612702236,35702758612702237⟩⟩,⟨⟨0,0⟩,⟨292476998555256723019,292476998555256723033⟩⟩,⟨⟨0,0⟩,⟨56921729219679268117129,56921729219679268119486⟩⟩,⟨⟨0,0⟩,⟨2395971572164663074980419,2395971572164663075079566⟩⟩,⟨⟨0,0⟩,⟨43582469009646285030256328,43582469009646285032059784⟩⟩,⟨⟨0,0⟩,⟨466302805767612564415528309,466302805767612564434824054⟩⟩]
lemma ha0_0_13_eq (j : Fin 7) : ha0_0_13 j = ((ha0_0_12 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 13 := by fin_cases j <;> decide +kernel
lemma ha0_0_13_contains (j : Fin 7) : (ha0_0_13 j).Contains (fullFactor false 0 13 ((j.val:ℝ)/6)) := by
  rw [ha0_0_13_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha0_0_12 j) false 0 12 j (ha0_0_12_contains j)
noncomputable def hk0_0_14 (j : Fin 6) (i k : Fin 16) : CBox := (power0 j i k).conj.mul (mpower0_14 j i k)
lemma hk0_0_14_contains (j : Fin 6) (i k : Fin 16) :
    (hk0_0_14 j i k).Contains (fullFactor false 0 14 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk0_0_14,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power0 j i k) (mpower0_14 j i k) (quadraturePoint j.val (16*i.val+k.val)) 0 14 (power0_contains j i k) (mpower0_14_contains j i k)
noncomputable def ha0_0_14 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1335280049649466),(-1335280049649465)⟩,⟨0,0⟩⟩,⟨⟨(-21877228333456835519),(-21877228333456835517)⟩,⟨0,0⟩⟩,⟨⟨(-6386603083791852241300),(-6386603083791852241014)⟩,⟨0,0⟩⟩,⟨⟨(-358436509015356793129496),(-358436509015356793113522)⟩,⟨0,0⟩⟩,⟨⟨(-8149902646786285757332178),(-8149902646786285756968990)⟩,⟨0,0⟩⟩,⟨⟨(-104638104924845707121447140),(-104638104924845707116784111)⟩,⟨0,0⟩⟩]
lemma ha0_0_14_eq (j : Fin 7) : ha0_0_14 j = ((ha0_0_13 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 14 := by fin_cases j <;> decide +kernel
lemma ha0_0_14_contains (j : Fin 7) : (ha0_0_14 j).Contains (fullFactor false 0 14 ((j.val:ℝ)/6)) := by
  rw [ha0_0_14_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha0_0_13 j) false 0 13 j (ha0_0_13_contains j)
noncomputable def hk0_0_15 (j : Fin 6) (i k : Fin 16) : CBox := (power0 j i k).conj.mul (mpower0_15 j i k)
lemma hk0_0_15_contains (j : Fin 6) (i k : Fin 16) :
    (hk0_0_15 j i k).Contains (fullFactor false 0 15 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk0_0_15,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power0 j i k) (mpower0_15 j i k) (quadraturePoint j.val (16*i.val+k.val)) 0 15 (power0_contains j i k) (mpower0_15_contains j i k)
noncomputable def ha0_0_15 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨0,0⟩,⟨(-46610066605154),(-46610066605153)⟩⟩,⟨⟨0,0⟩,⟨(-1527318662517654887),(-1527318662517654886)⟩⟩,⟨⟨0,0⟩,⟨(-668803510981146723272),(-668803510981146723239)⟩⟩,⟨⟨0,0⟩,⟨(-50047177933378515329214),(-50047177933378515326824)⟩⟩,⟨⟨0,0⟩,⟨(-1422426349034211492869813),(-1422426349034211492801896)⟩⟩,⟨⟨0,0⟩,⟨(-21915353447830215828154435),(-21915353447830215827108053)⟩⟩]
lemma ha0_0_15_eq (j : Fin 7) : ha0_0_15 j = ((ha0_0_14 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 15 := by fin_cases j <;> decide +kernel
lemma ha0_0_15_contains (j : Fin 7) : (ha0_0_15 j).Contains (fullFactor false 0 15 ((j.val:ℝ)/6)) := by
  rw [ha0_0_15_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha0_0_14 j) false 0 14 j (ha0_0_14_contains j)
noncomputable def hk0_0_16 (j : Fin 6) (i k : Fin 16) : CBox := (power0 j i k).conj.mul (mpower0_16 j i k)
lemma hk0_0_16_contains (j : Fin 6) (i k : Fin 16) :
    (hk0_0_16 j i k).Contains (fullFactor false 0 16 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk0_0_16,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power0 j i k) (mpower0_16 j i k) (quadraturePoint j.val (16*i.val+k.val)) 0 16 (power0_contains j i k) (mpower0_16_contains j i k)
noncomputable def ha0_0_16 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨1525310862813,1525310862814⟩,⟨0,0⟩⟩,⟨⟨99962772705334443,99962772705334444⟩,⟨0,0⟩⟩,⟨⟨65659631149794723621,65659631149794723625⟩,⟨0,0⟩⟩,⟨⟨6551160272016798098662,6551160272016798098997⟩,⟨0,0⟩⟩,⟨⟨232743967104084891369912,232743967104084891381767⟩,⟨0,0⟩⟩,⟨⟨4303069587032947007239892,4303069587032947007459047⟩,⟨0,0⟩⟩]
lemma ha0_0_16_eq (j : Fin 7) : ha0_0_16 j = ((ha0_0_15 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 16 := by fin_cases j <;> decide +kernel
lemma ha0_0_16_contains (j : Fin 7) : (ha0_0_16 j).Contains (fullFactor false 0 16 ((j.val:ℝ)/6)) := by
  rw [ha0_0_16_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha0_0_15 j) false 0 15 j (ha0_0_15_contains j)
noncomputable def hk0_0_17 (j : Fin 6) (i k : Fin 16) : CBox := (power0 j i k).conj.mul (mpower0_17 j i k)
lemma hk0_0_17_contains (j : Fin 6) (i k : Fin 16) :
    (hk0_0_17 j i k).Contains (fullFactor false 0 17 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk0_0_17,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power0 j i k) (mpower0_17 j i k) (quadraturePoint j.val (16*i.val+k.val)) 0 17 (power0_contains j i k) (mpower0_17_contains j i k)
noncomputable def ha0_0_17 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨0,0⟩,⟨46979464716,46979464717⟩⟩,⟨⟨0,0⟩,⟨6157692399285195,6157692399285196⟩⟩,⟨⟨0,0⟩,⟨6066935731106195666,6066935731106195668⟩⟩,⟨⟨0,0⟩,⟨807101058159109193405,807101058159109193450⟩⟩,⟨⟨0,0⟩,⟨35842487118702823485606,35842487118702823487546⟩⟩,⟨⟨0,0⟩,⟨795205400147551278466945,795205400147551278509977⟩⟩]
lemma ha0_0_17_eq (j : Fin 7) : ha0_0_17 j = ((ha0_0_16 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 17 := by fin_cases j <;> decide +kernel
lemma ha0_0_17_contains (j : Fin 7) : (ha0_0_17 j).Contains (fullFactor false 0 17 ((j.val:ℝ)/6)) := by
  rw [ha0_0_17_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha0_0_16 j) false 0 16 j (ha0_0_16_contains j)
noncomputable def hk0_0_18 (j : Fin 6) (i k : Fin 16) : CBox := (power0 j i k).conj.mul (mpower0_18 j i k)
lemma hk0_0_18_contains (j : Fin 6) (i k : Fin 16) :
    (hk0_0_18 j i k).Contains (fullFactor false 0 18 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk0_0_18,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power0 j i k) (mpower0_18 j i k) (quadraturePoint j.val (16*i.val+k.val)) 0 18 (power0_contains j i k) (mpower0_18_contains j i k)
noncomputable def ha0_0_18 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1366577234),(-1366577233)⟩,⟨0,0⟩⟩,⟨⟨(-358240022308520),(-358240022308519)⟩,⟨0,0⟩⟩,⟨⟨(-529440020073462377),(-529440020073462376)⟩,⟨0,0⟩⟩,⟨⟨(-93910472408044662742),(-93910472408044662736)⟩,⟨0,0⟩⟩,⟨⟨(-5213078436041832671824),(-5213078436041832671524)⟩,⟨0,0⟩⟩,⟨⟨(-138789524622137721150531),(-138789524622137721142578)⟩,⟨0,0⟩⟩]
lemma ha0_0_18_eq (j : Fin 7) : ha0_0_18 j = ((ha0_0_17 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 18 := by fin_cases j <;> decide +kernel
lemma ha0_0_18_contains (j : Fin 7) : (ha0_0_18 j).Contains (fullFactor false 0 18 ((j.val:ℝ)/6)) := by
  rw [ha0_0_18_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha0_0_17 j) false 0 17 j (ha0_0_17_contains j)
noncomputable def hk0_0_19 (j : Fin 6) (i k : Fin 16) : CBox := (power0 j i k).conj.mul (mpower0_19 j i k)
lemma hk0_0_19_contains (j : Fin 6) (i k : Fin 16) :
    (hk0_0_19 j i k).Contains (fullFactor false 0 19 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk0_0_19,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power0 j i k) (mpower0_19 j i k) (quadraturePoint j.val (16*i.val+k.val)) 0 19 (power0_contains j i k) (mpower0_19_contains j i k)
noncomputable def ha0_0_19 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨0,0⟩,⟨(-37659904),(-37659903)⟩⟩,⟨⟨0,0⟩,⟨(-19744635479058),(-19744635479057)⟩⟩,⟨⟨0,0⟩,⟨(-43770654673137423),(-43770654673137422)⟩⟩,⟨⟨0,0⟩,⟨(-10351875446044213762),(-10351875446044213761)⟩⟩,⟨⟨0,0⟩,⟨(-718305654265631155073),(-718305654265631155028)⟩⟩,⟨⟨0,0⟩,⟨(-22948428997269873111225),(-22948428997269873109836)⟩⟩]
lemma ha0_0_19_eq (j : Fin 7) : ha0_0_19 j = ((ha0_0_18 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 19 := by fin_cases j <;> decide +kernel
lemma ha0_0_19_contains (j : Fin 7) : (ha0_0_19 j).Contains (fullFactor false 0 19 ((j.val:ℝ)/6)) := by
  rw [ha0_0_19_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha0_0_18 j) false 0 18 j (ha0_0_18_contains j)
noncomputable def hk0_0_20 (j : Fin 6) (i k : Fin 16) : CBox := (power0 j i k).conj.mul (mpower0_20 j i k)
lemma hk0_0_20_contains (j : Fin 6) (i k : Fin 16) :
    (hk0_0_20 j i k).Contains (fullFactor false 0 20 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk0_0_20,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power0 j i k) (mpower0_20 j i k) (quadraturePoint j.val (16*i.val+k.val)) 0 20 (power0_contains j i k) (mpower0_20_contains j i k)
noncomputable def ha0_0_20 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨985933,985934⟩,⟨0,0⟩⟩,⟨⟨1033826696146,1033826696147⟩,⟨0,0⟩⟩,⟨⟨3437739179098606,3437739179098608⟩,⟨0,0⟩⟩,⟨⟨1084045861738968866,1084045861738968868⟩,⟨0,0⟩⟩,⟨⟨94025990269704865211,94025990269704865218⟩,⟨0,0⟩⟩,⟨⟨3604730797462500933798,3604730797462500934029⟩,⟨0,0⟩⟩]
lemma ha0_0_20_eq (j : Fin 7) : ha0_0_20 j = ((ha0_0_19 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 20 := by fin_cases j <;> decide +kernel
lemma ha0_0_20_contains (j : Fin 7) : (ha0_0_20 j).Contains (fullFactor false 0 20 ((j.val:ℝ)/6)) := by
  rw [ha0_0_20_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha0_0_19 j) false 0 19 j (ha0_0_19_contains j)
noncomputable def hk0_0_21 (j : Fin 6) (i k : Fin 16) : CBox := (power0 j i k).conj.mul (mpower0_21 j i k)
lemma hk0_0_21_contains (j : Fin 6) (i k : Fin 16) :
    (hk0_0_21 j i k).Contains (fullFactor false 0 21 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk0_0_21,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power0 j i k) (mpower0_21 j i k) (quadraturePoint j.val (16*i.val+k.val)) 0 21 (power0_contains j i k) (mpower0_21_contains j i k)
noncomputable def ha0_0_21 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨0,0⟩,⟨24582,24583⟩⟩,⟨⟨0,0⟩,⟨51553370693,51553370694⟩⟩,⟨⟨0,0⟩,⟨257142289286047,257142289286048⟩⟩,⟨⟨0,0⟩,⟨108115254456938454,108115254456938455⟩⟩,⟨⟨0,0⟩,⟨11721879376103578822,11721879376103578824⟩⟩,⟨⟨0,0⟩,⟨539266466260812848925,539266466260812848962⟩⟩]
lemma ha0_0_21_eq (j : Fin 7) : ha0_0_21 j = ((ha0_0_20 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 21 := by fin_cases j <;> decide +kernel
lemma ha0_0_21_contains (j : Fin 7) : (ha0_0_21 j).Contains (fullFactor false 0 21 ((j.val:ℝ)/6)) := by
  rw [ha0_0_21_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha0_0_20 j) false 0 20 j (ha0_0_20_contains j)
noncomputable def hk0_0_22 (j : Fin 6) (i k : Fin 16) : CBox := (power0 j i k).conj.mul (mpower0_22 j i k)
lemma hk0_0_22_contains (j : Fin 6) (i k : Fin 16) :
    (hk0_0_22 j i k).Contains (fullFactor false 0 22 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk0_0_22,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power0 j i k) (mpower0_22 j i k) (quadraturePoint j.val (16*i.val+k.val)) 0 22 (power0_contains j i k) (mpower0_22_contains j i k)
noncomputable def ha0_0_22 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-586),(-585)⟩,⟨0,0⟩⟩,⟨⟨(-2453934707),(-2453934706)⟩,⟨0,0⟩⟩,⟨⟨(-18359916521553),(-18359916521552)⟩,⟨0,0⟩⟩,⟨⟨(-10292548155845728),(-10292548155845727)⟩,⟨0,0⟩⟩,⟨⟨(-1394900383872451220),(-1394900383872451219)⟩,⟨0,0⟩⟩,⟨⟨(-77007071306013533802),(-77007071306013533796)⟩,⟨0,0⟩⟩]
lemma ha0_0_22_eq (j : Fin 7) : ha0_0_22 j = ((ha0_0_21 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 22 := by fin_cases j <;> decide +kernel
lemma ha0_0_22_contains (j : Fin 7) : (ha0_0_22 j).Contains (fullFactor false 0 22 ((j.val:ℝ)/6)) := by
  rw [ha0_0_22_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha0_0_21 j) false 0 21 j (ha0_0_21_contains j)
noncomputable def hk0_0_23 (j : Fin 6) (i k : Fin 16) : CBox := (power0 j i k).conj.mul (mpower0_23 j i k)
lemma hk0_0_23_contains (j : Fin 6) (i k : Fin 16) :
    (hk0_0_23 j i k).Contains (fullFactor false 0 23 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk0_0_23,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power0 j i k) (mpower0_23 j i k) (quadraturePoint j.val (16*i.val+k.val)) 0 23 (power0_contains j i k) (mpower0_23_contains j i k)
noncomputable def ha0_0_23 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨0,0⟩,⟨(-14),(-13)⟩⟩,⟨⟨0,0⟩,⟨(-111728453),(-111728452)⟩⟩,⟨⟨0,0⟩,⟨(-1253899540536),(-1253899540535)⟩⟩,⟨⟨0,0⟩,⟨(-937246193423888),(-937246193423887)⟩⟩,⟨⟨0,0⟩,⟨(-158775681103741858),(-158775681103741857)⟩⟩,⟨⟨0,0⟩,⟨(-10518471716932064456),(-10518471716932064454)⟩⟩]
lemma ha0_0_23_eq (j : Fin 7) : ha0_0_23 j = ((ha0_0_22 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 23 := by fin_cases j <;> decide +kernel
lemma ha0_0_23_contains (j : Fin 7) : (ha0_0_23 j).Contains (fullFactor false 0 23 ((j.val:ℝ)/6)) := by
  rw [ha0_0_23_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha0_0_22 j) false 0 22 j (ha0_0_22_contains j)
noncomputable def hk0_0_24 (j : Fin 6) (i k : Fin 16) : CBox := (power0 j i k).conj.mul (mpower0_24 j i k)
lemma hk0_0_24_contains (j : Fin 6) (i k : Fin 16) :
    (hk0_0_24 j i k).Contains (fullFactor false 0 24 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk0_0_24,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power0 j i k) (mpower0_24 j i k) (quadraturePoint j.val (16*i.val+k.val)) 0 24 (power0_contains j i k) (mpower0_24_contains j i k)
noncomputable def ha0_0_24 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨0,1⟩,⟨0,0⟩⟩,⟨⟨4875073,4875074⟩,⟨0,0⟩⟩,⟨⟨82067533018,82067533019⟩,⟨0,0⟩⟩,⟨⟨81790159885152,81790159885153⟩,⟨0,0⟩⟩,⟨⟨17319740045980249,17319740045980250⟩,⟨0,0⟩⟩,⟨⟨1376864728037741370,1376864728037741371⟩,⟨0,0⟩⟩]
lemma ha0_0_24_eq (j : Fin 7) : ha0_0_24 j = ((ha0_0_23 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 24 := by fin_cases j <;> decide +kernel
lemma ha0_0_24_contains (j : Fin 7) : (ha0_0_24 j).Contains (fullFactor false 0 24 ((j.val:ℝ)/6)) := by
  rw [ha0_0_24_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha0_0_23 j) false 0 23 j (ha0_0_23_contains j)
noncomputable def hk0_0_25 (j : Fin 6) (i k : Fin 16) : CBox := (power0 j i k).conj.mul (mpower0_25 j i k)
lemma hk0_0_25_contains (j : Fin 6) (i k : Fin 16) :
    (hk0_0_25 j i k).Contains (fullFactor false 0 25 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk0_0_25,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power0 j i k) (mpower0_25 j i k) (quadraturePoint j.val (16*i.val+k.val)) 0 25 (power0_contains j i k) (mpower0_25_contains j i k)
noncomputable def ha0_0_25 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨0,0⟩,⟨0,1⟩⟩,⟨⟨0,0⟩,⟨204206,204207⟩⟩,⟨⟨0,0⟩,⟨5156455176,5156455177⟩⟩,⟨⟨0,0⟩,⟨6852036411496,6852036411497⟩⟩,⟨⟨0,0⟩,⟨1813718936351216,1813718936351217⟩⟩,⟨⟨0,0⟩,⟨173021924583611076,173021924583611077⟩⟩]
lemma ha0_0_25_eq (j : Fin 7) : ha0_0_25 j = ((ha0_0_24 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 25 := by fin_cases j <;> decide +kernel
lemma ha0_0_25_contains (j : Fin 7) : (ha0_0_25 j).Contains (fullFactor false 0 25 ((j.val:ℝ)/6)) := by
  rw [ha0_0_25_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha0_0_24 j) false 0 24 j (ha0_0_24_contains j)
noncomputable def hk0_0_26 (j : Fin 6) (i k : Fin 16) : CBox := (power0 j i k).conj.mul (mpower0_26 j i k)
lemma hk0_0_26_contains (j : Fin 6) (i k : Fin 16) :
    (hk0_0_26 j i k).Contains (fullFactor false 0 26 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk0_0_26,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power0 j i k) (mpower0_26 j i k) (quadraturePoint j.val (16*i.val+k.val)) 0 26 (power0_contains j i k) (mpower0_26_contains j i k)
noncomputable def ha0_0_26 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),0⟩,⟨0,0⟩⟩,⟨⟨(-8225),(-8224)⟩,⟨0,0⟩⟩,⟨⟨(-311528495),(-311528494)⟩,⟨0,0⟩⟩,⟨⟨(-551956596218),(-551956596217)⟩,⟨0,0⟩⟩,⟨⟨(-182627118144798),(-182627118144797)⟩,⟨0,0⟩⟩,⟨⟨(-20906323353147685),(-20906323353147684)⟩,⟨0,0⟩⟩]
lemma ha0_0_26_eq (j : Fin 7) : ha0_0_26 j = ((ha0_0_25 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 26 := by fin_cases j <;> decide +kernel
lemma ha0_0_26_contains (j : Fin 7) : (ha0_0_26 j).Contains (fullFactor false 0 26 ((j.val:ℝ)/6)) := by
  rw [ha0_0_26_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha0_0_25 j) false 0 25 j (ha0_0_25_contains j)
noncomputable def hk0_0_27 (j : Fin 6) (i k : Fin 16) : CBox := (power0 j i k).conj.mul (mpower0_27 j i k)
lemma hk0_0_27_contains (j : Fin 6) (i k : Fin 16) :
    (hk0_0_27 j i k).Contains (fullFactor false 0 27 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk0_0_27,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power0 j i k) (mpower0_27 j i k) (quadraturePoint j.val (16*i.val+k.val)) 0 27 (power0_contains j i k) (mpower0_27_contains j i k)
noncomputable def ha0_0_27 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨0,0⟩,⟨(-1),0⟩⟩,⟨⟨0,0⟩,⟨(-320),(-318)⟩⟩,⟨⟨0,0⟩,⟨(-18123994),(-18123993)⟩⟩,⟨⟨0,0⟩,⟨(-42815377477),(-42815377475)⟩⟩,⟨⟨0,0⟩,⟨(-17708025083642),(-17708025083641)⟩⟩,⟨⟨0,0⟩,⟨(-2432561179993389),(-2432561179993388)⟩⟩]
lemma ha0_0_27_eq (j : Fin 7) : ha0_0_27 j = ((ha0_0_26 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 27 := by fin_cases j <;> decide +kernel
lemma ha0_0_27_contains (j : Fin 7) : (ha0_0_27 j).Contains (fullFactor false 0 27 ((j.val:ℝ)/6)) := by
  rw [ha0_0_27_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha0_0_26 j) false 0 26 j (ha0_0_26_contains j)
noncomputable def hk0_0_28 (j : Fin 6) (i k : Fin 16) : CBox := (power0 j i k).conj.mul (mpower0_28 j i k)
lemma hk0_0_28_contains (j : Fin 6) (i k : Fin 16) :
    (hk0_0_28 j i k).Contains (fullFactor false 0 28 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk0_0_28,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power0 j i k) (mpower0_28 j i k) (quadraturePoint j.val (16*i.val+k.val)) 0 28 (power0_contains j i k) (mpower0_28_contains j i k)
noncomputable def ha0_0_28 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨0,1⟩,⟨0,0⟩⟩,⟨⟨11,12⟩,⟨0,0⟩⟩,⟨⟨1016753,1016754⟩,⟨0,0⟩⟩,⟨⟨3202582746,3202582747⟩,⟨0,0⟩⟩,⟨⟨1655696473581,1655696473582⟩,⟨0,0⟩⟩,⟨⟨272932726159819,272932726159820⟩,⟨0,0⟩⟩]
lemma ha0_0_28_eq (j : Fin 7) : ha0_0_28 j = ((ha0_0_27 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 28 := by fin_cases j <;> decide +kernel
lemma ha0_0_28_contains (j : Fin 7) : (ha0_0_28 j).Contains (fullFactor false 0 28 ((j.val:ℝ)/6)) := by
  rw [ha0_0_28_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha0_0_27 j) false 0 27 j (ha0_0_27_contains j)
noncomputable def hk0_0_29 (j : Fin 6) (i k : Fin 16) : CBox := (power0 j i k).conj.mul (mpower0_29 j i k)
lemma hk0_0_29_contains (j : Fin 6) (i k : Fin 16) :
    (hk0_0_29 j i k).Contains (fullFactor false 0 29 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk0_0_29,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power0 j i k) (mpower0_29 j i k) (quadraturePoint j.val (16*i.val+k.val)) 0 29 (power0_contains j i k) (mpower0_29_contains j i k)
noncomputable def ha0_0_29 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨0,0⟩,⟨0,1⟩⟩,⟨⟨0,0⟩,⟨0,1⟩⟩,⟨⟨0,0⟩,⟨55072,55073⟩⟩,⟨⟨0,0⟩,⟨231292193,231292194⟩⟩,⟨⟨0,0⟩,⟨149469076953,149469076954⟩⟩,⟨⟨0,0⟩,⟨29567015428549,29567015428550⟩⟩]
lemma ha0_0_29_eq (j : Fin 7) : ha0_0_29 j = ((ha0_0_28 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 29 := by fin_cases j <;> decide +kernel
lemma ha0_0_29_contains (j : Fin 7) : (ha0_0_29 j).Contains (fullFactor false 0 29 ((j.val:ℝ)/6)) := by
  rw [ha0_0_29_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha0_0_28 j) false 0 28 j (ha0_0_28_contains j)
noncomputable def hk0_0_30 (j : Fin 6) (i k : Fin 16) : CBox := (power0 j i k).conj.mul (mpower0_30 j i k)
lemma hk0_0_30_contains (j : Fin 6) (i k : Fin 16) :
    (hk0_0_30 j i k).Contains (fullFactor false 0 30 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk0_0_30,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_direct_full (power0 j i k) (mpower0_30 j i k) (quadraturePoint j.val (16*i.val+k.val)) 0 30 (power0_contains j i k) (mpower0_30_contains j i k)
noncomputable def ha0_0_30 : Fin 7 → CBox := ![⟨⟨0,0⟩,⟨0,0⟩⟩,⟨⟨(-1),0⟩,⟨0,0⟩⟩,⟨⟨(-1),0⟩,⟨0,0⟩⟩,⟨⟨(-2884),(-2883)⟩,⟨0,0⟩⟩,⟨⟨(-16147242),(-16147241)⟩,⟨0,0⟩⟩,⟨⟨(-13043637614),(-13043637613)⟩,⟨0,0⟩⟩,⟨⟨(-3096250615297),(-3096250615296)⟩,⟨0,0⟩⟩]
lemma ha0_0_30_eq (j : Fin 7) : ha0_0_30 j = ((ha0_0_29 j).mul (piI.mul (rcast (atomPoints j).t))).scale 1 30 := by fin_cases j <;> decide +kernel
lemma ha0_0_30_contains (j : Fin 7) : (ha0_0_30 j).Contains (fullFactor false 0 30 ((j.val:ℝ)/6)) := by
  rw [ha0_0_30_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha0_0_29 j) false 0 29 j (ha0_0_29_contains j)
noncomputable def hk0_1_0 (j : Fin 6) (i k : Fin 16) : CBox := (kernel0_0 j i k).mul (mpower1_0 j i k)
lemma hk0_1_0_contains (j : Fin 6) (i k : Fin 16) :
    (hk0_1_0 j i k).Contains (fullFactor true 0 0 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk0_1_0,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel0_0 j i k) (mpower1_0 j i k) (quadraturePoint j.val (16*i.val+k.val)) 0 0 (kernel0_0_contains j i k) (mpower1_0_contains j i k)
noncomputable def ha0_1_0 : Fin 7 → CBox := ![⟨⟨2886751345948128822491487805010,2886751345948128822591487805032⟩,⟨0,0⟩⟩,⟨⟨2459717123174736984844818011358,2459717123174736984930025111996⟩,⟨1024882134656140410352007504727,1024882134656140410387510463337⟩⟩,⟨⟨1703656532034961272290058376722,1703656532034961272349074770188⟩,⟨1419713776695801060241715313933,1419713776695801060290895641830⟩⟩,⟨⟨1126537110613903930728385484882,1126537110613903930767409875134⟩,⟨1408171388267379913410481856103,1408171388267379913459262343918⟩⟩,⟨⟨764140062162739982424217360149,764140062162739982450687948391⟩,⟨1273566770271233304040362266913,1273566770271233304084479913987⟩⟩,⟨⟨540562020567660013574478860754,540562020567660013593204478445⟩,⟨1126170876182625028280164293239,1126170876182625028319175996763⟩⟩,⟨⟨398172599441121216895377628277,398172599441121216909170731728⟩,⟨995431498602803042238444070694,995431498602803042272926829319⟩⟩]
lemma ha0_1_0_eq (j : Fin 7) : ha0_1_0 j = atomKernel0_0 j := by fin_cases j <;> decide +kernel
lemma ha0_1_0_contains (j : Fin 7) : (ha0_1_0 j).Contains (fullFactor true 0 0 ((j.val:ℝ)/6)) := by
  rw [ha0_1_0_eq]
  simpa only [fullFactor,ite_true] using atomKernel0_0_contains j
noncomputable def hk0_1_1 (j : Fin 6) (i k : Fin 16) : CBox := (kernel0_0 j i k).mul (mpower1_1 j i k)
lemma hk0_1_1_contains (j : Fin 6) (i k : Fin 16) :
    (hk0_1_1 j i k).Contains (fullFactor true 0 1 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk0_1_1,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel0_0 j i k) (mpower1_1 j i k) (quadraturePoint j.val (16*i.val+k.val)) 0 1 (kernel0_0_contains j i k) (mpower1_1_contains j i k)
noncomputable def ha0_1_1 : Fin 7 → CBox := ![⟨⟨(-26602390675435195142530321043993),(-26602390675435195141524109159245)⟩,⟨0,0⟩⟩,⟨⟨(-15046386883137311960977771542034),(-15046386883137311960120407568771)⟩,⟨(-17001868484744399809876351294364),(-17001868484744399809233270664782)⟩⟩,⟨⟨(-1076288362329791189253868592463),(-1076288362329791188660038627375)⟩,⟨(-15764114872167322034205686079730),(-15764114872167322033609422385277)⟩⟩,⟨⟨4005248804305423355782453862022,4005248804305423356175121914620⟩,⟨(-9739775289205357801899857956194),(-9739775289205357801531459575359)⟩⟩,⟨⟨4725920142797114330304028335327,4725920142797114330570378540195⟩,⟨(-5460226459805430899811586813878),(-5460226459805430899605058580158)⟩⟩,⟨⟨4220020865203592699679309874866,4220020865203592699867729265570⟩,⟨(-3001523701832900019824858424479),(-3001523701832900019711328446699)⟩⟩,⟨⟨3519762856635247957323462123219,3519762856635247957462249969389⟩,⟨(-1624727135620028673173671104732),(-1624727135620028673112217238669)⟩⟩]
lemma ha0_1_1_eq (j : Fin 7) : ha0_1_1 j = ((ha0_1_0 j).mul (piI.mul (atomPoints j).z)).scale 1 1 := by fin_cases j <;> decide +kernel
lemma ha0_1_1_contains (j : Fin 7) : (ha0_1_1 j).Contains (fullFactor true 0 1 ((j.val:ℝ)/6)) := by
  rw [ha0_1_1_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha0_1_0 j) true 0 0 j (ha0_1_0_contains j)
noncomputable def hk0_1_2 (j : Fin 6) (i k : Fin 16) : CBox := (kernel0_0 j i k).mul (mpower1_2 j i k)
lemma hk0_1_2_contains (j : Fin 6) (i k : Fin 16) :
    (hk0_1_2 j i k).Contains (fullFactor true 0 2 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk0_1_2,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel0_0 j i k) (mpower1_2 j i k) (quadraturePoint j.val (16*i.val+k.val)) 0 2 (kernel0_0_contains j i k) (mpower1_2_contains j i k)
noncomputable def ha0_1_2 : Fin 7 → CBox := ![⟨⟨122575016833680145946165485035154,122575016833680145951191944967226⟩,⟨0,0⟩⟩,⟨⟨26069235626031647609706478198461,26069235626031647614472481490359⟩,⟨93140302574601179954538338970151,93140302574601179958893595750607⟩⟩,⟨⟨(-37944215806102898524592466427378),(-37944215806102898521457519868065)⟩,⟨41579190390315638283331423405430,41579190390315638286460796966097⟩⟩,⟨⟨(-30544155331490608593580758448756),(-30544155331490608591986969360482)⟩,⟨3551753641853769198810116530290,3551753641853769200410758846473⟩⟩,⟨⟨(-16193820427748643248264124005335),(-16193820427748643247533690618239)⟩,⟨(-6779755291778911362119083938956),(-6779755291778911361299416263861)⟩⟩,⟨⟨(-7617147420123301957985362582104),(-7617147420123301957662862301530)⟩,⟨(-7563023130467542967409370602406),(-7563023130467542966953713355555)⟩⟩,⟨⟨(-3263924834630237228947001158148),(-3263924834630237228812625677755)⟩,⟨(-6202437430717943902551971093760),(-6202437430717943902274904058483)⟩⟩]
lemma ha0_1_2_eq (j : Fin 7) : ha0_1_2 j = ((ha0_1_1 j).mul (piI.mul (atomPoints j).z)).scale 1 2 := by fin_cases j <;> decide +kernel
lemma ha0_1_2_contains (j : Fin 7) : (ha0_1_2 j).Contains (fullFactor true 0 2 ((j.val:ℝ)/6)) := by
  rw [ha0_1_2_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha0_1_1 j) true 0 1 j (ha0_1_1_contains j)
noncomputable def hk0_1_3 (j : Fin 6) (i k : Fin 16) : CBox := (kernel0_0 j i k).mul (mpower1_3 j i k)
lemma hk0_1_3_contains (j : Fin 6) (i k : Fin 16) :
    (hk0_1_3 j i k).Contains (fullFactor true 0 3 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk0_1_3,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel0_0 j i k) (mpower1_3 j i k) (quadraturePoint j.val (16*i.val+k.val)) 0 3 (kernel0_0_contains j i k) (mpower1_3_contains j i k)
noncomputable def ha0_1_3 : Fin 7 → CBox := ![⟨⟨(-376523421900594012592614772005042),(-376523421900594012575976084235160)⟩,⟨0,0⟩⟩,⟨⟨48809987803041999942073976988457,48809987803041999960229949915667⟩,⟨(-270318915570165811505208398992392),(-270318915570165811487312034815282)⟩⟩,⟨⟨133653069306944076432706769753192,133653069306944076443649467444468⟩,⟨(-3099516268066432372302167307032),(-3099516268066432361359922639148)⟩⟩,⟨⟨34860977790970562072704284207216,34860977790970562077044227997550⟩,⟨48658900604437533985790410931007,48658900604437533990190400092070⟩⟩,⟨⟨(-2260995287684620558357027388427),(-2260995287684620556666515253049)⟩,⟨28363007126667795566074427517862,28363007126667795567703604127357⟩⟩,⟨⟨(-8510797712665954827391102609601),(-8510797712665954826656416343930)⟩,⟨12148325821975021555980353941061,12148325821975021556565166867529⟩⟩,⟨⟨(-7261428317245967727087566777747),(-7261428317245967726721242894602)⟩,⟨4316923348433606886716098826636,4316923348433606886908926408839⟩⟩]
lemma ha0_1_3_eq (j : Fin 7) : ha0_1_3 j = ((ha0_1_2 j).mul (piI.mul (atomPoints j).z)).scale 1 3 := by fin_cases j <;> decide +kernel
lemma ha0_1_3_contains (j : Fin 7) : (ha0_1_3 j).Contains (fullFactor true 0 3 ((j.val:ℝ)/6)) := by
  rw [ha0_1_3_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha0_1_2 j) true 0 2 j (ha0_1_2_contains j)
noncomputable def hk0_1_4 (j : Fin 6) (i k : Fin 16) : CBox := (kernel0_0 j i k).mul (mpower1_4 j i k)
lemma hk0_1_4_contains (j : Fin 6) (i k : Fin 16) :
    (hk0_1_4 j i k).Contains (fullFactor true 0 4 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk0_1_4,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel0_0 j i k) (mpower1_4 j i k) (quadraturePoint j.val (16*i.val+k.val)) 0 4 (kernel0_0_contains j i k) (mpower1_4_contains j i k)
noncomputable def ha0_1_4 : Fin 7 → CBox := ![⟨⟨867447691841424037375730087701830,867447691841424037416824044255820⟩,⟨0,0⟩⟩,⟨⟨(-344799191015893237782636282188664),(-344799191015893237730107738612249)⟩,⟨472714532087218802170662546348818,472714532087218802223630815843831⟩⟩,⟨⟨(-168502477119929481021617292068649),(-168502477119929480993523159811359)⟩,⟨(-168268249794520808740366920378689),(-168268249794520808712249220012564)⟩⟩,⟨⟨37476798071125241954044574792413,37476798071125241963010474926808⟩,⟨(-78945935801875602754545117424259),(-78945935801875602745638433276186)⟩⟩,⟨⟨33615750077841320707998364320310,33615750077841320710627493279873⟩,⟨(-8133573042759238926567384524429),(-8133573042759238923955136817870)⟩⟩,⟨⟨13905926263215755875669178915598,13905926263215755876440087146115⟩,⟨6553250277975291833751138323388,6553250277975291834638939861295⟩⟩,⟨⟨4238006341972060242893386947745,4238006341972060243098149762052⟩,⟨6352650888734558808361745896356,6352650888734558808723010367829⟩⟩]
lemma ha0_1_4_eq (j : Fin 7) : ha0_1_4 j = ((ha0_1_3 j).mul (piI.mul (atomPoints j).z)).scale 1 4 := by fin_cases j <;> decide +kernel
lemma ha0_1_4_contains (j : Fin 7) : (ha0_1_4 j).Contains (fullFactor true 0 4 ((j.val:ℝ)/6)) := by
  rw [ha0_1_4_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha0_1_3 j) true 0 3 j (ha0_1_3_contains j)
noncomputable def hk0_1_5 (j : Fin 6) (i k : Fin 16) : CBox := (kernel0_0 j i k).mul (mpower1_5 j i k)
lemma hk0_1_5_contains (j : Fin 6) (i k : Fin 16) :
    (hk0_1_5 j i k).Contains (fullFactor true 0 5 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk0_1_5,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel0_0 j i k) (mpower1_5 j i k) (quadraturePoint j.val (16*i.val+k.val)) 0 5 (kernel0_0_contains j i k) (mpower1_5_contains j i k)
noncomputable def ha0_1_5 : Fin 7 → CBox := ![⟨⟨(-1598764813689965140490052670095148),(-1598764813689965140409224700052429)⟩,⟨0,0⟩⟩,⟨⟨880159352830126332701690401746935,880159352830126332824416945644927⟩,⟨(-468404530205674225270505881647072),(-468404530205674225147110568541910)⟩⟩,⟨⟨(-7395496229973392529015512495709),(-7395496229973392471309023135855)⟩,⟨339257937224101252378477233823803,339257937224101252436182688835634⟩⟩,⟨⟨(-101867374863453155668837116279098),(-101867374863453155654338616627522)⟩,⟨6394801612272420045432204455373,6394801612272420059897539275786⟩⟩,⟨⟨(-17703372700914776771292337060819),(-17703372700914776768025460729844)⟩,⟨(-28595827953225404735516853939339),(-28595827953225404732189130816710)⟩⟩,⟨⟨3395590697593533936409390239866,3395590697593533937266646197770⟩,⟨(-12285062530841304032610489393765),(-12285062530841304031816450538056)⟩⟩,⟨⟨4428760621654995248566013589851,4428760621654995248849720880012⟩,⟨(-3299281963373695137025726534974),(-3299281963373695136853776655157)⟩⟩]
lemma ha0_1_5_eq (j : Fin 7) : ha0_1_5 j = ((ha0_1_4 j).mul (piI.mul (atomPoints j).z)).scale 1 5 := by fin_cases j <;> decide +kernel
lemma ha0_1_5_contains (j : Fin 7) : (ha0_1_5 j).Contains (fullFactor true 0 5 ((j.val:ℝ)/6)) := by
  rw [ha0_1_5_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha0_1_4 j) true 0 4 j (ha0_1_4_contains j)
noncomputable def hk0_1_6 (j : Fin 6) (i k : Fin 16) : CBox := (kernel0_0 j i k).mul (mpower1_6 j i k)
lemma hk0_1_6_contains (j : Fin 6) (i k : Fin 16) :
    (hk0_1_6 j i k).Contains (fullFactor true 0 6 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk0_1_6,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel0_0 j i k) (mpower1_6 j i k) (quadraturePoint j.val (16*i.val+k.val)) 0 6 (kernel0_0_contains j i k) (mpower1_6_contains j i k)
noncomputable def ha0_1_6 : Fin 7 → CBox := ![⟨⟨2455526476825277280058497997797438,2455526476825277280190457031367505⟩,⟨0,0⟩⟩,⟨⟨(-1414827786667715020236885853709034),(-1414827786667715019999112899090889)⟩,⟨53097741910714307998261014478895,53097741910714308235611567960456⟩⟩,⟨⟨297273661166520986271217600146506,297273661166520986369049246171276⟩,⟨(-272043977029042819660125305689424),(-272043977029042819562333516631313)⟩⟩,⟨⟨53491640388523389895742478263826,53491640388523389915066674847407⟩,⟨83711656664765128452749033612300,83711656664765128472201218431782⟩⟩,⟨⟨(-17547582680759076158733007766277),(-17547582680759076155261266659985)⟩,⟨20853710522524487871235595170437,20853710522524487874657911271924⟩⟩,⟨⟨(-8763274820287268917616073715360),(-8763274820287268916946903765043)⟩,⟨(-869926967404599801785881395354),(-869926967404599801097033494485)⟩⟩,⟨⟨(-2124232719080088710657698913707),(-2124232719080088710538572577149)⟩,⟨(-2562142113913751173883818053394),(-2562142113913751173698878170568)⟩⟩]
lemma ha0_1_6_eq (j : Fin 7) : ha0_1_6 j = ((ha0_1_5 j).mul (piI.mul (atomPoints j).z)).scale 1 6 := by fin_cases j <;> decide +kernel
lemma ha0_1_6_contains (j : Fin 7) : (ha0_1_6 j).Contains (fullFactor true 0 6 ((j.val:ℝ)/6)) := by
  rw [ha0_1_6_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha0_1_5 j) true 0 5 j (ha0_1_5_contains j)
noncomputable def hk0_1_7 (j : Fin 6) (i k : Fin 16) : CBox := (kernel0_0 j i k).mul (mpower1_7 j i k)
lemma hk0_1_7_contains (j : Fin 6) (i k : Fin 16) :
    (hk0_1_7 j i k).Contains (fullFactor true 0 7 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk0_1_7,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel0_0 j i k) (mpower1_7 j i k) (quadraturePoint j.val (16*i.val+k.val)) 0 7 (kernel0_0_contains j i k) (mpower1_7_contains j i k)
noncomputable def ha0_1_7 : Fin 7 → CBox := ![⟨⟨(-3232643936883226917773237766128494),(-3232643936883226917589226918611983)⟩,⟨0,0⟩⟩,⟨⟨1577686393455906750370832667679233,1577686393455906750762320095248118⟩,⟨693296249765990635183047897382840,693296249765990635571852170235058⟩⟩,⟨⟨(-409244016092063194237369751191339),(-409244016092063194095306929978559)⟩,⟨(-27369098399286924816328417972231),(-27369098399286924674261706714316)⟩⟩,⟨⟨39463138294956164152879978741715,39463138294956164175151047477900⟩,⟨(-72879037225148672050585150013334),(-72879037225148672028387045744207)⟩⟩,⟨⟨17562108575747576133385804677433,17562108575747576136451990707720⟩,⟨7066976789719042660862309744334,7066976789719042663945749226886⟩⟩,⟨⟨374015629019298092985038314230,374015629019298093458810593804⟩,⟨5201895121772923680135740341424,5201895121772923680612143686970⟩⟩,⟨⟨(-1264726797943523122759333808060),(-1264726797943523122656346515208)⟩,⟨1164537382691026244145604000566,1164537382691026244215724421801⟩⟩]
lemma ha0_1_7_eq (j : Fin 7) : ha0_1_7 j = ((ha0_1_6 j).mul (piI.mul (atomPoints j).z)).scale 1 7 := by fin_cases j <;> decide +kernel
lemma ha0_1_7_contains (j : Fin 7) : (ha0_1_7 j).Contains (fullFactor true 0 7 ((j.val:ℝ)/6)) := by
  rw [ha0_1_7_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha0_1_6 j) true 0 6 j (ha0_1_6_contains j)
noncomputable def hk0_1_8 (j : Fin 6) (i k : Fin 16) : CBox := (kernel0_0 j i k).mul (mpower1_8 j i k)
lemma hk0_1_8_contains (j : Fin 6) (i k : Fin 16) :
    (hk0_1_8 j i k).Contains (fullFactor true 0 8 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk0_1_8,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel0_0 j i k) (mpower1_8 j i k) (quadraturePoint j.val (16*i.val+k.val)) 0 8 (kernel0_0_contains j i k) (mpower1_8_contains j i k)
noncomputable def ha0_1_8 : Fin 7 → CBox := ![⟨⟨3723738496054108744502617800747911,3723738496054108744726436108322157⟩,⟨0,0⟩⟩,⟨⟨(-1189665878201300779265569897725647),(-1189665878201300778703887799236207)⟩,⟨(-1397573397413262972223644018642461),(-1397573397413262971664675562753822)⟩⟩,⟨⟨234247050052601412598126672380769,234247050052601412777874205370450⟩,⟨280302729584929402694968535766483,280302729584929402874750389912882⟩⟩,⟨⟨(-60495846405266676032920492846514),(-60495846405266676010675304184064)⟩,⟨582247156042652058946927933532,582247156042652081182604253999⟩⟩,⟨⟨754562725148757516078660223484,754562725148757518463717644991⟩,⟨(-11480717599090984490110365048947),(-11480717599090984487719038756962)⟩⟩,⟨⟨2623482555263848135963066703520,2623482555263848136256618244621⟩,⟨(-648960687993370566361520301568),(-648960687993370566075575433927)⟩⟩,⟨⟨555332100573006390123999604184,555332100573006390159835398204⟩,⟨543536538610673671409349353332,543536538610673671459385563057⟩⟩]
lemma ha0_1_8_eq (j : Fin 7) : ha0_1_8 j = ((ha0_1_7 j).mul (piI.mul (atomPoints j).z)).scale 1 8 := by fin_cases j <;> decide +kernel
lemma ha0_1_8_contains (j : Fin 7) : (ha0_1_8 j).Contains (fullFactor true 0 8 ((j.val:ℝ)/6)) := by
  rw [ha0_1_8_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha0_1_7 j) true 0 7 j (ha0_1_7_contains j)
noncomputable def hk0_1_9 (j : Fin 6) (i k : Fin 16) : CBox := (kernel0_0 j i k).mul (mpower1_9 j i k)
lemma hk0_1_9_contains (j : Fin 6) (i k : Fin 16) :
    (hk0_1_9 j i k).Contains (fullFactor true 0 9 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk0_1_9,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel0_0 j i k) (mpower1_9 j i k) (quadraturePoint j.val (16*i.val+k.val)) 0 9 (kernel0_0_contains j i k) (mpower1_9_contains j i k)
noncomputable def ha0_1_9 : Fin 7 → CBox := ![⟨⟨(-3812834504711823004642566730148701),(-3812834504711823004401256605894691)⟩,⟨0,0⟩⟩,⟨⟨436029779665833495772881401000412,436029779665833496487294850257288⟩,⟨1681903459729391382822678914731646,1681903459729391383536192200713899⟩⟩,⟨⟨32252854678313675367562289219527,32252854678313675569691760113375⟩,⟨(-287387894315032030551503961936558),(-287387894315032030349379046364275)⟩⟩,⟨⟨19352974754520385713994106431730,19352974754520385733671229254843⟩,⟨34153557189255984149916607009275,34153557189255984169644415085074⟩⟩,⟨⟨(-6020469196966551652856073759826),(-6020469196966551651207786255929)⟩,⟨1545700877786890007968862817710,1545700877786890009603210078403⟩⟩,⟨⟨(-499880945114411518661863942528),(-499880945114411518507503964940)⟩,⟨(-1140070734293967039014126575594),(-1140070734293967038854547936297)⟩⟩,⟨⟨206494224749534439906533662372,206494224749534439928088165983⟩,⟨(-234153372680575324232183833792),(-234153372680575324216016339096)⟩⟩]
lemma ha0_1_9_eq (j : Fin 7) : ha0_1_9 j = ((ha0_1_8 j).mul (piI.mul (atomPoints j).z)).scale 1 9 := by fin_cases j <;> decide +kernel
lemma ha0_1_9_contains (j : Fin 7) : (ha0_1_9 j).Contains (fullFactor true 0 9 ((j.val:ℝ)/6)) := by
  rw [ha0_1_9_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha0_1_8 j) true 0 8 j (ha0_1_8_contains j)
noncomputable def hk0_1_10 (j : Fin 6) (i k : Fin 16) : CBox := (kernel0_0 j i k).mul (mpower1_10 j i k)
lemma hk0_1_10_contains (j : Fin 6) (i k : Fin 16) :
    (hk0_1_10 j i k).Contains (fullFactor true 0 10 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk0_1_10,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel0_0 j i k) (mpower1_10 j i k) (quadraturePoint j.val (16*i.val+k.val)) 0 10 (kernel0_0_contains j i k) (mpower1_10_contains j i k)
noncomputable def ha0_1_10 : Fin 7 → CBox := ![⟨⟨3513656041677860039312087919852527,3513656041677860039545647681055097⟩,⟨0,0⟩⟩,⟨⟨291037907098962430397909081541977,291037907098962431213923603265140⟩,⟨(-1451495633503554669863955680538988),(-1451495633503554669046730756510256)⟩⟩,⟨⟨(-163888969548784857950487938113228),(-163888969548784857746349502920945)⟩,⟨124886018935341366281753946749526,124886018935341366485874081985008⟩⟩,⟨⟨11969728111190136703970359994674,11969728111190136719689447063027⟩,⟨(-19551456905560631709121460841397),(-19551456905560631693424654790254)⟩⟩,⟨⟨1626427822473326756622937381668,1626427822473326757632955442113⟩,⟨2547221484270369346671637672226,2547221484270369347690405790208⟩⟩,⟨⟨(-430545778683493740604544317727),(-430545778683493740526885464801)⟩,⟨284511920552457943817955609450,284511920552457943893161063465⟩⟩,⟨⟨(-88430803894209769824217860403),(-88430803894209769817693515834)⟩,⟨(-70168825825250057564513242611),(-70168825825250057556174927703)⟩⟩]
lemma ha0_1_10_eq (j : Fin 7) : ha0_1_10 j = ((ha0_1_9 j).mul (piI.mul (atomPoints j).z)).scale 1 10 := by fin_cases j <;> decide +kernel
lemma ha0_1_10_contains (j : Fin 7) : (ha0_1_10 j).Contains (fullFactor true 0 10 ((j.val:ℝ)/6)) := by
  rw [ha0_1_10_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha0_1_9 j) true 0 9 j (ha0_1_9_contains j)
noncomputable def hk0_1_11 (j : Fin 6) (i k : Fin 16) : CBox := (kernel0_0 j i k).mul (mpower1_11 j i k)
lemma hk0_1_11_contains (j : Fin 6) (i k : Fin 16) :
    (hk0_1_11 j i k).Contains (fullFactor true 0 11 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk0_1_11,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel0_0 j i k) (mpower1_11 j i k) (quadraturePoint j.val (16*i.val+k.val)) 0 11 (kernel0_0_contains j i k) (mpower1_11_contains j i k)
noncomputable def ha0_1_11 : Fin 7 → CBox := ![⟨⟨(-2943593602073748658317270020841335),(-2943593602073748658112233703404174)⟩,⟨0,0⟩⟩,⟨⟨(-693420238709213552484898630347855),(-693420238709213551637774723613048)⟩,⟨913223666937108357981116331189836,913223666937108358830000583560964⟩⟩,⟨⟨131826974295335034158520428042053,131826974295335034345879547684918⟩,⟨20833738762883269547119948036078,20833738762883269734482002239739⟩⟩,⟨⟨(-12158955634272761580312817697288),(-12158955634272761568940613416110)⟩,⟨(-528577485031563430692678701287),(-528577485031563419320858079525)⟩⟩,⟨⟨845774348781293067805293494378,845774348781293068376433435271⟩,⟨(-1034002499164252522386354581687),(-1034002499164252521818511488346)⟩⟩,⟨⟨133231907503014887088853008216,133231907503014887122180013519⟩,⟨141683980481636900798579216895,141683980481636900832803180399⟩⟩,⟨⟨(-21525137137162247539767274487),(-21525137137162247536840514146)⟩,⟨30227433749918256434521159936,30227433749918256436901494254⟩⟩]
lemma ha0_1_11_eq (j : Fin 7) : ha0_1_11 j = ((ha0_1_10 j).mul (piI.mul (atomPoints j).z)).scale 1 11 := by fin_cases j <;> decide +kernel
lemma ha0_1_11_contains (j : Fin 7) : (ha0_1_11 j).Contains (fullFactor true 0 11 ((j.val:ℝ)/6)) := by
  rw [ha0_1_11_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha0_1_10 j) true 0 10 j (ha0_1_10_contains j)
noncomputable def hk0_1_12 (j : Fin 6) (i k : Fin 16) : CBox := (kernel0_0 j i k).mul (mpower1_12 j i k)
lemma hk0_1_12_contains (j : Fin 6) (i k : Fin 16) :
    (hk0_1_12 j i k).Contains (fullFactor true 0 12 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk0_1_12,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel0_0 j i k) (mpower1_12 j i k) (quadraturePoint j.val (16*i.val+k.val)) 0 12 (kernel0_0_contains j i k) (mpower1_12_contains j i k)
noncomputable def ha0_1_12 : Fin 7 → CBox := ![⟨⟨2260517608660374788210741455408337,2260517608660374788375393494756009⟩,⟨0,0⟩⟩,⟨⟨725929797062619660886299315683820,725929797062619661692800036415733⟩,⟨(-368578516548605769133937409647717),(-368578516548605768326627272817175)⟩⟩,⟨⟨(-45146595706461678253920992181173),(-45146595706461678096435852197792)⟩,⟨(-65125399634853769161008156587736),(-65125399634853769003516400295651)⟩⟩,⟨⟨2642464218391766458829705419506,2642464218391766466362353147120⟩,⟨5300602212145842245642156949330,5300602212145842253181906174376⟩⟩,⟨⟨(-504894166280150813408545989587),(-504894166280150813116196398746)⟩,⟨(-195048832577319844211081272438),(-195048832577319843918033734610)⟩⟩,⟨⟨40415425052457423855240828300,40415425052457423869026539440⟩,⟨(-53673377086763792320959630315),(-53673377086763792307434216596)⟩⟩,⟨⟨9432824795583496248224109195,9432824795583496249016219543⟩,⟨6004327005721240540302824779,6004327005721240541242912572⟩⟩]
lemma ha0_1_12_eq (j : Fin 7) : ha0_1_12 j = ((ha0_1_11 j).mul (piI.mul (atomPoints j).z)).scale 1 12 := by fin_cases j <;> decide +kernel
lemma ha0_1_12_contains (j : Fin 7) : (ha0_1_12 j).Contains (fullFactor true 0 12 ((j.val:ℝ)/6)) := by
  rw [ha0_1_12_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha0_1_11 j) true 0 11 j (ha0_1_11_contains j)
noncomputable def hk0_1_13 (j : Fin 6) (i k : Fin 16) : CBox := (kernel0_0 j i k).mul (mpower1_13 j i k)
lemma hk0_1_13_contains (j : Fin 6) (i k : Fin 16) :
    (hk0_1_13 j i k).Contains (fullFactor true 0 13 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk0_1_13,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel0_0 j i k) (mpower1_13 j i k) (quadraturePoint j.val (16*i.val+k.val)) 0 13 (kernel0_0_contains j i k) (mpower1_13_contains j i k)
noncomputable def ha0_1_13 : Fin 7 → CBox := ![⟨⟨(-1602418064399093470617130550010718),(-1602418064399093470495312643419349)⟩,⟨0,0⟩⟩,⟨⟨(-533497559334657600837614023742851),(-533497559334657600129432255036803)⟩,⟨9746259713948121886040683957501,9746259713948122594122811527524⟩⟩,⟨⟨(-8701876549661017563231409202711),(-8701876549661017441057036459112)⟩,⟨42550744195529186512203391653623,42550744195529186634376540532567⟩⟩,⟨⟨1507601799605413776025979318763,1507601799605413780636936793690⟩,⟨(-2192237478530848890137392497778),(-2192237478530848885529162422585)⟩⟩,⟨⟨(-10463758815251599700487063721),(-10463758815251599561856753267)⟩,⟨202167238564182152362426506653,202167238564182152501125673406⟩⟩,⟨⟨(-19056647863277587462456332078),(-19056647863277587457398390969)⟩,⟨(-9792811232569650169494635807),(-9792811232569650164379973100)⟩⟩,⟨⟨1531580616334536026493248868,1531580616334536026771562098⟩,⟨(-2706894505762408199249089964),(-2706894505762408199006869456)⟩⟩]
lemma ha0_1_13_eq (j : Fin 7) : ha0_1_13 j = ((ha0_1_12 j).mul (piI.mul (atomPoints j).z)).scale 1 13 := by fin_cases j <;> decide +kernel
lemma ha0_1_13_contains (j : Fin 7) : (ha0_1_13 j).Contains (fullFactor true 0 13 ((j.val:ℝ)/6)) := by
  rw [ha0_1_13_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha0_1_12 j) true 0 12 j (ha0_1_12_contains j)
noncomputable def hk0_1_14 (j : Fin 6) (i k : Fin 16) : CBox := (kernel0_0 j i k).mul (mpower1_14 j i k)
lemma hk0_1_14_contains (j : Fin 6) (i k : Fin 16) :
    (hk0_1_14 j i k).Contains (fullFactor true 0 14 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk0_1_14,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel0_0 j i k) (mpower1_14 j i k) (quadraturePoint j.val (16*i.val+k.val)) 0 14 (kernel0_0_contains j i k) (mpower1_14_contains j i k)
noncomputable def ha0_1_14 : Fin 7 → CBox := ![⟨⟨1054773200191494299232533696702989,1054773200191494299316076375403188⟩,⟨0,0⟩⟩,⟨⟨294725003293158601362261600038693,294725003293158601939030816619834⟩,⟨136339483774161985183159225905218,136339483774161985759430160268314⟩⟩,⟨⟨18713348448116571849730229258249,18713348448116571937699890067826⟩,⟨(-11763180479196340294889336842017),(-11763180479196340206921400192518)⟩⟩,⟨⟨(-1104647055334257746385521000076),(-1104647055334257743768498722415)⟩,⟨(-106946322060047951014622350064),(-106946322060047948397510871254)⟩⟩,⟨⟨67847627323076763073701641602,67847627323076763134693535020⟩,⟨(-18429498396970023871799948847),(-18429498396970023810958645070)⟩⟩,⟨⟨(-1898917132492807640001036894),(-1898917132492807638241943177)⟩,⟨6053512450024425851188025455,6053512450024425852940542205⟩⟩,⟨⟨(-718732612381274659639000910),(-718732612381274659570504228)⟩,⟨(-358735344680059668305668996),(-358735344680059668229261769)⟩⟩]
lemma ha0_1_14_eq (j : Fin 7) : ha0_1_14 j = ((ha0_1_13 j).mul (piI.mul (atomPoints j).z)).scale 1 14 := by fin_cases j <;> decide +kernel
lemma ha0_1_14_contains (j : Fin 7) : (ha0_1_14 j).Contains (fullFactor true 0 14 ((j.val:ℝ)/6)) := by
  rw [ha0_1_14_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha0_1_13 j) true 0 13 j (ha0_1_13_contains j)
noncomputable def hk0_1_15 (j : Fin 6) (i k : Fin 16) : CBox := (kernel0_0 j i k).mul (mpower1_15 j i k)
lemma hk0_1_15_contains (j : Fin 6) (i k : Fin 16) :
    (hk0_1_15 j i k).Contains (fullFactor true 0 15 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk0_1_15,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel0_0 j i k) (mpower1_15 j i k) (quadraturePoint j.val (16*i.val+k.val)) 0 15 (kernel0_0_contains j i k) (mpower1_15_contains j i k)
noncomputable def ha0_1_15 : Fin 7 → CBox := ![⟨⟨(-648006135220887869147836989149545),(-648006135220887869094449384272053)⟩,⟨0,0⟩⟩,⟨⟨(-116835886063254293265433551418553),(-116835886063254292827237148307118)⟩,⟨(-142730428393819731502210013429252),(-142730428393819731064277476886506)⟩⟩,⟨⟨(-10181212217768484333834206413574),(-10181212217768484274723742794050)⟩,⟨(-2564002401413315214098284423864),(-2564002401413315154987460541529)⟩⟩,⟨⟨171988370211309723097335334448,171988370211309724483120023251⟩,⟨396366935480575956887731784727,396366935480575958273985282316⟩⟩,⟨⟨(-12530494907205456367569140875),(-12530494907205456342628546694)⟩,⟨(-19035203056867144488154358570),(-19035203056867144463150038195)⟩⟩,⟨⟨1737853822152525982586462476,1737853822152525983151893458⟩,⟨232941288564883328970520952,232941288564883329534453586⟩⟩,⟨⟨(-77362922489835425084008726),(-77362922489835425064453837)⟩,⟨177514874465192841713786851,177514874465192841731797935⟩⟩]
lemma ha0_1_15_eq (j : Fin 7) : ha0_1_15 j = ((ha0_1_14 j).mul (piI.mul (atomPoints j).z)).scale 1 15 := by fin_cases j <;> decide +kernel
lemma ha0_1_15_contains (j : Fin 7) : (ha0_1_15 j).Contains (fullFactor true 0 15 ((j.val:ℝ)/6)) := by
  rw [ha0_1_15_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha0_1_14 j) true 0 14 j (ha0_1_14_contains j)
noncomputable def hk0_1_16 (j : Fin 6) (i k : Fin 16) : CBox := (kernel0_0 j i k).mul (mpower1_16 j i k)
lemma hk0_1_16_contains (j : Fin 6) (i k : Fin 16) :
    (hk0_1_16 j i k).Contains (fullFactor true 0 16 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk0_1_16,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel0_0 j i k) (mpower1_16 j i k) (quadraturePoint j.val (16*i.val+k.val)) 0 16 (kernel0_0_contains j i k) (mpower1_16_contains j i k)
noncomputable def ha0_1_16 : Fin 7 → CBox := ![⟨⟨373224740880026841431601079950799,373224740880026841463538144199432⟩,⟨0,0⟩⟩,⟨⟨22814926374318185286416785682787,22814926374318185598418460740269⟩,⟨95536490055561122485035519268995,95536490055561122796992419412787⟩⟩,⟨⟨2307666050569911074221630920023,2307666050569911111450653133517⟩,⟨4066173193370065816535442022896,4066173193370065853764802532825⟩⟩,⟨⟨96126789922046678212905225747,96126789922046678901100207633⟩,⟨(-125017397674459483743337763124),(-125017397674459483055311236521)⟩⟩,⟨⟨(-4309641632192142929707990518),(-4309641632192142920104618574)⟩,⟨5420991809334498599645476724,5420991809334498609232465653⟩⟩,⟨⟨(-17021567324879402485195716),(-17021567324879402315883663)⟩,⟨(-453981816122712493693562866),(-453981816122712493522921950)⟩⟩,⟨⟨40971095585372700713639361,40971095585372700718064176⟩,⟨15376685260568953183305910,15376685260568953187992820⟩⟩]
lemma ha0_1_16_eq (j : Fin 7) : ha0_1_16 j = ((ha0_1_15 j).mul (piI.mul (atomPoints j).z)).scale 1 16 := by fin_cases j <;> decide +kernel
lemma ha0_1_16_contains (j : Fin 7) : (ha0_1_16 j).Contains (fullFactor true 0 16 ((j.val:ℝ)/6)) := by
  rw [ha0_1_16_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha0_1_15 j) true 0 15 j (ha0_1_15_contains j)
noncomputable def hk0_1_17 (j : Fin 6) (i k : Fin 16) : CBox := (kernel0_0 j i k).mul (mpower1_17 j i k)
lemma hk0_1_17_contains (j : Fin 6) (i k : Fin 16) :
    (hk0_1_17 j i k).Contains (fullFactor true 0 17 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk0_1_17,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel0_0 j i k) (mpower1_17 j i k) (quadraturePoint j.val (16*i.val+k.val)) 0 17 (kernel0_0_contains j i k) (mpower1_17_contains j i k)
noncomputable def ha0_1_17 : Fin 7 → CBox := ![⟨⟨(-202317194430637044549638480430867),(-202317194430637044531682081495494)⟩,⟨0,0⟩⟩,⟨⟨10605113986302861128147140814412,10605113986302861337169274438422⟩,⟨(-48072200020569110415794831370721),(-48072200020569110206729334205808)⟩⟩,⟨⟨563500672749097368685831598465,563500672749097390752799832169⟩,⟨(-1876754012660895579111219849311),(-1876754012660895557044330738644)⟩⟩,⟨⟨(-53568328296592431519191222456),(-53568328296592431197713893361)⟩,⟨(-8073232532004175034274421651),(-8073232532004174712786841092)⟩⟩,⟨⟨1857386286204321649085359053,1857386286204321652552701708⟩,⟨687986049573731118720590298,687986049573731122190278864⟩⟩,⟨⟨(-108391867020127638470194368),(-108391867020127638421823327)⟩,⟨22898813022231402480639181,22898813022231402528469314⟩⟩,⟨⟨2813666519292644384423446,2813666519292644385479720⟩,⟨(-8872648514942035949700234),(-8872648514942035948680332)⟩⟩]
lemma ha0_1_17_eq (j : Fin 7) : ha0_1_17 j = ((ha0_1_16 j).mul (piI.mul (atomPoints j).z)).scale 1 17 := by fin_cases j <;> decide +kernel
lemma ha0_1_17_contains (j : Fin 7) : (ha0_1_17 j).Contains (fullFactor true 0 17 ((j.val:ℝ)/6)) := by
  rw [ha0_1_17_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha0_1_16 j) true 0 16 j (ha0_1_16_contains j)
noncomputable def hk0_1_18 (j : Fin 6) (i k : Fin 16) : CBox := (kernel0_0 j i k).mul (mpower1_18 j i k)
lemma hk0_1_18_contains (j : Fin 6) (i k : Fin 16) :
    (hk0_1_18 j i k).Contains (fullFactor true 0 18 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk0_1_18,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel0_0 j i k) (mpower1_18 j i k) (quadraturePoint j.val (16*i.val+k.val)) 0 18 (kernel0_0_contains j i k) (mpower1_18_contains j i k)
noncomputable def ha0_1_18 : Fin 7 → CBox := ![⟨⟨103578967835556427786774587618132,103578967835556427796297306020701⟩,⟨0,0⟩⟩,⟨⟨(-14445944614989657226049363438720),(-14445944614989657093798482630577)⟩,⟨18283565774466192717063898973019,18283565774466192849350452189535⟩⟩,⟨⟨(-691110514692608489597944766609),(-691110514692608477245992316558)⟩,⟨352120509448384041417954697653,352120509448384053769855517987⟩⟩,⟨⟨6130964598573962603574037473,6130964598573962745387341348⟩,⟨16471622608944049928192800166,16471622608944050070023136045⟩⟩,⟨⟨20215878635818402420621697,20215878635818403604136162⟩,⟨(-534647148781619432014133051),(-534647148781619430830381183)⟩⟩,⟨⟨9438298224518590756400101,9438298224518590769178380⟩,⟨23704728643718998620525493,23704728643718998633456487⟩⟩,⟨⟨(-1809316467681524803697637),(-1809316467681524803476253)⟩,⟨(-471898671919231725472976),(-471898671919231725248342)⟩⟩]
lemma ha0_1_18_eq (j : Fin 7) : ha0_1_18 j = ((ha0_1_17 j).mul (piI.mul (atomPoints j).z)).scale 1 18 := by fin_cases j <;> decide +kernel
lemma ha0_1_18_contains (j : Fin 7) : (ha0_1_18 j).Contains (fullFactor true 0 18 ((j.val:ℝ)/6)) := by
  rw [ha0_1_18_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha0_1_17 j) true 0 17 j (ha0_1_17_contains j)
noncomputable def hk0_1_19 (j : Fin 6) (i k : Fin 16) : CBox := (kernel0_0 j i k).mul (mpower1_19 j i k)
lemma hk0_1_19_contains (j : Fin 6) (i k : Fin 16) :
    (hk0_1_19 j i k).Contains (fullFactor true 0 19 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk0_1_19,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel0_0 j i k) (mpower1_19 j i k) (quadraturePoint j.val (16*i.val+k.val)) 0 19 (kernel0_0_contains j i k) (mpower1_19_contains j i k)
noncomputable def ha0_1_19 : Fin 7 → CBox := ![⟨⟨(-50237644471643132164178796923382),(-50237644471643132159400197479224)⟩,⟨0,0⟩⟩,⟨⟨9406404598397513344527218541887,9406404598397513423803931495603⟩,⟨(-4550420949692139690051069124353),(-4550420949692139610764404632815)⟩⟩,⟨⟨274536208968430725812906199879,274536208968430732362704373821⟩,⟨96086467227326991908819202017,96086467227326998458630861066⟩⟩,⟨⟨3515322059848394809442296185,3515322059848394868713986392⟩,⟨(-4101746048451185286730736623),(-4101746048451185227465035610)⟩⟩,⟨⟨(-131615700710536994218163657),(-131615700710536993835514861)⟩,⟨37725466733039574261904399,37725466733039574644246834⟩⟩,⟨⟨4747020686359656227694574,4747020686359656230965952⟩,⟨(-2908084322731030199882339),(-2908084322731030196646217)⟩⟩,⟨⟨(-71805103699340482398982),(-71805103699340482353758)⟩,⟨348531519645263477578158,348531519645263477623564⟩⟩]
lemma ha0_1_19_eq (j : Fin 7) : ha0_1_19 j = ((ha0_1_18 j).mul (piI.mul (atomPoints j).z)).scale 1 19 := by fin_cases j <;> decide +kernel
lemma ha0_1_19_contains (j : Fin 7) : (ha0_1_19 j).Contains (fullFactor true 0 19 ((j.val:ℝ)/6)) := by
  rw [ha0_1_19_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha0_1_18 j) true 0 18 j (ha0_1_18_contains j)
noncomputable def hk0_1_20 (j : Fin 6) (i k : Fin 16) : CBox := (kernel0_0 j i k).mul (mpower1_20 j i k)
lemma hk0_1_20_contains (j : Fin 6) (i k : Fin 16) :
    (hk0_1_20 j i k).Contains (fullFactor true 0 20 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk0_1_20,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel0_0 j i k) (mpower1_20 j i k) (quadraturePoint j.val (16*i.val+k.val)) 0 20 (kernel0_0_contains j i k) (mpower1_20_contains j i k)
noncomputable def ha0_1_20 : Fin 7 → CBox := ![⟨⟨23147844838179593232127123230037,23147844838179593234402625668477⟩,⟨0,0⟩⟩,⟨⟨(-4451474548549043889493135058891),(-4451474548549043844352450821112)⟩,⟨(-4356701230817925823237778276),(-4356701230817880683640435184)⟩⟩,⟨⟨(-42841576758221668944061702411),(-42841576758221665644730198908)⟩,⟨(-94349462053290777092958878388),(-94349462053290773793621091783)⟩⟩,⟨⟨(-1545059395899196461451191717),(-1545059395899196437922074491)⟩,⟨(-317468090099444859437903385),(-317468090099444835908316540)⟩⟩,⟨⟨18686797528906789383423315,18686797528906789500796160⟩,⟨27544779289029235210884119,27544779289029235328350913⟩⟩,⟨⟨(-761186797175995805270919),(-761186797175995804492267)⟩,⟨(-867240318397072782443455),(-867240318397072781657853)⟩⟩,⟨⟨63601973893574466150775,63601973893574466159601⟩,⟨9692258337107754598435,9692258337107754607079⟩⟩]
lemma ha0_1_20_eq (j : Fin 7) : ha0_1_20 j = ((ha0_1_19 j).mul (piI.mul (atomPoints j).z)).scale 1 20 := by fin_cases j <;> decide +kernel
lemma ha0_1_20_contains (j : Fin 7) : (ha0_1_20 j).Contains (fullFactor true 0 20 ((j.val:ℝ)/6)) := by
  rw [ha0_1_20_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha0_1_19 j) true 0 19 j (ha0_1_19_contains j)
noncomputable def hk0_1_21 (j : Fin 6) (i k : Fin 16) : CBox := (kernel0_0 j i k).mul (mpower1_21 j i k)
lemma hk0_1_21_contains (j : Fin 6) (i k : Fin 16) :
    (hk0_1_21 j i k).Contains (fullFactor true 0 21 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk0_1_21,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel0_0 j i k) (mpower1_21 j i k) (quadraturePoint j.val (16*i.val+k.val)) 0 21 (kernel0_0_contains j i k) (mpower1_21_contains j i k)
noncomputable def ha0_1_21 : Fin 7 → CBox := ![⟨⟨(-10157867837341913524759706938530),(-10157867837341913523728824625962)⟩,⟨0,0⟩⟩,⟨⟨1624277549844302967861670932692,1624277549844302992337398750840⟩,⟨789683983844511823026481640308,789683983844511847499343599008⟩⟩,⟨⟨(-13094362879676462635702127821),(-13094362879676461052906095159)⟩,⟨32627355682037620530946540777,32627355682037622113740736438⟩⟩,⟨⟨130989651995254227525864300,130989651995254236421194003⟩,⟨418620375530646612035249140,418620375530646620930951824⟩⟩,⟨⟨4711401116595262930944177,4711401116595262965279998⟩,⟨(-6098712468413171913985007),(-6098712468413171879667244)⟩⟩,⟨⟨(-143182178180077639067746),(-143182178180077638888182)⟩,⟨177165482457656683093313,177165482457656683271703⟩⟩,⟨⟨1097916250891256309739,1097916250891256311313⟩,⟨(-11023253890118668452387),(-11023253890118668450756)⟩⟩]
lemma ha0_1_21_eq (j : Fin 7) : ha0_1_21 j = ((ha0_1_20 j).mul (piI.mul (atomPoints j).z)).scale 1 21 := by fin_cases j <;> decide +kernel
lemma ha0_1_21_contains (j : Fin 7) : (ha0_1_21 j).Contains (fullFactor true 0 21 ((j.val:ℝ)/6)) := by
  rw [ha0_1_21_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha0_1_20 j) true 0 20 j (ha0_1_20_contains j)
noncomputable def hk0_1_22 (j : Fin 6) (i k : Fin 16) : CBox := (kernel0_0 j i k).mul (mpower1_22 j i k)
lemma hk0_1_22_contains (j : Fin 6) (i k : Fin 16) :
    (hk0_1_22 j i k).Contains (fullFactor true 0 22 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk0_1_22,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel0_0 j i k) (mpower1_22 j i k) (quadraturePoint j.val (16*i.val+k.val)) 0 22 (kernel0_0_contains j i k) (mpower1_22_contains j i k)
noncomputable def ha0_1_22 : Fin 7 → CBox := ![⟨⟨4254917729857252845698984040626,4254917729857252846144342837729⟩,⟨0,0⟩⟩,⟨⟨(-432552241827585182491346069135),(-432552241827585169824426341861)⟩,⟨(-549669869689692496523808604443),(-549669869689692483857879999018)⟩⟩,⟨⟨10568478417066088377047554111,10568478417066089101835664705⟩,⟨(-4236559225796058546834782373),(-4236559225796057822047293284)⟩⟩,⟨⟨80351423597483050358405489,80351423597483053568560290⟩,⟨(-84264652639745643586928473),(-84264652639745640376907111)⟩⟩,⟨⟨(-1605247173511678803210534),(-1605247173511678793633664)⟩,⟨(-569313588357886788739691),(-569313588357886779160896)⟩⟩,⟨⟨37482607861138001078429,37482607861138001117424⟩,⟨20916501982560748810970,20916501982560748850129⟩⟩,⟨⟨(-1818700738375698710149),(-1818700738375698709862)⟩,⟨(-86124127961573633107),(-86124127961573632833)⟩⟩]
lemma ha0_1_22_eq (j : Fin 7) : ha0_1_22 j = ((ha0_1_21 j).mul (piI.mul (atomPoints j).z)).scale 1 22 := by fin_cases j <;> decide +kernel
lemma ha0_1_22_contains (j : Fin 7) : (ha0_1_22 j).Contains (fullFactor true 0 22 ((j.val:ℝ)/6)) := by
  rw [ha0_1_22_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha0_1_21 j) true 0 21 j (ha0_1_21_contains j)
noncomputable def hk0_1_23 (j : Fin 6) (i k : Fin 16) : CBox := (kernel0_0 j i k).mul (mpower1_23 j i k)
lemma hk0_1_23_contains (j : Fin 6) (i k : Fin 16) :
    (hk0_1_23 j i k).Contains (fullFactor true 0 23 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk0_1_23,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel0_0 j i k) (mpower1_23 j i k) (quadraturePoint j.val (16*i.val+k.val)) 0 23 (kernel0_0_contains j i k) (mpower1_23_contains j i k)
noncomputable def ha0_1_23 : Fin 7 → CBox := ![⟨⟨(-1704804650425896415800460320443),(-1704804650425896415616593234907)⟩,⟨0,0⟩⟩,⟨⟨55323851223332981711798355407,55323851223332987982004417807⟩,⟨253133244217801512476029251239,253133244217801518746129166926⟩⟩,⟨⟨(-3211013251042785395164579833),(-3211013251042785077706850761)⟩,⟨(-1459581662251571579126951902),(-1459581662251571261669018129)⟩⟩,⟨⟨(-28601783853112188300778438),(-28601783853112187192757467)⟩,⟨(-7477813622827618162858473),(-7477813622827617054825518)⟩⟩,⟨⟨(-8595693871736428224586),(-8595693871736425668827)⟩,⟨359953809613934521811244,359953809613934524367187⟩⟩,⟨⟨2567431007409637150556,2567431007409637158723⟩,⟨(-7298223787407985654930),(-7298223787407985646780)⟩⟩,⟨⟨1326394302577871851,1326394302577871898⟩,⟨286241197351318080156,286241197351318080206⟩⟩]
lemma ha0_1_23_eq (j : Fin 7) : ha0_1_23 j = ((ha0_1_22 j).mul (piI.mul (atomPoints j).z)).scale 1 23 := by fin_cases j <;> decide +kernel
lemma ha0_1_23_contains (j : Fin 7) : (ha0_1_23 j).Contains (fullFactor true 0 23 ((j.val:ℝ)/6)) := by
  rw [ha0_1_23_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha0_1_22 j) true 0 22 j (ha0_1_22_contains j)
noncomputable def hk0_1_24 (j : Fin 6) (i k : Fin 16) : CBox := (kernel0_0 j i k).mul (mpower1_24 j i k)
lemma hk0_1_24_contains (j : Fin 6) (i k : Fin 16) :
    (hk0_1_24 j i k).Contains (fullFactor true 0 24 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk0_1_24,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel0_0 j i k) (mpower1_24 j i k) (quadraturePoint j.val (16*i.val+k.val)) 0 24 (kernel0_0_contains j i k) (mpower1_24_contains j i k)
noncomputable def ha0_1_24 : Fin 7 → CBox := ![⟨⟨654597993571342547950236620064,654597993571342548022920162823⟩,⟨0,0⟩⟩,⟨⟨21541204190706455928517760637,21541204190706458902873846025⟩,⟨(-89427665725107391351303364387),(-89427665725107388376861155187)⟩⟩,⟨⟨345520901943246880784648140,345520901943247014036661043⟩,⟨988480094418843916448719884,988480094418844049700783493⟩⟩,⟨⟨1780996679648801416413344,1780996679648801782922019⟩,⟨6969502533752295269303519,6969502533752295635817439⟩⟩,⟨⟨69833677160229208488925,69833677160229209142537⟩,⟨(-21072763191427638368252),(-21072763191427637714809)⟩⟩,⟨⟨(-1317652471557531306214),(-1317652471557531304582)⟩,⟨(-222855831198608193735),(-222855831198608192103)⟩⟩,⟨⟨43057306477136804562,43057306477136804571⟩,⟨(-2439088085245768535),(-2439088085245768527)⟩⟩]
lemma ha0_1_24_eq (j : Fin 7) : ha0_1_24 j = ((ha0_1_23 j).mul (piI.mul (atomPoints j).z)).scale 1 24 := by fin_cases j <;> decide +kernel
lemma ha0_1_24_contains (j : Fin 7) : (ha0_1_24 j).Contains (fullFactor true 0 24 ((j.val:ℝ)/6)) := by
  rw [ha0_1_24_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha0_1_23 j) true 0 23 j (ha0_1_23_contains j)
noncomputable def hk0_1_25 (j : Fin 6) (i k : Fin 16) : CBox := (kernel0_0 j i k).mul (mpower1_25 j i k)
lemma hk0_1_25_contains (j : Fin 6) (i k : Fin 16) :
    (hk0_1_25 j i k).Contains (fullFactor true 0 25 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk0_1_25,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel0_0 j i k) (mpower1_25 j i k) (quadraturePoint j.val (16*i.val+k.val)) 0 25 (kernel0_0_contains j i k) (mpower1_25_contains j i k)
noncomputable def ha0_1_25 : Fin 7 → CBox := ![⟨⟨(-241293682391912884886769410525),(-241293682391912884859209211026)⟩,⟨0,0⟩⟩,⟨⟨(-19904778416447496107110458232),(-19904778416447494752620704511)⟩,⟨24219432660822787875009130362,24219432660822789229546614036⟩⟩,⟨⟨135585393864685413549289519,135585393864685467243781384⟩,⟨(-265852462342779436907410846),(-265852462342779383212937991)⟩⟩,⟨⟨1222479086062008539439512,1222479086062008655823527⟩,⟨(-1152857451333707370889214),(-1152857451333707254507183)⟩⟩,⟨⟨(-8127154073815314563419),(-8127154073815314403018)⟩,⟨(-11627923450876749110235),(-11627923450876748949794)⟩⟩,⟨⟨703889137214255766,703889137214256080⟩,⟨221598356263623670782,221598356263623671096⟩⟩,⟨⟨(-675705017521252253),(-675705017521252251)⟩,⟨(-6200922363632815994),(-6200922363632815991)⟩⟩]
lemma ha0_1_25_eq (j : Fin 7) : ha0_1_25 j = ((ha0_1_24 j).mul (piI.mul (atomPoints j).z)).scale 1 25 := by fin_cases j <;> decide +kernel
lemma ha0_1_25_contains (j : Fin 7) : (ha0_1_25 j).Contains (fullFactor true 0 25 ((j.val:ℝ)/6)) := by
  rw [ha0_1_25_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha0_1_24 j) true 0 24 j (ha0_1_24_contains j)
noncomputable def hk0_1_26 (j : Fin 6) (i k : Fin 16) : CBox := (kernel0_0 j i k).mul (mpower1_26 j i k)
lemma hk0_1_26_contains (j : Fin 6) (i k : Fin 16) :
    (hk0_1_26 j i k).Contains (fullFactor true 0 26 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk0_1_26,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel0_0 j i k) (mpower1_26 j i k) (quadraturePoint j.val (16*i.val+k.val)) 0 26 (kernel0_0_contains j i k) (mpower1_26_contains j i k)
noncomputable def ha0_1_26 : Fin 7 → CBox := ![⟨⟨85523190354468574856651357295,85523190354468574866691915533⟩,⟨0,0⟩⟩,⟨⟨9332272679116857535420636632,9332272679116858128520025417⟩,⟨(-4294943490440916720219520164),(-4294943490440916127110797447)⟩⟩,⟨⟨(-78336206843192625623961059),(-78336206843192604819790590)⟩,⟨23486586321533778567369488,23486586321533799371536509⟩⟩,⟨⟨(-359566156896607253809319),(-359566156896607218274428)⟩,⟨(-114699775302073863356880),(-114699775302073827821795)⟩⟩,⟨⟨(-1592513281617125057105),(-1592513281617125019238)⟩,⟨2121838957507806662470,2121838957507806700331⟩⟩,⟨⟨34799966704316379910,34799966704316379969⟩,⟨(-6113401308409143732),(-6113401308409143673)⟩⟩,⟨⟨(-856338950808112631),(-856338950808112630)⟩,⟨138629092417247708,138629092417247710⟩⟩]
lemma ha0_1_26_eq (j : Fin 7) : ha0_1_26 j = ((ha0_1_25 j).mul (piI.mul (atomPoints j).z)).scale 1 26 := by fin_cases j <;> decide +kernel
lemma ha0_1_26_contains (j : Fin 7) : (ha0_1_26 j).Contains (fullFactor true 0 26 ((j.val:ℝ)/6)) := by
  rw [ha0_1_26_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha0_1_25 j) true 0 25 j (ha0_1_25_contains j)
noncomputable def hk0_1_27 (j : Fin 6) (i k : Fin 16) : CBox := (kernel0_0 j i k).mul (mpower1_27 j i k)
lemma hk0_1_27_contains (j : Fin 6) (i k : Fin 16) :
    (hk0_1_27 j i k).Contains (fullFactor true 0 27 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk0_1_27,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel0_0 j i k) (mpower1_27 j i k) (quadraturePoint j.val (16*i.val+k.val)) 0 27 (kernel0_0_contains j i k) (mpower1_27_contains j i k)
noncomputable def ha0_1_27 : Fin 7 → CBox := ![⟨⟨(-29189820166130956436190703278),(-29189820166130956432670857994)⟩,⟨0,0⟩⟩,⟨⟨(-3241161071801606097315338638),(-3241161071801605847233466772)⟩,⟨(-65558174658857429687752653),(-65558174658857179606860623)⟩⟩,⟨⟨18764864547021019260020391,18764864547021027022113231⟩,⟨10659484973469284924535687,10659484973469292686630021⟩⟩,⟨⟨15987003220282519797116,15987003220282530244953⟩,⟨80050511362438609819072,80050511362438620266959⟩⟩,⟨⟨452448086798722323219,452448086798722331825⟩,⟨153409325648267318099,153409325648267326705⟩⟩,⟨⟨(-1832772073530565542),(-1832772073530565530)⟩,⟨(-5106017288199958289),(-5106017288199958278)⟩⟩,⟨⟨24495959236594590,24495959236594591⟩,⟨113564125910997956,113564125910997957⟩⟩]
lemma ha0_1_27_eq (j : Fin 7) : ha0_1_27 j = ((ha0_1_26 j).mul (piI.mul (atomPoints j).z)).scale 1 27 := by fin_cases j <;> decide +kernel
lemma ha0_1_27_contains (j : Fin 7) : (ha0_1_27 j).Contains (fullFactor true 0 27 ((j.val:ℝ)/6)) := by
  rw [ha0_1_27_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha0_1_26 j) true 0 26 j (ha0_1_26_contains j)
noncomputable def hk0_1_28 (j : Fin 6) (i k : Fin 16) : CBox := (kernel0_0 j i k).mul (mpower1_28 j i k)
lemma hk0_1_28_contains (j : Fin 6) (i k : Fin 16) :
    (hk0_1_28 j i k).Contains (fullFactor true 0 28 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk0_1_28,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel0_0 j i k) (mpower1_28 j i k) (quadraturePoint j.val (16*i.val+k.val)) 0 28 (kernel0_0_contains j i k) (mpower1_28_contains j i k)
noncomputable def ha0_1_28 : Fin 7 → CBox := ![⟨⟨9606931147893012552728397476,9606931147893012553917426060⟩,⟨0,0⟩⟩,⟨⟨878705318217083792629038810,878705318217083894308715795⟩,⟨448313242223517886667138421,448313242223517988345251840⟩⟩,⟨⟨(-1338989007970705854770986),(-1338989007970703062147819)⟩,⟨(-5325869956917321966082246),(-5325869956917319173458882)⟩⟩,⟨⟨12988480910365772534811,12988480910365775496935⟩,⟨(-11007430336248213108404),(-11007430336248210146301)⟩⟩,⟨⟨826046342761578017,826046342761579904⟩,⟨(-82956253038068107040),(-82956253038068105153)⟩⟩,⟨⟨(-698884342741524279),(-698884342741524276)⟩,⟨395843220953149448,395843220953149451⟩⟩,⟨⟨14481547403249622,14481547403249623⟩,⟨(-3920709409332273),(-3920709409332272)⟩⟩]
lemma ha0_1_28_eq (j : Fin 7) : ha0_1_28 j = ((ha0_1_27 j).mul (piI.mul (atomPoints j).z)).scale 1 28 := by fin_cases j <;> decide +kernel
lemma ha0_1_28_contains (j : Fin 7) : (ha0_1_28 j).Contains (fullFactor true 0 28 ((j.val:ℝ)/6)) := by
  rw [ha0_1_28_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha0_1_27 j) true 0 27 j (ha0_1_27_contains j)
noncomputable def hk0_1_29 (j : Fin 6) (i k : Fin 16) : CBox := (kernel0_0 j i k).mul (mpower1_29 j i k)
lemma hk0_1_29_contains (j : Fin 6) (i k : Fin 16) :
    (hk0_1_29 j i k).Contains (fullFactor true 0 29 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk0_1_29,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel0_0 j i k) (mpower1_29 j i k) (quadraturePoint j.val (16*i.val+k.val)) 0 29 (kernel0_0_contains j i k) (mpower1_29_contains j i k)
noncomputable def ha0_1_29 : Fin 7 → CBox := ![⟨⟨(-3052797310302529882591970126),(-3052797310302529882204414810)⟩,⟨0,0⟩⟩,⟨⟨(-174813461545535431099307212),(-174813461545535391183734533)⟩,⟨(-231164710851134947758546994),(-231164710851134907843373719)⟩⟩,⟨⟨(-718498838513151174740022),(-718498838513150204665911)⟩,⟨1142005457792919088773196,1142005457792920058847207⟩⟩,⟨⟨(-3206423563734735854542),(-3206423563734735043702)⟩,⟨(-1213721250719765199532),(-1213721250719764388691)⟩⟩,⟨⟨(-13258922326659661568),(-13258922326659661168)⟩,⟨4203171326336672529,4203171326336672930⟩⟩,⟨⟨72736707079834220,72736707079834222⟩,⟨88839829736672856,88839829736672858⟩⟩,⟨⟨(-581966637725765),(-581966637725764)⟩,⟨(-1777828965400159),(-1777828965400158)⟩⟩]
lemma ha0_1_29_eq (j : Fin 7) : ha0_1_29 j = ((ha0_1_28 j).mul (piI.mul (atomPoints j).z)).scale 1 29 := by fin_cases j <;> decide +kernel
lemma ha0_1_29_contains (j : Fin 7) : (ha0_1_29 j).Contains (fullFactor true 0 29 ((j.val:ℝ)/6)) := by
  rw [ha0_1_29_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha0_1_28 j) true 0 28 j (ha0_1_28_contains j)
noncomputable def hk0_1_30 (j : Fin 6) (i k : Fin 16) : CBox := (kernel0_0 j i k).mul (mpower1_30 j i k)
lemma hk0_1_30_contains (j : Fin 6) (i k : Fin 16) :
    (hk0_1_30 j i k).Contains (fullFactor true 0 30 (quadraturePoint j.val (16*i.val+k.val))) := by
  simpa only [hk0_1_30,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using @momentPower_trans_full (kernel0_0 j i k) (mpower1_30 j i k) (quadraturePoint j.val (16*i.val+k.val)) 0 30 (kernel0_0_contains j i k) (mpower1_30_contains j i k)
noncomputable def ha0_1_30 : Fin 7 → CBox := ![⟨⟨937752014510188366842383715,937752014510188366964417120⟩,⟨0,0⟩⟩,⟨⟨16024061627868274676685549,16024061627868289823619528⟩,⟨80736464436127435910159778,80736464436127451057064798⟩⟩,⟨⟨313968769379739008895259,313968769379739334637334⟩,⟨(-64077911573074331505489),(-64077911573074005763423)⟩⟩,⟨⟨95803660365903055654,95803660365903270212⟩,⟨660470924325592463142,660470924325592677701⟩⟩,⟨⟨1317019989054446518,1317019989054446601⟩,⟨1829559169964478083,1829559169964478166⟩⟩,⟨⟨10390272510291510,10390272510291511⟩,⟨(-11990710695265079),(-11990710695265078)⟩⟩,⟨⟨(-210350295292229),(-210350295292228)⟩,⟨81177519670486,81177519670487⟩⟩]
lemma ha0_1_30_eq (j : Fin 7) : ha0_1_30 j = ((ha0_1_29 j).mul (piI.mul (atomPoints j).z)).scale 1 30 := by fin_cases j <;> decide +kernel
lemma ha0_1_30_contains (j : Fin 7) : (ha0_1_30 j).Contains (fullFactor true 0 30 ((j.val:ℝ)/6)) := by
  rw [ha0_1_30_eq]
  simpa only [Bool.false_eq_true,ite_false,ite_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha0_1_29 j) true 0 29 j (ha0_1_29_contains j)
end SharpPlanar.CachedData

end OAI
