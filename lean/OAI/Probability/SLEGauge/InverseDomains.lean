import Mathlib
import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLEGauge.EulerFlow

namespace OAI

/-! Hausdorff gauges, Loewner evolution and trace measures. -/

section
noncomputable section
open MeasureTheory Set Filter Metric
open scoped NNReal ENNReal Topology
noncomputable section
open Set Filter Metric
open scoped Topology NNReal
noncomputable section
open Set Filter Metric
open scoped Topology NNReal
namespace SLEExactGauge.LiteralTrace
lemma PositiveSolution.surviving {κ : ℝ} {b : Driver} {z : ℂ} {T : ℝ} {f : ℝ → ℂ}
    (hf : PositiveSolution κ b z T f) : Surviving κ b z T := by
  obtain ⟨j,hj,hgap⟩ := hf.exists_cutoff
  have he := hf.cutoff_eq hj (fun t ht => (hgap t ht).le)
  obtain ⟨t0,ht0,hmin⟩ := isCompact_Icc.exists_isMinOn ⟨0,le_rfl,hf.1⟩
    (Complex.continuous_im.comp_continuousOn hf.2.1)
  refine ⟨j,hj,(hgap t0 ht0).trans_le ?_⟩
  apply le_csInf (s := (fun u : ℝ => (cutoffFlow κ b j z u).im) '' Icc 0 T)
    (Set.Nonempty.image _ ⟨0,le_rfl,hf.1⟩)
  rintro y ⟨t,ht,rfl⟩
  dsimp only
  rw [he ht]
  exact hmin ht
end SLEExactGauge.LiteralTrace

namespace SLEExactGauge.LiteralTrace

lemma cutoff_positiveSolution {κ : ℝ} {b : Driver} {z : ℂ} {T : ℝ} (hT : 0 ≤ T)
    {j : ℕ} (hj : 1 ≤ j)
    (hgap : (j:ℝ)⁻¹ < sInf ((fun u : ℝ => (cutoffFlow κ b j z u).im) '' Icc 0 T)) :
    PositiveSolution κ b z T (cutoffFlow κ b j z) := by
  have hc := cutoffFlow_continuous κ b hj z hT
  have hb := (isCompact_Icc.image_of_continuousOn (Complex.continuous_im.comp_continuousOn hc)).bddBelow
  have hg t (ht : t ∈ Icc 0 T) : (j:ℝ)⁻¹ < (cutoffFlow κ b j z t).im :=
    hgap.trans_le (csInf_le hb ⟨t,ht,rfl⟩)
  refine ⟨hT,hc,(cutoffFlow_solution κ b j hj z hT).2.1,?_,?_⟩
  · intro t ht
    exact lt_trans (inv_pos.mpr (by exact_mod_cast (Nat.zero_lt_of_lt hj))) (hg t ht)
  · intro t ht
    rw [← cutoffField_of_height κ b hj (hg t ht).le]
    exact (cutoffFlow_solution κ b j hj z hT).2.2 t ht

lemma PositiveSolution.restrict {κ : ℝ} {b : Driver} {z : ℂ} {T : ℝ} {f : ℝ → ℂ}
    (hf : PositiveSolution κ b z T f) {t : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) :
    PositiveSolution κ b z t f := by
  have hi : Icc 0 t ⊆ Icc 0 T := Icc_subset_Icc_right htT
  exact ⟨ht,hf.2.1.mono hi,hf.2.2.1,fun u hu => hf.2.2.2.1 u (hi hu),
    fun u hu => (hf.2.2.2.2 u (hi hu)).mono hi⟩

lemma PositiveSolution.flow_eq {κ : ℝ} {b : Driver} {z : ℂ} {T : ℝ} {f : ℝ → ℂ}
    (hf : PositiveSolution κ b z T f) : flow κ b z T = f T := by
  have hs := hf.surviving
  have hn := Nat.find_spec hs
  rw [flow,dite_eq_left hs]
  exact (cutoff_positiveSolution hf.1 hn.1 hn.2).unique hf ⟨hf.1,le_rfl⟩

lemma PositiveSolution.flow_eqOn {κ : ℝ} {b : Driver} {z : ℂ} {T : ℝ} {f : ℝ → ℂ}
    (hf : PositiveSolution κ b z T f) : EqOn (flow κ b z) f (Icc 0 T) :=
  fun _ ht => (hf.restrict ht.1 ht.2).flow_eq

lemma surviving_iff_positiveSolution {κ : ℝ} {b : Driver} {z : ℂ} {T : ℝ} (hT : 0 ≤ T) :
    Surviving κ b z T ↔ ∃ f, PositiveSolution κ b z T f := by
  constructor
  · rintro ⟨j,hj,hgap⟩
    exact ⟨cutoffFlow κ b j z,cutoff_positiveSolution hT hj hgap⟩
  · rintro ⟨f,hf⟩
    exact hf.surviving

lemma surviving_flow_positiveSolution {κ : ℝ} {b : Driver} {z : ℂ} {T : ℝ}
    (hT : 0 ≤ T) (hs : Surviving κ b z T) : PositiveSolution κ b z T (flow κ b z) := by
  obtain ⟨f,hf⟩ := (surviving_iff_positiveSolution hT).mp hs
  have he := hf.flow_eqOn
  refine ⟨hT,hf.2.1.congr (fun t ht => he ht),?_,?_,?_⟩
  · rw [he ⟨le_rfl,hT⟩,hf.2.2.1]
  · intro t ht
    rw [he ht]
    exact hf.2.2.2.1 t ht
  · intro t ht
    rw [he ht]
    exact (hf.2.2.2.2 t ht).congr (fun u hu => he hu) (he ht)
end SLEExactGauge.LiteralTrace

namespace SLEExactGauge.LiteralTrace

 

lemma PositiveSolution.extend {κ : ℝ} {b : Driver} {z : ℂ} {T : ℝ} {f : ℝ → ℂ}
    (hf : PositiveSolution κ b z T f) :
    ∃ U : ℝ, T < U ∧ ∃ g : ℝ → ℂ, PositiveSolution κ b z U g ∧ EqOn g f (Icc 0 T) := by
  obtain ⟨j,hj,hgap⟩ := hf.exists_cutoff
  let g := cutoffFlow κ b j z
  have he : EqOn g f (Icc 0 T) := hf.cutoff_eq hj (fun t ht => (hgap t ht).le)
  have hc := cutoffFlow_continuous κ b hj z (show 0 ≤ T+1 by linarith [hf.1])
  have hy : (j:ℝ)⁻¹ < (g T).im := by rw [he ⟨hf.1,le_rfl⟩]; exact hgap T ⟨hf.1,le_rfl⟩
  have hci := (Complex.continuous_im.comp_continuousOn hc) T (show T ∈ Icc 0 (T+1) by constructor <;> linarith [hf.1])
  obtain ⟨δ,hδ,hnear⟩ := Metric.continuousWithinAt_iff.mp hci ((g T).im-(j:ℝ)⁻¹) (sub_pos.mpr hy)
  let U := T+min (δ/2) (1/2)
  have hTU : T < U := by dsimp [U]; have := lt_min (by linarith : 0 < δ/2) (by norm_num : (0:ℝ)<1/2); linarith
  have hU1 : U ≤ T+1 := by dsimp [U]; have := min_le_right (δ/2) (1/2:ℝ); linarith
  have hU : 0 ≤ U := hf.1.trans hTU.le
  have hg t (ht : t ∈ Icc 0 U) : (j:ℝ)⁻¹ < (g t).im := by
    by_cases htT : t ≤ T
    · rw [he ⟨ht.1,htT⟩]
      exact hgap _ ⟨ht.1,htT⟩
    · have hdist : dist t T < δ := by
        rw [Real.dist_eq,abs_of_nonneg (by linarith)]
        have hδU : U ≤ T+δ/2 := by dsimp [U]; exact add_le_add le_rfl (min_le_left (δ/2) (1/2:ℝ))
        linarith [ht.2]
      have hn := hnear ⟨ht.1,ht.2.trans hU1⟩ hdist
      rw [Real.dist_eq] at hn
      have hh := (abs_lt.mp hn).1
      change -((g T).im-(j:ℝ)⁻¹) < (g t).im-(g T).im at hh
      linarith
  refine ⟨U,hTU,g,⟨hU,hc.mono (Icc_subset_Icc_right hU1),?_,?_,?_⟩,he⟩
  · exact (cutoffFlow_solution κ b j hj z hU).2.1
  · intro t ht
    exact (inv_pos.mpr (by exact_mod_cast (Nat.zero_lt_of_lt hj))).trans (hg t ht)
  · intro t ht
    rw [← cutoffField_of_height κ b hj (hg t ht).le]
    exact (cutoffFlow_solution κ b j hj z hU).2.2 t ht

end SLEExactGauge.LiteralTrace

namespace SLEExactGauge.LiteralTrace

def clockIntegrand (b : Driver) (f : ℝ → ℂ) (t : ℝ) : ℝ :=
  (f t).im^2/‖f t-driverValue b t‖^4

def rawClock (κ : ℝ) (b : Driver) (z : ℂ) (t : ℝ) : ℝ :=
  ∫ u in Icc (0:ℝ) t, clockIntegrand b (flow κ b z) u

lemma PositiveSolution.shifted_ne_zero {κ : ℝ} {b : Driver} {z : ℂ} {T : ℝ} {f : ℝ → ℂ}
    (hf : PositiveSolution κ b z T f) {t : ℝ} (ht : t ∈ Icc 0 T) : f t-driverValue b t ≠ 0 := by
  intro he
  have hi := congrArg Complex.im he
  simp only [Complex.sub_im,Complex.ofReal_im,sub_zero,Complex.zero_im] at hi
  exact (hf.2.2.2.1 t ht).ne' hi

lemma PositiveSolution.continuous_clockIntegrand {κ : ℝ} {b : Driver} {z : ℂ} {T : ℝ} {f : ℝ → ℂ}
    (hf : PositiveSolution κ b z T f) : ContinuousOn (clockIntegrand b f) (Icc 0 T) := by
  apply ((Complex.continuous_im.comp_continuousOn hf.2.1).pow 2).div
    ((hf.2.1.sub (Complex.continuous_ofReal.comp (continuous_driverValue b)).continuousOn).norm.pow 4)
  intro t ht
  exact pow_ne_zero _ (norm_ne_zero_iff.mpr (hf.shifted_ne_zero ht))

def timeClip (T t : ℝ) : ℝ := max 0 (min T t)
lemma continuous_timeClip (T : ℝ) : Continuous (timeClip T) := continuous_const.max (continuous_const.min continuous_id)
lemma timeClip_mem {T : ℝ} (hT : 0 ≤ T) (t : ℝ) : timeClip T t ∈ Icc 0 T :=
  ⟨le_max_left _ _,max_le hT (min_le_left _ _)⟩
lemma timeClip_eq {T t : ℝ} (ht : t ∈ Icc 0 T) : timeClip T t = t :=
  by rw [timeClip,min_eq_right ht.2,max_eq_right ht.1]

 

def pathClock (b : Driver) (f : ℝ → ℂ) (T t : ℝ) : ℝ :=
  ∫ u in (0:ℝ)..t, clockIntegrand b f (timeClip T u)

lemma PositiveSolution.continuous_timeClippedIntegrand {κ : ℝ} {b : Driver} {z : ℂ} {T : ℝ} {f : ℝ → ℂ}
    (hf : PositiveSolution κ b z T f) : Continuous (fun t => clockIntegrand b f (timeClip T t)) :=
  hf.continuous_clockIntegrand.comp_continuous (continuous_timeClip T) (timeClip_mem hf.1)

lemma PositiveSolution.pathClock_deriv {κ : ℝ} {b : Driver} {z : ℂ} {T : ℝ} {f : ℝ → ℂ}
    (hf : PositiveSolution κ b z T f) {t : ℝ} (ht : t ∈ Icc 0 T) :
    HasDerivAt (pathClock b f T) (clockIntegrand b f t) t := by
  have hc := hf.continuous_timeClippedIntegrand
  have hd := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  convert hd using 1 <;> first | rfl | simp only [timeClip_eq ht]

lemma PositiveSolution.pathClock_continuous {κ : ℝ} {b : Driver} {z : ℂ} {T : ℝ} {f : ℝ → ℂ}
    (hf : PositiveSolution κ b z T f) : ContinuousOn (pathClock b f T) (Icc 0 T) :=
  fun _ ht => (hf.pathClock_deriv ht).continuousAt.continuousWithinAt

lemma PositiveSolution.rawClock_eq {κ : ℝ} {b : Driver} {z : ℂ} {T : ℝ} {f : ℝ → ℂ}
    (hf : PositiveSolution κ b z T f) {t : ℝ} (ht : t ∈ Icc 0 T) :
    rawClock κ b z t = pathClock b f T t := by
  rw [rawClock,integral_Icc_eq_integral_Ioc,pathClock,intervalIntegral.integral_of_le ht.1]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro u hu
  have huT : u ∈ Icc 0 T := ⟨hu.1.le,hu.2.trans ht.2⟩
  dsimp only
  rw [timeClip_eq huT]
  simp only [clockIntegrand,hf.flow_eqOn huT]

lemma PositiveSolution.pathClock_strictMono {κ : ℝ} {b : Driver} {z : ℂ} {T : ℝ} {f : ℝ → ℂ}
    (hf : PositiveSolution κ b z T f) : StrictMonoOn (pathClock b f T) (Icc 0 T) := by
  apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc _ _) hf.pathClock_continuous
    (fun t ht => (hf.pathClock_deriv (interior_subset ht)).hasDerivWithinAt)
  intro t ht
  unfold clockIntegrand
  exact div_pos (sq_pos_of_pos (hf.2.2.2.1 t (interior_subset ht)))
    (pow_pos (norm_pos_iff.mpr (hf.shifted_ne_zero (interior_subset ht))) _)

lemma PositiveSolution.rawClock_strictMono {κ : ℝ} {b : Driver} {z : ℂ} {T : ℝ} {f : ℝ → ℂ}
    (hf : PositiveSolution κ b z T f) : StrictMonoOn (rawClock κ b z) (Icc 0 T) := by
  intro u hu v hv huv
  rw [hf.rawClock_eq hu,hf.rawClock_eq hv]
  exact hf.pathClock_strictMono hu hv huv
end SLEExactGauge.LiteralTrace

namespace SLEExactGauge.LiteralTrace

def rawLevelTime (κ : ℝ) (b : Driver) (z : ℂ) (s : ℝ) : ℝ≥0∞ :=
  sInf {t | ∃ q : ℚ, 0 < q ∧ t = ENNReal.ofReal (q:ℝ) ∧
    Surviving κ b z q ∧ s < rawClock κ b z q}

lemma clock_eq_rawClock (κ θ : ℝ) (b : Driver) (x : ℂ) (t : ℝ) :
    clock κ θ b x t = rawClock κ b (diskMapInv θ x) t := rfl
lemma levelTime_eq_rawLevelTime (κ θ : ℝ) (b : Driver) (s : ℝ) :
    levelTime κ θ b s = rawLevelTime κ b (diskMapInv θ 0) s := rfl
lemma rawClock_zero (κ : ℝ) (b : Driver) (z : ℂ) : rawClock κ b z 0 = 0 := by
  simp [rawClock]

lemma PositiveSolution.rawClock_continuous {κ : ℝ} {b : Driver} {z : ℂ} {T : ℝ} {f : ℝ → ℂ}
    (hf : PositiveSolution κ b z T f) : ContinuousOn (rawClock κ b z) (Icc 0 T) :=
  hf.pathClock_continuous.congr (fun _ ht => hf.rawClock_eq ht)

 

lemma PositiveSolution.rawLevelTime_eq {κ : ℝ} {b : Driver} {z : ℂ} {T : ℝ} {f : ℝ → ℂ}
    (hf : PositiveSolution κ b z T f) :
    rawLevelTime κ b z (rawClock κ b z T) = ENNReal.ofReal T := by
  apply le_antisymm
  · obtain ⟨U,hTU,g,hg,_⟩ := hf.extend
    apply ENNReal.le_of_forall_pos_le_add
    intro ε hε _
    have hεr : (0:ℝ) < ε := by exact_mod_cast hε
    have hbar : T < min U (T+ε) := lt_min hTU (by linarith)
    obtain ⟨q,hTq,hq⟩ := exists_rat_btwn hbar
    have hq0 : (0:ℝ) < q := hf.1.trans_lt hTq
    have hqU : (q:ℝ) ≤ U := (hq.trans_le (min_le_left _ _)).le
    have hcq := hg.rawClock_strictMono ⟨hf.1,hTU.le⟩ ⟨hq0.le,hqU⟩ hTq
    have hle : rawLevelTime κ b z (rawClock κ b z T) ≤ ENNReal.ofReal (q:ℝ) :=
      sInf_le ⟨q,by exact_mod_cast hq0,rfl,(hg.restrict hq0.le hqU).surviving,hcq⟩
    refine hle.trans ?_
    calc
      ENNReal.ofReal (q:ℝ) ≤ ENNReal.ofReal (T+(ε:ℝ)) :=
        ENNReal.ofReal_le_ofReal (hq.trans_le (min_le_right _ _)).le
      _ = ENNReal.ofReal T + ε := by
        convert ENNReal.ofReal_add hf.1 ε.2 using 1
        all_goals try rfl
        exact congrArg (fun x : ℝ≥0∞ => ENNReal.ofReal T + x)
          (ENNReal.ofReal_coe_nnreal (p := ε)).symm
  · apply le_sInf
    rintro _ ⟨q,hq,rfl,_,hclock⟩
    apply ENNReal.ofReal_le_ofReal
    by_contra hTq
    have hq0 : (0:ℝ) ≤ q := by exact_mod_cast hq.le
    have hqt : (q:ℝ) < T := lt_of_not_ge hTq
    exact (not_lt_of_ge (hf.rawClock_strictMono ⟨hq0,hqt.le⟩ ⟨hf.1,le_rfl⟩ hqt).le) hclock

lemma rawLevelTime_eq_top_of_no_hit {κ : ℝ} {b : Driver} {z : ℂ} {s : ℝ}
    (hs : 0 ≤ s)
    (hn : ¬ ∃ T f, PositiveSolution κ b z T f ∧ rawClock κ b z T = s) :
    rawLevelTime κ b z s = ∞ := by
  apply top_unique
  apply le_sInf
  rintro _ ⟨q,hq,rfl,hqS,hqs⟩
  exfalso
  have hq0 : (0:ℝ) ≤ q := by exact_mod_cast hq.le
  let hf := surviving_flow_positiveSolution hq0 hqS
  have hr : s ∈ Icc (rawClock κ b z 0) (rawClock κ b z q) :=
    ⟨by simpa only [rawClock_zero] using hs,hqs.le⟩
  obtain ⟨T,hT,hTs⟩ := intermediate_value_Icc hq0 hf.rawClock_continuous hr
  exact hn ⟨T,flow κ b z,hf.restrict hT.1 hT.2,hTs⟩

end SLEExactGauge.LiteralTrace

namespace SLEExactGauge.LiteralTrace
open Set Filter Metric
open scoped NNReal Topology

lemma cutoffField_lipschitz (κ : ℝ) (b : Driver) {j : ℕ} (hj : 1 ≤ j) (t : ℝ) :
    LipschitzWith ⟨|a κ| *3/((j:ℝ)^(-(2:ℤ)))^2,by positivity⟩ (cutoffField κ b j t) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  simp only [dist_eq_norm,cutoffField_eq]
  exact Cutoff.field_sub_le (zpow_pos (by exact_mod_cast (Nat.zero_lt_of_lt hj)) _) _ _ _ _ _

 

lemma PositiveSolution.initial_eq_of_terminal_eq {κ : ℝ} {b : Driver} {z w : ℂ}
    {T : ℝ} {f g : ℝ → ℂ} (hf : PositiveSolution κ b z T f)
    (hg : PositiveSolution κ b w T g) (hfg : f T = g T) : z = w := by
  obtain ⟨j,hj,hjf⟩ := hf.exists_cutoff
  obtain ⟨k,hk,hkg⟩ := hg.exists_cutoff
  let n := max j k
  have hn : 1 ≤ n := hj.trans (le_max_left _ _)
  have hinj : (n:ℝ)⁻¹ ≤ (j:ℝ)⁻¹ :=
    inv_anti₀ (by exact_mod_cast (Nat.zero_lt_of_lt hj)) (by exact_mod_cast le_max_left j k)
  have hink : (n:ℝ)⁻¹ ≤ (k:ℝ)⁻¹ :=
    inv_anti₀ (by exact_mod_cast (Nat.zero_lt_of_lt hk)) (by exact_mod_cast le_max_right j k)
  have hd1 (t : ℝ) (ht : t ∈ Icc 0 T) :
      HasDerivWithinAt f (cutoffField κ b n t (f t)) (Icc 0 T) t := by
    rw [cutoffField_of_height κ b hn (hinj.trans (hjf t ht).le)]
    exact hf.2.2.2.2 t ht
  have hd2 (t : ℝ) (ht : t ∈ Icc 0 T) :
      HasDerivWithinAt g (cutoffField κ b n t (g t)) (Icc 0 T) t := by
    rw [cutoffField_of_height κ b hn (hink.trans (hkg t ht).le)]
    exact hg.2.2.2.2 t ht
  have he : EqOn f g (Icc 0 T) := by
    apply ODE_solution_unique_of_mem_Icc_left
      (v := cutoffField κ b n) (s := fun _ => univ)
      (K := ⟨|a κ| *3/((n:ℝ)^(-(2:ℤ)))^2,by positivity⟩)
      (fun t _ => (cutoffField_lipschitz κ b hn t).lipschitzOnWith)
      hf.2.1 _ (fun _ _ => mem_univ _) hg.2.1 _ (fun _ _ => mem_univ _) hfg
    · intro t ht
      exact (hd1 t ⟨ht.1.le,ht.2⟩).mono_of_mem_nhdsWithin
        (Filter.mem_of_superset (Icc_mem_nhdsLE ht.1) (Icc_subset_Icc_right ht.2))
    · intro t ht
      exact (hd2 t ⟨ht.1.le,ht.2⟩).mono_of_mem_nhdsWithin
        (Filter.mem_of_superset (Icc_mem_nhdsLE ht.1) (Icc_subset_Icc_right ht.2))
  exact hf.2.2.1.symm.trans ((he ⟨le_rfl,hf.1⟩).trans hg.2.2.1)

lemma flow_injOn (κ : ℝ) (b : Driver) {T : ℝ} (hT : 0 ≤ T) :
    InjOn (fun z => flow κ b z T) {z | Surviving κ b z T} := by
  intro z hz w hw he
  exact (surviving_flow_positiveSolution hT hz).initial_eq_of_terminal_eq
    (surviving_flow_positiveSolution hT hw) he

lemma inverseFlow_spec {κ : ℝ} {b : Driver} {T : ℝ} {w : ℂ}
    (hw : ∃ z, Surviving κ b z T ∧ flow κ b z T = w) :
    Surviving κ b (inverseFlow κ b T w) T ∧ flow κ b (inverseFlow κ b T w) T = w := by
  unfold inverseFlow
  rw [ite_eq_left hw]
  exact Classical.epsilon_spec hw

lemma inverseFlow_flow {κ : ℝ} {b : Driver} {T : ℝ} (hT : 0 ≤ T) {z : ℂ}
    (hz : Surviving κ b z T) : inverseFlow κ b T (flow κ b z T) = z := by
  have h := inverseFlow_spec (show ∃ w, Surviving κ b w T ∧ flow κ b w T = flow κ b z T from
    ⟨z,hz,rfl⟩)
  exact flow_injOn κ b hT h.1 hz h.2
end SLEExactGauge.LiteralTrace

namespace SLEExactGauge.LiteralTrace
open Set Filter Metric MeasureTheory
open scoped Topology

 
lemma reverse_height_formula {T : ℝ} {y r : ℝ → ℝ} (hT : 0 ≤ T)
    (hy : ContinuousOn y (Icc 0 T)) (hr : ContinuousOn r (Icc 0 T))
    (hd : ∀ t ∈ Icc 0 T, HasDerivWithinAt y (r t*y t) (Icc 0 T) t) :
    ∀ t ∈ Icc 0 T, y t = y 0 * Real.exp (∫ u in (0:ℝ)..t, r (timeClip T u)) := by
  let A (t : ℝ) := ∫ u in (0:ℝ)..t, r (timeClip T u)
  have hc : Continuous (fun u => r (timeClip T u)) :=
    hr.comp_continuous (continuous_timeClip T) (timeClip_mem hT)
  have hA (t : ℝ) : HasDerivAt A (r (timeClip T t)) t :=
    intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
      hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  have hA' : Continuous A := continuous_iff_continuousAt.mpr fun t => (hA t).continuousAt
  have hd0 (t : ℝ) (ht : t ∈ Icc 0 T) :
      HasDerivWithinAt (fun u => y u * Real.exp (-A u)) 0 (Icc 0 T) t := by
    have he := (hd t ht).mul ((hA t).neg.exp.hasDerivWithinAt)
    rw [timeClip_eq ht] at he
    convert! he using 1
    ring
  have hconst := constant_of_has_deriv_right_zero
    (hy.mul ((Real.continuous_exp.comp hA'.neg).continuousOn)) (fun t (ht : t ∈ Ico 0 T) =>
      (hd0 t ⟨ht.1,ht.2.le⟩).mono_of_mem_nhdsWithin
        (Filter.mem_of_superset (Icc_mem_nhdsGE ht.2) (Icc_subset_Icc_left ht.1)))
  intro t ht
  have he := hconst t ht
  dsimp only [Pi.mul_apply,Function.comp_def,Pi.neg_apply] at he
  have hA0 : A 0 = 0 := by simp [A]
  rw [hA0,neg_zero,Real.exp_zero,mul_one] at he
  calc
    y t = (y t * Real.exp (-A t))*Real.exp (A t) := by
      rw [mul_assoc,← Real.exp_add,neg_add_cancel,Real.exp_zero,mul_one]
    _ = y 0 * Real.exp (A t) := by rw [he]

lemma reverse_height_le {T : ℝ} {y r : ℝ → ℝ} (hT : 0 ≤ T)
    (hy : ContinuousOn y (Icc 0 T)) (hr : ContinuousOn r (Icc 0 T))
    (hd : ∀ t ∈ Icc 0 T, HasDerivWithinAt y (r t*y t) (Icc 0 T) t)
    (hy0 : 0 ≤ y 0) (hr0 : ∀ t ∈ Icc 0 T, 0 ≤ r t) (t : ℝ) (ht : t ∈ Icc 0 T) :
    y 0 ≤ y t := by
  rw [reverse_height_formula hT hy hr hd t ht]
  apply le_mul_of_one_le_right hy0
  apply Real.one_le_exp_iff.mpr
  apply intervalIntegral.integral_nonneg ht.1
  intro u _
  exact hr0 (timeClip T u) (timeClip_mem hT u)
end SLEExactGauge.LiteralTrace

namespace SLEExactGauge.Cutoff
open Set
lemma field_im (a q : ℝ) (b : ℝ → ℝ) (t : ℝ) (z : ℂ) :
    (field a q b t z).im = -a*z.im/denominator q (z-b t) := by
  simp [field,inverse,Complex.mul_im,Complex.div_ofReal_im]
  ring

lemma field_eq_div {q : ℝ} (hq : 0 < q) (a : ℝ) (b : ℝ → ℝ) (t : ℝ) (z : ℂ)
    (hz : q ≤ z.im) : field a q b t z = (a:ℂ)/(z-b t) := by
  have hqn : q ≤ ‖z-b t‖ := hz.trans (by simpa using Complex.im_le_norm (z-b t))
  have hsq : q^2 ≤ ‖z-b t‖^2 := pow_le_pow_left₀ hq.le hqn 2
  simp only [field,inverse,denominator,max_eq_left hsq,div_eq_mul_inv]
  rw [Complex.inv_def (z-b t)]
  simp only [Complex.normSq_eq_norm_sq,Complex.ofReal_inv,starRingEnd_apply]
end SLEExactGauge.Cutoff

namespace SLEExactGauge.LiteralTrace
open Set Filter Metric MeasureTheory
open scoped Topology

 

end SLEExactGauge.LiteralTrace
end
end
end
end

end OAI
