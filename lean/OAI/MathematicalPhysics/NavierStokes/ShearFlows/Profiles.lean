import OAI.MathematicalPhysics.NavierStokes.ShearFlows.Model

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff Topology

namespace ShearFlows
def smoothRamp (a b t : ℝ) : ℝ := Real.smoothTransition ((t - a) / (b - a))

theorem smoothRamp_smooth (a b : ℝ) : ContDiff ℝ ∞ (smoothRamp a b) :=
  Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)

theorem smoothRamp_range (a b t : ℝ) : smoothRamp a b t ∈ Icc (0 : ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

theorem smoothRamp_monotone {a b : ℝ} (hab : a < b) : Monotone (smoothRamp a b) := by
  intro s t hst
  exact Real.smoothTransition.monotone
    (div_le_div_of_nonneg_right (sub_le_sub_right hst _) (sub_pos.mpr hab).le)

theorem smoothRamp_before {a b t : ℝ} (hab : a < b) (ht : t ≤ a) :
    smoothRamp a b t = 0 :=
  Real.smoothTransition.zero_of_nonpos
    (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht) (sub_pos.mpr hab).le)

theorem smoothRamp_after {a b t : ℝ} (hab : a < b) (ht : b ≤ t) :
    smoothRamp a b t = 1 := by
  apply Real.smoothTransition.one_of_one_le
  rw [le_div_iff₀ (sub_pos.mpr hab)]
  linarith

def smoothPulse (a b : ℝ) : ℝ → ℝ := deriv (smoothRamp a b)

theorem smoothPulse_smooth (a b : ℝ) : ContDiff ℝ ∞ (smoothPulse a b) :=
  (contDiff_infty_iff_deriv.mp (smoothRamp_smooth a b)).2

theorem smoothPulse_nonneg {a b : ℝ} (hab : a < b) (t : ℝ) :
    0 ≤ smoothPulse a b t := (smoothRamp_monotone hab).deriv_nonneg

theorem smoothPulse_before {a b t : ℝ} (hab : a < b) (ht : t ≤ a) :
    smoothPulse a b t = 0 := by
  apply IsLocalMin.deriv_eq_zero
  apply Filter.Eventually.of_forall
  intro x
  rw [smoothRamp_before hab ht]
  exact (smoothRamp_range a b x).1

theorem smoothPulse_after {a b t : ℝ} (hab : a < b) (ht : b ≤ t) :
    smoothPulse a b t = 0 := by
  apply IsLocalMax.deriv_eq_zero
  apply Filter.Eventually.of_forall
  intro x
  rw [smoothRamp_after hab ht]
  exact (smoothRamp_range a b x).2

theorem smoothPulse_integral {a b : ℝ} (hab : a < b) :
    (∫ t in a..b, smoothPulse a b t) = 1 := by
  rw [smoothPulse, intervalIntegral.integral_deriv_eq_sub]
  · rw [smoothRamp_after hab le_rfl, smoothRamp_before hab le_rfl]
    norm_num
  · intro t _
    exact (smoothRamp_smooth a b).differentiable (by simp) t
  · exact (smoothPulse_smooth a b).continuous.intervalIntegrable _ _

def closedCutoff (a b c d t : ℝ) : ℝ :=
  smoothRamp a b t * smoothRamp (-d) (-c) (-t)

theorem closedCutoff_smooth (a b c d : ℝ) : ContDiff ℝ ∞ (closedCutoff a b c d) :=
  (smoothRamp_smooth a b).mul ((smoothRamp_smooth (-d) (-c)).comp contDiff_neg)

theorem closedCutoff_range (a b c d t : ℝ) : closedCutoff a b c d t ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨ha, hb⟩ := smoothRamp_range a b t
  obtain ⟨hc, hd⟩ := smoothRamp_range (-d) (-c) (-t)
  exact ⟨mul_nonneg ha hc, by simpa [closedCutoff] using mul_le_mul hb hd hc (by norm_num : (0:ℝ) ≤ 1)⟩

theorem closedCutoff_plateau {a b c d t : ℝ} (hab : a < b) (hcd : c < d)
    (ht : t ∈ Icc b c) : closedCutoff a b c d t = 1 := by
  rw [closedCutoff, smoothRamp_after hab ht.1,
    smoothRamp_after (neg_lt_neg hcd) (neg_le_neg ht.2)]
  norm_num

theorem closedCutoff_before {a b c d t : ℝ} (hab : a < b) (ht : t ≤ a) :
    closedCutoff a b c d t = 0 := by
  simp [closedCutoff, smoothRamp_before hab ht]

theorem closedCutoff_after {a b c d t : ℝ} (hcd : c < d) (ht : d ≤ t) :
    closedCutoff a b c d t = 0 := by
  simp [closedCutoff, smoothRamp_before (neg_lt_neg hcd) (neg_le_neg ht)]

theorem closedCutoff_compactSupport {a b c d : ℝ} (hab : a < b) (hcd : c < d) :
    HasCompactSupport (closedCutoff a b c d) := by
  apply HasCompactSupport.intro isCompact_Icc (K := Icc a d)
  intro t ht
  by_cases ha : t < a
  · exact closedCutoff_before hab ha.le
  · exact closedCutoff_after hcd
      (le_of_not_ge (fun hd => ht ⟨le_of_not_gt ha, hd⟩))

def derivativeMask (a b c d p : ℝ) : ℝ → ℝ :=
  deriv (fun t => (t - p) * closedCutoff a b c d t)

theorem derivativeMask_smooth (a b c d p : ℝ) :
    ContDiff ℝ ∞ (derivativeMask a b c d p) :=
  (contDiff_infty_iff_deriv.mp
    ((contDiff_id.sub contDiff_const).mul (closedCutoff_smooth a b c d))).2

theorem derivativeMask_compactSupport {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (p : ℝ) : HasCompactSupport (derivativeMask a b c d p) :=
  ((closedCutoff_compactSupport hab hcd).mul_left (f := fun t => t - p)).deriv

theorem derivativeMask_plateau {a b c d p t : ℝ} (hab : a < b) (hcd : c < d)
    (ht : t ∈ Ioo b c) : derivativeMask a b c d p t = 1 := by
  have heq : (fun s => (s - p) * closedCutoff a b c d s) =ᶠ[nhds t]
      (fun s => s - p) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    rw [closedCutoff_plateau hab hcd ⟨hs.1.le, hs.2.le⟩, mul_one]
  exact (((hasDerivAt_id t).sub_const p).congr_of_eventuallyEq heq).deriv

theorem derivativeMask_integral_zero {a b c d A D : ℝ} (hab : a < b) (hcd : c < d)
    (hA : A ≤ a) (hD : d ≤ D) (p : ℝ) :
    (∫ t in A..D, derivativeMask a b c d p t) = 0 := by
  rw [derivativeMask, intervalIntegral.integral_deriv_eq_sub]
  · rw [closedCutoff_before hab hA, closedCutoff_after hcd hD]
    ring
  · intro t _
    exact (((contDiff_id.sub contDiff_const).mul
      (closedCutoff_smooth a b c d)).differentiable (by simp)) t
  · exact (derivativeMask_smooth a b c d p).continuous.intervalIntegrable _ _

def stageStart (j : Fin 7) : ℚ := (2 * (j : ℕ) + 1) / 16

def stageFinish (j : Fin 7) : ℚ := (2 * (j : ℕ) + 2) / 16

theorem stage_intervals (j : Fin 7) :
    0 < stageStart j ∧ stageStart j < stageFinish j ∧ stageFinish j < 1 := by
  fin_cases j <;> norm_num [stageStart, stageFinish]

theorem stage_ordered (i j : Fin 7) (hij : i < j) : stageFinish i < stageStart j := by
  have hi : (i : ℕ) + 1 ≤ j := hij
  have hi' : (i : ℚ) + 1 ≤ j := by exact_mod_cast hi
  dsimp [stageFinish, stageStart]
  linarith

def standardSchedule : Schedule where
  start := stageStart
  finish := stageFinish
  intervals := stage_intervals
  ordered := stage_ordered
  progress j := smoothRamp (stageStart j) (stageFinish j)
  smooth j := smoothRamp_smooth _ _
  monotone j := smoothRamp_monotone (by exact_mod_cast (stage_intervals j).2.1)
  range j t := smoothRamp_range _ _ t
  before j t ht := smoothRamp_before (by exact_mod_cast (stage_intervals j).2.1) ht
  after j t ht := smoothRamp_after (by exact_mod_cast (stage_intervals j).2.1) ht

theorem standardPulses_separated :
    ∀ t i j, smoothPulse (stageStart i) (stageFinish i) t ≠ 0 →
      smoothPulse (stageStart j) (stageFinish j) t ≠ 0 → i = j := by
  intro t i j hi hj
  have inside (k : Fin 7)
      (hk : smoothPulse (stageStart k) (stageFinish k) t ≠ 0) :
      (stageStart k : ℝ) < t ∧ t < (stageFinish k : ℝ) := by
    have hab : (stageStart k : ℝ) < stageFinish k := by
      exact_mod_cast (stage_intervals k).2.1
    exact ⟨lt_of_not_ge (fun h => hk (smoothPulse_before hab h)),
      lt_of_not_ge (fun h => hk (smoothPulse_after hab h))⟩
  have hi' := inside i hi
  have hj' := inside j hj
  rcases lt_trichotomy i j with hij | hij | hij
  · have ho : (stageFinish i : ℝ) < stageStart j := by exact_mod_cast stage_ordered i j hij
    linarith
  · exact hij
  · have ho : (stageFinish j : ℝ) < stageStart i := by exact_mod_cast stage_ordered j i hij
    linarith

end ShearFlows

end

end OAI
