import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.KernelBasic
import OAI.Analysis.RieszRectifiability.Limits.CompactWeakConvergence

namespace OAI

/-!
# Ball-mass bounds through compact test functions

Compactly supported continuous cutoffs compare test integrals with ball masses from above
and below. These comparisons pass uniform growth bounds through convergence against
compact test functions.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal CompactlySupported

theorem compact_test_integral_le_ball_mass {d : ℕ} (μ : Measure (Ambient d))
    [IsFiniteMeasureOnCompacts μ] (f : C_c(Ambient d, ℝ)) (a : Ambient d) (R : ℝ)
    (hf : ∀ x, f x ≤ 1) (hz : ∀ x, x ∉ ball a R → f x = 0) :
    (∫ x, f x ∂μ) ≤ μ.real (ball a R) := by
  have : IsFiniteMeasure (μ.restrict (ball a R)) := isFiniteMeasure_restrict.mpr
    ((measure_mono ball_subset_closedBall).trans_lt (isCompact_closedBall a R).measure_lt_top).ne
  have hi : Integrable ((ball a R).indicator (fun _ : Ambient d => (1 : ℝ))) μ :=
    (integrable_indicator_iff measurableSet_ball).mpr (integrable_const 1)
  have h := integral_mono (f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport) hi
    (fun x => by
      by_cases hx : x ∈ ball a R
      · simpa only [indicator_of_mem hx] using! hf x
      · simpa only [indicator_of_notMem hx] using! (hz x hx).le)
  simpa only [integral_indicator measurableSet_ball, integral_const, smul_eq_mul,
    Measure.real, Measure.restrict_apply_univ, mul_one] using! h

theorem ball_mass_le_compact_test_integral {d : ℕ} (μ : Measure (Ambient d))
    [IsFiniteMeasureOnCompacts μ] (f : C_c(Ambient d, ℝ)) (a : Ambient d) (r : ℝ)
    (hf : ∀ x, 0 ≤ f x) (hone : ∀ x ∈ ball a r, f x = 1) :
    μ.real (ball a r) ≤ ∫ x, f x ∂μ := by
  have : IsFiniteMeasure (μ.restrict (ball a r)) := isFiniteMeasure_restrict.mpr
    ((measure_mono ball_subset_closedBall).trans_lt (isCompact_closedBall a r).measure_lt_top).ne
  have hi : Integrable ((ball a r).indicator (fun _ : Ambient d => (1 : ℝ))) μ :=
    (integrable_indicator_iff measurableSet_ball).mpr (integrable_const 1)
  have h := integral_mono hi (f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport)
    (fun x => by
      by_cases hx : x ∈ ball a r
      · simpa only [indicator_of_mem hx] using! (hone x hx).ge
      · simpa only [indicator_of_notMem hx] using! hf x)
  simpa only [integral_indicator measurableSet_ball, integral_const, smul_eq_mul,
    Measure.real, Measure.restrict_apply_univ, mul_one] using! h

theorem compactTestConvergence_upper_growth {d : ℕ} (n : ℕ)
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hlocal : CompactTestConvergence μ ν) (C : ℝ) (hg : ∀ j, GlobalUpperGrowth n C (μ j)) :
    GlobalUpperGrowth n (C * 2 ^ n) ν := by
  have hC : 0 ≤ C := (hg 0).1
  refine ⟨mul_nonneg hC (by positivity), ?_⟩
  intro a r hr
  have hsub : closedBall a r ⊆ ball a (2 * r) := closedBall_subset_ball (by linarith)
  obtain ⟨f, hone, hzero, hcomp, hbounds⟩ := exists_continuous_one_zero_of_isCompact
    (isCompact_closedBall a r) isOpen_ball.isClosed_compl (disjoint_compl_right_iff_subset.mpr hsub)
  let F : C_c(Ambient d, ℝ) := ⟨f, hcomp⟩
  have hfi : ∀ j, (∫ x, F x ∂μ j) ≤ C * (2 * r) ^ n := by
    intro j
    apply (compact_test_integral_le_ball_mass (μ j) F a (2 * r)
      (fun x => (hbounds x).2) (fun x hx => hzero hx)).trans
    exact ENNReal.toReal_le_of_le_ofReal (mul_nonneg hC (by positivity))
      ((hg j).2 a (2 * r) (by positivity))
  have hlim : (∫ x, F x ∂ν) ≤ C * (2 * r) ^ n :=
    le_of_tendsto (hlocal F) (Eventually.of_forall hfi)
  have hball : ν.real (ball a r) ≤ C * (2 * r) ^ n :=
    (ball_mass_le_compact_test_integral ν F a r (fun x => (hbounds x).1)
      (fun _ hx => hone (ball_subset_closedBall hx))).trans hlim
  have hfinite : ν (ball a r) ≠ ∞ :=
    ((measure_mono ball_subset_closedBall).trans_lt (isCompact_closedBall a r).measure_lt_top).ne
  apply (ENNReal.le_ofReal_iff_toReal_le hfinite (by positivity)).mpr
  simpa only [mul_pow, mul_assoc] using! hball

end

end RieszRectifiability

end OAI
