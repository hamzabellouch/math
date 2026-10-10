import Mathlib

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory Filter
open scoped Topology NNReal

namespace SharpIntegralFillings.SmoothCutoff
lemma deriv_transition_eq_zero {x : ℝ} (hx : x ∉ Icc (0:ℝ) 1) :
    deriv Real.smoothTransition x = 0 := by
  have hcases : x < 0 ∨ 1 < x := by simpa only [mem_Icc,not_and_or,not_le] using hx
  rcases hcases with hx | hx
  · have heq : Real.smoothTransition =ᶠ[𝓝 x] fun _ => (0:ℝ) := by
      filter_upwards [eventually_lt_nhds hx] with y hy
      exact Real.smoothTransition.zero_of_nonpos hy.le
    rw [heq.deriv_eq]
    simp
  · have heq : Real.smoothTransition =ᶠ[𝓝 x] fun _ => (1:ℝ) := by
      filter_upwards [eventually_gt_nhds hx] with y hy
      exact Real.smoothTransition.one_of_one_le hy.le
    rw [heq.deriv_eq]
    simp

lemma tsupport_deriv_transition :
    tsupport (deriv Real.smoothTransition) ⊆ Icc (0:ℝ) 1 := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  by_contra h
  exact hx (deriv_transition_eq_zero h)

lemma exists_derivative_bound : ∃ C : ℝ≥0, (∀ x, ‖deriv Real.smoothTransition x‖ ≤ C) ∧
    (∀ x, ‖deriv (deriv Real.smoothTransition) x‖ ≤ C) := by
  have hd : ContDiff ℝ (1:ℕ) (deriv Real.smoothTransition) :=
    (@Real.smoothTransition.contDiff 2).deriv'
  have hc := hd.continuous
  have hc2 := hd.continuous_deriv (by norm_num)
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc.continuousOn
  obtain ⟨D,hD⟩ := isCompact_Icc.exists_bound_of_continuousOn hc2.continuousOn
  refine ⟨⟨max 0 (max C D),le_max_left _ _⟩,?_,?_⟩
  · intro x
    by_cases hx : x ∈ Icc (0:ℝ) 1
    · exact (hC x hx).trans ((le_max_left C D).trans (le_max_right _ _))
    · rw [deriv_transition_eq_zero hx,norm_zero]
      exact le_max_left _ _
  · intro x
    by_cases hx : x ∈ Icc (0:ℝ) 1
    · exact (hD x hx).trans ((le_max_right C D).trans (le_max_right _ _))
    · have hz : deriv (deriv Real.smoothTransition) x = 0 := by
        exact deriv_of_notMem_tsupport (fun h => hx (tsupport_deriv_transition h))
      rw [hz,norm_zero]
      exact le_max_left _ _

lemma exists_lipschitz_transition : ∃ C : ℝ≥0, LipschitzWith C Real.smoothTransition ∧
    LipschitzWith C (deriv Real.smoothTransition) ∧
    ∀ x, |deriv Real.smoothTransition x| ≤ C := by
  obtain ⟨C,hC,hD⟩ := exists_derivative_bound
  refine ⟨C,?_,?_,?_⟩
  · apply lipschitzWith_of_nnnorm_deriv_le ((@Real.smoothTransition.contDiff 1).differentiable (by norm_num))
    exact fun x => hC x
  · apply lipschitzWith_of_nnnorm_deriv_le ((show ContDiff ℝ (1:ℕ) (deriv Real.smoothTransition) from (@Real.smoothTransition.contDiff 2).deriv').differentiable (by norm_num))
    exact fun x => hD x
  · simpa only [Real.norm_eq_abs] using hC

end SharpIntegralFillings.SmoothCutoff

end

end OAI
