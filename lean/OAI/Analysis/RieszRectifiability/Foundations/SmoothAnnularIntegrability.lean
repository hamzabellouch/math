import Mathlib
import OAI.Analysis.RieszRectifiability.Nets.SmoothAnnularCellComparison

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

theorem smoothAnnularTransform_integrable {d : ℕ} (n : ℕ) (hn : 1 ≤ n) (G : ℝ)
    (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth n G μ)
    (a : Ambient d) (r R : ℝ) (hr : 0 < r) (hrR : r ≤ R) :
    Integrable (fun y => smoothAnnularWeight a r R hr (hr.trans_le hrR) y • kernel n a y) μ := by
  let g := smoothAnnularWeight a r R hr (hr.trans_le hrR)
  have hgp := smoothAnnularWeight_properties n G μ hg a r R hr hrR
  have hi := truncation_integrable_of_globalGrowth n hn G μ hg g hgp.1 a (r / 2) (by positivity)
  have hE : MeasurableSet {y | r / 2 < dist a y} :=
    measurableSet_lt measurable_const (continuous_const.dist continuous_id).measurable
  have heq : {y | r / 2 < dist a y}.indicator (fun y => g y • kernel n a y) =
      (fun y => g y • kernel n a y) := by
    funext y
    by_cases hy : r / 2 < dist a y
    · have hyE : y ∈ {y : Ambient d | r / 2 < dist a y} := hy
      exact indicator_of_mem hyE _
    · have hzero : g y = 0 := by
        by_contra hne
        have hd := hgp.2.2.1 y hne
        linarith
      have hyE : y ∉ {y : Ambient d | r / 2 < dist a y} := hy
      rw [indicator_of_notMem hyE, hzero, zero_smul]
  rw [← heq]
  exact hi.integrable_indicator hE

theorem exists_unit_bounded_norm_direction {d : ℕ} (v : Ambient d) :
    ∃ e : Ambient d, ‖e‖ ≤ 1 ∧ inner ℝ e v = ‖v‖ := by
  by_cases hv : v = 0
  · refine ⟨0, by simp, ?_⟩
    simp [hv]
  · have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    refine ⟨‖v‖⁻¹ • v, ?_, ?_⟩
    · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg v)),
        inv_mul_cancel₀ hn]
    · rw [real_inner_smul_left, real_inner_self_eq_norm_sq, pow_two]
      field_simp

end

end RieszRectifiability

end OAI
