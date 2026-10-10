import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Topology.MetricSpace.Pseudo.Defs

namespace OAI

namespace Generator

/-! Scalar error budgets and lower bounds for perturbation correlation. -/

theorem exists_correlation_parameter {s : ℝ} (hs : 0 < s) :
    ∃ α : ℝ, 0 < α ∧ α < 1 / 4 ∧ α < s / 32 := by
  refine ⟨min (1 / 8) (s / 64), lt_min (by norm_num) (by positivity), ?_, ?_⟩
  · exact lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  · exact lt_of_le_of_lt (min_le_right _ _) (by linarith)

/-- The strict nonlinear error budget in the manuscript, with its original constants. -/
theorem correlation_error_budget {s α : ℝ} (hs : 0 < s) (hα : 0 < α)
    (hquarter : α < 1 / 4) (hsmall : α < s / 32) :
    s * (4 * α ^ 2 / (1 - 2 * α)) < α * s ^ 2 / 4 := by
  have hden : 0 < 1 - 2 * α := by linarith
  have hnum : 0 < 4 * α ^ 2 := by positivity
  have hquot : 4 * α ^ 2 / (1 - 2 * α) < 8 * α ^ 2 := by
    apply (div_lt_iff₀ hden).mpr
    nlinarith [mul_pos hnum (show 0 < 1 - 4 * α by linarith)]
  have hfirst := mul_lt_mul_of_pos_left hquot hs
  have hsecond : 8 * s * α ^ 2 < α * s ^ 2 / 4 := by
    have hp : 0 < α * s := mul_pos hα hs
    nlinarith [mul_pos hp (show 0 < s - 32 * α by linarith)]
  nlinarith

/-- Triangle-inequality step converting the correlation error into a lower bound. -/
theorem correlation_lower_bound {s α δ : ℝ} (hs : 0 < s) (hα : 0 < α)
    (hquarter : α < 1 / 4) (hsmall : α < s / 32) {c : ℂ}
    (hc : ‖c - ((α * s ^ 2 / 2 : ℝ) : ℂ)‖ ≤
      s * (4 * α ^ 2 / (1 - 2 * α)) + δ) :
    α * s ^ 2 / 4 - δ ≤ ‖c‖ := by
  have he := correlation_error_budget hs hα hquarter hsmall
  have hcenter : 0 ≤ α * s ^ 2 / 2 := by positivity
  have ht := norm_sub_le c (c - ((α * s ^ 2 / 2 : ℝ) : ℂ))
  rw [sub_sub_cancel, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hcenter] at ht
  linarith

/-! The numerical and topological contradiction for a continuous correlated sequence. -/
open Filter Topology

theorem no_continuous_correlated_sequence {X : Type*} [TopologicalSpace X]
    (F : X → ℝ) {x : X} (hF : ContinuousAt F x) (hzero : F x = 0)
    (u : ℕ → X) (hu : Tendsto u atTop (𝓝 x))
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0)) (c : ℕ → ℂ)
    {s α : ℝ} (hs : 0 < s) (hα : 0 < α) (hq : α < 1 / 4) (hsmall : α < s / 32)
    (hc : ∀ n, ‖c n - ((α * s ^ 2 / 2 : ℝ) : ℂ)‖ ≤
      s * (4 * α ^ 2 / (1 - 2 * α)) + δ n)
    (hproj : ∀ n, ‖c n‖ ≤ F (u n)) : False := by
  have hFu : Tendsto (fun n => F (u n)) atTop (𝓝 0) := by
    simpa only [hzero, Function.comp_def] using hF.tendsto.comp hu
  have hpos : 0 < α * s ^ 2 / 8 := by positivity
  have hnearF := Metric.tendsto_nhds.mp hFu (α * s ^ 2 / 8) hpos
  have hnearδ := Metric.tendsto_nhds.mp hδ (α * s ^ 2 / 8) hpos
  obtain ⟨n, hnF, hnδ⟩ := (hnearF.and hnearδ).exists
  rw [Real.dist_eq, sub_zero] at hnF hnδ
  have hlow := correlation_lower_bound hs hα hq hsmall (hc n)
  have hupp := hproj n
  have hFlt := (abs_lt.mp hnF).2
  have hδlt := (abs_lt.mp hnδ).2
  linarith

end Generator

end OAI
