import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.MeasureBounds

namespace OAI

/-!
# Analytic bounds for Schwartz test functions

Integration by parts shows that a Schwartz directional derivative has zero
integral. The zeroth Schwartz seminorms of a test function and its Fréchet
derivative also give global boundedness and Lipschitz constants.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set SchwartzMap
open scoped NNReal LineDeriv ContDiff

theorem schwartz_directional_derivative_integral_zero {d : ℕ}
    (g : 𝓢(Ambient d, ℝ)) (v : Ambient d) :
    (∫ x, ∂_{v} g x) = 0 := by
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := volume) (f := fun _ : Ambient d => (1 : ℝ)) (g := (g : Ambient d → ℝ)) (v := v)
    (by simp) (by simpa only [one_mul] using! (∂_{v} g).integrable)
    (by simpa only [one_mul] using! g.integrable)
    (fun _ _ => differentiableAt_const _) (fun _ _ => g.differentiableAt)
  simpa only [one_mul, fderiv_const_apply, zero_apply, zero_mul,
    integral_zero, neg_zero, ← lineDerivOp_apply_eq_fderiv] using! h

theorem schwartz_real_bounded_lipschitz {d : ℕ} (g : 𝓢(Ambient d, ℝ)) :
    ∃ L B : ℝ≥0, LipschitzWith L g ∧ ∀ x, |g x| ≤ (B : ℝ) := by
  let G := fderivCLM ℝ (Ambient d) ℝ g
  let L : ℝ≥0 := Real.toNNReal (SchwartzMap.seminorm ℝ 0 0 G)
  let B : ℝ≥0 := Real.toNNReal (SchwartzMap.seminorm ℝ 0 0 g)
  refine ⟨L, B, lipschitzWith_of_nnnorm_fderiv_le g.differentiable ?_, ?_⟩
  · intro x
    have h : ‖fderiv ℝ g x‖ ≤ (L : ℝ) :=
      (G.norm_le_seminorm ℝ x).trans (Real.le_coe_toNNReal _)
    exact_mod_cast h
  · intro x
    exact (g.norm_le_seminorm ℝ x).trans (Real.le_coe_toNNReal _)

theorem compact_smooth_directional_test_admissible {d : ℕ}
    (g : Ambient d → ℝ) (hc : HasCompactSupport g) (hg : ContDiff ℝ ∞ g)
    (v : Ambient d) :
    ∃ L B : ℝ≥0,
      HasCompactSupport (fun x => fderiv ℝ g x v) ∧
      LipschitzWith L (fun x => fderiv ℝ g x v) ∧
      (∀ x, |fderiv ℝ g x v| ≤ (B : ℝ)) ∧
      Integrable (fun x => fderiv ℝ g x v) ∧
      (∫ x, fderiv ℝ g x v) = 0 := by
  let G := hc.toSchwartzMap hg
  obtain ⟨L, B, hL, hB⟩ := schwartz_real_bounded_lipschitz (∂_{v} G)
  exact ⟨L, B, hc.fderiv_apply ℝ v, hL, hB, (∂_{v} G).integrable,
    schwartz_directional_derivative_integral_zero G v⟩

end

end RieszRectifiability

end OAI
