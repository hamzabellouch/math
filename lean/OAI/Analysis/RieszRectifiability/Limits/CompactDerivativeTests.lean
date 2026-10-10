import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.MeasureBounds

namespace OAI

/-!
# Compactly supported directional derivative tests

Directional derivatives of smooth compactly supported functions remain
continuous and compactly supported, with support inside that of the original
function. Integration by parts against the constant function shows that their
volume integral vanishes, making them mean-zero test functions.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set
open scoped ContDiff

theorem compact_smooth_directional_derivative_test {n : ℕ}
    (ψ : Ambient n → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) (e : Ambient n) :
    Continuous (fun x => fderiv ℝ ψ x e) ∧
      HasCompactSupport (fun x => fderiv ℝ ψ x e) ∧
      tsupport (fun x => fderiv ℝ ψ x e) ⊆ tsupport ψ ∧
      Integrable (fun x => fderiv ℝ ψ x e) volume ∧
      (∫ x, fderiv ℝ ψ x e) = 0 := by
  have hD : Continuous (fun x => fderiv ℝ ψ x e) :=
    (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hDc : HasCompactSupport (fun x => fderiv ℝ ψ x e) := hψc.fderiv_apply ℝ e
  have hDI : Integrable (fun x => fderiv ℝ ψ x e) volume := hD.integrable_of_hasCompactSupport hDc
  refine ⟨hD, hDc, tsupport_fderiv_apply_subset ℝ e, hDI, ?_⟩
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure (Ambient n))) (f := fun _ => (1 : ℝ)) (g := ψ) (v := e)
    (by simp only [fderiv_const_apply, zero_apply, zero_mul]; exact integrable_zero _ _ _)
    (by simpa only [one_mul] using! hDI)
    (by simpa only [one_mul] using! hψ.continuous.integrable_of_hasCompactSupport hψc)
    (fun x _ => differentiableAt_const (1 : ℝ))
    (fun x _ => hψ.differentiable (by simp) x)
  simpa only [one_mul, fderiv_const_apply, zero_apply, zero_mul, integral_zero, neg_zero] using! h

end

end RieszRectifiability

end OAI
