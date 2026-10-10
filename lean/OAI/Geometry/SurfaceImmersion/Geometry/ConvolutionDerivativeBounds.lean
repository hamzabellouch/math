import OAI.Geometry.SurfaceImmersion.Correction.SmoothingDerivativeBounds

namespace OAI

/-! Differentiating the compact kernel gives derivative gains without using
uncontrolled derivatives of the input. -/
noncomputable section
open scoped ContDiff Convolution

universe u v w
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open MeasureTheory ContinuousLinearMap
open JetPolynomial (Base)

variable {E : Type u} {F : Type v} {H : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- All derivatives may be placed on the compactly supported kernel. -/
theorem convolution_iterated_norm_le (L : E →L[ℝ] F →L[ℝ] H) (n : ℕ)
    {f : Base → E} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    {g : Base → F} (hg : Continuous g) {C : ℝ} (hb : ∀ x, ‖g x‖ ≤ C) (x : Base) :
    ‖iteratedFDeriv ℝ n (f ⋆[L, volume] g) x‖ ≤
      ‖L‖ * (∫ y, ‖iteratedFDeriv ℝ n f y‖) * C := by
  have hC : 0 ≤ C := (norm_nonneg (g 0)).trans (hb 0)
  induction n generalizing E H with
  | zero =>
    simp only [norm_iteratedFDeriv_zero]
    have hi := (hf.continuous.integrable_of_hasCompactSupport (μ := volume) hfc).norm
    change ‖∫ y, L (f y) (g (x - y))‖ ≤ _
    calc
      _ ≤ ∫ y, ‖L‖ * ‖f y‖ * C := by
        apply norm_integral_le_of_norm_le ((hi.const_mul ‖L‖).mul_const C)
        exact Filter.Eventually.of_forall fun y =>
          (L.le_opNorm₂ _ _).trans (mul_le_mul_of_nonneg_left (hb (x - y))
            (mul_nonneg (norm_nonneg L) (norm_nonneg (f y))))
      _ = _ := by rw [integral_mul_const, integral_const_mul]
  | succ n ih =>
    rw [← norm_iteratedFDeriv_fderiv]
    have heq : fderiv ℝ (f ⋆[L, volume] g) =
        (fderiv ℝ f ⋆[L.precompL Base, volume] g) := by
      funext y
      exact (hfc.hasFDerivAt_convolution_left L (hf.of_le (by simp)) hg.locallyIntegrable y).fderiv
    rw [heq]
    have h := ih (L.precompL Base) (hf.fderiv_right (m := ∞) (by simp))
      (hfc.fderiv ℝ)
    simp_rw [norm_iteratedFDeriv_fderiv] at h
    apply h.trans
    gcongr
    exact L.norm_precompL_le Base

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
