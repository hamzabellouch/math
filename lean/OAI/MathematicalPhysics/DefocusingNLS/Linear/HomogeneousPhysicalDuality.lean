import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousFourierPairing
import Mathlib.MeasureTheory.Integral.Prod

namespace OAI

/-! # Exact Fourier normalization for physical Schwartz tests -/

open MeasureTheory
open scoped SchwartzMap RealInnerProductSpace

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem integral_inverseRadianFourier_test (f : E → ℂ) (hf : Integrable f)
    (ψ : 𝓢(E, ℂ)) :
    (∫ y : E, ψ y * inverseRadianFourier f y) =
      (((2 * Real.pi) ^ (12 : ℕ))⁻¹ : ℂ) *
        ∫ ξ : E, f ξ * radianFourierKernel ψ (-ξ) := by
  let c : ℂ := (((2 * Real.pi) ^ (12 : ℕ))⁻¹ : ℝ)
  let G := fun (y ξ : E) => ψ y * (Complex.exp ((⟪ξ, y⟫ : ℝ) * Complex.I) * f ξ)
  have hG : Integrable (Function.uncurry G) (volume.prod volume) := by
    apply (ψ.integrable.norm.mul_prod hf.norm).mono'
    · have hp : Continuous (fun p : E × E => Complex.exp ((⟪p.2, p.1⟫ : ℝ) * Complex.I)) := by
        fun_prop
      exact ψ.continuous.aestronglyMeasurable.comp_fst.mul
        (hp.aestronglyMeasurable.mul hf.aestronglyMeasurable.comp_snd)
    · filter_upwards [] with p
      simp only [Function.uncurry, G, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, le_refl]
  have he (y : E) : ψ y * inverseRadianFourier f y = c * ∫ ξ : E, G y ξ := by
    unfold inverseRadianFourier radianFourierIntegral
    simp only [inner_neg_right, neg_neg]
    change ψ y * (c * ∫ ξ : E, Complex.exp ((⟪ξ, y⟫ : ℝ) * Complex.I) * f ξ) =
      c * ∫ ξ : E, ψ y * (Complex.exp ((⟪ξ, y⟫ : ℝ) * Complex.I) * f ξ)
    rw [integral_const_mul]
    ring
  have ht (ξ : E) : (∫ y : E, G y ξ) = f ξ * radianFourierKernel ψ (-ξ) := by
    rw [radianFourierKernel_apply, radianFourierIntegral, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with y
    simp only [G, inner_neg_right, neg_neg]
    rw [real_inner_comm ξ y]
    ring
  calc
    _ = ∫ y : E, c * ∫ ξ : E, G y ξ := integral_congr_ae (ae_of_all _ he)
    _ = c * ∫ y : E, ∫ ξ : E, G y ξ := integral_const_mul _ _
    _ = c * ∫ ξ : E, ∫ y : E, G y ξ := congrArg (c * ·) (integral_integral_swap hG)
    _ = c * ∫ ξ : E, f ξ * radianFourierKernel ψ (-ξ) := by simp only [ht]
    _ = _ := by simp only [c, Complex.ofReal_inv, Complex.ofReal_pow,
      Complex.ofReal_mul, Complex.ofReal_ofNat]

end DefocusingNLS

end OAI
