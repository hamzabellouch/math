import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousCZero

namespace OAI

/-! # Inversion with the exact radian Fourier normalization -/

open MeasureTheory
open scoped FourierTransform

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem inverseRadianFourier_radianFourier (f : E → ℂ) (y : E) :
    inverseRadianFourier (radianFourierIntegral f) y = (𝓕⁻ (𝓕 f)) y := by
  have hp : 0 < 2 * Real.pi := by positivity
  have he : radianFourierIntegral f = (fun ξ => 𝓕 f ((2 * Real.pi)⁻¹ • ξ)) :=
    funext (radianFourierIntegral_eq_fourier f)
  unfold inverseRadianFourier
  rw [he, radianFourier_dilation (2 * Real.pi) hp, radianFourierIntegral_eq_fourier]
  simp only [smul_smul, inv_mul_cancel₀ hp.ne', one_smul]
  rw [← Real.fourierInv_eq_fourier_neg (𝓕 f) y]
  change ((((2 * Real.pi) ^ (12 : ℕ))⁻¹ : ℝ) : ℂ) *
    ((((2 * Real.pi) ^ (12 : ℕ) : ℝ) : ℂ) * (𝓕⁻ (𝓕 f)) y) = (𝓕⁻ (𝓕 f)) y
  rw [← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ (pow_ne_zero 12 hp.ne'),
    Complex.ofReal_one, one_mul]

theorem inverseRadianFourier_radianFourier_of_integrable {f : E → ℂ}
    (hc : Continuous f) (hf : Integrable f) (hF : Integrable (radianFourierIntegral f)) (y : E) :
    inverseRadianFourier (radianFourierIntegral f) y = f y := by
  have hF' : Integrable (𝓕 f) := by
    have h := hF.comp_smul (by positivity : 2 * Real.pi ≠ 0)
    convert h using 1
    funext ξ
    rw [radianFourierIntegral_eq_fourier]
    simp only [smul_smul, inv_mul_cancel₀ (by positivity : 2 * Real.pi ≠ 0), one_smul]
  rw [inverseRadianFourier_radianFourier]
  exact congrFun (hc.fourierInv_fourier_eq hf hF') y

end DefocusingNLS

end OAI
