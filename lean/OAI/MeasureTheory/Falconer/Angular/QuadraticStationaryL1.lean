import OAI.MeasureTheory.Falconer.Angular.QuadraticStationaryExpansion
import OAI.MeasureTheory.Falconer.Fourier.SchwartzFourierMomentBounds

namespace OAI

namespace PlanarFalconer
open MeasureTheory
open scoped FourierTransform SchwartzMap

 theorem schwartz_inverse_fourier_moment_bound (φ : 𝓢(ℝ,ℂ)) (n : ℕ) :
    (∫ ξ : ℝ, ‖ξ‖^n*‖𝓕⁻ φ ξ‖) ≤
      (fourierDerivativeL1 φ n + fourierDerivativeL1 φ (n+2)) *
        ∫ ξ : ℝ, (1+ξ^2)⁻¹ := by
  have hpoint (ξ : ℝ) : 𝓕⁻ φ ξ = 𝓕 φ (-ξ) := rfl
  simp_rw [hpoint]
  have he := integral_neg_eq_self (fun ξ : ℝ => ‖ξ‖^n*‖𝓕 φ ξ‖) volume
  simp only [norm_neg] at he
  rw [he]
  exact schwartz_fourier_moment_bound φ n

 theorem quadratic_stationary_expansion_L1 {b : ℝ} (hb : 0 < b) (φ : 𝓢(ℝ,ℂ)) (n : ℕ) :
    ‖(∫ x : ℝ, Complex.exp (-((b:ℂ)*Complex.I)*(x:ℂ)^2)*φ x) -
      fresnelCoefficient b * quadraticExpansion φ n b‖ ≤
    ((Real.pi/b)^(1/2:ℝ) * ((Real.pi^2/b)^(n+1)/(n.factorial:ℝ))) *
      ((fourierDerivativeL1 φ (2*(n+1)) + fourierDerivativeL1 φ (2*(n+1)+2)) *
        ∫ ξ : ℝ, (1+ξ^2)⁻¹) := by
  apply (quadratic_stationary_expansion hb φ n).trans
  apply mul_le_mul_of_nonneg_left (schwartz_inverse_fourier_moment_bound φ (2*(n+1)))
  positivity

 theorem quadraticExpansion_zero (φ : 𝓢(ℝ,ℂ)) (b : ℝ) : quadraticExpansion φ 0 b = φ 0 := by
  simp [quadraticExpansion]

 theorem fresnelCoefficient_ne_zero {b : ℝ} (hb : 0 < b) : fresnelCoefficient b ≠ 0 := by
  rw [← norm_pos_iff,fresnelCoefficient_norm hb]
  positivity

end PlanarFalconer

end OAI
