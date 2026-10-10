import OAI.MeasureTheory.Falconer.Slicing.OscillatoryGaussian
import OAI.MeasureTheory.Falconer.Fourier.StationaryInverse
import OAI.MeasureTheory.Falconer.Fourier.OscillatoryTaylor

namespace OAI

/-! Exact frequency and phase normalization for the negative quadratic form. -/

namespace Falconer
open MeasureTheory
open scoped FourierTransform SchwartzMap

theorem normalized_gaussian_coefficient (n : ℕ) {Λ : ℝ} (hΛ : 0 < Λ) :
    ((Λ^((n : ℝ)/2) : ℝ) : ℂ) *
      (((Real.pi/(Λ/2))^((n : ℝ)/2) : ℝ) *
        Complex.exp (-(Real.pi : ℂ)*(n : ℂ)/4*Complex.I)) =
      sphereStationaryConstant n := by
  rw [sphereStationaryConstant, ← mul_assoc, ← Complex.ofReal_mul]
  congr 1
  rw [← Real.mul_rpow hΛ.le (by positivity)]
  congr 1
  field_simp [hΛ.ne']

theorem normalized_gaussian_identity {n : ℕ} (hn : 0 < n) {Λ : ℝ} (hΛ : 0 < Λ)
    (φ : 𝓢(Space n, ℂ)) :
    ((Λ^((n : ℝ)/2) : ℝ) : ℂ) *
      (∫ x : Space n, Complex.exp (-(Complex.I*(Λ : ℂ)/2)*(‖x‖^2 : ℝ)) * φ x) =
      sphereStationaryConstant n * ∫ ξ : Space n,
        PlanarFalconer.imaginaryExponential ((2*Real.pi^2/Λ)*‖ξ‖^2) * 𝓕⁻ φ ξ := by
  have hphase (x : Space n) :
      -(Complex.I*(Λ : ℂ)/2)*(‖x‖^2 : ℝ) =
        -(((Λ/2 : ℝ) : ℂ)*Complex.I)*(‖x‖^2 : ℝ) := by push_cast; ring
  simp_rw [hphase]
  rw [gaussian_stationary_identity hn (half_pos hΛ), ← mul_assoc,
    normalized_gaussian_coefficient n hΛ]
  congr 1
  apply integral_congr_ae
  filter_upwards with ξ
  congr 1
  unfold PlanarFalconer.imaginaryExponential
  congr 1
  push_cast
  field_simp

theorem norm_sphereStationaryConstant (n : ℕ) :
    ‖sphereStationaryConstant n‖ = (2*Real.pi)^((n : ℝ)/2) := by
  have hp : 0 ≤ (2*Real.pi)^((n : ℝ)/2) := Real.rpow_nonneg (by positivity) _
  simp [sphereStationaryConstant, Complex.norm_real, Complex.norm_exp,
    Complex.mul_re, abs_of_nonneg hp]

end Falconer

end OAI
