import OAI.MeasureTheory.Falconer.Geometry.QuadraticNormalization
import OAI.MeasureTheory.Falconer.Radial.RadialTaylor
import OAI.MeasureTheory.Falconer.Fourier.PublishedQuadraticStationary

namespace OAI

/-! Identification of the Fourier Taylor coefficients with the actual Laplacian jets. -/

namespace Falconer
open MeasureTheory
open scoped FourierTransform SchwartzMap

theorem quadratic_taylor_scalar (j : ℕ) {Λ : ℝ} (hΛ : 0 < Λ) :
    (((j.factorial : ℝ)⁻¹ * (2*Real.pi^2/Λ)^j : ℝ) : ℂ) * Complex.I^j *
      ((-(2 * (Real.pi : ℂ))^2)^j)⁻¹ =
        ((Λ^(-(j : ℝ)) : ℝ) : ℂ) / ((2*Complex.I)^j * (j.factorial : ℂ)) := by
  have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hl : (Λ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hΛ.ne'
  have hbase : (2*(Real.pi : ℂ)^2/(Λ : ℂ)) * Complex.I *
      (-(2*(Real.pi : ℂ))^2)⁻¹ = (Λ : ℂ)⁻¹ * (2*Complex.I)⁻¹ := by
    field_simp [hp, hl]
    simp [Complex.I_sq]
  rw [Real.rpow_neg hΛ.le, Real.rpow_natCast]
  push_cast
  calc
    _ = (j.factorial : ℂ)⁻¹ *
        ((2*(Real.pi : ℂ)^2/(Λ : ℂ))*Complex.I*(-(2*(Real.pi : ℂ))^2)⁻¹)^j := by
      rw [mul_pow, mul_pow, inv_pow]
      ring
    _ = _ := by
      rw [hbase]
      simp only [mul_pow, inv_pow, div_eq_mul_inv]
      ring

theorem normalized_quadratic_taylor {n : ℕ} (φ : 𝓢(Space n, ℂ)) (K : ℕ)
    {Λ : ℝ} (hΛ : 0 < Λ) :
    sphereStationaryConstant n *
      (∫ x : Space n, PlanarFalconer.imaginaryTaylor K ((2*Real.pi^2/Λ)*‖x‖^2)*𝓕⁻ φ x) =
      ∑ j ∈ Finset.range (K+1), ((Λ^(-(j : ℝ)) : ℝ) : ℂ) * quadraticJetCoefficient j φ := by
  rw [radial_taylor_inverse_integral, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  unfold quadraticJetCoefficient
  have h := quadratic_taylor_scalar j hΛ
  calc
    _ = sphereStationaryConstant n *
        ((((j.factorial : ℝ)⁻¹ * (2*Real.pi^2/Λ)^j : ℝ) : ℂ) * Complex.I^j *
          ((-(2*(Real.pi : ℂ))^2)^j)⁻¹) *
          ((Laplacian.laplacian : (Space n → ℂ) → (Space n → ℂ))^[j]
            (φ : Space n → ℂ)) 0 := by ring
    _ = _ := by rw [h]; ring

end Falconer

end OAI
