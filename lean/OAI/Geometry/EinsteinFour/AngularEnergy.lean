import OAI.Geometry.EinsteinFour.AngularDerivativeMoments

namespace OAI

/-! Integrate the exact angular identity and the classical Weyl equation.
The integrated Weitzenboeck equations are explicit premises; the derivative
energy inequality required by Jacobi comparison is derived from them.
The published input is Gursky--LeBrun (1999), equation (12), p.8 of the
arXiv version math/9807055: integrate that identity with scalar curvature
12 and determinant `2 * sigma * v^3` to obtain the normalization below. -/

namespace PositiveEinsteinFour.Angular

open MeasureTheory Filter Matrix

noncomputable section

variable {B : Type*} [MeasurableSpace B] {μ : Measure B}

theorem cubic_energy_le {v σ : ℝ} (hv : 0 ≤ v) (hv2 : v ≤ 2) (hσ : σ ≤ 1) :
    σ * v ^ 3 - v ^ 2 ≤ v ^ 2 := by
  have hs := mul_le_mul_of_nonneg_right hσ (pow_nonneg hv 3)
  have ht := mul_le_mul_of_nonneg_right hv2 (sq_nonneg v)
  nlinarith

theorem integrated_gradient_energy_le {v σ E : B → ℝ}
    (hv : ∀ᵐ c ∂μ, 0 ≤ v c ∧ v c ≤ 2 ∧ σ c ≤ 1)
    (hvi : Integrable (fun c => v c ^ 2) μ)
    (hci : Integrable (fun c => σ c * v c ^ 3 - v c ^ 2) μ)
    (hweitzenbock : (∫ c, E c ∂μ) =
      36 * (∫ c, σ c * v c ^ 3 - v c ^ 2 ∂μ)) :
    (∫ c, E c ∂μ) ≤ 36 * (∫ c, v c ^ 2 ∂μ) := by
  rw [hweitzenbock]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply integral_mono_ae hci hvi
  filter_upwards [hv] with c hc
  exact cubic_energy_le hc.1 hc.2.1 hc.2.2

/-- Equation (8)'s derivative estimate after base integration. The only
geometric differential premises are the two classical integrated equations. -/
theorem integral_normalDerivative_energy_le
    (h : FollandMoments) (Z W : B → Gradient) (v b σ τ : B → ℝ)
    (hZs : ∀ c a, (Z c a)ᵀ = Z c a)
    (hZt : ∀ c a, (Z c a).trace = 0)
    (hv : ∀ᵐ c ∂μ, 0 ≤ v c ∧ v c ≤ 2 ∧ σ c ≤ 1)
    (hb : ∀ᵐ c ∂μ, 0 ≤ b c ∧ b c ≤ 2 ∧ τ c ≤ 1)
    (hvi : Integrable (fun c => v c ^ 2) μ)
    (hbi : Integrable (fun c => b c ^ 2) μ)
    (hci : Integrable (fun c => σ c * v c ^ 3 - v c ^ 2) μ)
    (hdi : Integrable (fun c => τ c * b c ^ 3 - b c ^ 2) μ)
    (hZi : Integrable (fun c => gradientSquareNorm (Z c)) μ)
    (hWi : Integrable (fun c => gradientSquareNorm (W c)) μ)
    (hZ : (∫ c, gradientSquareNorm (Z c) ∂μ) =
      36 * (∫ c, σ c * v c ^ 3 - v c ^ 2 ∂μ))
    (hW : (∫ c, gradientSquareNorm (W c) ∂μ) =
      36 * (∫ c, τ c * b c ^ 3 - b c ^ 2 ∂μ)) :
    (∫ c, (∫ q, squareNorm (normalDerivative (Z c) (W c) q) ∂sphereMeasure) ∂μ) ≤
      (9 / 4) * (∫ c, v c ^ 2 + b c ^ 2 ∂μ) := by
  simp_rw [integral_normalDerivative_squareNorm_exact h _ _ (hZs _) (hZt _)]
  rw [integral_div, integral_add hZi hWi, integral_add hvi hbi]
  have hz := integrated_gradient_energy_le hv hvi hci hZ
  have hw := integrated_gradient_energy_le hb hbi hdi hW
  linarith

end

end PositiveEinsteinFour.Angular

end OAI
