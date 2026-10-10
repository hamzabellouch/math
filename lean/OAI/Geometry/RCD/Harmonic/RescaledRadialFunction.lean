import OAI.Geometry.RCD.Sobolev.ConstantLaplacianBochnerInput
import OAI.Geometry.RCD.Harmonic.LocalRadialDerivative
import OAI.Geometry.RCD.Coordinates.NormalizedPairing

namespace OAI

/-! # Exact radial and amplitude rescaling in the compactness argument -/

open Set MeasureTheory
open scoped ENNReal BigOperators

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

omit [BorelSpace X] [ProperSpace X] in
/-- A constant source rescales in the original weak equation. -/
theorem rescaled_radial_laplacian (Ω : Set X) (f : SobolevSpace μ hQ) {r c : ℝ}
    (hf : IsConstantLaplacianOn μ hQ Ω f c) :
    IsConstantLaplacianOn μ hQ Ω ((r ^ 2)⁻¹ • f) (c / r ^ 2) := by
  simpa only [div_eq_mul_inv, mul_comm c] using hf.smul μ hQ ((r ^ 2)⁻¹)

omit [BorelSpace X] [ProperSpace X] in
/-- The physical quadratic value bound becomes a dimensionless bound. -/
theorem rescaled_radial_value (Ω : Set X) (f : SobolevSpace μ hQ) {r A : ℝ}
    (hr : 0 < r)
    (hf : ∀ᵐ x ∂μ.restrict Ω, |SobolevSpace.toLp μ hQ f x| ≤ A * r ^ 2) :
    ∀ᵐ x ∂μ.restrict Ω, |SobolevSpace.toLp μ hQ ((r ^ 2)⁻¹ • f) x| ≤ A := by
  filter_upwards [hf, ae_restrict_of_ae
    (Lp.coeFn_smul ((r ^ 2)⁻¹) (SobolevSpace.toLp μ hQ f))] with x hx hs
  rw [map_smul, hs, Pi.smul_apply, smul_eq_mul, abs_mul,
    abs_of_pos (inv_pos.mpr (sq_pos_of_pos hr))]
  calc
    _ ≤ (r ^ 2)⁻¹ * (A * r ^ 2) :=
      mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr (sq_nonneg _))
    _ = A := by field_simp

/-- The same radial rescaling has uniformly bounded dimensionless energy. -/
theorem rescaled_radial_energy (Ω : Set X) (f : SobolevSpace μ hQ) {r B : ℝ}
    (hr : 0 < r)
    (hf : ∀ᵐ x ∂μ.restrict Ω, localGamma μ hQ f f x ≤ B * r ^ 2) :
    ∀ᵐ x ∂μ.restrict Ω,
      r ^ 2 * localGamma μ hQ ((r ^ 2)⁻¹ • f) ((r ^ 2)⁻¹ • f) x ≤ B := by
  filter_upwards [hf, ae_restrict_of_ae
    (localGamma_smul_left μ hQ ((r ^ 2)⁻¹) f ((r ^ 2)⁻¹ • f)),
    ae_restrict_of_ae (localGamma_smul_right μ hQ ((r ^ 2)⁻¹) f f)] with x hx hl hr'
  rw [hl, hr']
  have heq : r ^ 2 * ((r ^ 2)⁻¹ * ((r ^ 2)⁻¹ * localGamma μ hQ f f x)) =
      (r ^ 2)⁻¹ * localGamma μ hQ f f x := by field_simp
  rw [heq]
  calc
    _ ≤ (r ^ 2)⁻¹ * (B * r ^ 2) :=
      mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr (sq_nonneg _))
    _ = B := by field_simp

/-- The derivative with respect to the rescaled radial function, multiplied
by the metric scaling factor, is exactly the original radial derivative. -/
theorem rescaled_radial_derivative (Ω : Set X) (f w : SobolevSpace μ hQ) {r B B' : ℝ}
    (hr : 0 < r)
    (hf : ∀ᵐ x ∂μ.restrict Ω, localGamma μ hQ f f x ≤ B)
    (hf' : ∀ᵐ x ∂μ.restrict Ω,
      localGamma μ hQ ((r ^ 2)⁻¹ • f) ((r ^ 2)⁻¹ • f) x ≤ B') :
    r ^ 2 • localRadialDerivative μ hQ Ω ((r ^ 2)⁻¹ • f) hf' w =
      localRadialDerivative μ hQ Ω f hf w := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_smul (r ^ 2)
    (localRadialDerivative μ hQ Ω ((r ^ 2)⁻¹ • f) hf' w),
    localRadialDerivative_representative μ hQ Ω ((r ^ 2)⁻¹ • f) w hf',
    localRadialDerivative_representative μ hQ Ω f w hf,
    ae_restrict_of_ae (localGamma_smul_left μ hQ ((r ^ 2)⁻¹) f w)] with x hs hd hd' hg
  simp only [hs, Pi.smul_apply, smul_eq_mul, hd, hd', hg]
  field_simp

/-- Both changes of scale in the projected Euler equation are exact.
The coefficient and forcing scalings are made explicit. -/
theorem rescaled_projected_euler_identity {n : ℕ} (Ω : Set X) (hfin : μ Ω ≠ ∞)
    (f w e : SobolevSpace μ hQ) (u : Fin n → SobolevSpace μ hQ)
    (b : Fin n → ℝ) (k a : ℝ) {r B B' : ℝ} (hr : 0 < r)
    (hf : ∀ᵐ x ∂μ.restrict Ω, localGamma μ hQ f f x ≤ B)
    (hf' : ∀ᵐ x ∂μ.restrict Ω,
      localGamma μ hQ ((r ^ 2)⁻¹ • f) ((r ^ 2)⁻¹ • f) x ≤ B')
    (hid : localRadialDerivative μ hQ Ω f hf w =
      SobolevSpace.restrictLp μ hQ Ω w + (∑ j, b j • SobolevSpace.restrictLp μ hQ Ω (u j)) +
      k • restrictedOne μ Ω hfin + SobolevSpace.restrictLp μ hQ Ω e) :
    r ^ 2 • localRadialDerivative μ hQ Ω ((r ^ 2)⁻¹ • f) hf' (a • w) =
      SobolevSpace.restrictLp μ hQ Ω (a • w) +
      (∑ j, (a * b j) • SobolevSpace.restrictLp μ hQ Ω (u j)) +
      (a * k) • restrictedOne μ Ω hfin + SobolevSpace.restrictLp μ hQ Ω (a • e) := by
  rw [rescaled_radial_derivative μ hQ Ω f (a • w) hr hf hf', map_smul, hid]
  simp only [smul_add, Finset.smul_sum, smul_smul, map_smul]

end RegularPointCoordinates

end

end OAI
