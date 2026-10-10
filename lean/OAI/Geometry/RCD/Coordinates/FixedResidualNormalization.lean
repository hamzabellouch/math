import OAI.Geometry.RCD.Coordinates.NormalizedProjectionResidual
import OAI.Geometry.RCD.Coordinates.NormalizedPairing
import OAI.Geometry.RCD.Harmonic.LocalRadialDerivative

namespace OAI

/-! # A fixed outer normalization preserves a nonzero inner residual -/

open Set MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators

noncomputable section
namespace RegularPointCoordinates

/-- The fixed outer-bound constant makes every normalized outer norm at
most one, while retaining a definite inner norm. -/
theorem fixed_amplitude_bound {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (x : H) {M α : ℝ} (hM : 0 < M) (hα : 0 < α) (hx : ‖x‖ ≤ M * α) :
    ‖(M * α)⁻¹ • x‖ ≤ 1 := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (mul_pos hM hα))]
  calc
    _ ≤ (M * α)⁻¹ * (M * α) := mul_le_mul_of_nonneg_left hx (by positivity)
    _ = 1 := inv_mul_cancel₀ (mul_pos hM hα).ne'

/-- The same normalization bounds the affine coefficients uniformly. -/
theorem fixed_coefficient_bound {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (b : H) (k : ℝ) {M α C : ℝ} (hM : 0 < M) (hα : 0 < α)
    (hb : ‖b‖ + |k| ≤ C * α) :
    ‖(M * α)⁻¹ • b‖ + |(M * α)⁻¹ * k| ≤ C / M := by
  rw [norm_smul, Real.norm_eq_abs, abs_mul,
    abs_of_pos (inv_pos.mpr (mul_pos hM hα)), ← mul_add]
  calc
    _ ≤ (M * α)⁻¹ * (C * α) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = C / M := by field_simp

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- The inner diagonal moment is exactly `M⁻²`, independent of the small
residual norm. This supplies the nonzero norm in the compactness limit. -/
theorem fixed_residual_moment {n : ℕ} (s : Set X) (hfin : μ s ≠ ∞)
    (u : Fin n → SobolevSpace μ hQ) (w : SobolevSpace μ hQ)
    {M : ℝ} (hM : 0 < M)
    (hpos : 0 < ‖normalizeLocalL2 μ s hfin (SobolevSpace.restrictLp μ hQ s w)‖) :
    let α := ‖normalizeLocalL2 μ s hfin (SobolevSpace.restrictLp μ hQ s w)‖
    ⟪localAffineMomentFamily μ hQ u ((M * α)⁻¹ • w) s hfin none,
      localAffineMomentFamily μ hQ u ((M * α)⁻¹ • w) s hfin none⟫_ℝ = (M⁻¹) ^ 2 := by
  dsimp only
  let α := ‖normalizeLocalL2 μ s hfin (SobolevSpace.restrictLp μ hQ s w)‖
  change ⟪normalizeLocalL2 μ s hfin (SobolevSpace.restrictLp μ hQ s ((M * α)⁻¹ • w)),
    normalizeLocalL2 μ s hfin (SobolevSpace.restrictLp μ hQ s ((M * α)⁻¹ • w))⟫_ℝ = _
  rw [real_inner_self_eq_norm_sq, map_smul, normalizeLocalL2_smul, norm_smul,
    Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (mul_pos hM hpos))]
  change ((M * α)⁻¹ * α) ^ 2 = (M⁻¹) ^ 2
  have hα : α ≠ 0 := hpos.ne'
  field_simp [hM.ne', hα]

variable [BorelSpace X] [ProperSpace X]

/-- Amplitude normalization preserves the exact rescaled Euler identity. -/
theorem amplitude_euler_identity {n : ℕ} (Ω : Set X) (hfin : μ Ω ≠ ∞)
    (f w e : SobolevSpace μ hQ) (u : Fin n → SobolevSpace μ hQ)
    (b : Fin n → ℝ) (k a t : ℝ) {B : ℝ}
    (hf : ∀ᵐ x ∂μ.restrict Ω, localGamma μ hQ f f x ≤ B)
    (hid : t • localRadialDerivative μ hQ Ω f hf w =
      SobolevSpace.restrictLp μ hQ Ω w + (∑ j, b j • SobolevSpace.restrictLp μ hQ Ω (u j)) +
      k • restrictedOne μ Ω hfin + SobolevSpace.restrictLp μ hQ Ω e) :
    t • localRadialDerivative μ hQ Ω f hf (a • w) =
      SobolevSpace.restrictLp μ hQ Ω (a • w) +
      (∑ j, (a * b j) • SobolevSpace.restrictLp μ hQ Ω (u j)) +
      (a * k) • restrictedOne μ Ω hfin + SobolevSpace.restrictLp μ hQ Ω (a • e) := by
  rw [map_smul, smul_comm t a, hid]
  simp only [smul_add, Finset.smul_sum, smul_smul, map_smul]

end RegularPointCoordinates

end

end OAI
