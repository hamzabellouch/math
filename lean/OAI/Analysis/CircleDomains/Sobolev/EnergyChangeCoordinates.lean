import OAI.Analysis.CircleDomains.Sobolev.CoordinateEnergy
import OAI.Analysis.CircleDomains.Uniformization.ConformalMetric

namespace OAI

/-!
# The energy density under a change of coordinates

Pulling back a covector and its metric multiplies the planar Dirichlet
energy density by the absolute Jacobian determinant. Positive scalar
changes of metric have no effect in dimension two.
-/

open Matrix

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem covectorEnergy_pos_smul (v : Fin 2 → ℝ) {g : PlanarMetric}
    (hg : g.PosDef) {c : ℝ} (hc : 0 < c) :
    covectorEnergy v (c • g) = covectorEnergy v g := by
  simp only [covectorEnergy_eq_matrixEnergy, matrixEnergy_pos_smul _ hg hc]

theorem covectorEnergy_pullback (v : Fin 2 → ℝ) (g B : PlanarMetric)
    (hB : B.det ≠ 0) :
    covectorEnergy (Bᵀ *ᵥ v) (Bᵀ * g * B) = |B.det| * covectorEnergy v g := by
  have hunit : IsUnit B.det := isUnit_iff_ne_zero.mpr hB
  have hunitT : IsUnit Bᵀ.det := by simpa only [det_transpose] using hunit
  have hcancel : (Bᵀ * g * B)⁻¹ * Bᵀ = B⁻¹ * g⁻¹ := by
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev]
    simp only [Matrix.mul_assoc, nonsing_inv_mul _ hunitT, mul_one]
  have hquad : (Bᵀ *ᵥ v) ⬝ᵥ ((Bᵀ * g * B)⁻¹ *ᵥ (Bᵀ *ᵥ v)) =
      v ⬝ᵥ (g⁻¹ *ᵥ v) := by
    rw [mulVec_mulVec, hcancel, ← mulVec_mulVec]
    rw [dotProduct_comm, dotProduct_transpose_mulVec,
      mulVec_mulVec, mul_nonsing_inv _ hunit, one_mulVec]
  have hdet : (Bᵀ * g * B).det = B.det ^ 2 * g.det := by
    rw [det_mul, det_mul, det_transpose]
    ring
  unfold covectorEnergy
  rw [hquad, hdet, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]
  ring

theorem pullback_metric_posDef {g B : PlanarMetric} (hg : g.PosDef) (hB : B.det ≠ 0) :
    (Bᵀ * g * B).PosDef := by
  have hunit : IsUnit B := B.isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr hB)
  have hi := Matrix.mulVec_injective_iff_isUnit.mpr hunit
  simpa only [conjTranspose_eq_transpose_of_trivial] using hg.conjTranspose_mul_mul_same hi

theorem covectorEnergy_conformal_pullback (v : Fin 2 → ℝ) {g B : PlanarMetric}
    (hg : g.PosDef) (hB : B.det ≠ 0) {c : ℝ} (hc : 0 < c) :
    covectorEnergy (Bᵀ *ᵥ v) (c • (Bᵀ * g * B)) = |B.det| * covectorEnergy v g := by
  rw [covectorEnergy_pos_smul _ (pullback_metric_posDef hg hB) hc]
  exact covectorEnergy_pullback v g B hB

end CircleDomainRigidity.FiniteTransfer

end

end OAI
