import OAI.Geometry.RCD.Coordinates.FramedAffineProjection
import OAI.Geometry.RCD.Harmonic.LocalAffineMoments

namespace OAI

/-! # Normalizing the actual orthogonal projection residual -/

open Set MeasureTheory
open scoped InnerProductSpace ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- Scaling a genuine projection residual preserves all affine
orthogonality, including the constant term. -/
theorem normalized_projection_orthogonality {n : ℕ}
    (s : Set X) (hfin : μ s ≠ ∞) (u : Fin n → SobolevSpace μ hQ)
    (v w : SobolevSpace μ hQ)
    (hw : SobolevSpace.restrictLp μ hQ s w =
      affineResidual μ hQ u s hfin (SobolevSpace.restrictLp μ hQ s v))
    (a : ℝ) (j : Option (Fin n)) :
    ⟪localAffineMomentFamily μ hQ u (a • w) s hfin none,
      localAffineMomentFamily μ hQ u (a • w) s hfin (some j)⟫_ℝ = 0 := by
  cases j with
  | none =>
    have ho := affineProjection_orthogonal μ hQ u s hfin
      (SobolevSpace.restrictLp μ hQ s v) 1 0
    have ho' : ⟪affineResidual μ hQ u s hfin (SobolevSpace.restrictLp μ hQ s v),
        restrictedOne μ s hfin⟫_ℝ = 0 := by
      simpa only [affineCoordinateMap_apply, map_zero, one_smul, add_zero,
        affineResidual, sub_apply, ContinuousLinearMap.id_apply] using ho
    change ⟪normalizeLocalL2 μ s hfin (SobolevSpace.restrictLp μ hQ s (a • w)),
      normalizeLocalL2 μ s hfin (restrictedOne μ s hfin)⟫_ℝ = 0
    rw [map_smul, hw]
    simp only [normalizeLocalL2, real_inner_smul_left, real_inner_smul_right, ho', mul_zero]
  | some j =>
    have ho := affineResidual_coordinate_inner μ hQ u s hfin (SobolevSpace.restrictLp μ hQ s v) j
    change ⟪normalizeLocalL2 μ s hfin (SobolevSpace.restrictLp μ hQ s (a • w)),
      normalizeLocalL2 μ s hfin (SobolevSpace.restrictLp μ hQ s (u j))⟫_ℝ = 0
    rw [map_smul, hw]
    simp only [normalizeLocalL2, real_inner_smul_left, real_inner_smul_right, ho, mul_zero]

/-- Dividing by the nonzero inner mean norm makes the same residual's
diagonal moment exactly one. -/
theorem normalized_residual_unit_moment {n : ℕ}
    (s : Set X) (hfin : μ s ≠ ∞) (u : Fin n → SobolevSpace μ hQ)
    (w : SobolevSpace μ hQ)
    (hpos : 0 < ‖normalizeLocalL2 μ s hfin (SobolevSpace.restrictLp μ hQ s w)‖) :
    let α := ‖normalizeLocalL2 μ s hfin (SobolevSpace.restrictLp μ hQ s w)‖
    ⟪localAffineMomentFamily μ hQ u (α⁻¹ • w) s hfin none,
      localAffineMomentFamily μ hQ u (α⁻¹ • w) s hfin none⟫_ℝ = 1 := by
  dsimp only
  let α := ‖normalizeLocalL2 μ s hfin (SobolevSpace.restrictLp μ hQ s w)‖
  change ⟪normalizeLocalL2 μ s hfin (SobolevSpace.restrictLp μ hQ s (α⁻¹ • w)),
    normalizeLocalL2 μ s hfin (SobolevSpace.restrictLp μ hQ s (α⁻¹ • w))⟫_ℝ = 1
  have hs : normalizeLocalL2 μ s hfin (SobolevSpace.restrictLp μ hQ s (α⁻¹ • w)) =
      α⁻¹ • normalizeLocalL2 μ s hfin (SobolevSpace.restrictLp μ hQ s w) := by
    rw [map_smul]
    simp only [normalizeLocalL2, smul_comm α⁻¹]
  rw [hs, real_inner_self_eq_norm_sq, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_pos hpos, inv_mul_cancel₀ hpos.ne', one_pow]

end RegularPointCoordinates

end

end OAI
