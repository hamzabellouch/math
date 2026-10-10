import OAI.Geometry.ProjectionVolume.SimplexProjection
import OAI.Geometry.ProjectionVolume.ProjectionCoefficients

namespace OAI

noncomputable section

open Set MeasureTheory
open scoped RealInnerProductSpace

namespace Paper092

def diagonalVector (d : ℕ) : Euclidean d := WithLp.toLp 2 (1 : Fin d → ℝ)

def diagonalUnitNormal (d : ℕ) : Euclidean d :=
  (Real.sqrt d)⁻¹ • diagonalVector d

theorem diagonalVector_inner {d : ℕ} (u : Euclidean d) :
    ⟪diagonalVector d, u⟫ = ∑ i, u i := by
  simp [diagonalVector, EuclideanSpace.inner_eq_star_dotProduct, dotProduct]

theorem inner_diagonalVector {d : ℕ} (u : Euclidean d) :
    ⟪u, diagonalVector d⟫ = ∑ i, u i := by
  rw [real_inner_comm, diagonalVector_inner]

theorem diagonalVector_norm (d : ℕ) : ‖diagonalVector d‖ = Real.sqrt d := by
  rw [← Real.sqrt_sq (norm_nonneg _), ← real_inner_self_eq_norm_sq, diagonalVector_inner]
  simp [diagonalVector]

theorem diagonalUnitNormal_norm (d : ℕ) (hd : 0 < d) : ‖diagonalUnitNormal d‖ = 1 := by
  rw [diagonalUnitNormal, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_nonneg (Real.sqrt_nonneg _), diagonalVector_norm]
  exact inv_mul_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr (by exact_mod_cast hd)))

theorem diagonalUnitNormal_inner {d : ℕ} (x : Euclidean d) :
    ⟪diagonalUnitNormal d, x⟫ = (∑ i, x i) / Real.sqrt d := by
  rw [diagonalUnitNormal, real_inner_smul_left, diagonalVector_inner]
  ring

theorem inner_diagonalUnitNormal {d : ℕ} (u : Euclidean d) :
    ⟪u, diagonalUnitNormal d⟫ = (∑ i, u i) / Real.sqrt d := by
  rw [real_inner_comm, diagonalUnitNormal_inner]

theorem coordinate_normal_norm {d : ℕ} (i : Fin d) :
    ‖EuclideanSpace.single i (1 : ℝ)‖ = 1 := by simp

theorem simplexFacet_coordinate_plane {d : ℕ} (i : Fin d) (x : Euclidean d)
    (hx : x ∈ simplexFacet d (some i)) :
    ⟪EuclideanSpace.single i (1 : ℝ), x⟫ = 0 := by
  simpa [EuclideanSpace.inner_single_left, simplexCoordinates] using hx.2

theorem simplexFacet_diagonal_plane {d : ℕ} (x : Euclidean d)
    (hx : x ∈ simplexFacet d none) :
    ⟪diagonalUnitNormal d, x⟫ = (Real.sqrt d)⁻¹ := by
  have hsum : ∑ i, x i = 1 := by
    have h := hx.2
    change 1 - ∑ i, x i = 0 at h
    linarith
  rw [diagonalUnitNormal_inner, hsum, one_div]

end Paper092

end

end OAI
