import OAI.Geometry.ProjectionVolume.ProductProjection
import OAI.Geometry.ProjectionVolume.SimplexNormals

namespace OAI

noncomputable section

open Set
open scoped RealInnerProductSpace

namespace Paper092

theorem inner_splitBlocks (x y : Euclidean 20) :
    ⟪x, y⟫ = ⟪firstBlock x, firstBlock y⟫ + ⟪secondBlock x, secondBlock y⟫ := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct]
  exact Fin.sum_univ_add (fun i : Fin (10 + 10) => y i * star (x i))

def liftFirst (x : Euclidean 10) : Euclidean 20 := splitBlocks.symm (x, 0)
def liftSecond (x : Euclidean 10) : Euclidean 20 := splitBlocks.symm (0, x)

theorem firstBlock_liftFirst (x : Euclidean 10) : firstBlock (liftFirst x) = x := by
  change (splitBlocks (splitBlocks.symm (x, 0))).1 = x
  simp

theorem secondBlock_liftFirst (x : Euclidean 10) : secondBlock (liftFirst x) = 0 := by
  change (splitBlocks (splitBlocks.symm (x, 0))).2 = 0
  simp

theorem firstBlock_liftSecond (x : Euclidean 10) : firstBlock (liftSecond x) = 0 := by
  change (splitBlocks (splitBlocks.symm (0, x))).1 = 0
  simp

theorem secondBlock_liftSecond (x : Euclidean 10) : secondBlock (liftSecond x) = x := by
  change (splitBlocks (splitBlocks.symm (0, x))).2 = x
  simp

theorem inner_liftFirst (x : Euclidean 20) (y : Euclidean 10) :
    ⟪x, liftFirst y⟫ = ⟪firstBlock x, y⟫ := by
  rw [inner_splitBlocks, firstBlock_liftFirst, secondBlock_liftFirst, inner_zero_right, add_zero]

theorem inner_liftSecond (x : Euclidean 20) (y : Euclidean 10) :
    ⟪x, liftSecond y⟫ = ⟪secondBlock x, y⟫ := by
  rw [inner_splitBlocks, firstBlock_liftSecond, secondBlock_liftSecond, inner_zero_right, zero_add]

theorem liftFirst_norm (x : Euclidean 10) : ‖liftFirst x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← real_inner_self_eq_norm_sq, inner_liftFirst, firstBlock_liftFirst,
    real_inner_self_eq_norm_sq]

theorem liftSecond_norm (x : Euclidean 10) : ‖liftSecond x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← real_inner_self_eq_norm_sq, inner_liftSecond, secondBlock_liftSecond,
    real_inner_self_eq_norm_sq]

theorem productFacet_left_coordinate_plane (i : Fin 10) (x : Euclidean 20)
    (hx : x ∈ productFacet (.inl (some i))) :
    ⟪liftFirst (EuclideanSpace.single i (1 : ℝ)), x⟫ = 0 := by
  rw [real_inner_comm, inner_liftFirst, real_inner_comm]
  exact simplexFacet_coordinate_plane i (firstBlock x) ⟨hx.1.1, hx.2⟩

theorem productFacet_right_coordinate_plane (i : Fin 10) (x : Euclidean 20)
    (hx : x ∈ productFacet (.inr (some i))) :
    ⟪liftSecond (EuclideanSpace.single i (1 : ℝ)), x⟫ = 0 := by
  rw [real_inner_comm, inner_liftSecond, real_inner_comm]
  exact simplexFacet_coordinate_plane i (secondBlock x) ⟨hx.1.2, hx.2⟩

theorem productFacet_left_diagonal_plane (x : Euclidean 20)
    (hx : x ∈ productFacet (.inl none)) :
    ⟪liftFirst (diagonalUnitNormal 10), x⟫ = (Real.sqrt 10)⁻¹ := by
  rw [real_inner_comm, inner_liftFirst, real_inner_comm]
  exact simplexFacet_diagonal_plane (firstBlock x) ⟨hx.1.1, hx.2⟩

theorem productFacet_right_diagonal_plane (x : Euclidean 20)
    (hx : x ∈ productFacet (.inr none)) :
    ⟪liftSecond (diagonalUnitNormal 10), x⟫ = (Real.sqrt 10)⁻¹ := by
  rw [real_inner_comm, inner_liftSecond, real_inner_comm]
  exact simplexFacet_diagonal_plane (secondBlock x) ⟨hx.1.2, hx.2⟩

end Paper092

end

end OAI
