import OAI.Analysis.Pureness.GroupAlgebra.GroupCoordinateProjection
import OAI.Analysis.Pureness.Tensor.SpatialTensorNorm
import Mathlib.Analysis.CStarAlgebra.Hom

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzComparison
open scoped TensorProduct
variable {H G : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def spatialRightOperator : GroupOperator G →⋆ₐ[ℂ]
    (SpatialHilbert H (GroupL2 G) →L[ℂ] SpatialHilbert H (GroupL2 G)) where
  toFun T := spatialTensorOp 1 T
  map_one' := by apply spatialTensorOp_ext; intro x y; simp
  map_mul' S T := by simpa only [one_mul] using spatialTensorOp_mul (1 : H →L[ℂ] H) 1 S T
  map_zero' := spatialTensorOp_zero_right 1
  map_add' S T := spatialTensorOp_add_right 1 S T
  commutes' c := by
    apply spatialTensorOp_ext
    intro x y
    simp [Algebra.algebraMap_eq_smul_one]
  map_star' T := by simpa only [star_one] using (spatialTensorOp_star (1 : H →L[ℂ] H) T)

lemma spatialRightOperator_apply (T : GroupOperator G) :
    spatialRightOperator (H := H) T = spatialTensorOp 1 T := rfl

def spatialCoordinateProjection (s : Set G) :=
  spatialRightOperator (H := H) (groupCoordinateProjection s)

lemma spatialCoordinateProjection_norm_le (s : Set G) :
    ‖spatialCoordinateProjection (H := H) s‖ ≤ 1 := by
  apply (spatialTensorOp_norm_le (1 : H →L[ℂ] H) (groupCoordinateProjection s)).trans
  exact (mul_le_mul ContinuousLinearMap.norm_id_le (groupCoordinateProjection_norm_le s)
    (norm_nonneg _) zero_le_one).trans_eq (one_mul _)

lemma spatialCoordinateProjection_star (s : Set G) :
    star (spatialCoordinateProjection (H := H) s) = spatialCoordinateProjection (H := H) s := by
  change star (spatialRightOperator (H := H) _) = spatialRightOperator _
  rw [← map_star, groupCoordinateProjection_star]

lemma spatialCoordinateProjection_compl (s : Set G) :
    spatialCoordinateProjection (H := H) sᶜ = 1-spatialCoordinateProjection (H := H) s := by
  change spatialRightOperator (H := H) _ = _
  rw [groupCoordinateProjection_compl,map_sub,map_one]
  rfl

lemma spatialCoordinateProjection_disjoint (s t : Set G) (hst : Disjoint s t) :
    spatialCoordinateProjection (H := H) s*spatialCoordinateProjection (H := H) t = 0 := by
  change spatialRightOperator (H := H) _*spatialRightOperator _ = _
  rw [← map_mul,groupCoordinateProjection_disjoint s t hst,map_zero]

variable [Group G]
lemma spatialCoordinateProjection_conjugate (s : Set G) (k : G) :
    spatialRightOperator (H := H) (groupLeft k)*spatialCoordinateProjection (H := H) s*
      star (spatialRightOperator (H := H) (groupLeft k)) =
        spatialCoordinateProjection (H := H) ((fun g => k*g) '' s) := by
  change spatialRightOperator (H := H) _*spatialRightOperator _*star (spatialRightOperator _) = _
  rw [← map_star,← map_mul,← map_mul,groupCoordinateProjection_conjugate]
  rfl

lemma spatialCoordinateProjection_tensor_zero (s : Set G) (k : G)
    (hs : ∀ g ∈ s, k*g ∉ s) (S : H →L[ℂ] H) :
    spatialCoordinateProjection (H := H) s*spatialTensorOp S (groupLeft k)*
      spatialCoordinateProjection (H := H) s = 0 := by
  change spatialTensorOp 1 (groupCoordinateProjection s)*spatialTensorOp S (groupLeft k)*
    spatialTensorOp 1 (groupCoordinateProjection s) = _
  rw [← spatialTensorOp_mul,← spatialTensorOp_mul,groupCoordinateProjection_translation_zero s k hs,
    spatialTensorOp_zero_right]
end CuntzPureness

end

end OAI
