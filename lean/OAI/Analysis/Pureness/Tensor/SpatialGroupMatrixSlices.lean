import OAI.Analysis.Pureness.Tensor.SpatialFourierCoefficients
import OAI.Analysis.Pureness.GroupAlgebra.ReducedGroupMatrixCoefficients

namespace OAI
noncomputable section
namespace CuntzPureness
local instance spatialGroupMatrixSlicesDecidableEq {X : Type*} : DecidableEq X := Classical.decEq X
open scoped TensorProduct InnerProductSpace
variable {A H G : Type*} [Group G] [CStarAlgebra A]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (α : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (hα : Function.Injective α)

lemma algebraicSpatialSlice_group_matrix (g h : G) (z : A ⊗[ℂ] reducedGroupAlgebra G) :
    algebraicSpatialSlice (reducedGroupAlgebra G).subtype
      (lp.single 2 g 1) (lp.single 2 h 1) z =
    algebraicSpatialSlice (reducedGroupAlgebra G).subtype
      (lp.single 2 (g * h⁻¹) 1) groupVacuum z := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a b =>
    simp only [algebraicSpatialSlice_tmul]
    exact congrArg (fun c : ℂ => c • a) (reducedGroup_matrix_coefficient b g h)

include hα in

theorem spatialGroupMatrixSlice_eq_fourier (g h : G)
    (x : representedSpatialTensor α (reducedGroupAlgebra G).subtype) :
    spatialVectorSlice α (reducedGroupAlgebra G).subtype
      (lp.single 2 g 1) (lp.single 2 h 1) x = spatialGroupFourier α (g*h⁻¹) x := by
  refine (representedSpatialTensor_dense α (reducedGroupAlgebra G).subtype).induction_on x ?_ ?_
  · exact isClosed_eq (ContinuousLinearMap.continuous _) (ContinuousLinearMap.continuous _)
  · intro z
    exact (spatialVectorSlice_tensor α hα (reducedGroupAlgebra G).subtype
      (lp.single 2 g 1) (lp.single 2 h 1) z).trans
      ((algebraicSpatialSlice_group_matrix g h z).trans
        (spatialGroupFourier_tensor α hα (g*h⁻¹) z).symm)
end CuntzPureness

end

end OAI
