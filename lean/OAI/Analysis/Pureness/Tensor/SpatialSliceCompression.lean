import OAI.Analysis.Pureness.Tensor.SpatialVectorSlice

namespace OAI
noncomputable section
namespace CuntzPureness
open scoped CStarAlgebra
variable {A B H K : Type*} [CStarAlgebra A] [CStarAlgebra B]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable (α : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (hα : Function.Injective α)
variable (β : B →⋆ₐ[ℂ] (K →L[ℂ] K))

include hα in

theorem spatialVectorSlice_compression (v w : K) (x : representedSpatialTensor α β) :
    α (spatialVectorSlice α β v w x) =
      (spatialRightVector (H := H) v).adjoint.comp
        (x.val.comp (spatialRightVector w)) := by
  refine (representedSpatialTensor_dense α β).induction_on x ?_ ?_
  · apply isClosed_eq
    · exact (show Continuous α from map_continuous α).comp (ContinuousLinearMap.continuous _)
    · exact continuous_const.clm_comp (continuous_subtype_val.clm_comp continuous_const)
  · intro z
    exact (congrArg α (spatialVectorSlice_tensor α hα β v w z)).trans
      (algebraicSpatialSlice_compression α β v w z)
end CuntzPureness

end

end OAI
