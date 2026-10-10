import OAI.Analysis.Pureness.Tensor.SpatialVectorSlice

namespace OAI
noncomputable section
namespace CuntzPureness
variable {A B H K : Type*} [CStarAlgebra A] [CStarAlgebra B]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable (α : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (hα : Function.Injective α)
variable (β : B →⋆ₐ[ℂ] (K →L[ℂ] K)) (v w : K)

include hα in

lemma spatialUnitVectorSlice_norm_le (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (x : representedSpatialTensor α β) : ‖spatialVectorSlice α β v w x‖ ≤ ‖x‖ := by
  simpa only [hv, hw, one_mul] using spatialVectorSlice_norm_le α hα β v w x
end CuntzPureness

end

end OAI
