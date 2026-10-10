import OAI.Analysis.Pureness.Completion.CompletedSpatialTensorMap

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzComparison
open scoped TensorProduct
variable {A B H K : Type*} [CStarAlgebra A] [CStarAlgebra B]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable (α : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (β : B →⋆ₐ[ℂ] (K →L[ℂ] K))

lemma spatialCompletionMap_tmul_norm_le (a : A) (b : B) :
    ‖spatialCompletionMap α β (a ⊗ₜ[ℂ] b)‖ ≤ ‖a‖ * ‖b‖ := by
  change ‖spatialStarTensorHom α β (a ⊗ₜ[ℂ] b)‖ ≤ _
  rw [spatialStarTensorHom_tmul]
  exact (spatialTensorOp_norm_le _ _).trans (mul_le_mul
    (NonUnitalStarAlgHom.norm_apply_le α.toNonUnitalStarAlgHom a)
    (NonUnitalStarAlgHom.norm_apply_le β.toNonUnitalStarAlgHom b)
    (norm_nonneg _) (norm_nonneg _))

def spatialTensorLeftLeg (b : B) : A →L[ℂ] representedSpatialTensor α β :=
  LinearMap.mkContinuous
    { toFun := fun a => spatialCompletionMap α β (a ⊗ₜ[ℂ] b)
      map_add' := by intros; simp only [TensorProduct.add_tmul, map_add]
      map_smul' := by intros; simp [TensorProduct.smul_tmul] }
    ‖b‖ (fun a => (spatialCompletionMap_tmul_norm_le α β a b).trans_eq (mul_comm _ _))

def spatialTensorRightLeg (a : A) : B →L[ℂ] representedSpatialTensor α β :=
  LinearMap.mkContinuous
    { toFun := fun b => spatialCompletionMap α β (a ⊗ₜ[ℂ] b)
      map_add' := by intros; simp only [TensorProduct.tmul_add, map_add]
      map_smul' := by intros; simp [TensorProduct.tmul_smul] }
    ‖a‖ (spatialCompletionMap_tmul_norm_le α β a)

lemma spatialTensorLeftLeg_apply (b : B) (a : A) :
    spatialTensorLeftLeg α β b a = spatialCompletionMap α β (a ⊗ₜ[ℂ] b) := rfl

lemma spatialTensorRightLeg_apply (a : A) (b : B) :
    spatialTensorRightLeg α β a b = spatialCompletionMap α β (a ⊗ₜ[ℂ] b) := rfl
end CuntzPureness

end

end OAI
