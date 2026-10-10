import OAI.Analysis.Pureness.Tensor.SpatialRepresentationComparison

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzComparison
open scoped TensorProduct InnerProductSpace
variable {H K : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K]

def spatialTensorSwap : SpatialHilbert H K →ₗᵢ[ℂ] SpatialHilbert K H where
  toLinearMap := (TensorProduct.commIsometry ℂ H K).toContinuousLinearEquiv.toContinuousLinearMap.completion.toLinearMap
  norm_map' v := by
    induction v using UniformSpace.Completion.induction_on with
    | hp => exact isClosed_eq (by fun_prop) continuous_norm
    | ih v =>
      simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.completion_apply_coe,
        UniformSpace.Completion.norm_coe]
      exact (TensorProduct.commIsometry ℂ H K).norm_map v

lemma spatialTensorSwap_tmul (x : H) (y : K) :
    spatialTensorSwap (H := H) (K := K) (x ⊗ₜ[ℂ] y : H ⊗[ℂ] K) = (y ⊗ₜ[ℂ] x : K ⊗[ℂ] H) := by
  change (TensorProduct.commIsometry ℂ H K).toContinuousLinearEquiv.toContinuousLinearMap.completion (x ⊗ₜ[ℂ] y) = _
  simp

lemma spatialTensorSwap_op (S : H →L[ℂ] H) (T : K →L[ℂ] K) (v : SpatialHilbert H K) :
    spatialTensorSwap (spatialTensorOp S T v) = spatialTensorOp T S (spatialTensorSwap v) := by
  induction v using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih v =>
    induction v using TensorProduct.inductionOn with
    | add x y hx hy => simpa [UniformSpace.Completion.coe_add] using congrArg₂ (· + ·) hx hy
    | tmul x y => simp [spatialTensorSwap_tmul]

variable [CompleteSpace H] [CompleteSpace K]
variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

lemma spatialStarTensor_swap
    (α : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (β : B →⋆ₐ[ℂ] (K →L[ℂ] K))
    (z : A ⊗[ℂ] B) (v : SpatialHilbert H K) :
    spatialTensorSwap (spatialStarTensorHom α β z v) =
      spatialStarTensorHom β α (TensorProduct.comm ℂ A B z) (spatialTensorSwap v) := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simpa using congrArg₂ (· + ·) hx hy
  | tmul a b => simpa [spatialStarTensorHom_tmul] using spatialTensorSwap_op (α a) (β b) v

lemma spatialStarTensor_norm_le_swap
    (α : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (β : B →⋆ₐ[ℂ] (K →L[ℂ] K)) (z : A ⊗[ℂ] B) :
    ‖spatialStarTensorHom α β z‖ ≤ ‖spatialStarTensorHom β α (TensorProduct.comm ℂ A B z)‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _
    (norm_nonneg (spatialStarTensorHom β α (TensorProduct.comm ℂ A B z)))
  intro v
  rw [← spatialTensorSwap.norm_map (spatialStarTensorHom α β z v), spatialStarTensor_swap]
  simpa only [LinearIsometry.norm_map] using
    (spatialStarTensorHom β α (TensorProduct.comm ℂ A B z)).le_opNorm (spatialTensorSwap v)

theorem spatialStarTensor_norm_swap
    (α : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (β : B →⋆ₐ[ℂ] (K →L[ℂ] K)) (z : A ⊗[ℂ] B) :
    ‖spatialStarTensorHom α β z‖ = ‖spatialStarTensorHom β α (TensorProduct.comm ℂ A B z)‖ := by
  apply le_antisymm (spatialStarTensor_norm_le_swap α β z)
  simpa using spatialStarTensor_norm_le_swap β α (TensorProduct.comm ℂ A B z)

variable {H' K' : Type*}
variable [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
variable [NormedAddCommGroup K'] [InnerProductSpace ℂ K'] [CompleteSpace K']
variable [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]

theorem spatialStarTensor_norm_representation_independent
    (α : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (β : B →⋆ₐ[ℂ] (K →L[ℂ] K))
    (α' : A →⋆ₐ[ℂ] (H' →L[ℂ] H')) (β' : B →⋆ₐ[ℂ] (K' →L[ℂ] K'))
    (hα : Function.Injective α) (hβ : Function.Injective β)
    (hα' : Function.Injective α') (hβ' : Function.Injective β') (z : A ⊗[ℂ] B) :
    ‖spatialStarTensorHom α β z‖ = ‖spatialStarTensorHom α' β' z‖ := by
  rw [spatialStarTensor_norm_eq_of_left_faithful α α' hα hα' β z,
    spatialStarTensor_norm_swap α' β z,
    spatialStarTensor_norm_eq_of_left_faithful β β' hβ hβ' α' _,
    ← spatialStarTensor_norm_swap α' β' z]

theorem spatialStarTensor_norm_le_faithful
    (α : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (β : B →⋆ₐ[ℂ] (K →L[ℂ] K))
    (α' : A →⋆ₐ[ℂ] (H' →L[ℂ] H')) (β' : B →⋆ₐ[ℂ] (K' →L[ℂ] K'))
    (hα' : Function.Injective α') (hβ' : Function.Injective β') (z : A ⊗[ℂ] B) :
    ‖spatialStarTensorHom α β z‖ ≤ ‖spatialStarTensorHom α' β' z‖ := by
  apply (spatialStarTensor_norm_le_of_left_faithful α α' hα' β z).trans
  rw [spatialStarTensor_norm_swap α' β z, spatialStarTensor_norm_swap α' β' z]
  exact spatialStarTensor_norm_le_of_left_faithful β β' hβ' α' _
end CuntzPureness

end

end OAI
