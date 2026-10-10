import OAI.Analysis.Pureness.Tensor.SpatialCommutingTensor

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzComparison
open scoped TensorProduct InnerProductSpace
variable {H K H' K' : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K]
variable [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
variable [NormedAddCommGroup K'] [InnerProductSpace ℂ K']

def spatialTensorIsometry (J : H →ₗᵢ[ℂ] H') (L : K →ₗᵢ[ℂ] K') :
    SpatialHilbert H K →ₗᵢ[ℂ] SpatialHilbert H' K' where
  toLinearMap := (TensorProduct.mapIsometry J L).toContinuousLinearMap.completion.toLinearMap
  norm_map' x := by
    induction x using UniformSpace.Completion.induction_on with
    | hp => exact isClosed_eq (continuous_norm.comp
        (TensorProduct.mapIsometry J L).toContinuousLinearMap.completion.continuous) continuous_norm
    | ih x =>
      simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.completion_apply_coe,
        UniformSpace.Completion.norm_coe]
      exact (TensorProduct.mapIsometry J L).norm_map x

lemma spatialTensorIsometry_tmul (J : H →ₗᵢ[ℂ] H') (L : K →ₗᵢ[ℂ] K') (x : H) (y : K) :
    spatialTensorIsometry J L (x ⊗ₜ[ℂ] y : H ⊗[ℂ] K) =
      (J x ⊗ₜ[ℂ] L y : H' ⊗[ℂ] K') := by
  change (TensorProduct.mapIsometry J L).toContinuousLinearMap.completion (x ⊗ₜ[ℂ] y) = _
  simp

lemma spatialTensorIsometry_intertwines
    (J : H →ₗᵢ[ℂ] H') (L : K →ₗᵢ[ℂ] K')
    (S : H →L[ℂ] H) (S' : H' →L[ℂ] H') (T : K →L[ℂ] K) (T' : K' →L[ℂ] K')
    (hS : ∀ x, J (S x) = S' (J x)) (hT : ∀ y, L (T y) = T' (L y))
    (v : SpatialHilbert H K) :
    spatialTensorIsometry J L (spatialTensorOp S T v) =
      spatialTensorOp S' T' (spatialTensorIsometry J L v) := by
  induction v using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih v =>
    induction v using TensorProduct.inductionOn with
    | add x y hx hy => simpa [UniformSpace.Completion.coe_add] using congrArg₂ (· + ·) hx hy
    | tmul x y =>
      simp only [spatialTensorOp_coe, TensorProduct.mapL_tmul, spatialTensorIsometry_tmul, hS, hT]

variable [CompleteSpace H] [CompleteSpace K] [CompleteSpace H'] [CompleteSpace K']
variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
variable (α : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (β : B →⋆ₐ[ℂ] (K →L[ℂ] K))
variable (α' : A →⋆ₐ[ℂ] (H' →L[ℂ] H')) (β' : B →⋆ₐ[ℂ] (K' →L[ℂ] K'))
variable (J : H →ₗᵢ[ℂ] H') (L : K →ₗᵢ[ℂ] K')
variable (hα : ∀ a x, J (α a x) = α' a (J x)) (hβ : ∀ b y, L (β b y) = β' b (L y))

include hα hβ in
theorem spatialStarTensor_intertwines (z : A ⊗[ℂ] B) (v : SpatialHilbert H K) :
    spatialTensorIsometry J L (spatialStarTensorHom α β z v) =
      spatialStarTensorHom α' β' z (spatialTensorIsometry J L v) := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simpa using congrArg₂ (· + ·) hx hy
  | tmul a b =>
    rw [spatialStarTensorHom_tmul, spatialStarTensorHom_tmul]
    exact spatialTensorIsometry_intertwines J L _ _ _ _ (hα a) (hβ b) v

include J L hα hβ in

theorem spatialStarTensor_norm_le_of_intertwines (z : A ⊗[ℂ] B) :
    ‖spatialStarTensorHom α β z‖ ≤ ‖spatialStarTensorHom α' β' z‖ := by
  refine ContinuousLinearMap.opNorm_le_bound (spatialStarTensorHom α β z)
    (norm_nonneg (spatialStarTensorHom α' β' z)) ?_
  intro v
  rw [← (spatialTensorIsometry J L).norm_map (spatialStarTensorHom α β z v),
    spatialStarTensor_intertwines α β α' β' J L hα hβ]
  simpa only [LinearIsometry.norm_map] using (spatialStarTensorHom α' β' z).le_opNorm
    (spatialTensorIsometry J L v)
end CuntzPureness

end

end OAI
