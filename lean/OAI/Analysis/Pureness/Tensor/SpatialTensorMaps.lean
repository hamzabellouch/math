import OAI.Analysis.Pureness.Tensor.SpatialTensorIntertwining

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzComparison
open scoped TensorProduct InnerProductSpace
variable {H K H' K' H'' K'' : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K]
variable [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
variable [NormedAddCommGroup K'] [InnerProductSpace ℂ K']
variable [NormedAddCommGroup H''] [InnerProductSpace ℂ H'']
variable [NormedAddCommGroup K''] [InnerProductSpace ℂ K'']

def spatialTensorMap (S : H →L[ℂ] H') (T : K →L[ℂ] K') :
    SpatialHilbert H K →L[ℂ] SpatialHilbert H' K' :=
  (TensorProduct.mapL S T).completion

@[simp] lemma spatialTensorMap_tmul (S : H →L[ℂ] H') (T : K →L[ℂ] K') (x : H) (y : K) :
    spatialTensorMap S T (x ⊗ₜ[ℂ] y : H ⊗[ℂ] K) =
      (S x ⊗ₜ[ℂ] T y : H' ⊗[ℂ] K') := by
  simp [spatialTensorMap]

lemma spatialTensorMap_ext {S T : SpatialHilbert H K →L[ℂ] SpatialHilbert H' K'}
    (h : ∀ x y, S (x ⊗ₜ[ℂ] y : H ⊗[ℂ] K) = T (x ⊗ₜ[ℂ] y : H ⊗[ℂ] K)) : S = T := by
  apply ContinuousLinearMap.ext
  intro v
  induction v using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq S.continuous T.continuous
  | ih v =>
    induction v using TensorProduct.inductionOn with
    | tmul x y => exact h x y
    | add x y hx hy => simpa [UniformSpace.Completion.coe_add] using congrArg₂ (· + ·) hx hy

lemma spatialTensorMap_norm_le (S : H →L[ℂ] H') (T : K →L[ℂ] K') :
    ‖spatialTensorMap S T‖ ≤ ‖S‖ * ‖T‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) ?_
  intro v
  induction v using UniformSpace.Completion.induction_on with
  | hp => apply isClosed_le <;> fun_prop
  | ih v =>
    change ‖(TensorProduct.mapL S T).completion v‖ ≤ _
    rw [ContinuousLinearMap.completion_apply_coe, UniformSpace.Completion.norm_coe,
      UniformSpace.Completion.norm_coe]
    exact ((TensorProduct.mapL S T).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (TensorProduct.norm_mapL_le S T) (norm_nonneg v))

lemma spatialTensorMap_comp (S : H' →L[ℂ] H'') (S' : H →L[ℂ] H')
    (T : K' →L[ℂ] K'') (T' : K →L[ℂ] K') :
    spatialTensorMap (S.comp S') (T.comp T') =
      (spatialTensorMap S T).comp (spatialTensorMap S' T') := by
  apply spatialTensorMap_ext
  intro x y
  simp

lemma spatialTensorMap_id : spatialTensorMap (.id ℂ H) (.id ℂ K) = .id ℂ _ := by
  apply spatialTensorMap_ext
  intro x y
  simp

lemma spatialTensorMap_id_norm_le {T : K →L[ℂ] K'} (hT : ‖T‖ ≤ 1) :
    ‖spatialTensorMap (.id ℂ H) T‖ ≤ 1 := by
  exact (spatialTensorMap_norm_le _ _).trans
    (by nlinarith [ContinuousLinearMap.norm_id_le (𝕜 := ℂ) (E := H), norm_nonneg T])
end CuntzPureness

end

end OAI
