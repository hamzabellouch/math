import OAI.Analysis.Pureness.Completion.CompletedSpatialTensorMap

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzComparison
open scoped TensorProduct InnerProductSpace
variable {A B H K : Type*} [CStarAlgebra A] [CStarAlgebra B]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

def spatialRightVector (w : K) : H →L[ℂ] SpatialHilbert H K :=
  LinearMap.mkContinuous
    { toFun := fun x => (x ⊗ₜ[ℂ] w : H ⊗[ℂ] K)
      map_add' := by intros; simp [TensorProduct.add_tmul, UniformSpace.Completion.coe_add]
      map_smul' := by
        intro c x
        change ((c • x ⊗ₜ[ℂ] w : H ⊗[ℂ] K) : SpatialHilbert H K) = c • (x ⊗ₜ[ℂ] w : H ⊗[ℂ] K)
        exact UniformSpace.Completion.coe_smul c (x ⊗ₜ[ℂ] w : H ⊗[ℂ] K) }
    ‖w‖ (fun x => by simp [mul_comm])

omit [CompleteSpace H] [CompleteSpace K] in
lemma spatialRightVector_norm_le (w : K) : ‖spatialRightVector (H := H) w‖ ≤ ‖w‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _

def algebraicSpatialSlice (β : B →⋆ₐ[ℂ] (K →L[ℂ] K)) (v w : K) : A ⊗[ℂ] B →ₗ[ℂ] A :=
  TensorProduct.lift
    { toFun := fun a =>
        { toFun := fun b => ⟪v, β b w⟫_ℂ • a
          map_add' := by intros; simp [add_smul]
          map_smul' := by intros; simp [smul_smul] }
      map_add' := by intros; ext b; simp [smul_add]
      map_smul' := by intros; ext b; simp [smul_smul, mul_comm] }

lemma algebraicSpatialSlice_tmul (β : B →⋆ₐ[ℂ] (K →L[ℂ] K)) (v w : K) (a : A) (b : B) :
    algebraicSpatialSlice β v w (a ⊗ₜ[ℂ] b) = ⟪v, β b w⟫_ℂ • a := rfl

lemma algebraicSpatialSlice_compression (α : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (β : B →⋆ₐ[ℂ] (K →L[ℂ] K)) (v w : K) (z : A ⊗[ℂ] B) :
    α (algebraicSpatialSlice β v w z) =
      (spatialRightVector (H := H) v).adjoint.comp
        ((spatialStarTensorHom α β z).comp (spatialRightVector w)) := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simpa [ContinuousLinearMap.comp_add, ContinuousLinearMap.add_comp]
      using congrArg₂ (· + ·) hx hy
  | tmul a b =>
    apply ContinuousLinearMap.ext
    intro x
    apply ext_inner_left ℂ
    intro y
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.adjoint_inner_right]
    simp [algebraicSpatialSlice_tmul, spatialRightVector, spatialStarTensorHom_tmul,
      UniformSpace.Completion.inner_coe, TensorProduct.inner_tmul, inner_smul_right, mul_comm]

lemma algebraicSpatialSlice_norm_le (α : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hα : Function.Injective α) (β : B →⋆ₐ[ℂ] (K →L[ℂ] K)) (v w : K) (z : A ⊗[ℂ] B) :
    ‖algebraicSpatialSlice β v w z‖ ≤ (‖v‖ * ‖w‖) * ‖spatialCompletionMap α β z‖ := by
  rw [← NonUnitalStarAlgHom.norm_map α.toNonUnitalStarAlgHom hα]
  change ‖α (algebraicSpatialSlice β v w z)‖ ≤ (‖v‖ * ‖w‖) * ‖spatialCompletionMap α β z‖
  rw [algebraicSpatialSlice_compression]
  have hv := spatialRightVector_norm_le (H := H) v
  have hw := spatialRightVector_norm_le (H := H) w
  calc
    _ ≤ ‖(spatialRightVector (H := H) v).adjoint‖ *
        (‖spatialStarTensorHom α β z‖ * ‖spatialRightVector (H := H) w‖) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ ‖v‖ * (‖spatialStarTensorHom α β z‖ * ‖w‖) := by
      rw [LinearIsometryEquiv.norm_map]; gcongr
    _ = _ := by change _ = (‖v‖ * ‖w‖) * ‖spatialStarTensorHom α β z‖; ring

variable (α : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (hα : Function.Injective α)
variable (β : B →⋆ₐ[ℂ] (K →L[ℂ] K)) (v w : K)

def spatialVectorSlice : representedSpatialTensor α β →L[ℂ] A :=
  (algebraicSpatialSlice β v w).extendOfNorm (spatialCompletionMap α β).toLinearMap

include hα in
lemma spatialVectorSlice_tensor (z : A ⊗[ℂ] B) :
    spatialVectorSlice α β v w (spatialCompletionMap α β z) = algebraicSpatialSlice β v w z :=
  LinearMap.extendOfNorm_eq (representedSpatialTensor_dense α β)
    ⟨‖v‖ * ‖w‖, algebraicSpatialSlice_norm_le α hα β v w⟩ z

include hα in
lemma spatialVectorSlice_norm_le (x : representedSpatialTensor α β) :
    ‖spatialVectorSlice α β v w x‖ ≤ (‖v‖ * ‖w‖) * ‖x‖ :=
  LinearMap.norm_extendOfNorm_apply_le (representedSpatialTensor_dense α β)
    (‖v‖ * ‖w‖) (algebraicSpatialSlice_norm_le α hα β v w) x
end CuntzPureness

end

end OAI
