import Mathlib

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open scoped InnerProductSpace TensorProduct ComplexOrder
open UniformSpace
open scoped InnerProductSpace _root_.Topology
open scoped TensorProduct
open UniformSpace
open scoped TensorProduct InnerProductSpace

namespace Kadison.HilbertCompletion

variable {E F G H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def coeIsometry (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E] :
    E →ₗᵢ[ℂ] Completion E where
  toLinearMap := (Completion.toComplL : E →L[ℂ] Completion E).toLinearMap
  norm_map' := Completion.norm_coe

def map (U : E →ₗᵢ[ℂ] F) : Completion E →ₗᵢ[ℂ] Completion F where
  toLinearMap := U.toContinuousLinearMap.completion.toLinearMap
  norm_map' x := by
    induction x using Completion.induction_on with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih x => simp

@[simp] lemma map_coe (U : E →ₗᵢ[ℂ] F) (x : E) : map U (x : Completion E) = (U x : Completion F) := by
  simp [map]

def congr (U : E ≃ₗᵢ[ℂ] F) : Completion E ≃ₗᵢ[ℂ] Completion F :=
  LinearIsometryEquiv.ofSurjective (map U.toLinearIsometry) (by
    intro y
    refine ⟨map U.symm.toLinearIsometry y, ?_⟩
    induction y using Completion.induction_on with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih y => simp)

@[simp] lemma congr_coe (U : E ≃ₗᵢ[ℂ] F) (x : E) : congr U (x : Completion E) = (U x : Completion F) :=
  map_coe U.toLinearIsometry x

def tensorMap : Completion (E ⊗[ℂ] F) →ₗᵢ[ℂ] Completion (Completion E ⊗[ℂ] Completion F) :=
  map (TensorProduct.mapIsometry (coeIsometry E) (coeIsometry F))

@[simp] lemma tensorMap_coe_tmul (x : E) (y : F) :
    tensorMap (E := E) (F := F) ((x ⊗ₜ[ℂ] y) : Completion (E ⊗[ℂ] F)) =
      (((x : Completion E) ⊗ₜ[ℂ] (y : Completion F)) : Completion (Completion E ⊗[ℂ] Completion F)) := by
  simp [tensorMap, coeIsometry]

lemma tensorMap_surjective : Function.Surjective (tensorMap (E := E) (F := F)) := by
  let R := LinearMap.range (tensorMap (E := E) (F := F)).toLinearMap
  have hR : IsClosed (R : Set (Completion (Completion E ⊗[ℂ] Completion F))) :=
    (tensorMap (E := E) (F := F)).isometry.isClosedEmbedding.isClosed_range
  have hp : ∀ (x : Completion E) (y : Completion F),
      ((x ⊗ₜ[ℂ] y) : Completion (Completion E ⊗[ℂ] Completion F)) ∈ R := by
    intro x y
    induction x, y using Completion.induction_on₂ with
    | hp => exact hR.preimage (by fun_prop)
    | ih x y => exact ⟨((x ⊗ₜ[ℂ] y) : Completion (E ⊗[ℂ] F)), tensorMap_coe_tmul x y⟩
  intro z
  change z ∈ R
  induction z using Completion.induction_on with
  | hp => exact hR
  | ih z =>
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => simpa only [Completion.coe_add] using R.add_mem hx hy
    | tmul x y => exact hp x y

def tensor : Completion (E ⊗[ℂ] F) ≃ₗᵢ[ℂ] Completion (Completion E ⊗[ℂ] Completion F) :=
  LinearIsometryEquiv.ofSurjective tensorMap tensorMap_surjective

@[simp] lemma tensor_coe_tmul (x : E) (y : F) :
    tensor (E := E) (F := F) ((x ⊗ₜ[ℂ] y) : Completion (E ⊗[ℂ] F)) =
      (((x : Completion E) ⊗ₜ[ℂ] (y : Completion F)) : Completion (Completion E ⊗[ℂ] Completion F)) :=
  tensorMap_coe_tmul x y

def leftSwap : E ⊗[ℂ] (F ⊗[ℂ] G) ≃ₗᵢ[ℂ] F ⊗[ℂ] (E ⊗[ℂ] G) :=
  (TensorProduct.assocIsometry ℂ E F G).symm |>.trans
    (TensorProduct.congrIsometry (TensorProduct.commIsometry ℂ E F) (.refl ℂ G)) |>.trans
      (TensorProduct.assocIsometry ℂ F E G)

@[simp] lemma leftSwap_tmul (x : E) (y : F) (z : G) :
    leftSwap (x ⊗ₜ[ℂ] (y ⊗ₜ[ℂ] z)) = y ⊗ₜ[ℂ] (x ⊗ₜ[ℂ] z) := by
  simp [leftSwap]

end Kadison.HilbertCompletion
end

end OAI
