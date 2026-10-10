import OAI.Analysis.KadisonKastler.SpatialProduct
import Mathlib.Analysis.Normed.Operator.Extend

namespace OAI

/-! # The associator of the completed Hilbert tensor product

The algebraic Hilbert tensor associator is isometric.  Its two canonical
dense embeddings into the completed tensor products therefore extend it
to an actual unitary identification of the two parenthesizations.
-/

namespace KadisonKastler

open UnitalTomsWinter
open scoped TensorProduct Topology

noncomputable section

section DenseEmbedding

variable {E F E' F' : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup E'] [InnerProductSpace ℂ E']
  [NormedAddCommGroup F'] [InnerProductSpace ℂ F']

private def tensorDenseEmbedding (f : E →ₗᵢ[ℂ] E') (g : F →ₗᵢ[ℂ] F') :
    E ⊗[ℂ] F →ₗᵢ[ℂ] SpatialHilbert E' F' :=
  (UniformSpace.Completion.toComplₗᵢ : E' ⊗[ℂ] F' →ₗᵢ[ℂ] SpatialHilbert E' F').comp
    (TensorProduct.mapIsometry f g)

private theorem tensorDenseEmbedding_tmul (f : E →ₗᵢ[ℂ] E') (g : F →ₗᵢ[ℂ] F')
    (x : E) (y : F) :
    tensorDenseEmbedding f g (x ⊗ₜ[ℂ] y) =
      ((f x ⊗ₜ[ℂ] g y : E' ⊗[ℂ] F') : SpatialHilbert E' F') := by
  rfl

private theorem tensorDenseEmbedding_dense (f : E →ₗᵢ[ℂ] E') (g : F →ₗᵢ[ℂ] F')
    (hf : DenseRange f) (hg : DenseRange g) : DenseRange (tensorDenseEmbedding f g) := by
  let S := (tensorDenseEmbedding f g).toLinearMap.range.topologicalClosure
  have hS : IsClosed (S : Set (SpatialHilbert E' F')) :=
    Submodule.isClosed_topologicalClosure _
  have ht (x : E') (y : F') : ((x ⊗ₜ[ℂ] y : E' ⊗[ℂ] F') : SpatialHilbert E' F') ∈ S := by
    refine hf.induction_on (p := fun x =>
      ((x ⊗ₜ[ℂ] y : E' ⊗[ℂ] F') : SpatialHilbert E' F') ∈ S) x ?_ ?_
    · exact hS.preimage (by fun_prop)
    · intro a
      refine hg.induction_on (p := fun y =>
        ((f a ⊗ₜ[ℂ] y : E' ⊗[ℂ] F') : SpatialHilbert E' F') ∈ S) y ?_ ?_
      · exact hS.preimage (by fun_prop)
      · intro b
        apply Submodule.le_topologicalClosure
        exact ⟨a ⊗ₜ[ℂ] b, tensorDenseEmbedding_tmul f g a b⟩
  intro z
  change z ∈ S
  induction z using UniformSpace.Completion.induction_on with
  | hp => exact hS
  | ih z =>
      induction z using TensorProduct.inductionOn with
      | tmul x y => exact ht x y
      | add x y hx hy =>
          simpa only [UniformSpace.Completion.coe_add] using S.add_mem hx hy

end DenseEmbedding

variable {H K L : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [NormedAddCommGroup L] [InnerProductSpace ℂ L]

/-- The algebraic threefold tensor product in the left-associated completion. -/
def spatialAssocLeftEmbedding :
    (H ⊗[ℂ] K) ⊗[ℂ] L →ₗᵢ[ℂ] SpatialHilbert (SpatialHilbert H K) L :=
  tensorDenseEmbedding UniformSpace.Completion.toComplₗᵢ (.id : L →ₗᵢ[ℂ] L)

/-- The algebraic threefold tensor product in the right-associated completion. -/
def spatialAssocRightEmbedding :
    H ⊗[ℂ] (K ⊗[ℂ] L) →ₗᵢ[ℂ] SpatialHilbert H (SpatialHilbert K L) :=
  tensorDenseEmbedding (.id : H →ₗᵢ[ℂ] H) UniformSpace.Completion.toComplₗᵢ

theorem spatialAssocLeftEmbedding_dense :
    DenseRange (spatialAssocLeftEmbedding (H := H) (K := K) (L := L)) :=
  tensorDenseEmbedding_dense _ _ UniformSpace.Completion.denseRange_coe denseRange_id

theorem spatialAssocRightEmbedding_dense :
    DenseRange (spatialAssocRightEmbedding (H := H) (K := K) (L := L)) :=
  tensorDenseEmbedding_dense _ _ denseRange_id UniformSpace.Completion.denseRange_coe

/-- The canonical associator on completed Hilbert tensor products. -/
def spatialAssociator :
    SpatialHilbert (SpatialHilbert H K) L ≃ₗᵢ[ℂ] SpatialHilbert H (SpatialHilbert K L) :=
  (TensorProduct.assoc ℂ H K L).extendOfIsometry
    spatialAssocLeftEmbedding.toLinearMap spatialAssocRightEmbedding.toLinearMap
    spatialAssocLeftEmbedding_dense spatialAssocRightEmbedding_dense (fun x => by
      change ‖spatialAssocRightEmbedding (TensorProduct.assoc ℂ H K L x)‖ =
        ‖spatialAssocLeftEmbedding x‖
      rw [spatialAssocRightEmbedding.norm_map, spatialAssocLeftEmbedding.norm_map,
        TensorProduct.norm_assoc])

theorem spatialAssociator_embedding (x : (H ⊗[ℂ] K) ⊗[ℂ] L) :
    spatialAssociator (spatialAssocLeftEmbedding x) =
      spatialAssocRightEmbedding (TensorProduct.assoc ℂ H K L x) :=
  LinearEquiv.extendOfIsometry_eq _ _ _ _ _ _ x

@[simp]
theorem spatialAssociator_tmul (x : H) (y : K) (z : L) :
    spatialAssociator
      (((((x ⊗ₜ[ℂ] y : H ⊗[ℂ] K) : SpatialHilbert H K) ⊗ₜ[ℂ] z) :
        SpatialHilbert H K ⊗[ℂ] L) : SpatialHilbert (SpatialHilbert H K) L) =
      (((x ⊗ₜ[ℂ] ((y ⊗ₜ[ℂ] z : K ⊗[ℂ] L) : SpatialHilbert K L)) :
        H ⊗[ℂ] SpatialHilbert K L) : SpatialHilbert H (SpatialHilbert K L)) := by
  simpa only [TensorProduct.assoc_tmul, spatialAssocLeftEmbedding,
    spatialAssocRightEmbedding, tensorDenseEmbedding_tmul, LinearIsometry.id_apply,
    UniformSpace.Completion.coe_toComplₗᵢ] using
    spatialAssociator_embedding ((x ⊗ₜ[ℂ] y) ⊗ₜ[ℂ] z)

@[simp]
theorem spatialAssociator_symm_tmul (x : H) (y : K) (z : L) :
    spatialAssociator.symm
      (((x ⊗ₜ[ℂ] ((y ⊗ₜ[ℂ] z : K ⊗[ℂ] L) : SpatialHilbert K L)) :
        H ⊗[ℂ] SpatialHilbert K L) : SpatialHilbert H (SpatialHilbert K L)) =
      (((((x ⊗ₜ[ℂ] y : H ⊗[ℂ] K) : SpatialHilbert H K) ⊗ₜ[ℂ] z) :
        SpatialHilbert H K ⊗[ℂ] L) : SpatialHilbert (SpatialHilbert H K) L) := by
  apply spatialAssociator.injective
  rw [LinearIsometryEquiv.apply_symm_apply, spatialAssociator_tmul]

variable [CompleteSpace H] [CompleteSpace K] [CompleteSpace L]

omit [CompleteSpace H] [CompleteSpace K] [CompleteSpace L] in
/-- Equality of bounded operators can be checked on elementary threefold tensors. -/
theorem spatialTriple_ext
    {A B : SpatialHilbert H (SpatialHilbert K L) →L[ℂ] SpatialHilbert H (SpatialHilbert K L)}
    (h : ∀ x : H, ∀ y : K, ∀ z : L,
      A (((x ⊗ₜ[ℂ] ((y ⊗ₜ[ℂ] z : K ⊗[ℂ] L) : SpatialHilbert K L)) :
        H ⊗[ℂ] SpatialHilbert K L) : SpatialHilbert H (SpatialHilbert K L)) =
      B (((x ⊗ₜ[ℂ] ((y ⊗ₜ[ℂ] z : K ⊗[ℂ] L) : SpatialHilbert K L)) :
        H ⊗[ℂ] SpatialHilbert K L) : SpatialHilbert H (SpatialHilbert K L))) : A = B := by
  apply spatialTensorOp_ext
  intro x w
  induction w using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih w =>
      induction w using TensorProduct.inductionOn with
      | tmul y z => exact h x y z
      | add y z hy hz =>
          simpa only [UniformSpace.Completion.coe_add, TensorProduct.tmul_add,
            map_add] using congrArg₂ (· + ·) hy hz

omit [CompleteSpace H] [CompleteSpace K] [CompleteSpace L] in
/-- Conjugation by the associator reassociates the actual tensor operators. -/
theorem spatialAssociator_conjugate_tensor
    (a : H →L[ℂ] H) (b : K →L[ℂ] K) (c : L →L[ℂ] L) :
    spatialAssociator.conjStarAlgEquiv (spatialTensorOp (spatialTensorOp a b) c) =
      spatialTensorOp a (spatialTensorOp b c) := by
  apply spatialTriple_ext
  intro x y z
  simp only [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, spatialAssociator_symm_tmul,
    spatialTensorOp_coe, TensorProduct.mapL_tmul, spatialAssociator_tmul]

end

end KadisonKastler

end OAI
