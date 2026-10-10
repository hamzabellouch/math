import OAI.Analysis.Pureness.GroupAlgebra.ReducedFreeGroupAWEmbedding
import OAI.Analysis.Pureness.Tensor.NuclearSpatialTensor

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzComparison CuntzTrace OrderedSemigroup
open scoped TensorProduct InnerProductSpace
universe u
variable (A : Type u) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Nontrivial A]

def originalFreeGroupSpatialHom : A ⊗[ℂ] ReducedFreeGroup →⋆ₐ[ℂ]
    (SpatialHilbert (SimpleStateHilbert A) (GroupL2 (FreeGroup ℕ)) →L[ℂ]
      SpatialHilbert (SimpleStateHilbert A) (GroupL2 (FreeGroup ℕ))) :=
  spatialStarTensorHom (simpleStateGNS A) (reducedGroupAlgebra (FreeGroup ℕ)).subtype

lemma originalFreeGroupSpatialHom_injective (hsimple : TopologicallySimple A) :
    Function.Injective (originalFreeGroupSpatialHom A) :=
  spatialStarTensorHom_injective _ _ hsimple Subtype.val_injective

lemma originalFreeGroupSpatialHom_tmul_norm (hsimple : TopologicallySimple A)
    (a : A) (b : ReducedFreeGroup) :
    ‖originalFreeGroupSpatialHom A (a ⊗ₜ[ℂ] b)‖ = ‖a‖ * ‖b‖ := by
  rw [originalFreeGroupSpatialHom, spatialStarTensorHom_tmul, spatialTensorOp_norm,
    simpleStateGNS_norm A hsimple]
  rfl

abbrev OriginalFreeGroupSpatialCompletion :=
  representedSpatialTensor (simpleStateGNS A) (reducedGroupAlgebra (FreeGroup ℕ)).subtype

def originalFreeGroupSpatialCompletionMap : A ⊗[ℂ] ReducedFreeGroup →⋆ₐ[ℂ]
    OriginalFreeGroupSpatialCompletion A := commutingTensorClosureMap _ _ _

lemma originalFreeGroupSpatialCompletionMap_injective (hsimple : TopologicallySimple A) :
    Function.Injective (originalFreeGroupSpatialCompletionMap A) := by
  intro x y h
  exact originalFreeGroupSpatialHom_injective A hsimple (congrArg Subtype.val h)

lemma originalFreeGroupSpatialCompletionMap_dense :
    DenseRange (originalFreeGroupSpatialCompletionMap A) :=
  commutingTensorClosureMap_denseRange _ _ _

variable {A} (hsimple : TopologicallySimple A)
variable (y : finiteCuntzSubmonoid (A := A)) (hy : y ≠ 0) (f : StateSpace y)

abbrev OriginalFreeGroupAWImage :=
  commutingTensorClosure (matrixStateDiagonalAWEmbedding hsimple y hy f freeGroupScalarUltrafilter)
    (reducedFreeGroupAWEmbedding hsimple y hy f)
    (reducedFreeGroupAWEmbedding_commute hsimple y hy f)

def originalFreeGroupAWImageMap : A ⊗[ℂ] ReducedFreeGroup →⋆ₐ[ℂ]
    OriginalFreeGroupAWImage hsimple y hy f := commutingTensorClosureMap _ _ _

lemma originalFreeGroupAWImageMap_injective :
    Function.Injective (originalFreeGroupAWImageMap hsimple y hy f) :=
  commutingTensorClosureMap_injective _ _ _ hsimple
    (reducedFreeGroupAWEmbedding_injective hsimple y hy f)

lemma originalFreeGroupAWImageMap_dense :
    DenseRange (originalFreeGroupAWImageMap hsimple y hy f) :=
  commutingTensorClosureMap_denseRange _ _ _

variable (hA : IsNuclear.{u, 0} A)

include hA in

lemma originalFreeGroupSpatialHom_norm_eq_AW (z : A ⊗[ℂ] ReducedFreeGroup) :
    ‖originalFreeGroupSpatialHom A z‖ = ‖originalFreeGroupTensorHom hsimple y hy f z‖ :=
  hA.faithful_tensor_norm_eq _ _ (originalFreeGroupSpatialHom_injective A hsimple)
    (originalFreeGroupTensorHom_injective hsimple y hy f) z

def originalFreeGroupNuclearEquiv : OriginalFreeGroupSpatialCompletion A ≃⋆ₐ[ℂ]
    OriginalFreeGroupAWImage hsimple y hy f :=
  hA.tensorCompletionEquiv (originalFreeGroupSpatialCompletionMap A)
    (originalFreeGroupAWImageMap hsimple y hy f)
    (originalFreeGroupSpatialCompletionMap_injective A hsimple)
    (originalFreeGroupAWImageMap_injective hsimple y hy f)
    (originalFreeGroupSpatialCompletionMap_dense A)
    (originalFreeGroupAWImageMap_dense hsimple y hy f)

def originalFreeGroupSpatialAWEmbedding : OriginalFreeGroupSpatialCompletion A →⋆ₐ[ℂ]
    NormalizedMatrixStateUltraAW hsimple y hy f freeGroupScalarUltrafilter :=
  (OriginalFreeGroupAWImage hsimple y hy f).subtype.comp
    (originalFreeGroupNuclearEquiv hsimple y hy f hA).toStarAlgHom

lemma originalFreeGroupSpatialAWEmbedding_tensor (z : A ⊗[ℂ] ReducedFreeGroup) :
    originalFreeGroupSpatialAWEmbedding hsimple y hy f hA
      (originalFreeGroupSpatialCompletionMap A z) = originalFreeGroupTensorHom hsimple y hy f z := by
  exact congrArg (fun a : OriginalFreeGroupAWImage hsimple y hy f =>
      (a : NormalizedMatrixStateUltraAW hsimple y hy f freeGroupScalarUltrafilter))
    (hA.tensorCompletionEquiv_tensor (originalFreeGroupSpatialCompletionMap A)
      (originalFreeGroupAWImageMap hsimple y hy f)
      (originalFreeGroupSpatialCompletionMap_injective A hsimple)
      (originalFreeGroupAWImageMap_injective hsimple y hy f)
      (originalFreeGroupSpatialCompletionMap_dense A)
      (originalFreeGroupAWImageMap_dense hsimple y hy f) z)

lemma originalFreeGroupSpatialAWEmbedding_isometry :
    Isometry (originalFreeGroupSpatialAWEmbedding hsimple y hy f hA) := by
  exact NonUnitalStarAlgHom.isometry
    (originalFreeGroupSpatialAWEmbedding hsimple y hy f hA).toNonUnitalStarAlgHom
    (Subtype.val_injective.comp (originalFreeGroupNuclearEquiv hsimple y hy f hA).injective)
end CuntzPureness

end

end OAI
