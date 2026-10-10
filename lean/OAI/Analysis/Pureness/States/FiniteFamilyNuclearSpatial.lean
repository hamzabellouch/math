import OAI.Analysis.Pureness.States.FiniteFamilyFreeGroup
import OAI.Analysis.Pureness.Tensor.OriginalFreeGroupSpatialTensor

namespace OAI
noncomputable section
namespace CuntzPureness.CompatibleFiniteQuasitrace
open CuntzTrace
open scoped TensorProduct
universe u
variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Nontrivial A]
variable (F : CompatibleFiniteQuasitrace A)
variable (hmono : ∀ n, Monotone (fun a : Positive (FinMatrix A n) => (F.level n a.1).re))
variable (hF : F.level 1 1=1)

abbrev OriginalFreeGroupAWImage :=
  commutingTensorClosure (F.matrixDiagonalAWMap hmono hF freeGroupScalarUltrafilter)
    (reducedFreeGroupAWEmbedding F hmono hF)
    (reducedFreeGroupAWEmbedding_commute F hmono hF)

def originalFreeGroupAWImageMap : A ⊗[ℂ] ReducedFreeGroup →⋆ₐ[ℂ]
    OriginalFreeGroupAWImage F hmono hF := commutingTensorClosureMap _ _ _

lemma originalFreeGroupAWImageMap_injective (hsimple : TopologicallySimple A) :
    Function.Injective (originalFreeGroupAWImageMap F hmono hF) :=
  commutingTensorClosureMap_injective _ _ _ hsimple
    (reducedFreeGroupAWEmbedding_injective F hmono hF)

lemma originalFreeGroupAWImageMap_dense :
    DenseRange (originalFreeGroupAWImageMap F hmono hF) :=
  commutingTensorClosureMap_denseRange _ _ _

variable (hsimple : TopologicallySimple A) (hA : IsNuclear.{u, 0} A)

include hsimple hA in

lemma originalFreeGroupSpatialHom_norm_eq_AW (z : A ⊗[ℂ] ReducedFreeGroup) :
    ‖originalFreeGroupSpatialHom A z‖ = ‖originalFreeGroupTensorHom F hmono hF z‖ :=
  hA.faithful_tensor_norm_eq _ _ (originalFreeGroupSpatialHom_injective A hsimple)
    (originalFreeGroupTensorHom_injective F hmono hF hsimple) z

def originalFreeGroupNuclearEquiv : OriginalFreeGroupSpatialCompletion A ≃⋆ₐ[ℂ]
    OriginalFreeGroupAWImage F hmono hF :=
  hA.tensorCompletionEquiv (originalFreeGroupSpatialCompletionMap A)
    (originalFreeGroupAWImageMap F hmono hF)
    (originalFreeGroupSpatialCompletionMap_injective A hsimple)
    (originalFreeGroupAWImageMap_injective F hmono hF hsimple)
    (originalFreeGroupSpatialCompletionMap_dense A)
    (originalFreeGroupAWImageMap_dense F hmono hF)

def originalFreeGroupSpatialAWEmbedding : OriginalFreeGroupSpatialCompletion A →⋆ₐ[ℂ]
    F.MatrixUltraAW hmono hF freeGroupScalarUltrafilter :=
  (OriginalFreeGroupAWImage F hmono hF).subtype.comp
    (originalFreeGroupNuclearEquiv F hmono hF hsimple hA).toStarAlgHom

lemma originalFreeGroupSpatialAWEmbedding_tensor (z : A ⊗[ℂ] ReducedFreeGroup) :
    originalFreeGroupSpatialAWEmbedding F hmono hF hsimple hA
      (originalFreeGroupSpatialCompletionMap A z) = originalFreeGroupTensorHom F hmono hF z := by
  exact congrArg (fun a : OriginalFreeGroupAWImage F hmono hF =>
      (a : F.MatrixUltraAW hmono hF freeGroupScalarUltrafilter))
    (hA.tensorCompletionEquiv_tensor (originalFreeGroupSpatialCompletionMap A)
      (originalFreeGroupAWImageMap F hmono hF)
      (originalFreeGroupSpatialCompletionMap_injective A hsimple)
      (originalFreeGroupAWImageMap_injective F hmono hF hsimple)
      (originalFreeGroupSpatialCompletionMap_dense A)
      (originalFreeGroupAWImageMap_dense F hmono hF) z)

lemma originalFreeGroupSpatialAWEmbedding_isometry :
    Isometry (originalFreeGroupSpatialAWEmbedding F hmono hF hsimple hA) := by
  exact NonUnitalStarAlgHom.isometry
    (originalFreeGroupSpatialAWEmbedding F hmono hF hsimple hA).toNonUnitalStarAlgHom
    (Subtype.val_injective.comp (originalFreeGroupNuclearEquiv F hmono hF hsimple hA).injective)
end CuntzPureness.CompatibleFiniteQuasitrace

end

end OAI
