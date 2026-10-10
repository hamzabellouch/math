import OAI.Analysis.Pureness.GroupAlgebra.ReducedFreeGroupUltraEmbedding
import OAI.Analysis.Pureness.States.FiniteFamilyScalarValue
import OAI.Analysis.Pureness.Tensor.CommutingTensorInjective

namespace OAI
noncomputable section
namespace CuntzPureness.CompatibleFiniteQuasitrace
open CuntzTrace OrderedSemigroup
open scoped TensorProduct
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Nontrivial A]
variable (F : CompatibleFiniteQuasitrace A)
variable (hmono : ∀ n, Monotone (fun a : Positive (FinMatrix A n) => (F.level n a.1).re))
variable (hF : F.level 1 1=1)

def reducedFreeGroupAWEmbedding : ReducedFreeGroup →⋆ₐ[ℂ]
    F.MatrixUltraAW hmono hF freeGroupScalarUltrafilter :=
  (scalarTracialMatrixAWEmbedding F hmono hF freeGroupScalarUltrafilter).comp
    reducedFreeGroupUltraEmbedding

lemma reducedFreeGroupAWEmbedding_injective :
    Function.Injective (reducedFreeGroupAWEmbedding F hmono hF) :=
  (scalarTracialMatrixAWEmbedding_injective F hmono hF freeGroupScalarUltrafilter).comp
    reducedFreeGroupUltraEmbedding_injective

lemma reducedFreeGroupAWEmbedding_isometry :
    Isometry (reducedFreeGroupAWEmbedding F hmono hF) :=
  NonUnitalStarAlgHom.isometry (reducedFreeGroupAWEmbedding F hmono hF).toNonUnitalStarAlgHom
    (reducedFreeGroupAWEmbedding_injective F hmono hF)

lemma reducedFreeGroupAWEmbedding_commute (a : A) (b : ReducedFreeGroup) :
    Commute (F.matrixDiagonalAWMap hmono hF freeGroupScalarUltrafilter a)
      (reducedFreeGroupAWEmbedding F hmono hF b) :=
  scalarTracialMatrixAWEmbedding_commute F hmono hF freeGroupScalarUltrafilter a
    (reducedFreeGroupUltraEmbedding b)

lemma reducedFreeGroupAWEmbedding_value (b : ReducedFreeGroup) :
    F.matrixUltraQuasitrace hmono hF freeGroupScalarUltrafilter
      (reducedFreeGroupAWEmbedding F hmono hF b) =
        (reducedGroupTracialState (FreeGroup ℕ)).functional b :=
  (scalarTracialMatrixAWEmbedding_value F hmono hF freeGroupScalarUltrafilter
    (reducedFreeGroupUltraEmbedding b)).trans (reducedFreeGroupUltraEmbedding_trace b)

def originalFreeGroupTensorHom : A ⊗[ℂ] ReducedFreeGroup →⋆ₐ[ℂ]
    F.MatrixUltraAW hmono hF freeGroupScalarUltrafilter :=
  commutingStarTensorHom
    (F.matrixDiagonalAWMap hmono hF freeGroupScalarUltrafilter)
    (reducedFreeGroupAWEmbedding F hmono hF)
    (reducedFreeGroupAWEmbedding_commute F hmono hF)

lemma originalFreeGroupTensorHom_injective (hsimple : TopologicallySimple A) :
    Function.Injective (originalFreeGroupTensorHom F hmono hF) :=
  commutingStarTensorHom_injective hsimple _ _
    (reducedFreeGroupAWEmbedding_injective F hmono hF)
    (reducedFreeGroupAWEmbedding_commute F hmono hF)

lemma originalFreeGroupTensorHom_left (a : A) :
    originalFreeGroupTensorHom F hmono hF (a ⊗ₜ[ℂ] 1) =
      F.matrixDiagonalAWMap hmono hF freeGroupScalarUltrafilter a := by
  change F.matrixDiagonalAWMap hmono hF freeGroupScalarUltrafilter a *
    reducedFreeGroupAWEmbedding F hmono hF 1 = _
  exact (congrArg (fun t => F.matrixDiagonalAWMap hmono hF freeGroupScalarUltrafilter a * t)
    (reducedFreeGroupAWEmbedding F hmono hF).map_one).trans (mul_one _)

lemma originalFreeGroupTensorHom_right (b : ReducedFreeGroup) :
    originalFreeGroupTensorHom F hmono hF (1 ⊗ₜ[ℂ] b) =
      reducedFreeGroupAWEmbedding F hmono hF b := by
  change F.matrixDiagonalAWMap hmono hF freeGroupScalarUltrafilter 1 *
    reducedFreeGroupAWEmbedding F hmono hF b = _
  exact (congrArg (fun t => t * reducedFreeGroupAWEmbedding F hmono hF b)
    (F.matrixDiagonalAWMap hmono hF freeGroupScalarUltrafilter).map_one).trans (one_mul _)
end CuntzPureness.CompatibleFiniteQuasitrace

end

end OAI
