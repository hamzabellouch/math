import OAI.Analysis.Pureness.GroupAlgebra.CauchyFreeGroupTensorQuotient
import OAI.Analysis.Pureness.Quasitrace.QuasitraceQuotientCFC
import OAI.Analysis.Pureness.Operators.BoundedProductStarHom

namespace OAI
noncomputable section
namespace CuntzPureness.PositiveQuasitrace
open scoped TensorProduct ENNReal
variable {D H L : Type*}
variable [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [Nontrivial D]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]
variable (T : CuntzPureness.PositiveQuasitrace D)
variable (ht : ∀ x y, T.metricSize (x+y) ≤ T.metricSize x+T.metricSize y)
variable (α : T.cauchySequenceAlgebra ht →⋆ₐ[ℂ] (H →L[ℂ] H))
variable (δ : D →⋆ₐ[ℂ] (L →L[ℂ] L)) (hα : Function.Injective α)

def cauchySpatialEval (n : ℕ) :
    representedSpatialTensor α (reducedGroupAlgebra (FreeGroup ℕ)).subtype →⋆ₐ[ℂ]
      representedSpatialTensor δ (reducedGroupAlgebra (FreeGroup ℕ)).subtype :=
  spatialTensorQuotientMap (H := H) (L := L) (T.cauchySequenceEval ht n) α
    (reducedGroupAlgebra (FreeGroup ℕ)).subtype δ hα Subtype.val_injective

lemma cauchySpatialEval_tensor (n : ℕ) (u : T.cauchySequenceAlgebra ht) (b : ReducedFreeGroup) :
    T.cauchySpatialEval ht α δ hα n
      (spatialCompletionMap α (reducedGroupAlgebra (FreeGroup ℕ)).subtype (u ⊗ₜ[ℂ] b)) =
    spatialCompletionMap δ (reducedGroupAlgebra (FreeGroup ℕ)).subtype (u.1 n ⊗ₜ[ℂ] b) :=
  spatialTensorQuotientMap_tensor (H := H) (L := L) (T.cauchySequenceEval ht n) α
    (reducedGroupAlgebra (FreeGroup ℕ)).subtype δ hα Subtype.val_injective (u ⊗ₜ[ℂ] b)

lemma cauchySpatialEval_norm_le (n : ℕ)
    (x : representedSpatialTensor α (reducedGroupAlgebra (FreeGroup ℕ)).subtype) :
    ‖T.cauchySpatialEval ht α δ hα n x‖ ≤ ‖x‖ :=
  NonUnitalStarAlgHom.norm_apply_le (T.cauchySpatialEval ht α δ hα n) x

abbrev cauchySpatialEvaluationProduct :=
  boundedProductStarHom (fun n => (T.cauchySpatialEval ht α δ hα n).toNonUnitalStarAlgHom)

lemma cauchySpatialEvaluationProduct_apply
    (x : representedSpatialTensor α (reducedGroupAlgebra (FreeGroup ℕ)).subtype) (n : ℕ) :
    T.cauchySpatialEvaluationProduct ht α δ hα x n = T.cauchySpatialEval ht α δ hα n x := rfl

lemma cauchySpatialEvaluationProduct_norm_le
    (x : representedSpatialTensor α (reducedGroupAlgebra (FreeGroup ℕ)).subtype) :
    ‖T.cauchySpatialEvaluationProduct ht α δ hα x‖ ≤ ‖x‖ :=
  boundedProductStarHom_norm_le
    (fun n => (T.cauchySpatialEval ht α δ hα n).toNonUnitalStarAlgHom) x
end CuntzPureness.PositiveQuasitrace

end

end OAI
