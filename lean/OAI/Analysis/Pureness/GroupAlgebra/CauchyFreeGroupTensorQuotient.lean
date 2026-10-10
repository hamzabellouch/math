import OAI.Analysis.Pureness.Tensor.SpatialTensorQuotient
import OAI.Analysis.Pureness.Quasitrace.QuasitraceQuotientOrder
import OAI.Analysis.Pureness.Quasitrace.QuasitraceQuotientRealImag
import OAI.Analysis.Pureness.GroupAlgebra.FreeGroupMatrixApproximation

namespace OAI
noncomputable section
namespace CuntzPureness.PositiveQuasitrace
open scoped TensorProduct
variable {D H L : Type*}
variable [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [Nontrivial D]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]
variable (T : CuntzPureness.PositiveQuasitrace D)
variable (ht : ∀ x y, T.metricSize (x+y) ≤ T.metricSize x+T.metricSize y)

lemma cauchyQuotientStarHom_eq_zero_iff (u : T.cauchySequenceAlgebra ht) :
    T.cauchyQuotientStarHom ht u = 0 ↔ T.IsMetricNull (fun n => u.1 n) := by
  change u ∈ T.nullSequenceSubmodule ht ↔ _
  rw [← SetLike.mem_coe, T.nullSequenceSubmodule_coe ht]
  exact T.nullSequenceIdeal_mem ht u

variable (α : T.cauchySequenceAlgebra ht →⋆ₐ[ℂ] (H →L[ℂ] H))
variable (γ : T.CauchyQuotient ht →⋆ₐ[ℂ] (L →L[ℂ] L)) (hα : Function.Injective α)

def cauchyFreeGroupTensorMap :
    representedSpatialTensor α (reducedGroupAlgebra (FreeGroup ℕ)).subtype →⋆ₐ[ℂ]
      representedSpatialTensor γ (reducedGroupAlgebra (FreeGroup ℕ)).subtype :=
  spatialTensorQuotientMap (T.cauchyQuotientStarHom ht) α
    (reducedGroupAlgebra (FreeGroup ℕ)).subtype γ hα Subtype.val_injective

lemma cauchyFreeGroupTensorMap_surjective : Function.Surjective (T.cauchyFreeGroupTensorMap ht α γ hα) :=
  spatialTensorQuotientMap_surjective _ _ _ _ hα Subtype.val_injective (T.cauchyQuotientMap_surjective ht)

lemma cauchyFreeGroupTensorMap_tensor (u : T.cauchySequenceAlgebra ht) (b : ReducedFreeGroup) :
    T.cauchyFreeGroupTensorMap ht α γ hα
      (spatialCompletionMap α (reducedGroupAlgebra (FreeGroup ℕ)).subtype (u ⊗ₜ[ℂ] b)) =
    spatialCompletionMap γ (reducedGroupAlgebra (FreeGroup ℕ)).subtype
      (T.cauchyQuotientStarHom ht u ⊗ₜ[ℂ] b) :=
  spatialTensorQuotientMap_tensor _ _ _ _ hα Subtype.val_injective _

lemma cauchyFreeGroupTensorIdeal_coe :
    ((spatialTensorKernelIdeal (T.cauchyQuotientStarHom ht) α
      (reducedGroupAlgebra (FreeGroup ℕ)).subtype).ideal :
        Set (representedSpatialTensor α (reducedGroupAlgebra (FreeGroup ℕ)).subtype)) =
    closure (Set.range (fun z : T.nullSequenceSubmodule ht ⊗[ℂ] ReducedFreeGroup =>
      spatialCompletionMap α (reducedGroupAlgebra (FreeGroup ℕ)).subtype
        (TensorProduct.map (T.nullSequenceSubmodule ht).subtype (LinearMap.id : ReducedFreeGroup →ₗ[ℂ] ReducedFreeGroup) z))) :=
  spatialTensorKernelIdeal_coe _ _ _ (T.cauchyQuotientMap_surjective ht)

lemma cauchyFreeGroupTensorMap_ideal_zero
    (x : representedSpatialTensor α (reducedGroupAlgebra (FreeGroup ℕ)).subtype)
    (hx : x ∈ (spatialTensorKernelIdeal (T.cauchyQuotientStarHom ht) α
      (reducedGroupAlgebra (FreeGroup ℕ)).subtype).ideal) :
    T.cauchyFreeGroupTensorMap ht α γ hα x = 0 :=
  spatialTensorQuotientMap_ideal_zero _ _ _ _ hα Subtype.val_injective x hx
end CuntzPureness.PositiveQuasitrace

end

end OAI
