import OAI.Analysis.Pureness.GroupAlgebra.CauchyFreeGroupExactness
import OAI.Analysis.Pureness.GroupAlgebra.CanonicalCauchyFreeGroupTensor

namespace OAI
noncomputable section
namespace CuntzPureness.PositiveQuasitrace
variable {D : Type*}
variable [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [Nontrivial D]
variable (T : CuntzPureness.PositiveQuasitrace D)
variable (ht : ∀ x y, T.metricSize (x+y) ≤ T.metricSize x+T.metricSize y)

theorem canonicalCauchyFreeGroupTensorMap_zero_iff (x : T.CauchyFreeGroupTensorSource ht) :
    T.canonicalCauchyFreeGroupTensorMap ht x = 0 ↔
      x ∈ (spatialTensorKernelIdeal (T.cauchyQuotientStarHom ht) (T.cauchySourceGNS ht)
        (reducedGroupAlgebra (FreeGroup ℕ)).subtype).ideal :=
  T.cauchyFreeGroupTensorMap_zero_iff ht (T.cauchySourceGNS ht) (T.cauchyTargetGNS ht)
    (T.cauchySourceGNS_injective ht) (T.cauchyTargetGNS_injective ht) x

theorem canonicalCauchyFreeGroupTensorFactor_isometry :
    Isometry (spatialTensorQuotientFactor (T.cauchyQuotientStarHom ht) (T.cauchySourceGNS ht)
      (reducedGroupAlgebra (FreeGroup ℕ)).subtype (T.cauchyTargetGNS ht)
      (T.cauchySourceGNS_injective ht) Subtype.val_injective) :=
  T.cauchyFreeGroupTensorFactor_isometry ht (T.cauchySourceGNS ht) (T.cauchyTargetGNS ht)
    (T.cauchySourceGNS_injective ht) (T.cauchyTargetGNS_injective ht)
end CuntzPureness.PositiveQuasitrace

end

end OAI
