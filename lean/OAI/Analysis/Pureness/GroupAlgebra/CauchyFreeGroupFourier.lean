import OAI.Analysis.Pureness.GroupAlgebra.CauchyFreeGroupTensorQuotient
import OAI.Analysis.Pureness.Tensor.SpatialGroupFourier
import OAI.Analysis.Pureness.Tensor.SpatialSliceNaturality

namespace OAI
noncomputable section
namespace CuntzPureness.PositiveQuasitrace
local instance cauchyFreeGroupFourierDecidableEq {α : Type*} : DecidableEq α := Classical.decEq α
variable {D H L : Type*}
variable [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [Nontrivial D]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]
variable (T : CuntzPureness.PositiveQuasitrace D)
variable (ht : ∀ x y, T.metricSize (x+y) ≤ T.metricSize x+T.metricSize y)
variable (α : T.cauchySequenceAlgebra ht →⋆ₐ[ℂ] (H →L[ℂ] H))
variable (γ : T.CauchyQuotient ht →⋆ₐ[ℂ] (L →L[ℂ] L))
variable (hα : Function.Injective α) (hγ : Function.Injective γ)

include hγ in

theorem cauchyFreeGroupTensorMap_fourier_null
    (x : representedSpatialTensor (K := GroupL2 (FreeGroup ℕ)) α
      (reducedGroupAlgebra (FreeGroup ℕ)).subtype)
    (hx : T.cauchyFreeGroupTensorMap ht α γ hα x = 0) (g : FreeGroup ℕ) :
    T.IsMetricNull (fun n => (spatialGroupFourier α g x).1 n) := by
  apply (T.cauchyQuotientStarHom_eq_zero_iff ht (spatialGroupFourier α g x)).mp
  exact spatialVectorSlice_mem_kernel
    (A := T.cauchySequenceAlgebra ht) (B := ReducedFreeGroup) (C := T.CauchyQuotient ht)
    (H := H) (K := GroupL2 (FreeGroup ℕ)) (L := L)
    (T.cauchyQuotientStarHom ht) α (reducedGroupAlgebra (FreeGroup ℕ)).subtype γ
    hα Subtype.val_injective hγ (lp.single 2 g 1) groupVacuum x hx
end CuntzPureness.PositiveQuasitrace

end

end OAI
