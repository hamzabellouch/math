import OAI.Analysis.Pureness.GroupAlgebra.CauchyFreeGroupFourier

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
variable (α : T.cauchySequenceAlgebra ht →⋆ₐ[ℂ] (H →L[ℂ] H))
variable (γ : T.CauchyQuotient ht →⋆ₐ[ℂ] (L →L[ℂ] L))
variable (hα : Function.Injective α) (hγ : Function.Injective γ)

def cauchyFiniteFourier (s : Finset (FreeGroup ℕ)) (c : FreeGroup ℕ → ℂ)
    (x : representedSpatialTensor α (reducedGroupAlgebra (FreeGroup ℕ)).subtype) :=
  ∑ g ∈ s, spatialCompletionMap (H := H) (K := GroupL2 (FreeGroup ℕ)) α
    (reducedGroupAlgebra (FreeGroup ℕ)).subtype
    ((c g • spatialGroupFourier α g x) ⊗ₜ[ℂ]
      (reducedGroupUnitary (FreeGroup ℕ) g : ReducedFreeGroup))

include hγ in

theorem cauchyFiniteFourier_mem_ideal (s : Finset (FreeGroup ℕ)) (c : FreeGroup ℕ → ℂ)
    (x : representedSpatialTensor α (reducedGroupAlgebra (FreeGroup ℕ)).subtype)
    (hx : T.cauchyFreeGroupTensorMap ht α γ hα x = 0) :
    T.cauchyFiniteFourier ht α s c x ∈
      (spatialTensorKernelIdeal (T.cauchyQuotientStarHom ht) α
        (reducedGroupAlgebra (FreeGroup ℕ)).subtype).ideal := by
  apply sum_mem
  intro g hg
  apply spatialTensorKernelIdeal_tmul
  rw [_root_.map_smul]
  have hz := (T.cauchyQuotientStarHom_eq_zero_iff ht (spatialGroupFourier α g x)).mpr
    (T.cauchyFreeGroupTensorMap_fourier_null ht α γ hα hγ x hx g)
  rw [hz, smul_zero]

include hγ in

theorem cauchyTensorKernel_mem_ideal_of_fourier_tendsto
    (s : ℕ → Finset (FreeGroup ℕ)) (c : ℕ → FreeGroup ℕ → ℂ)
    (x : representedSpatialTensor α (reducedGroupAlgebra (FreeGroup ℕ)).subtype)
    (hx : T.cauchyFreeGroupTensorMap ht α γ hα x = 0)
    (hlim : Filter.Tendsto (fun n => T.cauchyFiniteFourier ht α (s n) (c n) x)
      Filter.atTop (nhds x)) :
    x ∈ (spatialTensorKernelIdeal (T.cauchyQuotientStarHom ht) α
      (reducedGroupAlgebra (FreeGroup ℕ)).subtype).ideal :=
  (spatialTensorKernelIdeal (T.cauchyQuotientStarHom ht) α
    (reducedGroupAlgebra (FreeGroup ℕ)).subtype).isClosed.mem_of_tendsto hlim
      (Filter.Eventually.of_forall fun n => T.cauchyFiniteFourier_mem_ideal ht α γ hα hγ (s n) (c n) x hx)
end CuntzPureness.PositiveQuasitrace

end

end OAI
