import OAI.Analysis.Pureness.GroupAlgebra.FreeGroupUniformMultipliers
import OAI.Analysis.Pureness.GroupAlgebra.CauchyUniformFourierExactness
import OAI.Analysis.Pureness.Tensor.AlgebraicQuotientTensorLift

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

include hα hγ in

theorem cauchyFreeGroupTensorMap_kernel_mem
    (x : representedSpatialTensor α (reducedGroupAlgebra (FreeGroup ℕ)).subtype)
    (hx : T.cauchyFreeGroupTensorMap ht α γ hα x = 0) :
    x ∈ (spatialTensorKernelIdeal (T.cauchyQuotientStarHom ht) α
      (reducedGroupAlgebra (FreeGroup ℕ)).subtype).ideal := by
  refine (exists_freeGroup_uniform_finite_multipliers
    (A := T.cauchySequenceAlgebra ht) (H := H) α hα).elim ?_
  intro s hs
  refine hs.elim ?_
  intro c h
  exact T.cauchyTensorKernel_mem_ideal_of_uniform_fourier ht α γ hα hγ s c 2 h.1 h.2 x hx

include hα hγ in
theorem cauchyFreeGroupTensorMap_zero_iff
    (x : representedSpatialTensor α (reducedGroupAlgebra (FreeGroup ℕ)).subtype) :
    T.cauchyFreeGroupTensorMap ht α γ hα x = 0 ↔
      x ∈ (spatialTensorKernelIdeal (T.cauchyQuotientStarHom ht) α
        (reducedGroupAlgebra (FreeGroup ℕ)).subtype).ideal :=
  ⟨T.cauchyFreeGroupTensorMap_kernel_mem ht α γ hα hγ x,
    T.cauchyFreeGroupTensorMap_ideal_zero ht α γ hα x⟩

include hα hγ in
theorem cauchyFreeGroupTensorFactor_injective :
    Function.Injective (spatialTensorQuotientFactor (T.cauchyQuotientStarHom ht) α
      (reducedGroupAlgebra (FreeGroup ℕ)).subtype γ hα Subtype.val_injective) :=
  (spatialTensorQuotientFactor_injective_iff (T.cauchyQuotientStarHom ht) α
    (reducedGroupAlgebra (FreeGroup ℕ)).subtype γ hα Subtype.val_injective).mpr
    (T.cauchyFreeGroupTensorMap_kernel_mem ht α γ hα hγ)

include hα hγ in

theorem cauchyFreeGroupTensorFactor_isometry :
    Isometry (spatialTensorQuotientFactor (T.cauchyQuotientStarHom ht) α
      (reducedGroupAlgebra (FreeGroup ℕ)).subtype γ hα Subtype.val_injective) :=
  NonUnitalStarAlgHom.isometry
    (spatialTensorQuotientFactor (T.cauchyQuotientStarHom ht) α
      (reducedGroupAlgebra (FreeGroup ℕ)).subtype γ hα Subtype.val_injective)
    (T.cauchyFreeGroupTensorFactor_injective ht α γ hα hγ)

include hα hγ in

theorem cauchyFreeGroupTensorLift_norm (z : T.CauchyQuotient ht ⊗[ℂ] ReducedFreeGroup) :
    ‖algebraicQuotientTensorLift (T.cauchyQuotientStarHom ht) (T.cauchyQuotientMap_surjective ht)
      α (reducedGroupAlgebra (FreeGroup ℕ)).subtype z‖ =
    ‖spatialCompletionMap γ (reducedGroupAlgebra (FreeGroup ℕ)).subtype z‖ := by
  let F := spatialTensorQuotientFactor (T.cauchyQuotientStarHom ht) α
    (reducedGroupAlgebra (FreeGroup ℕ)).subtype γ hα Subtype.val_injective
  let w := algebraicQuotientTensorLift (T.cauchyQuotientStarHom ht)
    (T.cauchyQuotientMap_surjective ht) α (reducedGroupAlgebra (FreeGroup ℕ)).subtype z
  have hn : ‖F w‖ = ‖w‖ :=
    (T.cauchyFreeGroupTensorFactor_isometry ht α γ hα hγ).norm_map_of_map_zero
      (_root_.map_zero F) w
  exact hn.symm.trans (congrArg norm (spatialTensorQuotientFactor_lift
    (T.cauchyQuotientStarHom ht) (T.cauchyQuotientMap_surjective ht) α
    (reducedGroupAlgebra (FreeGroup ℕ)).subtype γ hα Subtype.val_injective z))
end CuntzPureness.PositiveQuasitrace

end

end OAI
