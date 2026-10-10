import OAI.Algebra.AuslanderReiten.Evaluation.EvaluatedCoverComparison
import OAI.Algebra.AuslanderReiten.Coordinates.FiniteSourceCoordinates

namespace OAI

noncomputable section
namespace ArExplicit
open CategoryTheory
open CochainComplex CochainComplex.HomComplex CompleteComparison
open scoped TensorProduct ModuleCat.Algebra
universe u
variable {k R : Type u} [Field k] [CharP k 2] [Ring R] [Algebra k R] [Module.Finite k R]

namespace FiniteLeftModule
variable (τ : FrobeniusTrace k R) (S M : FiniteLeftModule k R)

theorem resolutionSourceAtStableEquiv_lift (e : S.carrier →ₗ[R] M.carrier) :
    resolutionSourceAtStableEquiv τ S M 0
      (CohomologyClass.mk (Cocycle.ofHom (resolutionMap τ e))) =
      StableHom.classOf R _ _ (e.comp (S.completeCochainCokernelEquiv τ).toLinearMap) := by
  rw [resolutionSourceAtStableEquiv_mk]
  apply congrArg (StableHom.classOf R _ _)
  apply LinearMap.ext
  intro z
  obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective
    (LinearMap.range ((S.completeCochain τ).d (-1) 0).hom) z
  simp only [LinearMap.comp_apply]
  erw [rawSourceAt_mk (k := k)]
  have h := LinearMap.congr_fun (resolutionMap_cokernel τ e) (Submodule.Quotient.mk z)
  change Submodule.Quotient.mk (((resolutionMap τ e).f 0).hom z) = _ at h
  change (M.completeCochainCokernelEquiv τ)
    (Submodule.Quotient.mk (((resolutionMap τ e).f 0).hom z)) = _
  rw [h]
  exact (M.completeCochainCokernelEquiv τ).apply_symm_apply _
end FiniteLeftModule

namespace TwoCone
variable (D : Data (R ⊗[k] Rᵐᵒᵖ)) (hf : ∀ n, Module.Finite k (D.term n))
variable (X : FiniteLeftModule k R)
variable (hex : ∀ n, Function.Exact (D.d (n+1)) (D.d n))
variable (hr : ∀ n, Module.Projective Rᵐᵒᵖ
  (EnvelopingBimodule k R (baseCokernelModule D hf n).carrier))
variable (hp : ∀ n, Module.Projective (R ⊗[k] Rᵐᵒᵖ) (D.term n))
variable (τ : FrobeniusTrace k R) (S : FiniteLeftModule k R)
variable (e : S.carrier →ₗ[R] (X.evaluated (baseCokernelModule D hf 0)).carrier)
variable (φ : EvaluatedCompleteComparison D hf X hex hr hp τ S e)
local notation "K" => FiniteLeftModule.completeCochain τ S

omit [CharP k 2] in
theorem evaluatedComparisonCokernel_zero :
    evaluatedComparisonCokernel D hf X hex hr hp τ S e φ 0 =
      e.comp (S.completeCochainCokernelEquiv τ).toLinearMap := by
  have h := φ.hom_f_zero_comp_π_f_zero
  erw [ChainComplex.single₀_map_f_zero] at h
  change φ.hom.f 0 ≫ (evaluatedOrdinaryAugmentation D hf X).f 0 =
    (nonnegativeTailAugmentation (chainOfCochain K)).f 0 ≫
      ModuleCat.ofHom (e.comp (S.fullCokernelEquiv τ).toLinearMap) at h
  rw [evaluatedOrdinaryAugmentation_zero, nonnegativeTailAugmentation_f_zero] at h
  apply LinearMap.ext
  intro z
  obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective
    (LinearMap.range ((K).d (-1) 0).hom) z
  have hh := congrArg (fun f => f.hom ((tailTermIso K 0).inv.hom z)) h
  change evaluatedBaseQuotient D hf X 0
    ((φ.hom.f 0).hom ((tailTermIso K 0).inv.hom z)) =
      e ((S.fullCokernelEquiv τ) (Submodule.Quotient.mk ((tailTermIso K 0).inv.hom z))) at hh
  change evaluatedBaseQuotient D hf X 0
    ((φ.hom.f 0).hom ((tailTermIso K 0).inv.hom z)) = _
  rw [hh]
  apply congrArg e
  change (S.completeCochainCokernelEquiv τ)
    (Submodule.Quotient.mk ((tailTermIso K 0).hom.hom ((tailTermIso K 0).inv.hom z))) =
      (S.completeCochainCokernelEquiv τ) (Submodule.Quotient.mk z)
  rw [show (tailTermIso K 0).hom.hom ((tailTermIso K 0).inv.hom z) = z from
    ModuleCat.hom_inv_apply (tailTermIso K 0) z]

theorem evaluatedComparison_initial :
    FiniteLeftModule.HasSourceCoordinates τ S (X.evaluated (baseCokernelModule D hf 0)) 0
      (CohomologyClass.mk (Cocycle.ofHom (FiniteLeftModule.resolutionMap τ e)))
      (evaluatedComparisonCokernel D hf X hex hr hp τ S e φ 0) := by
  change FiniteLeftModule.resolutionSourceAtStableEquiv _ _ _ _ _ = _
  rw [FiniteLeftModule.resolutionSourceAtStableEquiv_lift,
    evaluatedComparisonCokernel_zero]
  rfl
end TwoCone
end ArExplicit

end

end OAI
