import OAI.Algebra.AuslanderReiten.Stable.SourceStableCoordinates
import OAI.Algebra.AuslanderReiten.Modules.FiniteModuleTriangle

namespace OAI

noncomputable section
open CategoryTheory HomologicalComplex
open CochainComplex CochainComplex.HomComplex
open scoped ModuleCat.Algebra
namespace ArExplicit
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [CharP k 2]

namespace CompleteComparison
variable {K L : CochainComplex (ModuleCat.{u} R) ℤ}

include k in
theorem sourceCocycleMap_ofHom (f : K ⟶ L) :
    sourceCocycleMap (Cocycle.ofHom f) = cokernelMap (extendMap f negIndexEmbedding) 0 := by
  apply LinearMap.ext
  intro z
  obtain ⟨x, rfl⟩ := (LinearMap.range ((chainOfCochain K).d 1 0).hom).mkQ_surjective z
  change sourceCocycleMap (Cocycle.ofHom f) (Submodule.Quotient.mk x) = _
  rw [sourceCocycleMap_mk (k := k)]
  change Submodule.Quotient.mk ((sourceCocycleComponent (Cocycle.ofHom f)).hom x) =
    Submodule.Quotient.mk (((extendMap f negIndexEmbedding).f 0).hom x)
  congr 2
  unfold sourceCocycleComponent
  rw [extendMap_f f negIndexEmbedding (show negIndexEmbedding.f 0 = 0 from rfl)]
  rfl

end CompleteComparison

namespace FiniteLeftModule
open CompleteComparison
variable [Module.Finite k R] (τ : FrobeniusTrace k R) (M N : FiniteLeftModule k R)

def fullCokernelEquiv : Cokernel (chainOfCochain (M.completeCochain τ)) 0 ≃ₗ[R] M.carrier :=
  (cochainCokernelLinearEquiv _).trans (M.completeCochainCokernelEquiv τ)

def fullHomZeroEquiv : CohomologyClass (M.completeCochain τ) (N.completeCochain τ) 0 ≃ₗ[k]
    StableHom R M.carrier N.carrier :=
  (fullHomSourceStableLinearEquiv _ _ 0 (M.completeCochain_totallyAcyclic τ).to_chain
    (N.completeCochain_totallyAcyclic τ).to_chain.toExactProjectiveComplex).trans
      ((StableHom.sourceEquiv (k := k) (M.fullCokernelEquiv τ).symm).trans
        (StableHom.targetEquiv (k := k) (N.fullCokernelEquiv τ)))

theorem fullHomZeroEquiv_ofHom (f : M.completeCochain τ ⟶ N.completeCochain τ) :
    fullHomZeroEquiv τ M N (CohomologyClass.mk (Cocycle.ofHom f)) =
      StableHom.classOf R _ _ ((N.completeCochainCokernelEquiv τ).toLinearMap.comp
        ((cochainCokernelMap f).comp (M.completeCochainCokernelEquiv τ).symm.toLinearMap)) := by
  change StableHom.targetEquiv (k := k) (N.fullCokernelEquiv τ)
    (StableHom.sourceEquiv (k := k) (M.fullCokernelEquiv τ).symm
      (fullHomSourceStableLinearEquiv _ _ 0
        (M.completeCochain_totallyAcyclic τ).to_chain
        (N.completeCochain_totallyAcyclic τ).to_chain.toExactProjectiveComplex
        (CohomologyClass.mk (Cocycle.ofHom f)))) = _
  rw [fullHomSourceStableLinearEquiv_mk, sourceCocycleMap_ofHom (k := k),
    StableHom.sourceEquiv_classOf, StableHom.targetEquiv_classOf]
  congr 1
  apply LinearMap.ext
  intro x
  have h := DFunLike.congr_fun (cochainCokernelLinearEquiv_natural f)
    ((M.fullCokernelEquiv τ).symm x)
  change (cochainCokernelLinearEquiv _) (cokernelMap (extendMap f negIndexEmbedding) 0
    ((M.fullCokernelEquiv τ).symm x)) = cochainCokernelMap f
      ((cochainCokernelLinearEquiv _) ((M.fullCokernelEquiv τ).symm x)) at h
  change (N.completeCochainCokernelEquiv τ)
    ((cochainCokernelLinearEquiv _) (cokernelMap (extendMap f negIndexEmbedding) 0
      ((M.fullCokernelEquiv τ).symm x))) = _
  rw [h]
  simp only [fullCokernelEquiv, LinearEquiv.trans_symm, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]

@[simp]
theorem fullHomZeroEquiv_lift (f : M.carrier →ₗ[R] N.carrier) :
    fullHomZeroEquiv τ M N (CohomologyClass.mk (Cocycle.ofHom (resolutionMap τ f))) =
      StableHom.classOf R _ _ f := by
  rw [fullHomZeroEquiv_ofHom, resolutionMap_cokernel]
  congr 1
  ext x
  simp [resolutionCokernelMap]

@[simp]
theorem fullHomZeroEquiv_identity :
    fullHomZeroEquiv τ M M (CohomologyClass.mk (Cocycle.ofHom (𝟙 (M.completeCochain τ)))) =
      StableHom.identity := by
  rw [fullHomZeroEquiv_ofHom]
  change StableHom.classOf R _ _ _ = StableHom.classOf R _ _ LinearMap.id
  congr 1
  ext x
  change (M.completeCochainCokernelEquiv τ)
    (cochainCokernelMap (𝟙 _) ((M.completeCochainCokernelEquiv τ).symm x)) = x
  have hid : cochainCokernelMap (𝟙 (M.completeCochain τ)) = LinearMap.id := by
    apply LinearMap.ext
    intro z
    obtain ⟨y, rfl⟩ := (LinearMap.range ((M.completeCochain τ).d (-1) 0).hom).mkQ_surjective z
    rfl
  rw [hid]
  exact LinearEquiv.apply_symm_apply _ _

end FiniteLeftModule
end ArExplicit

end

end OAI
