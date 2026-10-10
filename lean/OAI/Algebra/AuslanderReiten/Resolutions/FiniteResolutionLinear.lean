import OAI.Algebra.AuslanderReiten.Modules.FiniteModuleNaturality
import OAI.Algebra.AuslanderReiten.HomComplex.FullHomLinear

namespace OAI

open CategoryTheory
open scoped ModuleCat.Algebra

namespace ArExplicit
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]

namespace CompleteComparison
variable {K L : CochainComplex (ModuleCat.{u} R) ℤ}

theorem cochainCokernelMap_smul (a : k) (f : K ⟶ L) :
    cochainCokernelMap (a • f) = a • cochainCokernelMap f := by
  apply LinearMap.ext
  intro z
  obtain ⟨x, rfl⟩ := (LinearMap.range (K.d (-1) 0).hom).mkQ_surjective z
  change (LinearMap.range (L.d (-1) 0).hom).mkQ (a • (f.f 0).hom x) =
    a • (LinearMap.range (L.d (-1) 0).hom).mkQ ((f.f 0).hom x)
  exact ((LinearMap.range (L.d (-1) 0).hom).mkQ.restrictScalars k).map_smul a _
end CompleteComparison

namespace FiniteLeftModule
open CompleteComparison
variable [Module.Finite k R] (τ : FrobeniusTrace k R)
variable {M N : FiniteLeftModule k R}

theorem resolutionCokernelMap_smul (a : k) (f : M.carrier →ₗ[R] N.carrier) :
    resolutionCokernelMap τ (a • f) = a • resolutionCokernelMap τ f := by
  apply LinearMap.ext
  intro x
  exact ((N.completeCochainCokernelEquiv τ).symm.toLinearMap.restrictScalars k).map_smul a _

theorem resolutionMap_smul (a : k) (f : M.carrier →ₗ[R] N.carrier) :
    (HomotopyCategory.quotient _ _).map (resolutionMap τ (a • f)) =
      a • (HomotopyCategory.quotient _ _).map (resolutionMap τ f) := by
  rw [← Functor.map_smul]
  apply (cochainHomotopyRawEquiv (M.completeCochain_totallyAcyclic τ).to_chain
    (N.completeCochain_totallyAcyclic τ).to_chain.toExactProjectiveComplex).injective
  rw [cochainHomotopyRawEquiv_map, cochainHomotopyRawEquiv_map,
    resolutionMap_cokernel, cochainCokernelMap_smul, resolutionMap_cokernel,
    resolutionCokernelMap_smul]
end FiniteLeftModule
end ArExplicit

end OAI
