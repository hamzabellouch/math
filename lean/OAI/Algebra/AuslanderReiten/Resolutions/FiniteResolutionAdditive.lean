import OAI.Algebra.AuslanderReiten.Resolutions.FiniteResolutionLinear

namespace OAI

open CategoryTheory
open scoped ModuleCat.Algebra
namespace ArExplicit
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
namespace CompleteComparison
variable {K L : CochainComplex (ModuleCat.{u} R) ℤ}
theorem cochainCokernelMap_add (f g : K ⟶ L) :
    cochainCokernelMap (f+g) = cochainCokernelMap f + cochainCokernelMap g := by
  apply LinearMap.ext
  intro z
  obtain ⟨x, rfl⟩ := (LinearMap.range (K.d (-1) 0).hom).mkQ_surjective z
  exact (LinearMap.range (L.d (-1) 0).hom).mkQ.map_add _ _
end CompleteComparison
namespace FiniteLeftModule
open CompleteComparison
variable [Module.Finite k R] (τ : FrobeniusTrace k R)
variable {M N : FiniteLeftModule k R}
theorem resolutionCokernelMap_add (f g : M.carrier →ₗ[R] N.carrier) :
    resolutionCokernelMap τ (f+g) = resolutionCokernelMap τ f + resolutionCokernelMap τ g := by
  ext x
  exact (N.completeCochainCokernelEquiv τ).symm.map_add _ _

theorem resolutionMap_add (f g : M.carrier →ₗ[R] N.carrier) :
    (HomotopyCategory.quotient _ _).map (resolutionMap τ (f+g)) =
      (HomotopyCategory.quotient _ _).map (resolutionMap τ f) +
      (HomotopyCategory.quotient _ _).map (resolutionMap τ g) := by
  rw [← Functor.map_add]
  apply (cochainHomotopyRawEquiv (M.completeCochain_totallyAcyclic τ).to_chain
    (N.completeCochain_totallyAcyclic τ).to_chain.toExactProjectiveComplex).injective
  rw [cochainHomotopyRawEquiv_map, cochainHomotopyRawEquiv_map,
    resolutionMap_cokernel, cochainCokernelMap_add, resolutionMap_cokernel,
    resolutionMap_cokernel, resolutionCokernelMap_add]
end FiniteLeftModule
end ArExplicit

end OAI
