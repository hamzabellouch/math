import OAI.Algebra.AuslanderReiten.Resolutions.FiniteCochainResolution
import OAI.Algebra.AuslanderReiten.Homology.ShortExactTriangle

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Pretriangulated

namespace ArExplicit.FiniteLeftModule

open CompleteComparison

universe u

variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]
variable (τ : FrobeniusTrace k R)
variable {M N L : FiniteLeftModule k R}

def resolutionCokernelMap (f : M.carrier →ₗ[R] N.carrier) :
    CochainCokernel (M.completeCochain τ) →ₗ[R] CochainCokernel (N.completeCochain τ) :=
  (N.completeCochainCokernelEquiv τ).symm.toLinearMap.comp
    (f.comp (M.completeCochainCokernelEquiv τ).toLinearMap)

def resolutionMap (f : M.carrier →ₗ[R] N.carrier) : M.completeCochain τ ⟶ N.completeCochain τ :=
  Classical.choose (cochainCokernelMap_surjective
    (M.completeCochain_totallyAcyclic τ).to_chain
    (N.completeCochain_totallyAcyclic τ).to_chain.toExactProjectiveComplex
    (resolutionCokernelMap τ f))

@[simp]
theorem resolutionMap_cokernel (f : M.carrier →ₗ[R] N.carrier) :
    cochainCokernelMap (resolutionMap τ f) = resolutionCokernelMap τ f :=
  Classical.choose_spec (cochainCokernelMap_surjective
    (M.completeCochain_totallyAcyclic τ).to_chain
    (N.completeCochain_totallyAcyclic τ).to_chain.toExactProjectiveComplex
    (resolutionCokernelMap τ f))

theorem resolutionCokernelMap_injective (f : M.carrier →ₗ[R] N.carrier)
    (hf : Function.Injective f) : Function.Injective (resolutionCokernelMap τ f) :=
  (N.completeCochainCokernelEquiv τ).symm.injective.comp
    (hf.comp (M.completeCochainCokernelEquiv τ).injective)

theorem resolutionCokernelMap_surjective (f : M.carrier →ₗ[R] N.carrier)
    (hf : Function.Surjective f) : Function.Surjective (resolutionCokernelMap τ f) :=
  (N.completeCochainCokernelEquiv τ).symm.surjective.comp
    (hf.comp (M.completeCochainCokernelEquiv τ).surjective)

theorem resolutionCokernelMap_exact
    (f : M.carrier →ₗ[R] N.carrier) (g : N.carrier →ₗ[R] L.carrier)
    (h : Function.Exact f g) : Function.Exact (resolutionCokernelMap τ f) (resolutionCokernelMap τ g) := by
  intro x
  constructor
  · intro hx
    have hx' : g ((N.completeCochainCokernelEquiv τ) x) = 0 := by
      have hh := congrArg (L.completeCochainCokernelEquiv τ) hx
      simpa [resolutionCokernelMap] using hh
    obtain ⟨m, hm⟩ := (h _).mp hx'
    refine ⟨(M.completeCochainCokernelEquiv τ).symm m, ?_⟩
    simp [resolutionCokernelMap, hm]
  · rintro ⟨m, rfl⟩
    change (L.completeCochainCokernelEquiv τ).symm
      (g ((N.completeCochainCokernelEquiv τ)
        ((N.completeCochainCokernelEquiv τ).symm
          (f ((M.completeCochainCokernelEquiv τ) m))))) = 0
    rw [LinearEquiv.apply_symm_apply, (h _).mpr ⟨_, rfl⟩, map_zero]

theorem exists_resolution_triangle
    (f : M.carrier →ₗ[R] N.carrier) (g : N.carrier →ₗ[R] L.carrier)
    (hf : Function.Injective f) (hg : Function.Surjective g) (hex : Function.Exact f g) :
    ∃ δ : (HomotopyCategory.quotient _ _).obj (L.completeCochain τ) ⟶
        ((HomotopyCategory.quotient _ _).obj (M.completeCochain τ))⟦(1 : ℤ)⟧,
      Triangle.mk ((HomotopyCategory.quotient _ _).map (resolutionMap τ f))
        ((HomotopyCategory.quotient _ _).map (resolutionMap τ g)) δ ∈
        distTriang (HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ)) := by
  let := τ.regular_injective
  apply exists_shortExact_distinguished (resolutionMap τ f) (resolutionCokernelMap τ g)
    (hF := M.completeCochain_totallyAcyclic τ)
    (hG := N.completeCochain_totallyAcyclic τ)
    (hH := L.completeCochain_totallyAcyclic τ)
    (ψ := resolutionMap τ g)
  · rw [resolutionMap_cokernel]
    exact resolutionCokernelMap_exact τ f g hex
  · rw [resolutionMap_cokernel]
    exact resolutionCokernelMap_injective τ f hf
  · exact resolutionCokernelMap_surjective τ g hg
  · exact resolutionMap_cokernel τ g

end ArExplicit.FiniteLeftModule

end

end OAI
