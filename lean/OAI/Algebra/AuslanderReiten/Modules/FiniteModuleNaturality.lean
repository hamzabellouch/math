import OAI.Algebra.AuslanderReiten.Modules.FiniteModuleTriangle
import OAI.Algebra.AuslanderReiten.Homology.ShortExactNaturality

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Pretriangulated

namespace ArExplicit.FiniteLeftModule
open CompleteComparison

universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]
variable (τ : FrobeniusTrace k R)
variable {M N L : FiniteLeftModule k R}

theorem resolutionCokernelMap_comp (f : M.carrier →ₗ[R] N.carrier) (g : N.carrier →ₗ[R] L.carrier) :
    resolutionCokernelMap τ (g.comp f) = (resolutionCokernelMap τ g).comp (resolutionCokernelMap τ f) := by
  apply LinearMap.ext
  intro x
  simp [resolutionCokernelMap]

@[simp]
theorem resolutionMap_id :
    (HomotopyCategory.quotient _ _).map (resolutionMap τ (LinearMap.id : M.carrier →ₗ[R] M.carrier)) = 𝟙 _ := by
  apply (cochainHomotopyRawEquiv (M.completeCochain_totallyAcyclic τ).to_chain
    (M.completeCochain_totallyAcyclic τ).to_chain.toExactProjectiveComplex).injective
  rw [← (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)).map_id,
    cochainHomotopyRawEquiv_map, cochainHomotopyRawEquiv_map, resolutionMap_cokernel]
  apply congrArg (StableHom.classOf R _ _)
  apply LinearMap.ext
  intro x
  obtain ⟨x, rfl⟩ := (LinearMap.range ((M.completeCochain τ).d (-1) 0).hom).mkQ_surjective x
  simp [resolutionCokernelMap, cochainCokernelMap_mk]

theorem resolutionMap_comp (f : M.carrier →ₗ[R] N.carrier) (g : N.carrier →ₗ[R] L.carrier) :
    (HomotopyCategory.quotient _ _).map (resolutionMap τ (g.comp f)) =
      (HomotopyCategory.quotient _ _).map (resolutionMap τ f) ≫
        (HomotopyCategory.quotient _ _).map (resolutionMap τ g) := by
  apply (cochainHomotopyRawEquiv (M.completeCochain_totallyAcyclic τ).to_chain
    (L.completeCochain_totallyAcyclic τ).to_chain.toExactProjectiveComplex).injective
  rw [← Functor.map_comp, cochainHomotopyRawEquiv_map, cochainHomotopyRawEquiv_map,
    cochainCokernelMap_comp, resolutionMap_cokernel, resolutionMap_cokernel, resolutionMap_cokernel,
    resolutionCokernelMap_comp]

theorem resolutionMap_surjective : Function.Surjective
    (fun f : M.carrier →ₗ[R] N.carrier =>
      (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)).map (resolutionMap τ f)) := by
  intro h
  let E := cochainHomotopyRawEquiv (M.completeCochain_totallyAcyclic τ).to_chain
    (N.completeCochain_totallyAcyclic τ).to_chain.toExactProjectiveComplex
  obtain ⟨u, hu⟩ := StableHom.classOf_surjective (E h)
  let f := (N.completeCochainCokernelEquiv τ).toLinearMap.comp
    (u.comp (M.completeCochainCokernelEquiv τ).symm.toLinearMap)
  refine ⟨f, E.injective ?_⟩
  change cochainHomotopyRawEquiv _ _ _ = _
  rw [cochainHomotopyRawEquiv_map, resolutionMap_cokernel]
  have hf : resolutionCokernelMap τ f = u := by
    apply LinearMap.ext
    intro x
    simp [resolutionCokernelMap, f]
  rw [hf]
  exact hu

variable (f : M.carrier →ₗ[R] N.carrier) (g : N.carrier →ₗ[R] L.carrier)
variable (hf : Function.Injective f) (hg : Function.Surjective g) (hex : Function.Exact f g)

def resolutionTriangle : Triangle (HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ)) := by
  letI := τ.regular_injective
  exact shortExactTriangle (resolutionMap τ f) (resolutionCokernelMap τ g)
    (by rw [resolutionMap_cokernel]; exact resolutionCokernelMap_exact τ f g hex)
    (M.completeCochain_totallyAcyclic τ) (N.completeCochain_totallyAcyclic τ)
    (L.completeCochain_totallyAcyclic τ)
    (by rw [resolutionMap_cokernel]; exact resolutionCokernelMap_injective τ f hf)
    (resolutionCokernelMap_surjective τ g hg)

theorem resolutionTriangle_distinguished :
    resolutionTriangle τ f g hf hg hex ∈
      distTriang (HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ)) := by
  let := τ.regular_injective
  apply shortExactTriangle_distinguished

@[simp]
theorem resolutionTriangle_first :
    (resolutionTriangle τ f g hf hg hex).mor₁ =
      (HomotopyCategory.quotient _ _).map (resolutionMap τ f) := rfl

theorem resolutionTriangle_second :
    (resolutionTriangle τ f g hf hg hex).mor₂ =
      (HomotopyCategory.quotient _ _).map (resolutionMap τ g) := by
  let := τ.regular_injective
  apply shortExactTriangle_second
  exact resolutionMap_cokernel τ g

abbrev resolutionConnecting :
    (HomotopyCategory.quotient _ _).obj (L.completeCochain τ) ⟶
      ((HomotopyCategory.quotient _ _).obj (M.completeCochain τ))⟦(1 : ℤ)⟧ :=
  (resolutionTriangle τ f g hf hg hex).mor₃

variable {M₁ N₁ L₁ M₂ N₂ L₂ : FiniteLeftModule k R}
variable (f₁ : M₁.carrier →ₗ[R] N₁.carrier) (g₁ : N₁.carrier →ₗ[R] L₁.carrier)
  (f₂ : M₂.carrier →ₗ[R] N₂.carrier) (g₂ : N₂.carrier →ₗ[R] L₂.carrier)
variable (hf₁ : Function.Injective f₁) (hg₁ : Function.Surjective g₁) (hex₁ : Function.Exact f₁ g₁)
  (hf₂ : Function.Injective f₂) (hg₂ : Function.Surjective g₂) (hex₂ : Function.Exact f₂ g₂)
variable (a : M₁.carrier →ₗ[R] M₂.carrier) (b : N₁.carrier →ₗ[R] N₂.carrier)
  (c : L₁.carrier →ₗ[R] L₂.carrier)

theorem resolutionConnecting_natural
    (hab : b.comp f₁ = f₂.comp a) (hbc : g₂.comp b = c.comp g₁) :
    (HomotopyCategory.quotient _ _).map (resolutionMap τ c) ≫
        resolutionConnecting τ f₂ g₂ hf₂ hg₂ hex₂ =
      resolutionConnecting τ f₁ g₁ hf₁ hg₁ hex₁ ≫
        (CategoryTheory.shiftFunctor (HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ)) 1).map
          ((HomotopyCategory.quotient _ _).map (resolutionMap τ a)) := by
  let := τ.regular_injective
  apply shortExactTriangle_connecting_natural
  · rw [resolutionMap_cokernel, ← resolutionCokernelMap_comp,
      resolutionMap_cokernel, ← resolutionCokernelMap_comp, hbc]
  · rw [cochainCokernelMap_comp, cochainCokernelMap_comp,
      resolutionMap_cokernel, resolutionMap_cokernel, resolutionMap_cokernel, resolutionMap_cokernel,
      ← resolutionCokernelMap_comp, ← resolutionCokernelMap_comp, hab]

end ArExplicit.FiniteLeftModule

end

end OAI
