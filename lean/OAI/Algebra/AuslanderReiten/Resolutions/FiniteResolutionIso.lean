import OAI.Algebra.AuslanderReiten.Modules.FiniteModuleNaturality

namespace OAI

noncomputable section
open CategoryTheory

namespace ArExplicit.FiniteLeftModule

universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]
variable (τ : FrobeniusTrace k R) {M N : FiniteLeftModule k R}

def resolutionIso (e : M.carrier ≃ₗ[R] N.carrier) :
    (HomotopyCategory.quotient _ _).obj (M.completeCochain τ) ≅
      (HomotopyCategory.quotient _ _).obj (N.completeCochain τ) where
  hom := (HomotopyCategory.quotient _ _).map (resolutionMap τ e.toLinearMap)
  inv := (HomotopyCategory.quotient _ _).map (resolutionMap τ e.symm.toLinearMap)
  hom_inv_id := by
    rw [← resolutionMap_comp, e.symm_comp, resolutionMap_id]
  inv_hom_id := by
    rw [← resolutionMap_comp, e.comp_symm, resolutionMap_id]

@[simp]
theorem resolutionIso_hom (e : M.carrier ≃ₗ[R] N.carrier) :
    (resolutionIso τ e).hom = (HomotopyCategory.quotient _ _).map (resolutionMap τ e.toLinearMap) := rfl

end ArExplicit.FiniteLeftModule

end

end OAI
