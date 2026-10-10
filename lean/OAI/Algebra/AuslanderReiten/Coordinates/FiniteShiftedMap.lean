import OAI.Algebra.AuslanderReiten.Modules.FiniteModuleNaturality
import OAI.Algebra.AuslanderReiten.Stable.CanonicalCosyzygyShift

namespace OAI

noncomputable section
open CategoryTheory

namespace ArExplicit.FiniteLeftModule

universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]
variable (τ : FrobeniusTrace k R)
variable {U M N : FiniteLeftModule k R} (n : ℕ)
variable (e : (HomotopyCategory.quotient _ _).obj (U.completeCochain τ) ≅
  ((HomotopyCategory.quotient _ _).obj (M.completeCochain τ))⟦(n : ℤ)⟧)
variable (f : M.carrier →ₗ[R] N.carrier)

def shiftedResolutionMap :
    (HomotopyCategory.quotient _ _).obj (U.completeCochain τ) ⟶
      (HomotopyCategory.quotient _ _).obj ((N.canonicalCosyzygies n).completeCochain τ) :=
  e.hom ≫
    (CategoryTheory.shiftFunctor (HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ)) (n : ℤ)).map
      ((HomotopyCategory.quotient _ _).map (resolutionMap τ f)) ≫
    (canonicalCosyzygiesShiftIso τ N n).inv

def shiftedModuleMap : U.carrier →ₗ[R] (N.canonicalCosyzygies n).carrier :=
  Classical.choose (resolutionMap_surjective τ (shiftedResolutionMap τ n e f))

theorem shiftedModuleMap_spec :
    (HomotopyCategory.quotient _ _).map (resolutionMap τ (shiftedModuleMap τ n e f)) =
      shiftedResolutionMap τ n e f :=
  Classical.choose_spec (resolutionMap_surjective τ (shiftedResolutionMap τ n e f))

end ArExplicit.FiniteLeftModule

end

end OAI
