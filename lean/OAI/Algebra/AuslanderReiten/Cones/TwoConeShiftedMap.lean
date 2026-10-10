import OAI.Algebra.AuslanderReiten.Cones.TwoConeModuleTriangles
import OAI.Algebra.AuslanderReiten.Coordinates.FiniteShiftedMap
import OAI.Algebra.AuslanderReiten.Resolutions.FiniteResolutionIso

namespace OAI

noncomputable section
open CategoryTheory
open scoped ModuleCat.Algebra

namespace ArExplicit.TwoCone

universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]
variable (D : Data R) (hf : ∀ n, Module.Finite k (D.term n))
variable (τ : FrobeniusTrace k R)
variable (hex : ∀ n, Function.Exact (D.d (n+1)) (D.d n))
variable (hp : ∀ n, Module.Projective R (D.term n))
variable {U N : FiniteLeftModule k R} (n : ℕ)
variable (e : U.carrier ≃ₗ[R] BaseCokernel D 0)
variable (f : BaseCokernel D n →ₗ[R] N.carrier)

def tailSourceShiftIso :
    (HomotopyCategory.quotient _ _).obj (U.completeCochain τ) ≅
      ((HomotopyCategory.quotient _ _).obj
        ((baseCokernelModule D hf n).completeCochain τ))⟦(n : ℤ)⟧ :=
  FiniteLeftModule.resolutionIso τ (M := U) (N := baseCokernelModule D hf 0) e ≪≫
    baseIteratedShiftIso D hf τ hex hp n

def shiftedTailMap : U.carrier →ₗ[R] (N.canonicalCosyzygies n).carrier :=
  FiniteLeftModule.shiftedModuleMap τ (M := baseCokernelModule D hf n) n
    (tailSourceShiftIso D hf τ hex hp n e) f

theorem shiftedTailMap_spec :
    (HomotopyCategory.quotient _ _).map
      (FiniteLeftModule.resolutionMap τ (shiftedTailMap D hf τ hex hp n e f)) =
        FiniteLeftModule.shiftedResolutionMap τ n
          (tailSourceShiftIso D hf τ hex hp n e) f :=
  FiniteLeftModule.shiftedModuleMap_spec τ n
    (tailSourceShiftIso D hf τ hex hp n e) f

end ArExplicit.TwoCone

end

end OAI
