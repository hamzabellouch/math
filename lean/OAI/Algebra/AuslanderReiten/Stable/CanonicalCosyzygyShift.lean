import OAI.Algebra.AuslanderReiten.Stable.CanonicalCosyzygy
import OAI.Algebra.AuslanderReiten.Complete.ProjectiveCompleteResolution

namespace OAI

noncomputable section
open CategoryTheory

namespace ArExplicit.FiniteLeftModule

open CompleteComparison

universe u

variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]
variable (τ : FrobeniusTrace k R) (M : FiniteLeftModule k R)

def canonicalEnvelopeModule : FiniteLeftModule k R where
  carrier := M.canonicalEnvelope
  scalar := inferInstanceAs (Module k (CoinducedModule k R M.carrier))
  tower := inferInstanceAs (IsScalarTower k R (CoinducedModule k R M.carrier))
  finite := inferInstanceAs (Module.Finite k (CoinducedModule k R M.carrier))

def canonicalCosyzygyQuotient : (M.canonicalEnvelopeModule).carrier →ₗ[R]
    M.canonicalCosyzygy.carrier :=
  (LinearMap.range (M.canonicalEmbedding).hom).mkQ

theorem canonicalCosyzygyQuotient_surjective : Function.Surjective M.canonicalCosyzygyQuotient :=
  (LinearMap.range (M.canonicalEmbedding).hom).mkQ_surjective

theorem canonicalCosyzygy_exact : Function.Exact (M.canonicalEmbedding).hom
    M.canonicalCosyzygyQuotient := by
  intro x
  exact Submodule.Quotient.mk_eq_zero _

def canonicalCosyzygyShiftIso :
    (HomotopyCategory.quotient _ _).obj (M.canonicalCosyzygy.completeCochain τ) ≅
      ((HomotopyCategory.quotient _ _).obj (M.completeCochain τ))⟦(1 : ℤ)⟧ := by
  letI : Module.Projective R M.canonicalEnvelopeModule.carrier :=
    CoinducedModule.projective (M := M.carrier) τ
  exact projectiveMiddleShiftIso τ (M.canonicalEmbedding).hom M.canonicalCosyzygyQuotient
    CoinducedModule.embedding_injective M.canonicalCosyzygyQuotient_surjective
    M.canonicalCosyzygy_exact

def canonicalCosyzygiesShiftIso (n : ℕ) :
    (HomotopyCategory.quotient _ _).obj ((M.canonicalCosyzygies n).completeCochain τ) ≅
      ((HomotopyCategory.quotient _ _).obj (M.completeCochain τ))⟦(n : ℤ)⟧ := by
  induction n with
  | zero =>
    exact ((shiftFunctorZero (HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ)) ℤ).app _).symm
  | succ n ih =>
    exact canonicalCosyzygyShiftIso τ (M.canonicalCosyzygies n) ≪≫
      (CategoryTheory.shiftFunctor (HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ)) 1).mapIso ih ≪≫
      (shiftFunctorAdd' (HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ))
        (n : ℤ) 1 ((n + 1 : ℕ) : ℤ) (by omega)).symm.app _

end ArExplicit.FiniteLeftModule

end

end OAI
