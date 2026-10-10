import OAI.Algebra.AuslanderReiten.Stable.CanonicalCosyzygyShift
import OAI.Algebra.AuslanderReiten.Modules.FiniteModuleEvaluation

namespace OAI

noncomputable section
namespace ArExplicit.FiniteLeftModule
open CategoryTheory
open scoped TensorProduct
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]
variable (X : FiniteLeftModule k R) (τe : FrobeniusTrace k (R ⊗[k] Rᵐᵒᵖ))
variable (τ : FrobeniusTrace k R) (M : FiniteLeftModule k (R ⊗[k] Rᵐᵒᵖ))
variable [Module.Projective Rᵐᵒᵖ (EnvelopingBimodule k R M.canonicalCosyzygy.carrier)]

def evaluatedCanonicalCosyzygyShiftIso :
    (HomotopyCategory.quotient _ _).obj ((X.evaluated M.canonicalCosyzygy).completeCochain τ) ≅
      ((HomotopyCategory.quotient _ _).obj ((X.evaluated M).completeCochain τ))⟦(1 : ℤ)⟧ := by
  letI : Module.Projective (R ⊗[k] Rᵐᵒᵖ) M.canonicalEnvelopeModule.carrier :=
    CoinducedModule.projective (M := M.carrier) τe
  exact evaluationSuccessorIso X (M.canonicalEmbedding).hom M.canonicalCosyzygyQuotient
    CoinducedModule.embedding_injective M.canonicalCosyzygyQuotient_surjective
    M.canonicalCosyzygy_exact τ

variable (hr : ∀ n, Module.Projective Rᵐᵒᵖ
  (EnvelopingBimodule k R (M.canonicalCosyzygies n).carrier))

def evaluatedCanonicalCosyzygiesShiftIso (n : ℕ) :
    (HomotopyCategory.quotient _ _).obj ((X.evaluated (M.canonicalCosyzygies n)).completeCochain τ) ≅
      ((HomotopyCategory.quotient _ _).obj ((X.evaluated M).completeCochain τ))⟦(n : ℤ)⟧ := by
  induction n with
  | zero =>
    exact ((shiftFunctorZero (HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ)) ℤ).app _).symm
  | succ n ih =>
    letI : Module.Projective Rᵐᵒᵖ
        (EnvelopingBimodule k R (M.canonicalCosyzygies n).canonicalCosyzygy.carrier) := hr (n+1)
    exact evaluatedCanonicalCosyzygyShiftIso X τe τ (M.canonicalCosyzygies n) ≪≫
      (CategoryTheory.shiftFunctor (HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ)) 1).mapIso ih ≪≫
      (shiftFunctorAdd' (HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ))
        (n : ℤ) 1 ((n+1 : ℕ) : ℤ) (by omega)).symm.app _

end ArExplicit.FiniteLeftModule

end

end OAI
