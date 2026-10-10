import OAI.Algebra.AuslanderReiten.Cones.ConcreteTwoConeEvaluation
import OAI.Algebra.AuslanderReiten.Tensor.EnvelopingBalancedEquiv
import OAI.Algebra.AuslanderReiten.Bar.AugmentedBarEvaluation
import OAI.Algebra.AuslanderReiten.Resolutions.FiniteResolutionIso
import OAI.Algebra.AuslanderReiten.Coordinates.ShiftedObjectCoordinates

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory
open scoped TensorProduct
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)
local notation "R" => A k q
local notation "X" => A.simpleFiniteModule q
local notation "D" => bimoduleTwoConeData q
local notation "hf" => bimodule_term_finite_k q
local notation "τ" => AFrobeniusTrace k q
local notation "Q" => HomotopyCategory.quotient (ModuleCat R) (ComplexShape.up ℤ)
local notation "HC" => HomotopyCategory (ModuleCat R) (ComplexShape.up ℤ)

local instance baseScalar (n : ℕ) : Module k (TwoCone.baseCokernelModule D hf n).carrier :=
  (TwoCone.baseCokernelModule D hf n).scalar
local instance baseTower (n : ℕ) : IsScalarTower k (R ⊗[k] Rᵐᵒᵖ)
    (TwoCone.baseCokernelModule D hf n).carrier :=
  (TwoCone.baseCokernelModule D hf n).tower

abbrev evaluatedBaseModule (n : ℕ) :=
  FiniteLeftModule.evaluated X (TwoCone.baseCokernelModule D hf n)

abbrev evaluatedBaseResolution (n : ℕ) := (Q).obj ((evaluatedBaseModule q n).completeCochain τ)

def evaluatedBaseZeroEquiv : (evaluatedBaseModule q 0).carrier ≃ₗ[R] (X).carrier :=
  (EnvelopingBimodule.tensorCongr
    (M := (TwoCone.baseCokernelModule D hf 0).carrier)
    (N := AbsoluteBar.moduleObject k R 0) (bimoduleBaseCokernelEquiv q) (X).carrier).trans
      (BarBalanced.zeroEvaluationEquiv k R (X).carrier)

@[simp] theorem evaluatedBaseZeroEquiv_tmul
    (b : EnvelopingBimodule k R (TwoCone.baseCokernelModule D hf 0).carrier)
    (x : (X).carrier) :
    evaluatedBaseZeroEquiv q (BalancedTensor.tmul b x) =
      (show R from bimoduleBaseCokernelEquiv q b.value) • x := rfl

def evaluatedBaseZeroResolutionIso : evaluatedBaseResolution q 0 ≅
    (Q).obj ((X).completeCochain τ) :=
  FiniteLeftModule.resolutionIso (M := evaluatedBaseModule q 0) (N := X) τ
    (evaluatedBaseZeroEquiv q)

def evaluatedBaseStepIso (n : ℕ) : evaluatedBaseResolution q n ≅
    (evaluatedBaseResolution q (n+1))⟦(1 : ℤ)⟧ :=
  TwoCone.evaluatedBaseSuccessorIso D hf (bimodule_exact q) (baseTail_right_projective q)
    (bimodule_term_projective q) X τ n

def evaluatedBaseIteration (n : ℕ) : evaluatedBaseResolution q 0 ≅
    (evaluatedBaseResolution q n)⟦(n : ℤ)⟧ :=
  iteratedShiftIso (evaluatedBaseResolution q) (evaluatedBaseStepIso q) n

def simpleToEvaluatedBaseShiftIso (n : ℕ) : (Q).obj ((X).completeCochain τ) ≅
    (evaluatedBaseResolution q n)⟦(n : ℤ)⟧ :=
  (evaluatedBaseZeroResolutionIso q).symm ≪≫ evaluatedBaseIteration q n

theorem simpleToEvaluatedBaseShiftIso_succ (n : ℕ) :
    (simpleToEvaluatedBaseShiftIso q (n+1)).hom =
      (simpleToEvaluatedBaseShiftIso q n).hom ≫
        (CategoryTheory.shiftFunctor HC (n : ℤ)).map (evaluatedBaseStepIso q n).hom ≫
          (CategoryTheory.shiftFunctorAdd' HC (1 : ℤ) (n : ℤ)
            ((n+1 : ℕ) : ℤ) (by omega)).inv.app (evaluatedBaseResolution q (n+1)) := by
  simp only [simpleToEvaluatedBaseShiftIso, evaluatedBaseIteration, iteratedShiftIso,
    Iso.trans_hom, Category.assoc, Functor.mapIso_hom, Iso.app_hom, Iso.symm_hom]

def evaluatedBaseNegativeShiftIso (n : ℕ) : evaluatedBaseResolution q n ≅
    ((Q).obj ((X).completeCochain τ))⟦-(n : ℤ)⟧ :=
  negativeShiftIso (n : ℤ) (simpleToEvaluatedBaseShiftIso q n)

def evaluatedBaseGradedIso (n : ℕ) (a : ℤ) : (evaluatedBaseResolution q n)⟦a⟧ ≅
    ((Q).obj ((X).completeCochain τ))⟦a-(n : ℤ)⟧ :=
  shiftedNegativeIso (n : ℤ) (simpleToEvaluatedBaseShiftIso q n) a

open scoped ModuleCat.Algebra

def evaluatedBaseHomEquiv (n : ℕ) (a : ℤ) :
    ((Q).obj ((X).completeCochain τ) ⟶ (evaluatedBaseResolution q n)⟦a⟧) ≃ₗ[k]
      ((Q).obj ((X).completeCochain τ) ⟶ ((Q).obj ((X).completeCochain τ))⟦a-(n : ℤ)⟧) :=
  shiftedNegativeHomEquiv (n : ℤ) (simpleToEvaluatedBaseShiftIso q n) k _ a

end ArExplicit.T

end

end OAI
