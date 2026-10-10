import OAI.Algebra.AuslanderReiten.Evaluation.EvaluatedCoverCoordinates
import OAI.Algebra.AuslanderReiten.Evaluation.EvaluatedBaseShift
import OAI.Algebra.AuslanderReiten.Evaluation.EvaluatedQuotientCubic
import OAI.Algebra.AuslanderReiten.HomComplex.FullHomShiftedMaps
import OAI.Algebra.AuslanderReiten.HomComplex.TensorFullHomZero

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory
open CochainComplex CochainComplex.HomComplex CompleteComparison
open scoped TensorProduct ModuleCat.Algebra
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)
local notation "R₀" => A k q
local notation "X₀" => A.simpleFiniteModule q
local notation "D₀" => bimoduleTwoConeData q
local notation "hf₀" => bimodule_term_finite_k q
local notation "τ₀" => AFrobeniusTrace k q
local notation "Q₀" => HomotopyCategory.quotient (ModuleCat R₀) (ComplexShape.up ℤ)

abbrev simpleCoverClass (n : ℕ) :=
  (TwoCone.evaluatedCoverTower D₀ hf₀ X₀ (bimodule_exact q)
    (baseTail_right_projective q) (bimodule_term_projective q)).coverClassFrom τ₀ X₀
    (CohomologyClass.mk (Cocycle.ofHom
      (FiniteLeftModule.resolutionMap τ₀ (evaluatedBaseZeroEquiv q).symm.toLinearMap))) n

theorem simpleCoverClass_hom (n : ℕ) :
    fullHomShiftedHomotopyEquiv k _ _ (n : ℤ) (simpleCoverClass q n) =
      (simpleToEvaluatedBaseShiftIso q n).hom :=
  TwoCone.evaluatedCoverTower_coverClassFrom_hom D₀ hf₀ X₀ (bimodule_exact q)
    (baseTail_right_projective q) (bimodule_term_projective q) τ₀ X₀
    (FiniteLeftModule.resolutionMap τ₀ (evaluatedBaseZeroEquiv q).symm.toLinearMap) n

def firstCubicBack : (evaluatedBaseModule q 3).carrier →ₗ[R₀] (X₀).carrier :=
  (evaluatedBaseZeroEquiv q).toLinearMap.comp
    (FiniteLeftModule.evaluationMap X₀
      (M := TwoCone.baseCokernelModule D₀ hf₀ 3)
      (N := TwoCone.baseCokernelModule D₀ hf₀ 0) (TwoCone.firstCokernelMap D₀ 0))

def secondCubicBack : (evaluatedBaseModule q 3).carrier →ₗ[R₀] (X₀).carrier :=
  (evaluatedBaseZeroEquiv q).toLinearMap.comp
    (FiniteLeftModule.evaluationMap X₀
      (M := TwoCone.baseCokernelModule D₀ hf₀ 3)
      (N := TwoCone.baseCokernelModule D₀ hf₀ 0) (TwoCone.secondCokernelMap D₀ 0))

def firstCoverClass : CohomologyClass (A.simpleComplete q) (A.simpleComplete q) 3 :=
  fullHomPostcomp (FiniteLeftModule.resolutionMap τ₀ (firstCubicBack q)) 3 (simpleCoverClass q 3)

def secondCoverClass : CohomologyClass (A.simpleComplete q) (A.simpleComplete q) 3 :=
  fullHomPostcomp (FiniteLeftModule.resolutionMap τ₀ (secondCubicBack q)) 3 (simpleCoverClass q 3)

theorem firstCoverClass_hom :
    fullHomShiftedHomotopyEquiv k _ _ 3 (firstCoverClass q) =
      (simpleToEvaluatedBaseShiftIso q 3).hom ≫
        (TwoCone.evaluatedFirstCokernel D₀ hf₀ X₀ τ₀ 0 ≫ (evaluatedBaseZeroResolutionIso q).hom)⟦(3 : ℤ)⟧' := by
  erw [firstCoverClass, fullHomShiftedHomotopyEquiv_postcomp, simpleCoverClass_hom]
  congr 1
  apply congrArg (fun f => (CategoryTheory.shiftFunctor
    (HomotopyCategory (ModuleCat R₀) (ComplexShape.up ℤ)) (3 : ℤ)).map f)
  change (Q₀).map (FiniteLeftModule.resolutionMap τ₀ (firstCubicBack q)) = _
  exact FiniteLeftModule.resolutionMap_comp τ₀ _ _

theorem secondCoverClass_hom :
    fullHomShiftedHomotopyEquiv k _ _ 3 (secondCoverClass q) =
      (simpleToEvaluatedBaseShiftIso q 3).hom ≫
        (TwoCone.evaluatedSecondCokernel D₀ hf₀ X₀ τ₀ 0 ≫ (evaluatedBaseZeroResolutionIso q).hom)⟦(3 : ℤ)⟧' := by
  erw [secondCoverClass, fullHomShiftedHomotopyEquiv_postcomp, simpleCoverClass_hom]
  congr 1
  apply congrArg (fun f => (CategoryTheory.shiftFunctor
    (HomotopyCategory (ModuleCat R₀) (ComplexShape.up ℤ)) (3 : ℤ)).map f)
  change (Q₀).map (FiniteLeftModule.resolutionMap τ₀ (secondCubicBack q)) = _
  exact FiniteLeftModule.resolutionMap_comp τ₀ _ _

end ArExplicit.T

end

end OAI
