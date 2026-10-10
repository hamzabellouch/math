import OAI.Algebra.AuslanderReiten.Coordinates.ConcreteMainCriterion
import OAI.Algebra.AuslanderReiten.Fibers.ConcreteFiberProfile
import OAI.Algebra.AuslanderReiten.Coordinates.ConcreteParameters
import OAI.Algebra.AuslanderReiten.BaseChange.MainScalarExtension

namespace OAI

noncomputable section
open CategoryTheory
open scoped ModuleCat.Algebra
namespace ArExplicit
universe v

attribute [local instance] moduleCatBaseModule moduleCatBaseTower

local instance : HasDerivedCategory (ModuleCat (T BaseField q)) :=
  HasDerivedCategory.standard (ModuleCat (T BaseField q))
local instance : HasDerivedCategory (ModuleCat (A BaseField q)) :=
  HasDerivedCategory.standard (ModuleCat (A BaseField q))

def diagonalClass := T.fiberDiagonalClass q q_ne_zero one_add_q_ne_zero q_noPositivePowerOne
  (parameterUnit 1) (parameterUnit 2)

private abbrev explicitConclusionProof :=
  let hspan := fun z =>
    Exists.elim (T.fiberDiagonalClass_spans q q_ne_zero one_add_q_ne_zero
      q_noPositivePowerOne (parameterUnit 1) (parameterUnit 2) z)
      (fun a ha => Exists.intro a ha.symm)
  T.explicit_mainConclusions q (parameterUnit 1) (parameterUnit 2)
    diagonalClass q_ne_zero one_add_q_ne_zero q_noPositivePowerOne
    (T.fiberDiagonalClass_image q q_ne_zero one_add_q_ne_zero q_noPositivePowerOne
      (parameterUnit 1) (parameterUnit 2))
    hspan
    (T.fiberPositiveRhoPair_bijective q q_ne_zero one_add_q_ne_zero q_noPositivePowerOne
      (parameterUnit 1) (parameterUnit 2))
    parameterUnit_twist_ne

private def verifiedCandidate {R M : Type} [Ring R] [Algebra BaseField R]
    [AddCommGroup M] [Module R M] [Module BaseField M] [IsScalarTower BaseField R M]
    (h : MainConclusions BaseField R M) :
    {c : Candidate // MainConclusions BaseField c.R c.M} :=
  ⟨{ R := R, M := M }, h⟩

private def verifiedCounterexample := verifiedCandidate explicitConclusionProof

def counterexample : Candidate := verifiedCounterexample.val

theorem counterexample_mainConclusions :
    MainConclusions BaseField counterexample.R counterexample.M :=
  verifiedCounterexample.property

theorem fullMainTheorem : FullMainTheorem.{v} :=
  fullMainTheorem_of_mainConclusions counterexample counterexample_mainConclusions

theorem main : AlgebraicIndependent (ZMod 2) parameter ∧ FullMainTheorem.{v} :=
  ⟨parameters_algebraicallyIndependent, fullMainTheorem⟩

end ArExplicit

end

end OAI
