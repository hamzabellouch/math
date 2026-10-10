import OAI.Algebra.AuslanderReiten.Evaluation.ConcreteEvaluatedConeShift
import OAI.Algebra.AuslanderReiten.Cones.ConcreteTwoConeCoordinates

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)
local notation "R₀" => A k q
local notation "X₀" => A.simpleFiniteModule q
local notation "τ₀" => AFrobeniusTrace k q
local notation "HC" => HomotopyCategory (ModuleCat R₀) (ComplexShape.up ℤ)
local notation "Q₀" => HomotopyCategory.quotient (ModuleCat R₀) (ComplexShape.up ℤ)

abbrev branchTargetObject :=
  (Q₀).obj ((FiniteLeftModule.evaluated X₀ (fiberTarget q)).completeCochain τ₀)

abbrev BranchHom (a : ℤ) := evaluatedSimpleObject q ⟶ (branchTargetObject q)⟦a⟧

def branchTargetGradedIso (a : ℤ) : (branchTargetObject q)⟦a⟧ ≅
    ((simpleTopTriangle q 0).obj₂)⟦a+3⟧ :=
  (CategoryTheory.shiftFunctor HC a).mapIso (evaluatedBranchTargetShiftIso q) ≪≫
    (CategoryTheory.shiftFunctorAdd' HC 3 a (a+3) (add_comm 3 a)).symm.app _

def branchHomEquiv (a : ℤ) : BranchHom q a ≃ₗ[k] twoConeHom q (a+3) :=
  Linear.homCongr k (Iso.refl _) (branchTargetGradedIso q a)

def branchPlainHomEquiv :
    (evaluatedSimpleObject q ⟶ branchTargetObject q) ≃ₗ[k] twoConeHom q 3 :=
  Linear.homCongr k (Iso.refl _) (evaluatedBranchTargetShiftIso q)

end ArExplicit.T

end

end OAI
