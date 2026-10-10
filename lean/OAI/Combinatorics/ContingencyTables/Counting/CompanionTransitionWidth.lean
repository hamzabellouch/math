import OAI.Combinatorics.ContingencyTables.Counting.CompanionMetropolisWordSemantics
import OAI.Combinatorics.ContingencyTables.Machines.ScalarScheduleProgram

namespace OAI

/-! # Executing the exact companion transition word length -/

namespace ContingencyTables.CompanionTransitionWidth

open MatchingFPRAS MatchingFPRAS.TreeTyped ScalarScheduleProgram
open CompanionMetropolisWordProgram

def values (z : Input) : List ℕ := [proposalWidth z,queryWidth z,z.1.1.2]
attribute [local irreducible] proposalWidth queryWidth
def valuesRealizer : Realizer values := by
  let k : Realizer (fun z : Input => z.1.1.2) := composition (composition first first) second
  let ks : Realizer (fun z : Input => [z.1.1.2]) :=
    composition (f := fun z : Input => (z.1.1.2,([] : List ℕ))) (g := fun p => p.1::p.2)
      (pair k (constant [])) listCons
  let qs : Realizer (fun z : Input => [queryWidth z,z.1.1.2]) :=
    composition (f := fun z : Input => (queryWidth z,[z.1.1.2])) (g := fun p => p.1::p.2)
      (pair queryWidthRealizer ks) listCons
  exact composition (f := fun z : Input => (proposalWidth z,[queryWidth z,z.1.1.2]))
    (g := fun p => p.1::p.2) (pair proposalWidthRealizer qs) listCons
lemma polynomial_values : PolynomialTime valuesRealizer := by
  unfold valuesRealizer
  exact polynomial_composition (polynomial_pair polynomial_proposalWidth
    (polynomial_composition (polynomial_pair polynomial_queryWidth
      (polynomial_composition (polynomial_pair
        (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_second)
        (polynomial_constant [])) polynomial_listCons)) polynomial_listCons)) polynomial_listCons

def expression : Expr := 1+(Expr.input 0+((Expr.input 1+Expr.input 1)+Expr.input 2))
def width (z : Input) : ℕ := expression.eval (values z)
def widthRealizer : Realizer width :=
  composition (f := values) (g := expression.eval) valuesRealizer expression.realizer
theorem polynomial_width : PolynomialTime widthRealizer :=
  polynomial_composition polynomial_values expression.polynomial

lemma width_eq (z : Input) : width z=1+(proposalWidth z+((queryWidth z+queryWidth z)+z.1.1.2)) := by
  rfl

lemma width_pos (z : Input) : 0 < width z := by rw [width_eq]; omega

noncomputable section
open CompanionFactorialApplication CompanionComputedInitial CompanionArithmeticProposal
open CompanionOracleDensity CompanionWeightOracle GridBoundary
variable {m n : ℕ}

theorem width_config (A : Instance (Fin m) (Fin n)) (C K j k : ℕ) (xi : ℚ)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (degree depth : List Bool) (w : CompanionMultiplierMatrixProgram.FractionMatrix)
    (S : Set (Labels A × Bool)) (bits : List Bool) :
    width (packed (RootedLabelWeightProgram.config A C K j xi xi z v degree depth,w)
      k (encodeSet (coordinateOrder A) S) bits)=CompanionBooleanPhase.stepBits A C K j k xi := by
  rw [width_eq,proposalWidth_code,queryWidth_config]
  rfl

end
end ContingencyTables.CompanionTransitionWidth

end OAI
