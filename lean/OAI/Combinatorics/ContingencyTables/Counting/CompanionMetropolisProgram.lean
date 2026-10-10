import OAI.Combinatorics.ContingencyTables.Counting.CompanionEvaluatedWeightProgram
import OAI.Combinatorics.ContingencyTables.Machines.FractionMetropolisProgram

namespace OAI

/-! # One physical companion-chain step with independent word fields

The proposed state is computed by the quadratic arithmetic candidate
list. Two disjoint words evaluate the current and candidate states, and
a third field supplies the rational acceptance coin.
-/

namespace ContingencyTables.CompanionMetropolisProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped

abbrev Frame := CompanionEvaluatedWeightProgram.Frame
abbrev Words := Bool × (List Bool × ((List Bool × List Bool) × List Bool))
abbrev Input := (Frame × List ℕ) × Words

def proposed (z : Input) : Option (List ℕ) :=
  CompanionComputedProposal.proposalProgram (z.1.2,z.2.2.1)
def proposedRealizer : Realizer proposed :=
  composition (f := fun z : Input => (z.1.2,z.2.2.1))
    (g := CompanionComputedProposal.proposalProgram)
    (pair (composition first second) (composition (composition second second) first))
    CompanionComputedProposal.proposalProgramRealizer
lemma polynomial_proposed : PolynomialTime proposedRealizer :=
  polynomial_composition (polynomial_pair (polynomial_composition polynomial_first polynomial_second)
    (polynomial_composition (polynomial_composition polynomial_second polynomial_second) polynomial_first))
    CompanionComputedProposal.polynomial_proposalProgram

private def defaultCode (z : List ℕ × Option (List ℕ)) : List ℕ := z.2.getD z.1
private def defaultCodeRealizer : Realizer defaultCode :=
  (optionCases identity second).recode id defaultCode (fun _ => rfl)
    (by rintro ⟨d,o⟩; cases o <;> rfl)
private lemma polynomial_defaultCode : PolynomialTime defaultCodeRealizer := by
  unfold defaultCodeRealizer
  apply polynomial_recode
  exact polynomial_optionCases polynomial_identity polynomial_second

def candidate (z : Input) : List ℕ := (proposed z).getD z.1.2
def candidateRealizer : Realizer candidate :=
  composition (f := fun z : Input => (z.1.2,proposed z))
    (g := defaultCode) (pair (composition first second) proposedRealizer) defaultCodeRealizer
lemma polynomial_candidate : PolynomialTime candidateRealizer :=
  polynomial_composition (polynomial_pair (polynomial_composition polynomial_first polynomial_second)
    polynomial_proposed) polynomial_defaultCode

attribute [local irreducible] candidate

def currentInput (z : Input) : CompanionEvaluatedWeightProgram.Input := (z.1,z.2.2.2.1.1)
def currentInputRealizer : Realizer currentInput :=
  pair first (composition (composition (composition (composition second second) second) first) first)
lemma polynomial_currentInput : PolynomialTime currentInputRealizer :=
  polynomial_pair polynomial_first (polynomial_composition
    (polynomial_composition (polynomial_composition (polynomial_composition
      polynomial_second polynomial_second) polynomial_second) polynomial_first) polynomial_first)

def targetInput (z : Input) : CompanionEvaluatedWeightProgram.Input :=
  ((z.1.1,candidate z),z.2.2.2.1.2)
def targetInputRealizer : Realizer targetInput :=
  pair (pair (composition first first) candidateRealizer)
    (composition (composition (composition (composition second second) second) first) second)
lemma polynomial_targetInput : PolynomialTime targetInputRealizer :=
  polynomial_pair (polynomial_pair (polynomial_composition polynomial_first polynomial_first) polynomial_candidate)
    (polynomial_composition (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_second polynomial_second) polynomial_second) polynomial_first) polynomial_second)

attribute [local irreducible] currentInput targetInput CompanionEvaluatedWeightProgram.output

def currentValue (z : Input) : TreeFraction.Fraction := CompanionEvaluatedWeightProgram.output (currentInput z)
def currentValueRealizer : Realizer currentValue :=
  composition (f := currentInput) (g := CompanionEvaluatedWeightProgram.output)
    currentInputRealizer CompanionEvaluatedWeightProgram.outputRealizer
lemma polynomial_currentValue : PolynomialTime currentValueRealizer :=
  polynomial_composition polynomial_currentInput CompanionEvaluatedWeightProgram.polynomial_output

def targetValue (z : Input) : TreeFraction.Fraction := CompanionEvaluatedWeightProgram.output (targetInput z)
def targetValueRealizer : Realizer targetValue :=
  composition (f := targetInput) (g := CompanionEvaluatedWeightProgram.output)
    targetInputRealizer CompanionEvaluatedWeightProgram.outputRealizer
lemma polynomial_targetValue : PolynomialTime targetValueRealizer :=
  polynomial_composition polynomial_targetInput CompanionEvaluatedWeightProgram.polynomial_output

attribute [local irreducible] currentValue targetValue

def acceptanceInput (z : Input) : FractionMetropolisProgram.Input :=
  ((currentValue z,targetValue z),z.2.2.2.2)
def acceptanceInputRealizer : Realizer acceptanceInput :=
  pair (pair currentValueRealizer targetValueRealizer)
    (composition (composition (composition second second) second) second)
lemma polynomial_acceptanceInput : PolynomialTime acceptanceInputRealizer :=
  polynomial_pair (polynomial_pair polynomial_currentValue polynomial_targetValue)
    (polynomial_composition (polynomial_composition (polynomial_composition
      polynomial_second polynomial_second) polynomial_second) polynomial_second)

def accepted (z : Input) : Bool := FractionMetropolisProgram.accept (acceptanceInput z)
def acceptedRealizer : Realizer accepted :=
  composition (f := acceptanceInput) (g := FractionMetropolisProgram.accept)
    acceptanceInputRealizer FractionMetropolisProgram.acceptRealizer
lemma polynomial_accepted : PolynomialTime acceptedRealizer :=
  polynomial_composition polynomial_acceptanceInput FractionMetropolisProgram.polynomial_accept

attribute [local irreducible] accepted

def output (z : Input) : List ℕ := if z.2.1 then z.1.2 else if accepted z then candidate z else z.1.2
def outputRealizer : Realizer output :=
  choose (composition second first) (composition first second)
    (choose acceptedRealizer candidateRealizer (composition first second))
theorem polynomial_output : PolynomialTime outputRealizer :=
  polynomial_choose (polynomial_composition polynomial_second polynomial_first)
    (polynomial_composition polynomial_first polynomial_second)
    (polynomial_choose polynomial_accepted polynomial_candidate
      (polynomial_composition polynomial_first polynomial_second))

lemma output_hold (z : Input) (h : z.2.1=true) : output z=z.1.2 := by
  simp only [output,h,ite_true]

end ContingencyTables.CompanionMetropolisProgram

end OAI
