import OAI.Combinatorics.ContingencyTables.Counting.CountingDirectProgram
import OAI.Combinatorics.ContingencyTables.Counting.CountingInputParser
import OAI.Combinatorics.ContingencyTables.Machines.NetworkFeasibilityProgram
import OAI.Combinatorics.ContingencyTables.Machines.FractionOutputProgram

namespace OAI

/-! # Public dispatch for the two counting branches

The positive-label evaluator is a program parameter, instantiated by the
adaptive estimator. Feasibility and the zero-label branch are computed from
the same parsed input used by the complete public machine.
-/
namespace ContingencyTables.CountingBranchProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped
abbrev Request := CountingDirectProgram.Request
abbrev Input := CountingDirectProgram.Input

/-- Reassociate the two rational parameters without re-encoding them. -/
def request (z : CountingInputParser.Input) : Request := ((z.1,z.2.1),z.2.2)
def requestRealizer : Realizer request :=
  pair (pair first (composition second first)) (composition second second)
lemma polynomial_request : PolynomialTime requestRealizer :=
  polynomial_pair (polynomial_pair polynomial_first
    (polynomial_composition polynomial_second polynomial_first))
    (polynomial_composition polynomial_second polynomial_second)

def feasible (z : Request) : Bool := NetworkFeasibilityProgram.test z.1.1
def feasibleRealizer : Realizer feasible :=
  composition (f := fun z : Request => z.1.1) (g := NetworkFeasibilityProgram.test)
    (composition first first) NetworkFeasibilityProgram.testRealizer
lemma polynomial_feasible : PolynomialTime feasibleRealizer :=
  polynomial_composition (polynomial_composition polynomial_first polynomial_first)
    NetworkFeasibilityProgram.polynomial_test

def direct (z : Request) : Bool := decide (CountingComputedSettings.labelCount z.1=0)
def directRealizer : Realizer direct :=
  composition (f := fun z : Request => (CountingComputedSettings.labelCount z.1,0))
    (g := fun p : ℕ×ℕ => decide (p.1=p.2))
    (pair (composition (f := fun z : Request => z.1) (g := CountingComputedSettings.labelCount)
      first CountingComputedSettings.labelCountRealizer) (constant 0)) natEqual
lemma polynomial_direct : PolynomialTime directRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first CountingComputedSettings.polynomial_labelCount)
    (polynomial_constant 0)) polynomial_natEqual

attribute [local irreducible] feasible direct

section Evaluator
variable (positive : Input → TreeFraction.Fraction) (F : Realizer positive)

def feasibleOutput (z : Input) : TreeFraction.Fraction :=
  if direct z.1 then CountingDirectProgram.output z else positive z
def feasibleOutputRealizer : Realizer (feasibleOutput positive) :=
  choose (composition (f := fun z : Input => z.1) (g := direct) first directRealizer) CountingDirectProgram.outputRealizer F
lemma polynomial_feasibleOutput (hF : PolynomialTime F) :
    PolynomialTime (feasibleOutputRealizer positive F) :=
  polynomial_choose (polynomial_composition polynomial_first polynomial_direct)
    CountingDirectProgram.polynomial_output hF

attribute [local irreducible] feasibleOutput

def output (z : Input) : TreeFraction.Fraction :=
  if feasible z.1 then feasibleOutput positive z else (0,1)
def outputRealizer : Realizer (output positive) :=
  choose (composition (f := fun z : Input => z.1) (g := feasible) first feasibleRealizer) (feasibleOutputRealizer positive F) (constant (0,1))
lemma polynomial_output (hF : PolynomialTime F) : PolynomialTime (outputRealizer positive F) :=
  polynomial_choose (polynomial_composition polynomial_first polynomial_feasible)
    (polynomial_feasibleOutput positive F hF) (polynomial_constant (0,1))

attribute [local irreducible] output

def parsedInput (z : List Symbol×List Bool) : Input :=
  (request (CountingInputParser.parseInput z.1),z.2)
def parsedInputRealizer : Realizer parsedInput :=
  pair (composition (composition first CountingInputParser.publicRealizer) requestRealizer) second
lemma polynomial_parsedInput : PolynomialTime parsedInputRealizer :=
  polynomial_pair (polynomial_composition
    (polynomial_composition polynomial_first CountingInputParser.polynomial_public) polynomial_request)
    polynomial_second

def publicOutput (z : List Symbol×List Bool) : List Symbol :=
  FractionOutputProgram.output (output positive (parsedInput z))
def publicOutputRealizer : Realizer (publicOutput positive) :=
  composition (f := fun z => output positive (parsedInput z)) (g := FractionOutputProgram.output)
    (composition (f := parsedInput) (g := output positive) parsedInputRealizer (outputRealizer positive F))
    FractionOutputProgram.outputRealizer
lemma polynomial_publicOutput (hF : PolynomialTime F) :
    PolynomialTime (publicOutputRealizer positive F) :=
  polynomial_composition (polynomial_composition polynomial_parsedInput
    (polynomial_output positive F hF)) FractionOutputProgram.polynomial_output

lemma publicOutput_eq (z : List Symbol×List Bool) :
    publicOutput positive z=encodeRat (TreeFraction.val (output positive (parsedInput z))) :=
  FractionOutputProgram.output_eq _

lemma publicOutput_symbols (z : List Symbol×List Bool) (a : Symbol)
    (ha : a∈publicOutput positive z) : a≠0 ∧ a≠6 ∧ a≠7 :=
  FractionOutputProgram.output_symbols _ a ha

lemma output_nonnegative (z : Input) : 0 ≤ TreeFraction.val (output positive z) :=
  TreeFraction.val_nonneg _

end Evaluator

section Budget
variable (positive : Request → ℕ) (N : Realizer positive)

def feasibleBudget (z : Request) : ℕ := if direct z then CountingDirectProgram.budget z else positive z
def feasibleBudgetRealizer : Realizer (feasibleBudget positive) :=
  choose directRealizer CountingDirectProgram.budgetRealizer N
lemma polynomial_feasibleBudget (hN : PolynomialTime N) :
    PolynomialTime (feasibleBudgetRealizer positive N) :=
  polynomial_choose polynomial_direct CountingDirectProgram.polynomial_budget hN

attribute [local irreducible] feasibleBudget

def budget (z : Request) : ℕ := if feasible z then feasibleBudget positive z else 0
def budgetRealizer : Realizer (budget positive) :=
  choose feasibleRealizer (feasibleBudgetRealizer positive N) (constant 0)
lemma polynomial_budget (hN : PolynomialTime N) : PolynomialTime (budgetRealizer positive N) :=
  polynomial_choose polynomial_feasible (polynomial_feasibleBudget positive N hN) (polynomial_constant 0)

attribute [local irreducible] budget

def publicBudget (as : List Symbol) : ℕ := budget positive (request (CountingInputParser.parseInput as))
def publicBudgetRealizer : Realizer (publicBudget positive) :=
  composition (f := fun as => request (CountingInputParser.parseInput as)) (g := budget positive)
    (composition CountingInputParser.publicRealizer requestRealizer) (budgetRealizer positive N)
lemma polynomial_publicBudget (hN : PolynomialTime N) : PolynomialTime (publicBudgetRealizer positive N) :=
  polynomial_composition (polynomial_composition CountingInputParser.polynomial_public polynomial_request)
    (polynomial_budget positive N hN)
end Budget

end ContingencyTables.CountingBranchProgram

end OAI
