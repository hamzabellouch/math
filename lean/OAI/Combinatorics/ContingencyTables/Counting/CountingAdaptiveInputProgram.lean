import OAI.Combinatorics.ContingencyTables.Counting.CountingPreparedState
import OAI.Combinatorics.ContingencyTables.Counting.CompanionInitialStoredProgram
import OAI.Combinatorics.ContingencyTables.Counting.CompanionRestartInitializer
import OAI.Combinatorics.ContingencyTables.Counting.CompanionPhaseFinishProgram
import OAI.Combinatorics.ContingencyTables.Counting.CountingDirectProgram

namespace OAI

/-! # Original-input preparation for a positive-label counting run -/
namespace ContingencyTables.CountingAdaptiveInputProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped

abbrev Input := CountingBaseProgram.Input×List Bool
abbrev Prepared := CompanionRestartInitializer.Prepared
abbrev Stored := CompanionPhaseFinishProgram.Stored
abbrev Output := Prepared×Stored

def prepared (z : Input) : Prepared := CountingPreparedState.output z.1
def preparedRealizer : Realizer prepared :=
  composition (f := Prod.fst) (g := CountingPreparedState.output) first CountingPreparedState.outputRealizer
lemma polynomial_prepared : PolynomialTime preparedRealizer :=
  polynomial_composition polynomial_first CountingPreparedState.polynomial_output

def capacities (z : Input) : List ℕ := CompanionRestartInitializer.capacities (prepared z)
def capacitiesRealizer : Realizer capacities :=
  composition (f := prepared) (g := CompanionRestartInitializer.capacities)
    preparedRealizer CompanionRestartInitializer.capacitiesRealizer
lemma polynomial_capacities : PolynomialTime capacitiesRealizer :=
  polynomial_composition polynomial_prepared CompanionRestartInitializer.polynomial_capacities

def labelWidth (z : Input) : ℕ := 2*CountingComputedSettings.labelCount z.1
def labelWidthRealizer : Realizer labelWidth :=
  composition (f := fun z : Input => (2,CountingComputedSettings.labelCount z.1))
    (g := fun p : ℕ×ℕ => p.1*p.2)
    (pair (constant 2) (composition (f := Prod.fst) (g := CountingComputedSettings.labelCount)
      first CountingComputedSettings.labelCountRealizer)) multiply
lemma polynomial_labelWidth : PolynomialTime labelWidthRealizer :=
  polynomial_composition (polynomial_pair (polynomial_constant 2)
    (polynomial_composition polynomial_first CountingComputedSettings.polynomial_labelCount)) polynomial_multiply

def zeroCode (z : Input) : List ℕ := (z.2.take (labelWidth z)).map (fun _ => 0)
def zeroCodeRealizer : Realizer zeroCode :=
  composition (f := fun z : Input => z.2.take (labelWidth z))
    (g := fun bs : List Bool => bs.map (fun _ => (0:ℕ)))
    (composition (f := fun z : Input => (z.2,labelWidth z)) (g := fun p : List Bool×ℕ => p.1.take p.2)
      (pair second labelWidthRealizer) takeFast) (map (constant 0))
lemma polynomial_zeroCode : PolynomialTime zeroCodeRealizer :=
  polynomial_composition (polynomial_composition (polynomial_pair polynomial_second polynomial_labelWidth)
    polynomial_takeFast) (polynomial_map (polynomial_constant 0))

def initialInput (z : Input) : CompanionInitialStoredProgram.Input :=
  (CountingPreparedState.catalog z.1,(capacities z,zeroCode z))
def initialInputRealizer : Realizer initialInput :=
  pair (composition (f := Prod.fst) (g := CountingPreparedState.catalog)
    first CountingPreparedState.catalogRealizer) (pair capacitiesRealizer zeroCodeRealizer)
lemma polynomial_initialInput : PolynomialTime initialInputRealizer :=
  polynomial_pair (polynomial_composition polynomial_first CountingPreparedState.polynomial_catalog)
    (polynomial_pair polynomial_capacities polynomial_zeroCode)

def initial (z : Input) : Stored := CompanionInitialStoredProgram.output (initialInput z)
def initialRealizer : Realizer initial :=
  composition (f := initialInput) (g := CompanionInitialStoredProgram.output)
    initialInputRealizer CompanionInitialStoredProgram.outputRealizer
lemma polynomial_initial : PolynomialTime initialRealizer :=
  polynomial_composition polynomial_initialInput CompanionInitialStoredProgram.polynomial_output

def output (z : Input) : Output := (prepared z,initial z)
def outputRealizer : Realizer output := pair preparedRealizer initialRealizer
theorem polynomial_output : PolynomialTime outputRealizer :=
  polynomial_pair polynomial_prepared polynomial_initial

/-- The outer confidence parameter is handled by independent repetition. -/
def runInput (z : CountingDirectProgram.Input) : Output×List Bool := (output (z.1.1,z.2),z.2)
def runInputRealizer : Realizer runInput :=
  pair (composition (f := fun z : CountingDirectProgram.Input => (z.1.1,z.2)) (g := output)
    (pair (composition first first) second) outputRealizer) second
theorem polynomial_runInput : PolynomialTime runInputRealizer :=
  polynomial_pair (polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_first) polynomial_second)
    polynomial_output) polynomial_second

end ContingencyTables.CountingAdaptiveInputProgram

end OAI
