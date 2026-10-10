import OAI.Combinatorics.ContingencyTables.Counting.CompanionObservationQueriesProgram
import OAI.Combinatorics.ContingencyTables.Counting.CompanionPhaseFinishProgram

namespace OAI

/-! # Executing a phase update from its trajectory and fresh query word -/
namespace ContingencyTables.CompanionObservedUpdateProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped
abbrev Base := (CompanionTraceProgram.ReturnInput×CompanionMultiplierMatrixProgram.FractionMatrix)×TreeFraction.Fraction
abbrev Configs := CompanionObservationQueriesProgram.Config×CompanionObservationQueriesProgram.Config
abbrev Input := (Configs×Base)×List Bool

local instance : Codec Configs := inferInstance
local instance : Codec Base := inferInstance
local instance : Codec (Configs×Base) := inferInstance
local instance : Codec Input := inferInstance

def queryInput (z : Input) : CompanionObservationQueriesProgram.Input :=
  (z.1.1,(z.1.2.1.1.2,z.2))
def queryInputRealizer : Realizer queryInput :=
  pair (composition first first)
    (pair (composition (composition (composition (composition first second) first) first) second) second)
lemma polynomial_queryInput : PolynomialTime queryInputRealizer :=
  polynomial_pair (polynomial_composition polynomial_first polynomial_first)
    (polynomial_pair (polynomial_composition (polynomial_composition
      (polynomial_composition (polynomial_composition polynomial_first polynomial_second) polynomial_first)
        polynomial_first) polynomial_second) polynomial_second)

attribute [local irreducible] queryInput

def finishInput (z : Input) : CompanionPhaseFinishProgram.Input :=
  (z.1.2,CompanionObservationQueriesProgram.output (queryInput z))
def finishInputRealizer : Realizer finishInput :=
  pair (composition first second)
    (composition (f := queryInput) (g := CompanionObservationQueriesProgram.output)
      queryInputRealizer CompanionObservationQueriesProgram.outputRealizer)
lemma polynomial_finishInput : PolynomialTime finishInputRealizer :=
  polynomial_pair (polynomial_composition polynomial_first polynomial_second)
    (polynomial_composition polynomial_queryInput CompanionObservationQueriesProgram.polynomial_output)

attribute [local irreducible] finishInput

def output (z : Input) : Option CompanionPhaseFinishProgram.Stored :=
  CompanionPhaseFinishProgram.output (finishInput z)
def outputRealizer : Realizer output :=
  composition (f := finishInput) (g := CompanionPhaseFinishProgram.output)
    finishInputRealizer CompanionPhaseFinishProgram.outputRealizer
lemma polynomial_output : PolynomialTime outputRealizer :=
  polynomial_composition polynomial_finishInput CompanionPhaseFinishProgram.polynomial_output

end ContingencyTables.CompanionObservedUpdateProgram

end OAI
