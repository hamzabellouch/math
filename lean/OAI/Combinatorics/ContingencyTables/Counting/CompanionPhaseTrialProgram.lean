import OAI.Combinatorics.ContingencyTables.Counting.CompanionTrajectoryProgram
import OAI.Combinatorics.ContingencyTables.Counting.CompanionObservedUpdateProgram

namespace OAI

/-! # A complete executed trajectory and fresh-observation phase trial -/
namespace ContingencyTables.CompanionPhaseTrialProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped
abbrev Stored := CompanionPhaseFinishProgram.Stored
abbrev Frame := CompanionObservedUpdateProgram.Configs×Stored
abbrev Input := (Frame×CompanionTrajectoryProgram.Input)×List Bool
local instance : Codec CompanionObservedUpdateProgram.Configs := inferInstance
local instance : Codec CompanionObservedUpdateProgram.Base := inferInstance
local instance : Codec (CompanionObservedUpdateProgram.Configs×CompanionObservedUpdateProgram.Base) := inferInstance
local instance : Codec CompanionObservedUpdateProgram.Input := inferInstance
local instance : Codec Frame := inferInstance
local instance : Codec (Frame×CompanionTrajectoryProgram.Input) := inferInstance
local instance : Codec Input := inferInstance

def trajectory (z : Input) : List (List ℕ) := CompanionTrajectoryProgram.output z.1.2
def trajectoryRealizer : Realizer trajectory :=
  composition (f := fun z : Input => z.1.2) (g := CompanionTrajectoryProgram.output)
    (composition first second) CompanionTrajectoryProgram.outputRealizer
lemma polynomial_trajectory : PolynomialTime trajectoryRealizer :=
  polynomial_composition (polynomial_composition polynomial_first polynomial_second)
    CompanionTrajectoryProgram.polynomial_output

def catalogue (z : Input) : List (ℕ×ℕ) := PairedCatalogProgram.catalog z.1.2.1.1.2
def catalogueRealizer : Realizer catalogue :=
  composition (f := fun z : Input => z.1.2.1.1.2) (g := PairedCatalogProgram.catalog)
    (composition (composition (composition (composition first second) first) first) second)
    PairedCatalogProgram.catalogRealizer
lemma polynomial_catalogue : PolynomialTime catalogueRealizer :=
  polynomial_composition (polynomial_composition (polynomial_composition
    (polynomial_composition (polynomial_composition polynomial_first polynomial_second) polynomial_first)
      polynomial_first) polynomial_second) PairedCatalogProgram.polynomial_catalog

attribute [local irreducible] trajectory catalogue

def returnInput (z : Input) : CompanionTraceProgram.ReturnInput := (catalogue z,trajectory z)
def returnInputRealizer : Realizer returnInput := pair catalogueRealizer trajectoryRealizer
lemma polynomial_returnInput : PolynomialTime returnInputRealizer :=
  polynomial_pair polynomial_catalogue polynomial_trajectory

def storedInput (z : Input) : CompanionObservedUpdateProgram.Base :=
  ((returnInput z,z.1.1.2.1),z.1.1.2.2)
def storedInputRealizer : Realizer storedInput :=
  pair (pair returnInputRealizer
    (composition (composition (composition first first) second) first))
    (composition (composition (composition first first) second) second)
lemma polynomial_storedInput : PolynomialTime storedInputRealizer :=
  polynomial_pair (polynomial_pair polynomial_returnInput
    (polynomial_composition (polynomial_composition (polynomial_composition
      polynomial_first polynomial_first) polynomial_second) polynomial_first))
    (polynomial_composition (polynomial_composition (polynomial_composition
      polynomial_first polynomial_first) polynomial_second) polynomial_second)

def updateInput (z : Input) : CompanionObservedUpdateProgram.Input :=
  ((z.1.1.1,storedInput z),z.2)
def updateInputRealizer : Realizer updateInput :=
  pair (pair (composition (composition first first) first) storedInputRealizer) second
lemma polynomial_updateInput : PolynomialTime updateInputRealizer :=
  polynomial_pair (polynomial_pair (polynomial_composition
    (polynomial_composition polynomial_first polynomial_first) polynomial_first) polynomial_storedInput)
    polynomial_second

attribute [local irreducible] updateInput

def output (z : Input) : Option Stored := CompanionObservedUpdateProgram.output (updateInput z)
def outputRealizer : Realizer output :=
  composition (f := updateInput) (g := CompanionObservedUpdateProgram.output)
    updateInputRealizer CompanionObservedUpdateProgram.outputRealizer
lemma polynomial_output : PolynomialTime outputRealizer :=
  polynomial_composition polynomial_updateInput CompanionObservedUpdateProgram.polynomial_output

end ContingencyTables.CompanionPhaseTrialProgram

end OAI
