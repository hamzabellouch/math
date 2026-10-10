import OAI.Combinatorics.ContingencyTables.Counting.CompanionOuterPhaseProgram

namespace OAI

/-! # Chronological execution of all counting phases -/
namespace ContingencyTables.CompanionOuterHistoryProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped
abbrev Prepared := CompanionPhaseContextProgram.Prepared
abbrev Stored := CompanionPhaseFinishProgram.Stored
abbrev Fixed := Prepared×Stored
abbrev State := Fixed×List Stored
abbrev Input := Fixed×List (List Bool)
local instance : Codec Fixed := inferInstance
local instance : Codec State := inferInstance
local instance : Codec Input := inferInstance

def phaseInput (z : List Bool×State) : CompanionOuterPhaseProgram.Input := (z.2,z.1)
def phaseInputRealizer : Realizer phaseInput := pair second first
lemma polynomial_phaseInput : PolynomialTime phaseInputRealizer :=
  polynomial_pair polynomial_second polynomial_first

def next (z : List Bool×State) : Stored := CompanionOuterPhaseProgram.output (phaseInput z)
def nextRealizer : Realizer next :=
  composition (f := phaseInput) (g := CompanionOuterPhaseProgram.output)
    phaseInputRealizer CompanionOuterPhaseProgram.outputRealizer
lemma polynomial_next : PolynomialTime nextRealizer :=
  polynomial_composition polynomial_phaseInput CompanionOuterPhaseProgram.polynomial_output

def advance (z : List Bool×State) : State := (z.2.1,z.2.2++[next z])
def advanceRealizer : Realizer advance :=
  pair (composition second first)
    (composition (pair (composition second second)
      (composition (pair nextRealizer (constant [])) listCons)) append)
lemma polynomial_advance : PolynomialTime advanceRealizer :=
  polynomial_pair (polynomial_composition polynomial_second polynomial_first)
    (polynomial_composition (polynomial_pair (polynomial_composition polynomial_second polynomial_second)
      (polynomial_composition (polynomial_pair polynomial_next (polynomial_constant [])) polynomial_listCons))
      polynomial_append)

def run (z : Input) : State := z.2.foldl (fun state bits => advance (bits,state)) (z.1,[])
def runRealizer : Realizer run :=
  composition (pair second (pair first (constant []))) (fold advanceRealizer)

def storedHistory (z : Input) : List Stored := (run z).2
def storedHistoryRealizer : Realizer storedHistory :=
  composition (f := run) (g := Prod.snd) runRealizer second

def output (z : Input) : Stored :=
  CompanionOuterPhaseProgram.old ((z.1,storedHistory z),[])
def outputRealizer : Realizer output :=
  composition (f := fun z : Input => ((z.1,storedHistory z),[]))
    (g := CompanionOuterPhaseProgram.old)
    (pair (pair first storedHistoryRealizer) (constant [])) CompanionOuterPhaseProgram.oldRealizer

lemma advance_fixed (bits : List Bool) (state : State) : (advance (bits,state)).1=state.1 := rfl
lemma run_fixed (z : Input) : (run z).1=z.1 := by
  have h (words : List (List Bool)) (state : State) :
      (words.foldl (fun state bits => advance (bits,state)) state).1=state.1 := by
    induction words generalizing state with
    | nil => rfl
    | cons word words ih => exact ih _
  exact h z.2 (z.1,[])

end ContingencyTables.CompanionOuterHistoryProgram

end OAI
