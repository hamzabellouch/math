import OAI.Computability.UniqueGames.Machines.MachineCanonicalOutputLemmas
import OAI.Computability.UniqueGames.Machines.MachineLazyTable
import OAI.Computability.UniqueGames.PCP.PreprocessingTablesLemmas

namespace OAI

/-!
Canonical polynomial-time computation of the executable lazy preprocessing map.
The raw machine's retained original input is physically drained by the checked
canonical-output wrapper before it reaches the standard `haltList` endpoint.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineLazyTableRuntime

open Turing PCP
open MachineLazyTable (Tape Label State)

def rawProgram (d : Nat) (positive : 0 < d) :
    MachineCanonicalOutput.Program Tape (Label d) (State d) where
  input := .input
  output := .output
  main := .split .copyFirst
  initial := MachineLazyTable.clean d positive
  code := MachineLazyTable.program d positive

theorem sourceMachine_eq (d : Nat) (positive : 0 < d) :
    MachineCanonicalOutput.sourceMachine (rawProgram d positive) =
      MachineLazyTable.machine d positive := rfl

/-- A fixed explicit list of every non-output tape, independent of input data. -/
def cleanupTapes : List Tape :=
  [.input, .source, .vertices, .darts, .fuel, .vertex, .reverse,
    .tail, .old, .relation, .scratch, .divided, .quotient, .newReverse, .rowBuffer]

theorem cleanup_complete (d : Nat) (positive : 0 < d) (k : Tape) :
    k ∈ cleanupTapes ↔ k ≠ (rawProgram d positive).output := by
  cases k <;> simp [cleanupTapes, rawProgram]

/-- The terminal witness is the checked full lazy-table execution. The wrapper
then drains the retained original input rather than assuming it disappeared. -/
def terminalRun (d : Nat) (positive : 0 < d) (a : PortTables.Input d) :
    MachineCanonicalOutput.TerminalRun (rawProgram d positive) (PortTables.inputBits a)
      (PortTables.inputBits (PreprocessingStageMaps.lazy d a))
      ((MachineLazyTable.timePolynomial d).eval (PortTables.inputBits a).length) where
  state := MachineLazyTable.clean d positive
  tapes := MachineLazyTable.finalTapes (PortTables.inputBits a)
    (PortTables.inputBits (PreprocessingStageMaps.lazy d a))
  execution := MachineLazyTable.machineInTime a.2 positive
  output_eq := rfl

/-- The actual canonical-output finite machine computes precisely the shared
degree-d to degree-2d stage map in polynomial time. -/
noncomputable def computableInPolyTime (d : Nat) (positive : 0 < d) :
    TM2ComputableInPolyTime (PortTables.inputBits (ports := d))
      (PortTables.inputBits (ports := 2 * d)) (PreprocessingStageMaps.lazy d) :=
  MachineCanonicalOutput.computableInPolyTime (rawProgram d positive) cleanupTapes
    (cleanup_complete d positive) PortTables.inputBits PortTables.inputBits
    (PreprocessingStageMaps.lazy d) (MachineLazyTable.timePolynomial d) (terminalRun d positive)

/-- Every tape alphabet of this exact completed computation certificate is finite. -/
theorem finite_alphabet (d : Nat) (positive : 0 < d) :
    ∀ k, Finite ((computableInPolyTime d positive).tm.Γ k) :=
  MachineCanonicalOutput.computableInPolyTime_finite_alphabet (rawProgram d positive) cleanupTapes
    (cleanup_complete d positive) PortTables.inputBits PortTables.inputBits
    (PreprocessingStageMaps.lazy d) (MachineLazyTable.timePolynomial d) (terminalRun d positive)

end UniqueGamesTheorem.Foundations.Complexity.MachineLazyTableRuntime

end OAI
