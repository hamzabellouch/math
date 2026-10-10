import Mathlib
import OAI.Combinatorics.IndependentSets.PCP.Driver

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.AlphabetTable.Initialization

open Turing
open IndependentSetsGames.Foundations.Complexity
open RuntimeModel

variable {q : Nat}

def inputTapes (input : GenericGraphTables.Table q) : Tape → List Bool
  | .original => GenericGraphTables.tableBits input
  | _ => []

def rowsBits (input : GenericGraphTables.Table q) : List Bool :=
  encodeWords ((GenericGraphTables.rowList input).flatMap GenericGraphTables.rowWords)

def headerBits (input : GenericGraphTables.Table q) : List Bool :=
  encodeWords [Enumeration.vertexCount input.vertices input.darts q,
    Enumeration.dartCount input.darts q]

def setupTapes (input : GenericGraphTables.Table q) : Tape → List Bool
  | .original => GenericGraphTables.tableBits input
  | .cursor => rowsBits input
  | .vertices => encodeWord input.vertices
  | .darts | .counter => encodeWord input.darts
  | .edge => encodeWord 0
  | _ => []

def loopTapes (input : GenericGraphTables.Table q) : Tape → List Bool
  | .original => GenericGraphTables.tableBits input
  | .cursor => rowsBits input
  | .vertices => encodeWord input.vertices
  | .darts | .counter => encodeWord input.darts
  | .edge => encodeWord 0
  | .reversed => (headerBits input).reverse
  | _ => []

def loopStart (input : GenericGraphTables.Table q) :
    TM2.Cfg Alphabet (Driver.Label q) (State q) :=
  ⟨some .guard, initial q, loopTapes input⟩

theorem setupResult_eq (input : GenericGraphTables.Table q) :
    Setup.resultTapes setupPorts (inputTapes input) input.vertices input.darts (rowsBits input) =
      setupTapes input := by
  funext tape
  cases tape <;> simp [Setup.resultTapes, setupPorts, inputTapes, setupTapes]

theorem headerResult_eq (input : GenericGraphTables.Table q) :
    Emitter.resultTapes Tape.reversed (setupTapes input) (headerBits input) = loopTapes input := by
  funext tape
  cases tape <;> simp [Emitter.resultTapes, setupTapes, loopTapes]

theorem machineInitial_eq (input : GenericGraphTables.Table q) :
    initList (Driver.machine q) (GenericGraphTables.tableBits input) =
      (⟨some (.setup .copyFirst), initial q, inputTapes input⟩ :
        TM2.Cfg Alphabet (Driver.Label q) (State q)) := by
  change (⟨some (.setup .copyFirst), initial q, _⟩ :
    TM2.Cfg Alphabet (Driver.Label q) (State q)) = _
  congr 1
  funext tape
  cases tape <;> rfl

def setupInTime (input : GenericGraphTables.Table q) :
    StateTransition.EvalsToInTime (TM2.step (Driver.program q))
      (initList (Driver.machine q) (GenericGraphTables.tableBits input))
      (some ⟨some (Driver.headerEntry q), initial q, setupTapes input⟩)
      (6 * (GenericGraphTables.tableBits input).length + 11) := by
  have initialized : ∀ i : Fin 7, inputTapes input (setupPorts i) =
      if i = 0 then GenericGraphTables.tableBits input else [] := by
    intro i
    fin_cases i <;> rfl
  have run := Setup.tableSetupInTime setupPorts setupPorts_injective Driver.Label.setup
    (some (Driver.headerEntry q)) (Driver.program q) (Driver.program_setup q)
    (inputTapes input) input initialized (initial q).1 none
  have initialState : ((initial q).1, (none : Option Bool)) = initial q := rfl
  have result := setupResult_eq input
  unfold rowsBits at result
  rw [initialState, result] at run
  rw [machineInitial_eq]
  exact run

private theorem headerView_at (label : Emitter.Label (Driver.headerPlan q).length
    (Addresses.fieldBound q)) :
    (MachineControl.program (Equiv.refl (Driver.Label q)) (emitterEquiv q).symm
      (Driver.program q)) (.header label) =
      Emitter.statement (Emitter.listCommands (Driver.headerPlan q)) headerSources
        Tape.scratch Tape.reversed Driver.Label.header (some .guard) label := by
  change MachineControl.statement id (emitterEquiv q).symm
    (MachineControl.statement id (emitterEquiv q) _) = _
  exact MachineFieldProfile.statement_roundtrip (emitterEquiv q).symm _

def headerInTime (input : GenericGraphTables.Table q) :
    StateTransition.EvalsToInTime (TM2.step (Driver.program q))
      ⟨some (Driver.headerEntry q), initial q, setupTapes input⟩
      (some (loopStart input))
      (7 * (3 * ((GenericGraphTables.tableBits input).length + 1) + 3) + 1) := by
  let view := MachineControl.program (Equiv.refl (Driver.Label q)) (emitterEquiv q).symm
    (Driver.program q)
  have sourceScratch : ∀ i : Fin 2, headerSources i ≠ Tape.scratch := by
    intro i
    fin_cases i <;> decide
  have sourceOutput : ∀ i : Fin 2, headerSources i ≠ Tape.reversed := by
    intro i
    fin_cases i <;> decide
  have operands : ∀ i : Fin 2, setupTapes input (headerSources i) =
      encodeWord (![input.vertices, input.darts] i) := by
    intro i
    fin_cases i <;> rfl
  have run := EmitRows.headerInTime q input.vertices input.darts headerSources
    Tape.scratch Tape.reversed sourceScratch sourceOutput (by decide)
    Driver.Label.header (some .guard) view headerView_at
    (setupTapes input) operands (by rfl) (initial q).1
    (GenericGraphTables.tableBits input).length
    (GenericGraphTables.vertices_le_tableBits_length input)
    (GenericGraphTables.darts_le_tableBits_length input)
  have restored : MachineControl.program (Equiv.refl (Driver.Label q)) (emitterEquiv q) view =
      Driver.program q := by
    funext label
    exact MachineFieldProfile.statement_roundtrip (emitterEquiv q) (Driver.program q label)
  have transported := transportInTime (emitterEquiv q) view run
  rw [restored] at transported
  change StateTransition.EvalsToInTime (TM2.step (Driver.program q))
    ⟨some (Driver.headerEntry q), initial q, setupTapes input⟩
    (some ⟨some .guard, initial q,
      Emitter.resultTapes Tape.reversed (setupTapes input) (headerBits input)⟩)
    (7 * (3 * ((GenericGraphTables.tableBits input).length + 1) + 3) + 1) at transported
  rw [headerResult_eq] at transported
  exact transported

def time (N : Nat) : Nat := (6 * N + 11) + (7 * (3 * (N + 1) + 3) + 1)

theorem time_eq (N : Nat) : time N = 27 * N + 54 := by
  unfold time
  omega

def initializeInTime (input : GenericGraphTables.Table q) :
    StateTransition.EvalsToInTime (TM2.step (Driver.program q))
      (initList (Driver.machine q) (GenericGraphTables.tableBits input))
      (some (loopStart input)) (time (GenericGraphTables.tableBits input).length) := by
  let run := StateTransition.EvalsToInTime.trans _ _ _ _ _ _
    (setupInTime input) (headerInTime input)
  refine { toEvalsTo := run.toEvalsTo, steps_le_m := ?_ }
  have bound := run.steps_le_m
  unfold time
  omega

end IndependentSetsGames.Foundations.PCP.AlphabetTable.Initialization

end OAI
