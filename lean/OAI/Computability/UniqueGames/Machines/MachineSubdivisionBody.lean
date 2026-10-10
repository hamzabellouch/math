import OAI.Computability.UniqueGames.Machines.MachineSubdivisionTableRead

namespace OAI

section

/-!
One whole occurrence iteration of the actual subdivision controller.
The proved trace includes both endpoint loads, the dynamic full-table reader,
the four-row template, all three local drains, and private-index increments.
-/

namespace UniqueGamesTheorem.Explicit.MachineSubdivisionBody

open Turing
open UniqueGamesTheorem.Foundations UniqueGamesTheorem.Foundations.Complexity
open UniqueGamesTheorem.Foundations.Hastad
open UniqueGamesTheorem.Reduction
open MachineSubdivisionProgram

def tableBits {q : Nat} (table : Target.PermutationTable q) : List Bool :=
  encodeWords (tableWords table)

structure Ready {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool) : Prop where
  input : base .input = encodeWord u ++ encodeWord v ++ tableBits table ++ suffix
  uEmpty : base .u = []
  vEmpty : base .v = []
  permutationEmpty : base .permutation = []
  reverseEmpty : base .permutationReverse = []
  scratchEmpty : base .copyScratch = []

def afterU {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool) : Tape → List Bool :=
  SourceMachine.afterField .input .u base u (encodeWord v ++ tableBits table ++ suffix)

def afterV {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool) : Tape → List Bool :=
  SourceMachine.afterField .input .v (afterU base u v table suffix) v (tableBits table ++ suffix)

def afterTable {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool) : Tape → List Bool :=
  MachineSubdivisionTableRead.finalTapes (afterV base u v table suffix) suffix (tableBits table)

def rowPayload {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool) : List Bool :=
  MachineFieldTemplate.templateOutput (rowTokens q)
    (fun j => afterTable base u v table suffix (rowField j))

def afterRows {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool) : Tape → List Bool :=
  MachineFieldTemplate.outputTapes (afterTable base u v table suffix) .accumulator
    (rowPayload base u v table suffix)

def afterDrainU {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool) : Tape → List Bool :=
  Function.update (afterRows base u v table suffix) .u []

def afterDrainV {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool) : Tape → List Bool :=
  Function.update (afterDrainU base u v table suffix) .v []

def afterDrainTable {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool) : Tape → List Bool :=
  Function.update (afterDrainV base u v table suffix) .permutation []

def incrementTapes (base : Tape → List Bool) : Tape → List Bool :=
  Function.update
    (Function.update (Function.update base .middle (true :: base .middle))
      .first (true :: true :: base .first))
    .last (true :: true :: base .last)

def bodyResult {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool) : Tape → List Bool :=
  incrementTapes (afterDrainTable base u v table suffix)

def bodyBudget {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool) : Nat :=
  (u + 2) + (v + 2) + (2 * (q * (q + 1)) + 2) +
    (3 * MachineFieldTemplate.copiedLength (rowTokens q)
      (fun j => afterTable base u v table suffix (rowField j)) + 37) +
    ((afterRows base u v table suffix .u).length + 1) +
    ((afterDrainU base u v table suffix .v).length + 1) +
    ((afterDrainV base u v table suffix .permutation).length + 1) + 1

private theorem rowField_ne_scratch (j : Fin 6) : rowField j ≠ Tape.copyScratch := by
  fin_cases j <;> decide

private theorem rowField_ne_accumulator (j : Fin 6) : rowField j ≠ Tape.accumulator := by
  fin_cases j <;> decide

def incrementInTime (q : Nat) (base : Tape → List Bool) :
    StateTransition.EvalsToInTime (TM2.step (program q))
      ⟨some .increment, initialState, base⟩
      (some ⟨some .guard, initialState, incrementTapes base⟩) 1 where
  steps := 1
  evals_in_steps := by
    change some (TM2.stepAux (program q .increment) initialState base) = _
    simp [program, TM2.stepAux, incrementTapes, initialState]
  steps_le_m := Nat.le_refl _

/-- Complete actual `.startU → .guard` execution, without a phase-run premise. -/
def bodyInTime {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool)
    (ready : Ready base u v table suffix) :
    StateTransition.EvalsToInTime (TM2.step (program q))
      ⟨some .startU, initialState, base⟩
      (some ⟨some .guard, initialState, bodyResult base u v table suffix⟩)
      (bodyBudget base u v table suffix) := by
  have hu : base .input = encodeWord u ++ (encodeWord v ++ tableBits table ++ suffix) := by
    simpa only [List.append_assoc] using ready.input
  let p₀ := SourceMachine.fieldInTime Tape.input Tape.u (by decide)
    Label.startU Label.readU (some .startV) (program q) rfl rfl base u
    (encodeWord v ++ tableBits table ++ suffix) hu ((), ()) none
  have hv : afterU base u v table suffix .input =
      encodeWord v ++ (tableBits table ++ suffix) := by
    simp [afterU, SourceMachine.afterField, SourceMachine.fieldTapes, List.append_assoc]
  let p₁ := SourceMachine.fieldInTime Tape.input Tape.v (by decide)
    Label.startV Label.readV (some (.readTable 0)) (program q) rfl rfl
    (afterU base u v table suffix) v (tableBits table ++ suffix) hv ((), ()) none
  have tableStart : MachineSubdivisionTableRead.tapes (afterV base u v table suffix)
      (tableBits table ++ suffix) [] = afterV base u v table suffix := by
    funext k
    cases k <;> simp [MachineSubdivisionTableRead.tapes, afterV, afterU,
      SourceMachine.afterField, SourceMachine.fieldTapes, ready.reverseEmpty]
  have p₂ : StateTransition.EvalsToInTime (TM2.step (program q))
      ⟨some (.readTable 0), initialState, afterV base u v table suffix⟩
      (some ⟨some (rowEntry q), initialState, afterTable base u v table suffix⟩)
      (2 * (q * (q + 1)) + 2) := by
    have h := MachineSubdivisionTableRead.tableInTime table
      (afterV base u v table suffix) suffix ((), ()) none
    change StateTransition.EvalsToInTime (TM2.step (program q))
      ⟨_, _, MachineSubdivisionTableRead.tapes (afterV base u v table suffix)
        (tableBits table ++ suffix) []⟩ _ _ at h
    rw [tableStart] at h
    exact h
  have scratch : afterTable base u v table suffix .copyScratch = [] := by
    simp [afterTable, MachineSubdivisionTableRead.finalTapes, MachineSubdivisionTableRead.tapes,
      afterV, afterU, SourceMachine.afterField, SourceMachine.fieldTapes, ready.scratchEmpty]
  let p₃ := MachineFieldTemplate.phaseInTime (rowTokens q) rowField
    Tape.copyScratch Tape.accumulator rowField_ne_scratch rowField_ne_accumulator (by decide)
    Label.emitRows (some .drainU) (program q) (fun _ => rfl)
    (afterTable base u v table suffix) scratch initialState
  let p₄ := MachineDrain.drainInTime Tape.u Label.drainU (some .drainV)
    (program q) rfl (afterRows base u v table suffix) ((), ()) none
  let p₅ := MachineDrain.drainInTime Tape.v Label.drainV (some .drainPermutation)
    (program q) rfl (afterDrainU base u v table suffix) ((), ()) none
  let p₆ := MachineDrain.drainInTime Tape.permutation Label.drainPermutation (some .increment)
    (program q) rfl (afterDrainV base u v table suffix) ((), ()) none
  let p₇ := incrementInTime q (afterDrainTable base u v table suffix)
  let p₀₁ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ p₀ p₁
  let p₀₁₂ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ p₀₁ p₂
  let p₀₁₂₃ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ p₀₁₂ p₃
  let p₀₁₂₃₄ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ p₀₁₂₃ p₄
  let p₀₁₂₃₄₅ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ p₀₁₂₃₄ p₅
  let p₀₁₂₃₄₅₆ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ p₀₁₂₃₄₅ p₆
  let full := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ p₀₁₂₃₄₅₆ p₇
  exact {
    toEvalsTo := full.toEvalsTo
    steps_le_m := by
      have h := full.steps_le_m
      have tokens_length : (rowTokens q).length = 12 := rfl
      unfold bodyBudget
      omega
  }

end UniqueGamesTheorem.Explicit.MachineSubdivisionBody

end

end OAI
