import OAI.Computability.UniqueGames.Machines.MachineExpanderFamilyTransferLemmas

namespace OAI

namespace UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable

open Turing
open MachineComposition
open PCP.ExpanderTables PCP.ExpanderRowControl

variable {ρ : Type} {d : Nat}

@[simp] theorem clearRegister_position (state : State ρ d) :
    (clearRegister state).2 = state.2 := rfl

@[simp] theorem clearRegister_register (state : State ρ d) :
    (clearRegister state).1.2 = none := rfl

@[simp] theorem clearRegister_idempotent (state : State ρ d) :
    clearRegister (clearRegister state) = clearRegister state := rfl

theorem boundaryTapes_reverse_update (vertex remaining : Nat)
    (oldTable output countSuffix result nextOutput nextResult : List Bool) :
    Function.update
      (Function.update (boundaryTapes vertex remaining oldTable output countSuffix result)
        (.inl .output) nextOutput)
      (.inr .result) nextResult =
      boundaryTapes vertex remaining oldTable nextOutput countSuffix nextResult := by
  funext tape
  rcases tape with row | extra
  · cases row <;>
      simp [boundaryTapes, rowTapes, MachineEmbedding.tapes, Function.update]
  · cases extra <;>
      simp [boundaryTapes, extraTapes, MachineEmbedding.tapes, Function.update]

variable [Fintype ρ]

/-- Exact execution of the entire final reverse loop, including its empty
test. No reversal-execution hypothesis is assumed. -/
theorem reverseOutputTrace (positive : 0 < d) (H : Table (cloudSize d) d)
    (vertex remaining : Nat) (oldTable output countSuffix result : List Bool)
    (state : State ρ d) :
    (advance (TM2.step (program positive H)))^[output.length + 1]
      (some ⟨some (.inr .reverseOutput), state,
        boundaryTapes vertex remaining oldTable output countSuffix result⟩) =
      some ⟨some (.inr .done), clearRegister state,
        boundaryTapes vertex remaining oldTable [] countSuffix (output.reverse ++ result)⟩ := by
  induction output generalizing result state with
  | nil =>
      simpa only [List.length_nil, Nat.zero_add, Function.iterate_one, advance_some,
        List.reverse_nil, List.nil_append] using
        reverseOutput_nilStep positive H
          (boundaryTapes vertex remaining oldTable [] countSuffix result) state rfl
  | cons symbol output ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      simp only [advance_some]
      rw [reverseOutput_consStep positive H
        (boundaryTapes vertex remaining oldTable (symbol :: output) countSuffix result)
        state symbol output rfl]
      change (advance (TM2.step (program positive H)))^[output.length + 1]
        (some ⟨some (.inr .reverseOutput), ((state.1.1, some symbol), state.2),
          Function.update
            (Function.update
              (boundaryTapes vertex remaining oldTable (symbol :: output) countSuffix result)
              (.inl .output) output)
            (.inr .result) (symbol :: result)⟩) = _
      rw [boundaryTapes_reverse_update]
      simpa only [clearRegister, List.reverse_cons, List.append_assoc,
        List.singleton_append] using
        ih (symbol :: result) ((state.1.1, some symbol), state.2)

/-- The actual `done` statement halts one transition after reversal completes. -/
theorem reverseOutputHaltTrace (positive : 0 < d) (H : Table (cloudSize d) d)
    (vertex remaining : Nat) (oldTable output countSuffix result : List Bool)
    (state : State ρ d) :
    (advance (TM2.step (program positive H)))^[output.length + 2]
      (some ⟨some (.inr .reverseOutput), state,
        boundaryTapes vertex remaining oldTable output countSuffix result⟩) =
      some ⟨none, clearRegister state,
        boundaryTapes vertex remaining oldTable [] countSuffix (output.reverse ++ result)⟩ := by
  rw [show output.length + 2 = (output.length + 1) + 1 by omega,
    Function.iterate_succ_apply',
    reverseOutputTrace positive H vertex remaining oldTable output countSuffix result state]
  exact doneStep positive H
    (boundaryTapes vertex remaining oldTable [] countSuffix (output.reverse ++ result))
    (clearRegister state)

def reverseOutputInTime (positive : 0 < d) (H : Table (cloudSize d) d)
    (vertex remaining : Nat) (oldTable output countSuffix result : List Bool)
    (state : State ρ d) :
    StateTransition.EvalsToInTime (TM2.step (program positive H))
      ⟨some (.inr .reverseOutput), state,
        boundaryTapes vertex remaining oldTable output countSuffix result⟩
      (some ⟨some (.inr .done), clearRegister state,
        boundaryTapes vertex remaining oldTable [] countSuffix (output.reverse ++ result)⟩)
      (output.length + 1) where
  steps := output.length + 1
  evals_in_steps := reverseOutputTrace positive H vertex remaining oldTable output countSuffix result state
  steps_le_m := Nat.le_refl _

def reverseOutputHaltInTime (positive : 0 < d) (H : Table (cloudSize d) d)
    (vertex remaining : Nat) (oldTable output countSuffix result : List Bool)
    (state : State ρ d) :
    StateTransition.EvalsToInTime (TM2.step (program positive H))
      ⟨some (.inr .reverseOutput), state,
        boundaryTapes vertex remaining oldTable output countSuffix result⟩
      (some ⟨none, clearRegister state,
        boundaryTapes vertex remaining oldTable [] countSuffix (output.reverse ++ result)⟩)
      (output.length + 2) where
  steps := output.length + 2
  evals_in_steps := reverseOutputHaltTrace positive H vertex remaining oldTable output countSuffix result state
  steps_le_m := Nat.le_refl _

end UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable

end OAI
