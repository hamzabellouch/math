import OAI.Computability.UniqueGames.Machines.MachineExpanderFamilyTransferLemmas
import OAI.Computability.UniqueGames.Machines.MachineExpanderRow
import OAI.Computability.UniqueGames.PCP.ExpanderTableEnumeration

namespace OAI

/-!
# Actual execution of all expander-table positions for one vertex

The inner loop calls the complete row machine once per fixed cloud/port position.
The returned state and the successful machine execution are constructed together.
Neither a row execution nor an inner-loop execution is a caller premise.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords
open PCP.ExpanderTableEnumeration

private def singleStep {α : Type*} (step : α → Option α) (a b : α)
    (h : step a = some b) : StateTransition.EvalsToInTime step a (some b) 1 where
  steps := 1
  evals_in_steps := by change step a = some b; exact h
  steps_le_m := Nat.le_refl _

private def sequence {α : Type*} {step : α → Option α} {a b c : α} {m n : Nat}
    (first : StateTransition.EvalsToInTime step a (some b) m)
    (second : StateTransition.EvalsToInTime step b (some c) n) :
    StateTransition.EvalsToInTime step a (some c) (m + n) := by
  simpa only [Nat.add_comm n m] using
    StateTransition.EvalsToInTime.trans step m n a b (some c) first second

private def widen {α : Type*} {step : α → Option α} {a : α} {b : Option α} {m n : Nat}
    (run : StateTransition.EvalsToInTime step a b m) (bound : m ≤ n) :
    StateTransition.EvalsToInTime step a b n where
  toEvalsTo := run.toEvalsTo
  steps_le_m := run.steps_le_m.trans bound

def tableRowData {v d : Nat} (G : Table v (degree d)) (H : Table (cloudSize d) d)
    (vertex : Fin v) (position : Position d) : MachineExpanderRow.RowData v d :=
  MachineExpanderRow.rowData G H vertex (positionPair position).1 (positionPair position).2

theorem tableRowData_finalValue {v d : Nat} (G : Table v (degree d))
    (H : Table (cloudSize d) d) (vertex : Fin v) (position : Position d) :
    (tableRowData G H vertex position).finalValue = rowValue G H vertex position := rfl

theorem tableRowData_frame0 {v d : Nat} (G : Table v (degree d))
    (H : Table (cloudSize d) d) (vertex : Fin v) (position : Position d) (output : List Bool) :
    MachineExpanderRow.frame0 (tableRowData G H vertex position) output =
      rowTapes vertex.val (encodeWords (rotationWords G)) output := by
  funext tape
  cases tape <;> rfl

theorem tableRowData_finalFrame {v d : Nat} (G : Table v (degree d))
    (H : Table (cloudSize d) d) (vertex : Fin v) (position : Position d) (output : List Bool) :
    MachineExpanderRow.emittedWord .output
      (MachineExpanderRow.frame0 (tableRowData G H vertex position) output)
      (tableRowData G H vertex position).finalValue =
      rowTapes vertex.val (encodeWords (rotationWords G))
        ((encodeWord (rowValue G H vertex position)).reverse ++ output) := by
  rw [tableRowData_frame0, tableRowData_finalValue]
  funext tape
  cases tape <;> simp [MachineExpanderRow.emittedWord, rowTapes]

variable {ρ : Type} [Fintype ρ] {v d : Nat}

def rowAfterState (positive : 0 < d) (G : Table v (degree d))
    (H : Table (cloudSize d) d) (vertex : Fin v) (state : State ρ d) : State ρ d :=
  (MachineExpanderRow.divisionState positive (caller state)
    (tableRowData G H vertex state.2).control2 none, state.2)

omit [Fintype ρ] in
@[simp] theorem rowAfterState_position (positive : 0 < d) (G : Table v (degree d))
    (H : Table (cloudSize d) d) (vertex : Fin v) (state : State ρ d) :
    (rowAfterState positive G H vertex state).2 = state.2 := rfl

omit [Fintype ρ] in
@[simp] theorem caller_rowAfterState (positive : 0 < d) (G : Table v (degree d))
    (H : Table (cloudSize d) d) (vertex : Fin v) (state : State ρ d) :
    caller (rowAfterState positive G H vertex state) = caller state := rfl

/-- Preparation and one actual embedded row call, with the two extra tapes
retained. The row value is computed from the actual old and small tables. -/
def preparedRowInTime (positive : 0 < d) (G : Table v (degree d))
    (H : Table (cloudSize d) d) (vertex : Fin v) (state : State ρ d)
    (remaining : Nat) (output countSuffix result : List Bool) :
    StateTransition.EvalsToInTime (TM2.step (program positive H))
      ⟨some (.inr .prepareRow), state,
        boundaryTapes vertex.val remaining (encodeWords (rotationWords G)) output countSuffix result⟩
      (some ⟨some (.inr .afterRow), rowAfterState positive G H vertex state,
        boundaryTapes vertex.val remaining (encodeWords (rotationWords G))
          ((encodeWord (rowValue G H vertex state.2)).reverse ++ output) countSuffix result⟩)
      (1 + 80 * ((encodeWords (rotationWords G)).length + 1)) := by
  have raw := rowExecution positive H state.2 (extraTapes remaining countSuffix result)
    (MachineExpanderRow.rowInTime positive (tableRowData G H vertex state.2) output (caller state))
  have run : StateTransition.EvalsToInTime (TM2.step (program positive H))
      ⟨some (.inl .initialize), prepareState positive H state,
        boundaryTapes vertex.val remaining (encodeWords (rotationWords G)) output countSuffix result⟩
      (some ⟨some (.inr .afterRow), rowAfterState positive G H vertex state,
        boundaryTapes vertex.val remaining (encodeWords (rotationWords G))
          ((encodeWord (rowValue G H vertex state.2)).reverse ++ output) countSuffix result⟩)
      (80 * ((encodeWords (rotationWords G)).length + 1)) := by
    rw [tableRowData_finalFrame, tableRowData_frame0] at raw
    simpa only [MachineEmbedding.configuration, MachineEmbedding.label, rowReturn,
      prepareState, boundaryState, rowAfterState, boundaryTapes,
      MachineExpanderRow.RowData.tableLength, MachineExpanderRow.RowData.control0,
      tableRowData, MachineExpanderRow.rowData] using raw
  exact sequence
    (singleStep _ _ _ (prepareRowStep positive H
      (boundaryTapes vertex.val remaining (encodeWords (rotationWords G)) output countSuffix result)
      state)) run

/-- A successful suffix of the finite position loop, returning actual finite
state together with the execution certificate and its preserved caller. -/
structure VertexSuffixRun (positive : 0 < d) (G : Table v (degree d))
    (H : Table (cloudSize d) d) (vertex : Fin v) (state : State ρ d)
    (remaining : Nat) (output countSuffix result : List Bool) where
  finalState : State ρ d
  caller_preserved : caller finalState = caller state
  position_zero : finalState.2 = zeroPosition positive
  execution : StateTransition.EvalsToInTime (TM2.step (program positive H))
    ⟨some (.inr .prepareRow), state,
      boundaryTapes vertex.val remaining (encodeWords (rotationWords G)) output countSuffix result⟩
    (some ⟨some (.inr .vertexGuard), finalState,
      boundaryTapes (vertex.val + 1) remaining (encodeWords (rotationWords G))
        (accumulate ((vertexWords G H vertex).drop state.2.val) output) countSuffix result⟩)
    ((rowFactor d - state.2.val) * (80 * ((encodeWords (rotationWords G)).length + 1) + 2))

private def suffixRun_aux (positive : 0 < d) (G : Table v (degree d))
    (H : Table (cloudSize d) d) (vertex : Fin v) (remaining : Nat)
    (countSuffix result : List Bool) (n : Nat) :
    (state : State ρ d) → state.2.val + n = rowFactor d → (output : List Bool) →
      VertexSuffixRun positive G H vertex state remaining output countSuffix result := by
  induction n with
  | zero =>
      intro state count output
      have hp := state.2.isLt
      exact False.elim (by omega)
  | succ n ih =>
      intro state count output
      let after := rowAfterState positive G H vertex state
      let nextOutput := (encodeWord (rowValue G H vertex state.2)).reverse ++ output
      have row := preparedRowInTime positive G H vertex state remaining output countSuffix result
      by_cases last : n = 0
      · have hp : state.2.val + 1 = rowFactor d := by omega
        have finish := singleStep _ _ _ (afterRow_last_boundaryStep positive H vertex.val remaining
          (encodeWords (rotationWords G)) nextOutput countSuffix result after (by
            change ¬ state.2.val + 1 < rowFactor d
            omega))
        refine ⟨resetPositionState positive after, ?_, rfl, ?_⟩
        · rfl
        · have all := sequence row finish
          have words : accumulate ((vertexWords G H vertex).drop state.2.val) output =
              nextOutput := by
            rw [vertexWords_drop_last G H vertex state.2 hp]
            rfl
          have budget : rowFactor d - state.2.val = 1 := by omega
          rw [words, budget, Nat.one_mul]
          exact widen all (by omega)
      · have more : state.2.val + 1 < rowFactor d := by omega
        let next := advancePositionState positive after
        have nextPositionValue : next.2.val = state.2.val + 1 :=
          nextPosition_val_of_lt positive state.2 more
        have nextCount : next.2.val + n = rowFactor d := by omega
        let tail := ih next nextCount nextOutput
        have advance := singleStep _ _ _ (afterRow_moreStep positive H
          (boundaryTapes vertex.val remaining (encodeWords (rotationWords G))
            nextOutput countSuffix result) after more)
        have all := sequence (sequence row advance) tail.execution
        refine ⟨tail.finalState, ?_, tail.position_zero, ?_⟩
        · exact tail.caller_preserved
        · have words : accumulate ((vertexWords G H vertex).drop state.2.val) output =
              accumulate ((vertexWords G H vertex).drop next.2.val) nextOutput := by
            rw [vertexWords_drop_succ G H vertex state.2, nextPositionValue]
            rfl
          rw [words]
          apply widen all
          have hcount : rowFactor d - state.2.val = n + 1 := by omega
          have hnext : rowFactor d - next.2.val = n := by omega
          rw [hcount, hnext, Nat.add_mul, Nat.one_mul]
          omega

def suffixInTime (positive : 0 < d) (G : Table v (degree d))
    (H : Table (cloudSize d) d) (vertex : Fin v) (state : State ρ d)
    (remaining : Nat) (output countSuffix result : List Bool) :
    VertexSuffixRun positive G H vertex state remaining output countSuffix result :=
  suffixRun_aux positive G H vertex remaining countSuffix result
    (rowFactor d - state.2.val) state (by have h := state.2.isLt; omega) output

/-- The complete inner loop for one vertex, starting at position zero. -/
structure VertexRun (positive : 0 < d) (G : Table v (degree d))
    (H : Table (cloudSize d) d) (vertex : Fin v) (state : State ρ d)
    (remaining : Nat) (output countSuffix result : List Bool) where
  finalState : State ρ d
  caller_preserved : caller finalState = caller state
  position_zero : finalState.2 = zeroPosition positive
  execution : StateTransition.EvalsToInTime (TM2.step (program positive H))
    ⟨some (.inr .prepareRow), state,
      boundaryTapes vertex.val remaining (encodeWords (rotationWords G)) output countSuffix result⟩
    (some ⟨some (.inr .vertexGuard), finalState,
      boundaryTapes (vertex.val + 1) remaining (encodeWords (rotationWords G))
        (accumulate (vertexWords G H vertex) output) countSuffix result⟩)
    (rowFactor d * (80 * ((encodeWords (rotationWords G)).length + 1) + 2))

def vertexInTime (positive : 0 < d) (G : Table v (degree d))
    (H : Table (cloudSize d) d) (vertex : Fin v) (state : State ρ d)
    (position : state.2 = zeroPosition positive)
    (remaining : Nat) (output countSuffix result : List Bool) :
    VertexRun positive G H vertex state remaining output countSuffix result := by
  let run := suffixInTime positive G H vertex state remaining output countSuffix result
  refine ⟨run.finalState, run.caller_preserved, run.position_zero, ?_⟩
  have zero : state.2.val = 0 := congrArg Fin.val position
  simpa only [zero, List.drop_zero, Nat.sub_zero] using run.execution

end UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable

end OAI
