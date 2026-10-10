import Mathlib
import OAI.Computability.DirectedFeedback.Machines.MachineExpanderRowLookup

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Foundations.Complexity.MachineExpanderRow

open Turing MachineComposition
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords PCP.AlphabetTable

private theorem concatenate_inline_MachineExpanderRow {A : Type*} {f : A → A} {m n : Nat} {a b c : A}
    (first : f^[m] a = b) (second : f^[n] b = c) : f^[m + n] a = c := by
  rw [Nat.add_comm m n, Function.iterate_add_apply, first, second]

def rowSteps {v d : Nat} (r : RowData v d) (output : List Bool) : Nat :=
  1 + emitSteps r.inputVertex.val + (r.query1 + 2) +
    MachinePreservingLookupClean.steps (rotationWords r.oldTable) r.firstRow.val +
    (r.firstValue + 2) + 1 + emitSteps r.firstVertex.val + (r.query2 + 2) +
    MachinePreservingLookupClean.steps (rotationWords r.oldTable) r.secondRow.val +
    (r.secondValue + 2) + emitSteps r.secondVertex.val +
    (cleanupSteps id (frame11 r output) + 1)

section Execution

variable {v d : Nat} {ρ Λ : Type} [Fintype ρ]
    (positive : 0 < d) (r : RowData v d) (output : List Bool) (ambient : ρ)
    (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : Tape => Bool) Λ (State ρ d))
    (code : ∀ l, target (labels l) = statement positive r.smallTable id labels exit l)

include code

theorem rowTraceAt :
    (advance (TM2.step target))^[rowSteps r output]
      (some ⟨some (labels .initialize), divisionState positive ambient r.control0 none,
        frame0 r output⟩) =
      some ⟨exit, divisionState positive ambient r.control2 none,
        emittedWord .output (frame0 r output) r.finalValue⟩ := by
  let zero := MachineFixedDivMod.residue (degree d) (Nat.mul_pos positive positive) 0
  have h0 : (advance (TM2.step target))^[1]
      (some ⟨some (labels .initialize), divisionState positive ambient r.control0 none,
        frame0 r output⟩) =
      some ⟨some (labels (.firstEmit (Emitter.labelAt 3 _ 0 .entry))),
        divisionState positive ambient r.control0 none, frame1 r output⟩ := by
    simpa only [Function.iterate_one, advance_some, divisionState, frame1] using
      initializeStepAt positive r.smallTable id Function.injective_id labels exit target code
        (frame0 r output) (divisionState positive ambient r.control0 none)
  have h1 := firstEmitTraceAt positive r.smallTable id Function.injective_id
    labels exit target code r.inputVertex.val (frame1 r output)
    (by simp) (by simp) ((ambient,r.control0),zero)
  change (advance (TM2.step target))^[emitSteps r.inputVertex.val]
      (some ⟨some (labels (.firstEmit (Emitter.labelAt 3 _ 0 .entry))),
        divisionState positive ambient r.control0 none, frame1 r output⟩) =
      some ⟨some (labels .firstReverse), divisionState positive ambient r.control0 none,
        frame2 r output⟩ at h1
  have h2 := reversePhaseTrace_unary false positive r.smallTable id Function.injective_id
    labels exit target code (frame2 r output) (((ambient,r.control0),zero),()) none
    r.query1 [] (by simp) (by simp)
  simp only [List.append_nil] at h2
  change (advance (TM2.step target))^[r.query1 + 2]
      (some ⟨some (labels .firstReverse), divisionState positive ambient r.control0 none,
        frame2 r output⟩) =
      some ⟨some (labels (.firstLookup (.run .copyFirst))),
        divisionState positive ambient r.control0 none, frame3 r output⟩ at h2
  have h3 := lookupPhaseTrace false positive r.smallTable id Function.injective_id
    labels exit target code (frame3 r output) r.oldTable
    (by simp) (by simp)
    (r.inputVertex, firstOffset r.control0) []
    (by simpa [frameContents, RowData.firstRow] using
      congrArg encodeWord r.query1_eq_firstRow)
    (by simp) (((ambient,r.control0),zero),()) none
  change (advance (TM2.step target))^[MachinePreservingLookupClean.steps
      (rotationWords r.oldTable) r.firstRow.val]
      (some ⟨some (labels (.firstLookup (.run .copyFirst))),
        divisionState positive ambient r.control0 none, frame3 r output⟩) =
      some ⟨some (labels .firstScan), divisionState positive ambient r.control0 none,
        frame4 r output⟩ at h3
  have h4 := firstDivisionTrace positive r.smallTable id Function.injective_id labels exit
    target code (frame4 r output) r.firstValue [] [] []
    (by simp) (by simp) (by simp)
    ambient r.control0 none
  rw [← r.firstReturn_eq_residue positive] at h4
  change (advance (TM2.step target))^[r.firstValue + 2]
      (some ⟨some (labels .firstScan), divisionState positive ambient r.control0 none,
        frame4 r output⟩) =
      some ⟨some (labels .clearQuery), divisionState positive ambient r.control1 none,
        frame5 r output⟩ at h4
  have h5 : (advance (TM2.step target))^[1]
      (some ⟨some (labels .clearQuery), divisionState positive ambient r.control1 none,
        frame5 r output⟩) =
      some ⟨some (labels (.secondEmit (Emitter.labelAt 3 _ 0 .entry))),
        divisionState positive ambient r.control1 none, frame6 r output⟩ := by
    simpa only [Function.iterate_one, advance_some, frame6] using
      clearQueryStepAt positive r.smallTable id Function.injective_id labels exit target code
        (frame5 r output) (divisionState positive ambient r.control1 none)
  have h6 := secondEmitTraceAt positive r.smallTable id Function.injective_id
    labels exit target code r.firstVertex.val (frame6 r output)
    (by simp) (by simp) ((ambient,r.control1),zero)
  change (advance (TM2.step target))^[emitSteps r.firstVertex.val]
      (some ⟨some (labels (.secondEmit (Emitter.labelAt 3 _ 0 .entry))),
        divisionState positive ambient r.control1 none, frame6 r output⟩) =
      some ⟨some (labels .secondReverse), divisionState positive ambient r.control1 none,
        frame7 r output⟩ at h6
  have h7 := reversePhaseTrace_unary true positive r.smallTable id Function.injective_id
    labels exit target code (frame7 r output) (((ambient,r.control1),zero),()) none
    r.query2 [] (by simp) (by simp)
  simp only [List.append_nil] at h7
  change (advance (TM2.step target))^[r.query2 + 2]
      (some ⟨some (labels .secondReverse), divisionState positive ambient r.control1 none,
        frame7 r output⟩) =
      some ⟨some (labels (.secondLookup (.run .copyFirst))),
        divisionState positive ambient r.control1 none, frame8 r output⟩ at h7
  have h8 := lookupPhaseTrace true positive r.smallTable id Function.injective_id
    labels exit target code (frame8 r output) r.oldTable
    (by simp) (by simp)
    (r.firstVertex, secondOffset r.control1) []
    (by simpa [frameContents, RowData.secondRow] using
      congrArg encodeWord r.query2_eq_secondRow)
    (by simp) (((ambient,r.control1),zero),()) none
  change (advance (TM2.step target))^[MachinePreservingLookupClean.steps
      (rotationWords r.oldTable) r.secondRow.val]
      (some ⟨some (labels (.secondLookup (.run .copyFirst))),
        divisionState positive ambient r.control1 none, frame8 r output⟩) =
      some ⟨some (labels .secondScan), divisionState positive ambient r.control1 none,
        frame9 r output⟩ at h8
  have h9 := secondDivisionTrace positive r.smallTable id Function.injective_id labels exit
    target code (frame9 r output) r.secondValue [] [] []
    (by simp) (by simp) (by simp)
    ambient r.control1 none
  rw [← r.secondReturn_eq_residue positive] at h9
  change (advance (TM2.step target))^[r.secondValue + 2]
      (some ⟨some (labels .secondScan), divisionState positive ambient r.control1 none,
        frame9 r output⟩) =
      some ⟨some (labels (.outputEmit (Emitter.labelAt 3 _ 0 .entry))),
        divisionState positive ambient r.control2 none, frame10 r output⟩ at h9
  have h10 := outputEmitTraceAt positive r.smallTable id Function.injective_id
    labels exit target code r.secondVertex.val (frame10 r output)
    (by simp) (by simp) ((ambient,r.control2),zero)
  change (advance (TM2.step target))^[emitSteps r.secondVertex.val]
      (some ⟨some (labels (.outputEmit (Emitter.labelAt 3 _ 0 .entry))),
        divisionState positive ambient r.control2 none, frame10 r output⟩) =
      some ⟨some (labels (.cleanup 0)), divisionState positive ambient r.control2 none,
        frame11 r output⟩ at h10
  have h11 := cleanupExitTraceAt positive r.smallTable id Function.injective_id
    labels exit target code (frame11 r output) (divisionState positive ambient r.control2 none)
  change (advance (TM2.step target))^[cleanupSteps id (frame11 r output) + 1]
      (some ⟨some (labels (.cleanup 0)), divisionState positive ambient r.control2 none,
        frame11 r output⟩) =
      some ⟨exit, divisionState positive ambient r.control2 none, frame12 r output⟩ at h11
  rw [final_frame_eq] at h11
  exact concatenate_inline_MachineExpanderRow (concatenate_inline_MachineExpanderRow (concatenate_inline_MachineExpanderRow (concatenate_inline_MachineExpanderRow (concatenate_inline_MachineExpanderRow
    (concatenate_inline_MachineExpanderRow (concatenate_inline_MachineExpanderRow (concatenate_inline_MachineExpanderRow (concatenate_inline_MachineExpanderRow (concatenate_inline_MachineExpanderRow
      (concatenate_inline_MachineExpanderRow h0 h1) h2) h3) h4) h5) h6) h7) h8) h9) h10) h11

end Execution

theorem rowSteps_le {v d : Nat} (r : RowData v d) (output : List Bool) :
    rowSteps r output ≤ 80 * (r.tableLength + 1) := by
  have lookup1 := MachinePreservingLookupClean.steps_le (rotationWords r.oldTable)
    r.firstRow.val r.firstValue (rotationWords_getElem? r.oldTable r.firstRow)
  have lookup2 := MachinePreservingLookupClean.steps_le (rotationWords r.oldTable)
    r.secondRow.val r.secondValue (rotationWords_getElem? r.oldTable r.secondRow)
  have h0 := r.inputVertex_le_tableLength
  have h1 := r.query1_le_tableLength
  have h2 := r.firstValue_le_tableLength
  have h3 := r.firstVertex_le_tableLength
  have h4 := r.query2_le_tableLength
  have h5 := r.secondValue_le_tableLength
  have h6 := r.secondVertex_le_tableLength
  have clean := cleanupSteps_le_tableLength r output
  change _ ≤ 6 * r.tableLength + 4 at lookup1 lookup2
  simp only [rowSteps, emitSteps]
  omega

def rowInTimeAt {v d : Nat} {ρ Λ : Type} [Fintype ρ]
    (positive : 0 < d) (r : RowData v d) (output : List Bool) (ambient : ρ)
    (labels : Label d → Λ) (exit : Option Λ)
    (target : Λ → TM2.Stmt (fun _ : Tape => Bool) Λ (State ρ d))
    (code : ∀ l, target (labels l) = statement positive r.smallTable id labels exit l) :
    StateTransition.EvalsToInTime (TM2.step target)
      ⟨some (labels .initialize), divisionState positive ambient r.control0 none,
        frame0 r output⟩
      (some ⟨exit, divisionState positive ambient r.control2 none,
        emittedWord .output (frame0 r output) r.finalValue⟩)
      (80 * (r.tableLength + 1)) where
  steps := rowSteps r output
  evals_in_steps := rowTraceAt positive r output ambient labels exit target code
  steps_le_m := rowSteps_le r output

def rowInTime {v d : Nat} {ρ : Type} [Fintype ρ]
    (positive : 0 < d) (r : RowData v d) (output : List Bool) (ambient : ρ) :
    StateTransition.EvalsToInTime (TM2.step (program positive r.smallTable))
      ⟨some .initialize, divisionState positive ambient r.control0 none, frame0 r output⟩
      (some ⟨none, divisionState positive ambient r.control2 none,
        emittedWord .output (frame0 r output) r.finalValue⟩)
      (80 * (r.tableLength + 1)) :=
  rowInTimeAt positive r output ambient id none (program positive r.smallTable) (fun _ => rfl)

end DFVSGames.Foundations.Complexity.MachineExpanderRow
end

section

namespace DFVSGames.Foundations.Complexity.MachineExpanderTable

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl

variable {ρ : Type} {d : Nat}

@[simp] theorem caller_boundaryState (positive : 0 < d) (H : Table (cloudSize d) d)
    (ambient : ρ) (position : Position d) :
    caller (boundaryState positive H ambient position) = ambient := rfl

@[simp] theorem prepareState_boundaryState (positive : 0 < d) (H : Table (cloudSize d) d)
    (ambient : ρ) (position : Position d) :
    prepareState positive H (boundaryState positive H ambient position) =
      boundaryState positive H ambient position := rfl

@[simp] theorem clearRegister_boundaryState (positive : 0 < d) (H : Table (cloudSize d) d)
    (ambient : ρ) (position : Position d) :
    clearRegister (boundaryState positive H ambient position) =
      boundaryState positive H ambient position := rfl

@[simp] theorem caller_prepareState (positive : 0 < d) (H : Table (cloudSize d) d)
    (state : State ρ d) : caller (prepareState positive H state) = caller state := rfl

@[simp] theorem caller_resetState (positive : 0 < d) (H : Table (cloudSize d) d)
    (state : State ρ d) : caller (resetState positive H state) = caller state := rfl

@[simp] theorem caller_clearRegister (state : State ρ d) :
    caller (clearRegister state) = caller state := rfl

@[simp] theorem caller_advancePositionState (positive : 0 < d) (state : State ρ d) :
    caller (advancePositionState positive state) = caller state := rfl

@[simp] theorem caller_resetPositionState (positive : 0 < d) (state : State ρ d) :
    caller (resetPositionState positive state) = caller state := rfl

theorem nextPosition_val_of_lt (positive : 0 < d) (position : Position d)
    (more : position.val + 1 < rowFactor d) :
    (nextPosition positive position).val = position.val + 1 := Nat.mod_eq_of_lt more

theorem boundaryTapes_update_count (vertex remaining next : Nat)
    (oldTable output countSuffix result : List Bool) :
    Function.update (boundaryTapes vertex remaining oldTable output countSuffix result)
      (.inr .vertexCount) (encodeWord next ++ countSuffix) =
      boundaryTapes vertex next oldTable output countSuffix result := by
  funext tape
  rcases tape with row | extra
  · cases row <;> simp [boundaryTapes, rowTapes, MachineEmbedding.tapes, Function.update]
  · cases extra <;> simp [boundaryTapes, extraTapes, MachineEmbedding.tapes, Function.update]

theorem boundaryTapes_increment_vertex (vertex remaining : Nat)
    (oldTable output countSuffix result : List Bool) :
    Function.update (boundaryTapes vertex remaining oldTable output countSuffix result)
      (.inl .inputVertex) (true :: encodeWord vertex) =
      boundaryTapes (vertex + 1) remaining oldTable output countSuffix result := by
  funext tape
  rcases tape with row | extra
  · cases row <;>
      simp [boundaryTapes, rowTapes, MachineEmbedding.tapes, Function.update,
        encodeWord, List.replicate_succ]
  · cases extra <;>
      simp [boundaryTapes, extraTapes, MachineEmbedding.tapes, Function.update]

theorem initialTapes_initialize (vertices : Nat) (oldTable countSuffix : List Bool) :
    Function.update (initialTapes vertices oldTable countSuffix) (.inl .inputVertex) [false] =
      boundaryTapes 0 vertices oldTable [] countSuffix [] := by
  funext tape
  rcases tape with row | extra
  · cases row <;>
      simp [initialTapes, boundaryTapes, rowTapes, MachineEmbedding.tapes,
        Function.update, encodeWord]
  · cases extra <;>
      simp [initialTapes, boundaryTapes, extraTapes, MachineEmbedding.tapes,
        Function.update]

variable [Fintype ρ]

theorem initializeStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (base : ∀ tape, List (Alphabet tape)) (state : State ρ d) :
    TM2.step (program positive H) ⟨some (.inr .initialize), state, base⟩ =
      some ⟨some (.inr .vertexGuard), resetState positive H state,
        Function.update base (.inl .inputVertex) (false :: base (.inl .inputVertex))⟩ := by
  change some (TM2.stepAux (program positive H (.inr .initialize)) state base) = _
  rw [program_outer]
  rfl

theorem initialize_boundaryStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (vertices : Nat) (oldTable countSuffix : List Bool) (state : State ρ d) :
    TM2.step (program positive H)
      ⟨some (.inr .initialize), state, initialTapes vertices oldTable countSuffix⟩ =
      some ⟨some (.inr .vertexGuard), initialState positive H (caller state),
        boundaryTapes 0 vertices oldTable [] countSuffix []⟩ := by
  have h := initializeStep positive H (initialTapes vertices oldTable countSuffix) state
  have input : initialTapes vertices oldTable countSuffix (.inl .inputVertex) = [] := rfl
  simp only [input, resetState] at h
  exact h.trans (congrArg
    (fun tapes : ∀ tape, List (Alphabet tape) =>
      (some ⟨some (.inr .vertexGuard), initialState positive H (caller state), tapes⟩ :
        Option (TM2.Cfg Alphabet (Label d) (State ρ d))))
    (initialTapes_initialize vertices oldTable countSuffix))

theorem vertexGuard_succStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (base : ∀ tape, List (Alphabet tape)) (state : State ρ d)
    (remaining : Nat) (suffix : List Bool)
    (counter : base (.inr .vertexCount) = encodeWord (remaining + 1) ++ suffix) :
    TM2.step (program positive H) ⟨some (.inr .vertexGuard), state, base⟩ =
      some ⟨some (.inr .prepareRow), clearRegister state,
        Function.update base (.inr .vertexCount) (encodeWord remaining ++ suffix)⟩ := by
  change some (TM2.stepAux (program positive H (.inr .vertexGuard)) state base) = _
  rw [program_outer]
  simp [outerStatement, MachineControl.statement, vertexGuardCore, TM2.stepAux,
    guardStates, clearRegister, counter, encodeWord, List.replicate_succ]

theorem vertexGuard_zeroStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (base : ∀ tape, List (Alphabet tape)) (state : State ρ d)
    (suffix : List Bool)
    (counter : base (.inr .vertexCount) = encodeWord 0 ++ suffix) :
    TM2.step (program positive H) ⟨some (.inr .vertexGuard), state, base⟩ =
      some ⟨some (.inr .reverseOutput), clearRegister state, base⟩ := by
  change some (TM2.stepAux (program positive H (.inr .vertexGuard)) state base) = _
  rw [program_outer]
  simp [outerStatement, MachineControl.statement, vertexGuardCore, TM2.stepAux,
    guardStates, clearRegister, counter, encodeWord]

theorem vertexGuard_boundary_succStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (vertex remaining : Nat) (oldTable output countSuffix result : List Bool)
    (state : State ρ d) :
    TM2.step (program positive H)
      ⟨some (.inr .vertexGuard), state,
        boundaryTapes vertex (remaining + 1) oldTable output countSuffix result⟩ =
      some ⟨some (.inr .prepareRow), clearRegister state,
        boundaryTapes vertex remaining oldTable output countSuffix result⟩ := by
  simpa only [boundaryTapes_update_count] using
    vertexGuard_succStep positive H
      (boundaryTapes vertex (remaining + 1) oldTable output countSuffix result)
      state remaining countSuffix rfl

theorem vertexGuard_boundary_zeroStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (vertex : Nat) (oldTable output countSuffix result : List Bool) (state : State ρ d) :
    TM2.step (program positive H)
      ⟨some (.inr .vertexGuard), state,
        boundaryTapes vertex 0 oldTable output countSuffix result⟩ =
      some ⟨some (.inr .reverseOutput), clearRegister state,
        boundaryTapes vertex 0 oldTable output countSuffix result⟩ :=
  vertexGuard_zeroStep positive H
    (boundaryTapes vertex 0 oldTable output countSuffix result) state countSuffix rfl

theorem prepareRowStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (base : ∀ tape, List (Alphabet tape)) (state : State ρ d) :
    TM2.step (program positive H) ⟨some (.inr .prepareRow), state, base⟩ =
      some ⟨some (.inl .initialize), prepareState positive H state, base⟩ := by
  change some (TM2.stepAux (program positive H (.inr .prepareRow)) state base) = _
  rw [program_outer]
  rfl

theorem afterRow_moreStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (base : ∀ tape, List (Alphabet tape)) (state : State ρ d)
    (more : state.2.val + 1 < rowFactor d) :
    TM2.step (program positive H) ⟨some (.inr .afterRow), state, base⟩ =
      some ⟨some (.inr .prepareRow), advancePositionState positive state, base⟩ := by
  change some (TM2.stepAux (program positive H (.inr .afterRow)) state base) = _
  rw [program_outer]
  simp [outerStatement, TM2.stepAux, more]

theorem afterRow_lastStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (base : ∀ tape, List (Alphabet tape)) (state : State ρ d)
    (last : ¬ state.2.val + 1 < rowFactor d) :
    TM2.step (program positive H) ⟨some (.inr .afterRow), state, base⟩ =
      some ⟨some (.inr .vertexGuard), resetPositionState positive state,
        Function.update base (.inl .inputVertex) (true :: base (.inl .inputVertex))⟩ := by
  change some (TM2.stepAux (program positive H (.inr .afterRow)) state base) = _
  rw [program_outer]
  simp [outerStatement, TM2.stepAux, last]

theorem afterRow_last_boundaryStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (vertex remaining : Nat) (oldTable output countSuffix result : List Bool)
    (state : State ρ d) (last : ¬ state.2.val + 1 < rowFactor d) :
    TM2.step (program positive H)
      ⟨some (.inr .afterRow), state,
        boundaryTapes vertex remaining oldTable output countSuffix result⟩ =
      some ⟨some (.inr .vertexGuard), resetPositionState positive state,
        boundaryTapes (vertex + 1) remaining oldTable output countSuffix result⟩ := by
  have input : boundaryTapes vertex remaining oldTable output countSuffix result
      (.inl .inputVertex) = encodeWord vertex := rfl
  have h := afterRow_lastStep positive H
    (boundaryTapes vertex remaining oldTable output countSuffix result) state last
  simp only [input] at h
  exact h.trans (congrArg
    (fun tapes : ∀ tape, List (Alphabet tape) =>
      (some ⟨some (.inr .vertexGuard), resetPositionState positive state, tapes⟩ :
        Option (TM2.Cfg Alphabet (Label d) (State ρ d))))
    (boundaryTapes_increment_vertex vertex remaining oldTable output countSuffix result))

theorem reverseOutput_consStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (base : ∀ tape, List (Alphabet tape)) (state : State ρ d)
    (symbol : Bool) (word : List Bool) (source : base (.inl .output) = symbol :: word) :
    TM2.step (program positive H) ⟨some (.inr .reverseOutput), state, base⟩ =
      some ⟨some (.inr .reverseOutput), ((state.1.1, some symbol), state.2),
        Function.update (Function.update base (.inl .output) word)
          (.inr .result) (symbol :: base (.inr .result))⟩ := by
  change some (TM2.stepAux (program positive H (.inr .reverseOutput)) state base) = _
  rw [program_outer]
  simp [outerStatement, MachineControl.statement, Reduction.MachineTransfer.loopAt,
    Reduction.MachineTransfer.exitAt, TM2.stepAux, guardStates, source]

theorem reverseOutput_nilStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (base : ∀ tape, List (Alphabet tape)) (state : State ρ d)
    (source : base (.inl .output) = []) :
    TM2.step (program positive H) ⟨some (.inr .reverseOutput), state, base⟩ =
      some ⟨some (.inr .done), clearRegister state, base⟩ := by
  have same : Function.update base (.inl .output) [] = base := by
    simpa only [source] using Function.update_eq_self (.inl .output) base
  change some (TM2.stepAux (program positive H (.inr .reverseOutput)) state base) = _
  rw [program_outer]
  simp [outerStatement, MachineControl.statement, Reduction.MachineTransfer.loopAt,
    Reduction.MachineTransfer.exitAt, TM2.stepAux, guardStates, clearRegister, source, same]

theorem doneStep (positive : 0 < d) (H : Table (cloudSize d) d)
    (base : ∀ tape, List (Alphabet tape)) (state : State ρ d) :
    TM2.step (program positive H) ⟨some (.inr .done), state, base⟩ =
      some ⟨none, state, base⟩ := by
  change some (TM2.stepAux (program positive H (.inr .done)) state base) = _
  rw [program_outer]
  rfl

end DFVSGames.Foundations.Complexity.MachineExpanderTable
end

section

namespace DFVSGames.Foundations.PCP.ExpanderTableEnumeration

open ExpanderTables ExpanderRowControl ExpanderTableWords
open DFVSGames.Foundations.Complexity

variable {v d : Nat}

def globalIndex (vertex : Fin v) (position : Fin (rowFactor d)) :
    Fin ((v * cloudSize d) * degree d) :=
  let pair := (rowIndex (cloudSize d) (degree d)).symm position
  rowIndex (v * cloudSize d) (degree d)
    (rowIndex v (cloudSize d) (vertex, pair.1), pair.2)

theorem globalIndex_val (vertex : Fin v) (position : Fin (rowFactor d)) :
    (globalIndex vertex position).val = position.val + rowFactor d * vertex.val := by
  let pair := (rowIndex (cloudSize d) (degree d)).symm position
  have hp := congrArg Fin.val
    ((rowIndex (cloudSize d) (degree d)).apply_symm_apply position)
  change pair.2.val + degree d * pair.1.val = position.val at hp
  change pair.2.val + degree d * (pair.1.val + cloudSize d * vertex.val) = _
  calc
    _ = (pair.2.val + degree d * pair.1.val) + rowFactor d * vertex.val := by
      dsimp only [rowFactor]
      ring
    _ = position.val + rowFactor d * vertex.val := by rw [hp]

def rowValue (G : Table v (degree d)) (H : Table (cloudSize d) d)
    (vertex : Fin v) (position : Fin (rowFactor d)) : Nat :=
  let pair := (rowIndex (cloudSize d) (degree d)).symm position
  let result := evaluateRow G H vertex pair.1 pair.2
  outputAddress result.1.val result.2

theorem rowValue_eq_reverseIndex (G : Table v (degree d)) (H : Table (cloudSize d) d)
    (vertex : Fin v) (position : Fin (rowFactor d)) :
    rowValue G H vertex position = (reverseIndex (step G H) (globalIndex vertex position)).val := by
  exact outputAddress_eq_step_reverseIndex G H vertex
    ((rowIndex (cloudSize d) (degree d)).symm position).1
    ((rowIndex (cloudSize d) (degree d)).symm position).2

def vertexWords (G : Table v (degree d)) (H : Table (cloudSize d) d) (vertex : Fin v) :
    List Nat := List.ofFn (rowValue G H vertex)

def generatedWords (G : Table v (degree d)) (H : Table (cloudSize d) d) : List Nat :=
  (List.ofFn (vertexWords G H)).flatten

@[simp] theorem vertexWords_length (G : Table v (degree d)) (H : Table (cloudSize d) d)
    (vertex : Fin v) : (vertexWords G H vertex).length = rowFactor d := by
  simp [vertexWords]

theorem vertexWords_drop_succ (G : Table v (degree d)) (H : Table (cloudSize d) d)
    (vertex : Fin v) (position : Fin (rowFactor d)) :
    (vertexWords G H vertex).drop position.val =
      rowValue G H vertex position :: (vertexWords G H vertex).drop (position.val + 1) := by
  rw [List.drop_eq_getElem_cons (by simp)]
  simp [vertexWords]

@[simp] theorem vertexWords_drop_full (G : Table v (degree d)) (H : Table (cloudSize d) d)
    (vertex : Fin v) : (vertexWords G H vertex).drop (rowFactor d) = [] := by
  apply List.drop_eq_nil_of_le
  simp

theorem vertexWords_drop_last (G : Table v (degree d)) (H : Table (cloudSize d) d)
    (vertex : Fin v) (position : Fin (rowFactor d))
    (last : position.val + 1 = rowFactor d) :
    (vertexWords G H vertex).drop position.val = [rowValue G H vertex position] := by
  rw [vertexWords_drop_succ, last, vertexWords_drop_full]

private theorem ofFn_cast_inline_ExpanderTableEnumeration {α : Type*} {n m : Nat} (h : n = m) (f : Fin m → α) :
    List.ofFn (fun i : Fin n => f (Fin.cast h i)) = List.ofFn f := by
  cases h
  rfl

theorem rotationWords_eq_ofFn {n q : Nat} (G : Table n q) :
    rotationWords G = List.ofFn (fun i : Fin (n * q) => (reverseIndex G i).val) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    rw [List.getElem_ofFn]
    exact rotationWords_getElem G i (by simpa only [rotationWords_length] using hi)

theorem rowCount_eq : v * rowFactor d = (v * cloudSize d) * degree d :=
  (Nat.mul_assoc v (cloudSize d) (degree d)).symm

theorem generatedWords_eq_flat_ofFn (G : Table v (degree d)) (H : Table (cloudSize d) d) :
    generatedWords G H = List.ofFn (fun i : Fin (v * rowFactor d) =>
      (reverseIndex (step G H) (Fin.cast rowCount_eq i)).val) := by
  rw [List.ofFn_mul]
  unfold generatedWords vertexWords
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext vertex
  apply congrArg List.ofFn
  funext position
  rw [rowValue_eq_reverseIndex]
  apply congrArg (fun i : Fin ((v * cloudSize d) * degree d) =>
    (reverseIndex (step G H) i).val)
  apply Fin.ext
  rw [globalIndex_val]
  change position.val + rowFactor d * vertex.val = vertex.val * rowFactor d + position.val
  ac_rfl

theorem generatedWords_eq_rotationWords (G : Table v (degree d)) (H : Table (cloudSize d) d) :
    generatedWords G H = rotationWords (step G H) := by
  rw [generatedWords_eq_flat_ofFn]
  exact (ofFn_cast_inline_ExpanderTableEnumeration (rowCount_eq (v := v) (d := d))
    (fun i => (reverseIndex (step G H) i).val)).trans
    (rotationWords_eq_ofFn (step G H)).symm

@[simp] theorem generatedWords_length (G : Table v (degree d)) (H : Table (cloudSize d) d) :
    (generatedWords G H).length = v * rowFactor d := by
  rw [generatedWords_eq_rotationWords, rotationWords_length]
  exact rowCount_eq.symm

def priorVertices (G : Table v (degree d)) (H : Table (cloudSize d) d) (count : Nat) :
    List Nat := ((List.ofFn (vertexWords G H)).take count).flatten

def prefixRows (G : Table v (degree d)) (H : Table (cloudSize d) d)
    (vertex : Fin v) (completedPositions : Nat) : List Nat :=
  priorVertices G H vertex.val ++ (vertexWords G H vertex).take completedPositions

@[simp] theorem priorVertices_zero (G : Table v (degree d)) (H : Table (cloudSize d) d) :
    priorVertices G H 0 = [] := by simp [priorVertices]

@[simp] theorem priorVertices_full (G : Table v (degree d)) (H : Table (cloudSize d) d) :
    priorVertices G H v = generatedWords G H := by
  unfold priorVertices generatedWords
  rw [List.take_of_length_le (by simp)]

theorem priorVertices_succ (G : Table v (degree d)) (H : Table (cloudSize d) d)
    (k : Nat) (hk : k < v) :
    priorVertices G H (k + 1) = priorVertices G H k ++ vertexWords G H ⟨k, hk⟩ := by
  unfold priorVertices
  rw [List.take_succ_eq_append_getElem (by simpa using hk), List.flatten_append]
  simp

@[simp] theorem prefixRows_zero (G : Table v (degree d)) (H : Table (cloudSize d) d)
    (vertex : Fin v) : prefixRows G H vertex 0 = priorVertices G H vertex.val := by
  simp [prefixRows]

theorem prefixRows_succ (G : Table v (degree d)) (H : Table (cloudSize d) d)
    (vertex : Fin v) (r : Nat) (hr : r < rowFactor d) :
    prefixRows G H vertex (r + 1) =
      prefixRows G H vertex r ++ [rowValue G H vertex ⟨r, hr⟩] := by
  unfold prefixRows
  rw [List.take_succ_eq_append_getElem (by simpa using hr)]
  simp [vertexWords, List.append_assoc]

theorem prefixRows_complete (G : Table v (degree d)) (H : Table (cloudSize d) d)
    (vertex : Fin v) :
    prefixRows G H vertex (rowFactor d) = priorVertices G H (vertex.val + 1) := by
  rw [prefixRows, List.take_of_length_le (by simp)]
  simpa using (priorVertices_succ G H vertex.val vertex.isLt).symm

def accumulate (values : List Nat) (initial : List Bool) : List Bool :=
  values.foldl (fun accumulator value => (encodeWord value).reverse ++ accumulator) initial

theorem accumulate_eq (values : List Nat) (initial : List Bool) :
    accumulate values initial = (encodeWords values).reverse ++ initial := by
  induction values generalizing initial with
  | nil => simp [accumulate, encodeWords]
  | cons value values ih =>
      simpa only [accumulate, List.foldl_cons, encodeWords, List.reverse_append,
        List.append_assoc] using ih ((encodeWord value).reverse ++ initial)

theorem accumulate_append (first second : List Nat) (initial : List Bool) :
    accumulate (first ++ second) initial = accumulate second (accumulate first initial) := by
  simp only [accumulate, List.foldl_append]

theorem accumulate_prefixRows_succ (G : Table v (degree d)) (H : Table (cloudSize d) d)
    (vertex : Fin v) (r : Nat) (hr : r < rowFactor d) (initial : List Bool) :
    accumulate (prefixRows G H vertex (r + 1)) initial =
      (encodeWord (rowValue G H vertex ⟨r, hr⟩)).reverse ++
        accumulate (prefixRows G H vertex r) initial := by
  rw [prefixRows_succ G H vertex r hr, accumulate_append]
  rfl

theorem accumulate_generatedWords (G : Table v (degree d)) (H : Table (cloudSize d) d)
    (initial : List Bool) :
    accumulate (generatedWords G H) initial =
      (encodeWords (rotationWords (step G H))).reverse ++ initial := by
  rw [accumulate_eq, generatedWords_eq_rotationWords]

theorem encode_generatedWords_length_le (G : Table v (degree d)) (H : Table (cloudSize d) d) :
    (encodeWords (generatedWords G H)).length ≤
      (v * rowFactor d) * (v * rowFactor d + 1) := by
  rw [generatedWords_eq_rotationWords, rowCount_eq]
  exact encode_rotationWords_length_le (step G H)

theorem accumulate_generatedWords_length_le (G : Table v (degree d))
    (H : Table (cloudSize d) d) (initial : List Bool) :
    (accumulate (generatedWords G H) initial).length ≤
      (v * rowFactor d) * (v * rowFactor d + 1) + initial.length := by
  rw [accumulate_eq, List.length_append, List.length_reverse]
  exact Nat.add_le_add_right (encode_generatedWords_length_le G H) initial.length

end DFVSGames.Foundations.PCP.ExpanderTableEnumeration

end

section

namespace DFVSGames.Foundations.Complexity.MachineExpanderTable

open Turing
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords
open PCP.ExpanderTableEnumeration

private def singleStep_inline_MachineExpanderTableRows {α : Type*} (step : α → Option α) (a b : α)
    (h : step a = some b) : StateTransition.EvalsToInTime step a (some b) 1 where
  steps := 1
  evals_in_steps := by change step a = some b; exact h
  steps_le_m := Nat.le_refl _

private def sequence_inline_MachineExpanderTableRows {α : Type*} {step : α → Option α} {a b c : α} {m n : Nat}
    (first : StateTransition.EvalsToInTime step a (some b) m)
    (second : StateTransition.EvalsToInTime step b (some c) n) :
    StateTransition.EvalsToInTime step a (some c) (m + n) := by
  simpa only [Nat.add_comm n m] using
    StateTransition.EvalsToInTime.trans step m n a b (some c) first second

private def widen_inline_MachineExpanderTableRows {α : Type*} {step : α → Option α} {a : α} {b : Option α} {m n : Nat}
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
  exact sequence_inline_MachineExpanderTableRows
    (singleStep_inline_MachineExpanderTableRows _ _ _ (prepareRowStep positive H
      (boundaryTapes vertex.val remaining (encodeWords (rotationWords G)) output countSuffix result)
      state)) run

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

private def suffixRun_aux_inline_MachineExpanderTableRows (positive : 0 < d) (G : Table v (degree d))
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
        have finish := singleStep_inline_MachineExpanderTableRows _ _ _ (afterRow_last_boundaryStep positive H vertex.val remaining
          (encodeWords (rotationWords G)) nextOutput countSuffix result after (by
            change ¬ state.2.val + 1 < rowFactor d
            omega))
        refine ⟨resetPositionState positive after, ?_, rfl, ?_⟩
        · rfl
        · have all := sequence_inline_MachineExpanderTableRows row finish
          have words : accumulate ((vertexWords G H vertex).drop state.2.val) output =
              nextOutput := by
            rw [vertexWords_drop_last G H vertex state.2 hp]
            rfl
          have budget : rowFactor d - state.2.val = 1 := by omega
          rw [words, budget, Nat.one_mul]
          exact widen_inline_MachineExpanderTableRows all (by omega)
      · have more : state.2.val + 1 < rowFactor d := by omega
        let next := advancePositionState positive after
        have nextPositionValue : next.2.val = state.2.val + 1 :=
          nextPosition_val_of_lt positive state.2 more
        have nextCount : next.2.val + n = rowFactor d := by omega
        let tail := ih next nextCount nextOutput
        have advance := singleStep_inline_MachineExpanderTableRows _ _ _ (afterRow_moreStep positive H
          (boundaryTapes vertex.val remaining (encodeWords (rotationWords G))
            nextOutput countSuffix result) after more)
        have all := sequence_inline_MachineExpanderTableRows (sequence_inline_MachineExpanderTableRows row advance) tail.execution
        refine ⟨tail.finalState, ?_, tail.position_zero, ?_⟩
        · exact tail.caller_preserved
        · have words : accumulate ((vertexWords G H vertex).drop state.2.val) output =
              accumulate ((vertexWords G H vertex).drop next.2.val) nextOutput := by
            rw [vertexWords_drop_succ G H vertex state.2, nextPositionValue]
            rfl
          rw [words]
          apply widen_inline_MachineExpanderTableRows all
          have hcount : rowFactor d - state.2.val = n + 1 := by omega
          have hnext : rowFactor d - next.2.val = n := by omega
          rw [hcount, hnext, Nat.add_mul, Nat.one_mul]
          omega

def suffixInTime (positive : 0 < d) (G : Table v (degree d))
    (H : Table (cloudSize d) d) (vertex : Fin v) (state : State ρ d)
    (remaining : Nat) (output countSuffix result : List Bool) :
    VertexSuffixRun positive G H vertex state remaining output countSuffix result :=
  suffixRun_aux_inline_MachineExpanderTableRows positive G H vertex remaining countSuffix result
    (rowFactor d - state.2.val) state (by have h := state.2.isLt; omega) output

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

end DFVSGames.Foundations.Complexity.MachineExpanderTable
end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
