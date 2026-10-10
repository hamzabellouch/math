import Mathlib
import OAI.Combinatorics.IndependentSets.Machines.MachineExpanderRowFrames

namespace OAI

namespace IndependentSetsGames.Foundations.Complexity.MachineExpanderRow

open Turing MachineComposition
open PCP.ExpanderTables PCP.ExpanderRowControl PCP.ExpanderTableWords PCP.AlphabetTable

private theorem concatenate {A : Type*} {f : A → A} {m n : Nat} {a b c : A}
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
  exact concatenate (concatenate (concatenate (concatenate (concatenate
    (concatenate (concatenate (concatenate (concatenate (concatenate
      (concatenate h0 h1) h2) h3) h4) h5) h6) h7) h8) h9) h10) h11

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

end IndependentSetsGames.Foundations.Complexity.MachineExpanderRow

end OAI
