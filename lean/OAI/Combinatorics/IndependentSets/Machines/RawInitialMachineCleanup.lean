import Mathlib
import OAI.Combinatorics.IndependentSets.Machines.RawInitialMachineReadClause
import OAI.Combinatorics.IndependentSets.Machines.RawInitialMachineRows

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.RawInitialMachineCleanup

open Turing Complexity RawInitialMachineModel RawInitialMachineReadClause

theorem trace_trans {α : Type*} (f : α → α) {a b : ℕ} {x y z : α}
    (first : f^[a] x = y) (second : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

theorem incrementIndexTrace (base : Tape → List Bool) (state : State) :
    (MachineComposition.advance (TM2.step program))^[1]
      (some ⟨some .incrementIndex, state, base⟩) =
      some ⟨some .guard, state, Function.update base .index (true :: base .index)⟩ := by
  rfl

theorem cleanupTrace {n : ℕ} (base : Tape → List Bool) (c : Target.Clause n)
    (suffix : List Bool) (i : ℕ)
    (hempty : ∀ j, base (.field j) = []) (hindex : base .index = encodeWord i)
    (incoming : State) :
    (MachineComposition.advance (TM2.step program))^[
        (encodeWords (Complexity.clauseWords c)).length + 7]
      (some ⟨some (.cleanupField 0), incoming, recordTapes base c suffix⟩) =
      some ⟨some .guard, (incoming.1, none),
        Function.update (Function.update base .input suffix) .index (encodeWord (i + 1))⟩ := by
  let r := recordTapes base c suffix
  let t1 := Function.update r (.field 0) []
  let t2 := Function.update t1 (.field 1) []
  let t3 := Function.update t2 (.field 2) []
  let t4 := Function.update t3 (.field 3) []
  let t5 := Function.update t4 (.field 4) []
  let t6 := Function.update t5 (.field 5) []
  have h1 := (RawInitialMachinePhases.cleanupFieldInTime 0 r incoming).evals_in_steps
  change (MachineComposition.advance (TM2.step program))^[
      (encodeWord (fieldValue c 0)).length + 1]
    (some ⟨some (.cleanupField 0), incoming, r⟩) =
    some ⟨some (.cleanupField 1), (incoming.1, none), t1⟩ at h1
  have h2 := (RawInitialMachinePhases.cleanupFieldInTime 1 t1 (incoming.1, none)).evals_in_steps
  have hf2 : t1 (.field 1) = encodeWord (fieldValue c 1) := by
    simp [t1, r]
  change (MachineComposition.advance (TM2.step program))^[(t1 (.field 1)).length + 1]
    (some ⟨some (.cleanupField 1), (incoming.1, none), t1⟩) =
    some ⟨some (.cleanupField 2), (incoming.1, none), t2⟩ at h2
  rw [hf2] at h2
  have h3 := (RawInitialMachinePhases.cleanupFieldInTime 2 t2 (incoming.1, none)).evals_in_steps
  have hf3 : t2 (.field 2) = encodeWord (fieldValue c 2) := by
    simp [t2, t1, r]
  change (MachineComposition.advance (TM2.step program))^[(t2 (.field 2)).length + 1]
    (some ⟨some (.cleanupField 2), (incoming.1, none), t2⟩) =
    some ⟨some (.cleanupField 3), (incoming.1, none), t3⟩ at h3
  rw [hf3] at h3
  have h4 := (RawInitialMachinePhases.cleanupFieldInTime 3 t3 (incoming.1, none)).evals_in_steps
  have hf4 : t3 (.field 3) = encodeWord (fieldValue c 3) := by
    simp [t3, t2, t1, r]
  change (MachineComposition.advance (TM2.step program))^[(t3 (.field 3)).length + 1]
    (some ⟨some (.cleanupField 3), (incoming.1, none), t3⟩) =
    some ⟨some (.cleanupField 4), (incoming.1, none), t4⟩ at h4
  rw [hf4] at h4
  have h5 := (RawInitialMachinePhases.cleanupFieldInTime 4 t4 (incoming.1, none)).evals_in_steps
  have hf5 : t4 (.field 4) = encodeWord (fieldValue c 4) := by
    simp [t4, t3, t2, t1, r]
  change (MachineComposition.advance (TM2.step program))^[(t4 (.field 4)).length + 1]
    (some ⟨some (.cleanupField 4), (incoming.1, none), t4⟩) =
    some ⟨some (.cleanupField 5), (incoming.1, none), t5⟩ at h5
  rw [hf5] at h5
  have h6 := (RawInitialMachinePhases.cleanupFieldInTime 5 t5 (incoming.1, none)).evals_in_steps
  have hf6 : t5 (.field 5) = encodeWord (fieldValue c 5) := by
    simp [t5, t4, t3, t2, t1, r]
  change (MachineComposition.advance (TM2.step program))^[(t5 (.field 5)).length + 1]
    (some ⟨some (.cleanupField 5), (incoming.1, none), t5⟩) =
    some ⟨some .incrementIndex, (incoming.1, none), t6⟩ at h6
  rw [hf6] at h6
  have last := incrementIndexTrace t6 (incoming.1, none)
  have total := trace_trans _ (trace_trans _ (trace_trans _ (trace_trans _
    (trace_trans _ (trace_trans _ h1 h2) h3) h4) h5) h6) last
  have htime :
      ((((((encodeWord (fieldValue c 0)).length + 1 +
        ((encodeWord (fieldValue c 1)).length + 1)) +
        ((encodeWord (fieldValue c 2)).length + 1)) +
        ((encodeWord (fieldValue c 3)).length + 1)) +
        ((encodeWord (fieldValue c 4)).length + 1)) +
        ((encodeWord (fieldValue c 5)).length + 1)) + 1 =
      (encodeWords (Complexity.clauseWords c)).length + 7 := by
    simp [fieldValue, Complexity.clauseWords, Complexity.literalWords, encodeWords]
    omega
  rw [htime] at total
  have frame : Function.update t6 .index (true :: t6 .index) =
      Function.update (Function.update base .input suffix) .index (encodeWord (i + 1)) := by
    funext k
    cases k with
    | field j =>
      fin_cases j <;> simp [t6, t5, t4, t3, t2, t1, r, recordTapes, hempty]
    | index =>
      simp [t6, t5, t4, t3, t2, t1, r, recordTapes, hindex,
        encodeWord, List.replicate_succ]
    | _ => simp [t6, t5, t4, t3, t2, t1, r, recordTapes]
  rw [frame] at total
  exact total

def cleanupInTime {n : ℕ} (base : Tape → List Bool) (c : Target.Clause n)
    (suffix : List Bool) (i : ℕ)
    (hempty : ∀ j, base (.field j) = []) (hindex : base .index = encodeWord i)
    (incoming : State) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.cleanupField 0), incoming, recordTapes base c suffix⟩
      (some ⟨some .guard, (incoming.1, none),
        Function.update (Function.update base .input suffix) .index (encodeWord (i + 1))⟩)
      ((encodeWords (Complexity.clauseWords c)).length + 7) where
  steps := (encodeWords (Complexity.clauseWords c)).length + 7
  evals_in_steps := cleanupTrace base c suffix i hempty hindex incoming
  steps_le_m := Nat.le_refl _

end IndependentSetsGames.Foundations.PCP.RawInitialMachineCleanup

namespace IndependentSetsGames.Foundations.PCP.RawInitialMachineBody

open Turing Target Complexity RawInitialMachineModel RawInitialMachineLoopData
open RawInitialMachineReadClause RawInitialMachineRows RawInitialMachineBudget

theorem trace_trans {α : Type*} (f : α → α) {a b : Nat} {x y z : α}
    (first : f^[a] x = y) (second : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

theorem guardTrace_succ (n i remaining : Nat) (input reversed : List Bool)
    (state : State) :
    (MachineComposition.advance (TM2.step program))^[1]
      (some ⟨some .guard, state, loopTapes n i (remaining + 1) input reversed⟩) =
      some ⟨some (.fieldStart 0), (state.1, none),
        loopTapes n i remaining input reversed⟩ := by
  have h := MachineUnaryCounter.guardTrace_succ Tape.counter Label.guard
    (.fieldStart 0) (.scan .dummyVariables) program rfl
    (loopTapes n i remaining input reversed) remaining [] state.1 state.2
  have heq (r : Nat) : MachineUnaryCounter.counterTapes Tape.counter
      (loopTapes n i remaining input reversed) r [] = loopTapes n i r input reversed := by
    funext tape
    cases tape <;> simp [MachineUnaryCounter.counterTapes, loopTapes]
  simpa only [heq, Prod.mk.eta] using h

theorem guardTrace_zero (n i : Nat) (input reversed : List Bool) (state : State) :
    (MachineComposition.advance (TM2.step program))^[1]
      (some ⟨some .guard, state, loopTapes n i 0 input reversed⟩) =
      some ⟨some (.scan .dummyVariables), (state.1, none),
        loopTapes n i 0 input reversed⟩ := by
  have h := MachineUnaryCounter.guardTrace_zero Tape.counter Label.guard
    (.fieldStart 0) (.scan .dummyVariables) program rfl
    (loopTapes n i 0 input reversed) [] state.1 state.2
  have heq : MachineUnaryCounter.counterTapes Tape.counter
      (loopTapes n i 0 input reversed) 0 [] = loopTapes n i 0 input reversed := by
    funext tape
    cases tape <;> simp [MachineUnaryCounter.counterTapes, loopTapes]
  simpa only [heq, Prod.mk.eta] using h

theorem bodyTrace {n : Nat} (i remaining : Nat) (c : Clause n)
    (suffix reversed : List Bool) (state : State) :
    (MachineComposition.advance (TM2.step program))^[bodyTime i c]
      (some ⟨some .guard, state,
        loopTapes n i (remaining + 1)
          (encodeWords (Complexity.clauseWords c) ++ suffix) reversed⟩) =
      some ⟨some .guard, (RawInitialRows.clauseSigns c, none),
        loopTapes n (i + 1) remaining suffix
          ((encodeWords (RawInitialRows.clauseWords n i
            (RawInitialRows.clauseNames c) (RawInitialRows.clauseSigns c))).reverse ++ reversed)⟩ := by
  let input := encodeWords (Complexity.clauseWords c) ++ suffix
  let base := loopTapes n i remaining input reversed
  let chunk := (encodeWords (RawInitialRows.clauseWords n i
    (RawInitialRows.clauseNames c) (RawInitialRows.clauseSigns c))).reverse
  let emitted := loopTapes n i remaining input (chunk ++ reversed)
  have first := guardTrace_succ n i remaining input reversed state
  have read := readClauseTrace base c suffix rfl (fun _ => rfl) (state.1, none)
  have rows := rowsTrace (recordTapes base c suffix) n i
    (RawInitialRows.clauseNames c) (RawInitialRows.clauseSigns c)
    rfl rfl rfl rfl rfl rfl
  have frame : outputTapes (recordTapes base c suffix) chunk =
      recordTapes emitted c suffix := by
    funext tape
    cases tape <;> simp [outputTapes, recordTapes, emitted, base, loopTapes]
  change (MachineComposition.advance (TM2.step program))^[6 * n + 18 * i +
      2 * nameSum c + 48]
    (some ⟨some (.scan (.tailVariables 0)), (RawInitialRows.clauseSigns c, none),
      recordTapes base c suffix⟩) =
    some ⟨some (.cleanupField 0), (RawInitialRows.clauseSigns c, none),
    outputTapes (recordTapes base c suffix) chunk⟩ at rows
  rw [frame] at rows
  have cleanup := RawInitialMachineCleanup.cleanupTrace emitted c suffix i
    (fun _ => rfl) rfl (RawInitialRows.clauseSigns c, none)
  have finalFrame : Function.update (Function.update emitted .input suffix)
      .index (encodeWord (i + 1)) =
      loopTapes n (i + 1) remaining suffix (chunk ++ reversed) := by
    funext tape
    cases tape <;> simp [emitted, loopTapes]
  rw [finalFrame] at cleanup
  have total := trace_trans _ (trace_trans _ (trace_trans _ first read) rows) cleanup
  have time : 1 + ((encodeWords (Complexity.clauseWords c)).length + 7) +
      (6 * n + 18 * i + 2 * nameSum c + 48) +
      ((encodeWords (Complexity.clauseWords c)).length + 7) = bodyTime i c := by
    simp only [bodyTime, nameSum]
    omega
  simpa only [time] using total

end IndependentSetsGames.Foundations.PCP.RawInitialMachineBody

end OAI
