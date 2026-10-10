import Mathlib
import OAI.Computability.DirectedFeedback.Machines.RawInitialMachineStart

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

namespace DFVSGames.Foundations.PCP.RawInitialMachineBody

open Turing Target Complexity RawInitialMachineModel RawInitialMachineLoopData
open RawInitialMachineReadClause RawInitialMachineRows RawInitialMachineBudget

private theorem trace_trans_inline_RawInitialMachineBody {α : Type*} (f : α → α) {a b : Nat} {x y z : α}
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
  have total := trace_trans_inline_RawInitialMachineBody _ (trace_trans_inline_RawInitialMachineBody _ (trace_trans_inline_RawInitialMachineBody _ first read) rows) cleanup
  have time : 1 + ((encodeWords (Complexity.clauseWords c)).length + 7) +
      (6 * n + 18 * i + 2 * nameSum c + 48) +
      ((encodeWords (Complexity.clauseWords c)).length + 7) = bodyTime i c := by
    simp only [bodyTime, nameSum]
    omega
  simpa only [time] using total

end DFVSGames.Foundations.PCP.RawInitialMachineBody

end

section

namespace DFVSGames.Foundations.PCP.RawInitialMachineFinish

open Turing Complexity RawInitialMachineModel RawInitialMachinePhases

private def tapes_inline_RawInitialMachineFinish (varsWord counter index reversed output : List Bool) : Tape → List Bool
  | .«variables» => varsWord
  | .counter => counter
  | .index => index
  | .reversed => reversed
  | .output => output
  | _ => []

def finishTapes (n m : Nat) (rev : List Bool) : Tape → List Bool :=
  tapes_inline_RawInitialMachineFinish (encodeWord n) [false] (encodeWord m) rev []

private theorem trace_trans_inline_RawInitialMachineFinish {α : Type*} (f : α → α) {a b : Nat} {x y z : α}
    (first : f^[a] x = y) (second : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

theorem trueRelationWords :
    GraphTables.relationWords (GraphTables.relationOf (fun _ _ => true)) =
      List.replicate 4096 1 := by
  unfold GraphTables.relationWords
  rw [GraphTables.relationOf, Vector.toList_ofFn, List.map_ofFn]
  exact List.ofFn_const 4096 1

theorem dummyBits_length (n m : Nat) :
    (encodeWords (RawInitialRows.dummyWords n m)).length = n + 7 * m + 8194 := by
  rw [encodeWords_length]
  simp only [RawInitialRows.dummyWords, List.sum_append, List.sum_cons,
    List.sum_nil, List.length_append, List.length_cons, List.length_nil,
    List.sum_replicate, List.length_replicate, nsmul_eq_mul, Nat.mul_one]
  omega

private theorem update_reversed_inline_RawInitialMachineFinish (varsWord counter index rev out word : List Bool) :
    Function.update (tapes_inline_RawInitialMachineFinish varsWord counter index rev out) .reversed word =
      tapes_inline_RawInitialMachineFinish varsWord counter index word out := by
  funext k
  cases k <;> simp [tapes_inline_RawInitialMachineFinish]

private theorem cleanupTrace_inline_RawInitialMachineFinish (n m : Nat) (rev : List Bool) (state : State) :
    (MachineComposition.advance (TM2.step program))^[n + m + 6]
      (some ⟨some (.cleanupFinal 0), state, finishTapes n m rev⟩) =
      some ⟨some .reset, (state.1, none), tapes_inline_RawInitialMachineFinish [] [] [] rev []⟩ := by
  have h0 := (cleanupFinalInTime 0 (finishTapes n m rev) state).evals_in_steps
  change (MachineComposition.advance (TM2.step program))^[(encodeWord n).length + 1]
    (some ⟨some (.cleanupFinal 0), state, finishTapes n m rev⟩) = _ at h0
  rw [encodeWord_length] at h0
  have f0 : Function.update (finishTapes n m rev) .«variables» [] =
      tapes_inline_RawInitialMachineFinish [] [false] (encodeWord m) rev [] := by
    funext k
    cases k <;> simp [finishTapes, tapes_inline_RawInitialMachineFinish]
  change (MachineComposition.advance (TM2.step program))^[n + 2]
    (some ⟨some (.cleanupFinal 0), state, finishTapes n m rev⟩) =
    some ⟨some (.cleanupFinal 1), (state.1, none),
      Function.update (finishTapes n m rev) .«variables» []⟩ at h0
  rw [f0] at h0
  have h1 := (cleanupFinalInTime 1 (tapes_inline_RawInitialMachineFinish [] [false] (encodeWord m) rev [])
    (state.1, none)).evals_in_steps
  change (MachineComposition.advance (TM2.step program))^[2]
    (some ⟨some (.cleanupFinal 1), (state.1, none),
      tapes_inline_RawInitialMachineFinish [] [false] (encodeWord m) rev []⟩) = _ at h1
  have f1 : Function.update (tapes_inline_RawInitialMachineFinish [] [false] (encodeWord m) rev []) .counter [] =
      tapes_inline_RawInitialMachineFinish [] [] (encodeWord m) rev [] := by
    funext k
    cases k <;> simp [tapes_inline_RawInitialMachineFinish]
  change (MachineComposition.advance (TM2.step program))^[2]
    (some ⟨some (.cleanupFinal 1), (state.1, none), tapes_inline_RawInitialMachineFinish [] [false] (encodeWord m) rev []⟩) =
    some ⟨some (.cleanupFinal 2), (state.1, none),
      Function.update (tapes_inline_RawInitialMachineFinish [] [false] (encodeWord m) rev []) .counter []⟩ at h1
  rw [f1] at h1
  have h2 := (cleanupFinalInTime 2 (tapes_inline_RawInitialMachineFinish [] [] (encodeWord m) rev [])
    (state.1, none)).evals_in_steps
  change (MachineComposition.advance (TM2.step program))^[(encodeWord m).length + 1]
    (some ⟨some (.cleanupFinal 2), (state.1, none),
      tapes_inline_RawInitialMachineFinish [] [] (encodeWord m) rev []⟩) = _ at h2
  rw [encodeWord_length] at h2
  have f2 : Function.update (tapes_inline_RawInitialMachineFinish [] [] (encodeWord m) rev []) .index [] =
      tapes_inline_RawInitialMachineFinish [] [] [] rev [] := by
    funext k
    cases k <;> simp [tapes_inline_RawInitialMachineFinish]
  change (MachineComposition.advance (TM2.step program))^[m + 2]
    (some ⟨some (.cleanupFinal 2), (state.1, none), tapes_inline_RawInitialMachineFinish [] [] (encodeWord m) rev []⟩) =
    some ⟨some .reset, (state.1, none),
      Function.update (tapes_inline_RawInitialMachineFinish [] [] (encodeWord m) rev []) .index []⟩ at h2
  rw [f2] at h2
  have total := trace_trans_inline_RawInitialMachineFinish _ (trace_trans_inline_RawInitialMachineFinish _ h0 h1) h2
  simpa only [show (n + 2) + 2 + (m + 2) = n + m + 6 by omega] using total

private theorem resetReverseTrace_inline_RawInitialMachineFinish (rev : List Bool) (state : State) :
    (MachineComposition.advance (TM2.step program))^[rev.length + 2]
      (some ⟨some .reset, state, tapes_inline_RawInitialMachineFinish [] [] [] rev []⟩) =
      some (haltList machine rev.reverse) := by
  have reset : (MachineComposition.advance (TM2.step program))^[1]
      (some ⟨some .reset, state, tapes_inline_RawInitialMachineFinish [] [] [] rev []⟩) =
      some ⟨some .finalReverse, initialState, tapes_inline_RawInitialMachineFinish [] [] [] rev []⟩ := rfl
  have transfer := (Reduction.MachineTransfer.transferAtInTime
    .reversed .output (by decide) id false .finalReverse none program rfl
    (tapes_inline_RawInitialMachineFinish [] [] [] rev []) (false, false, false) none).evals_in_steps
  change (MachineComposition.advance (TM2.step program))^[rev.length + 1]
    (some ⟨some .finalReverse, initialState, tapes_inline_RawInitialMachineFinish [] [] [] rev []⟩) = _ at transfer
  have frame : Reduction.MachineTransfer.tapesAt .reversed .output
      (tapes_inline_RawInitialMachineFinish [] [] [] rev []) [] (rev.reverse.map id ++ []) =
      (haltList machine rev.reverse).stk := by
    funext k
    change Tape at k
    cases k <;> simp [Reduction.MachineTransfer.tapesAt, tapes_inline_RawInitialMachineFinish, haltList, machine]
    rfl
  change (MachineComposition.advance (TM2.step program))^[rev.length + 1]
    (some ⟨some .finalReverse, initialState, tapes_inline_RawInitialMachineFinish [] [] [] rev []⟩) =
    some ⟨none, initialState, Reduction.MachineTransfer.tapesAt .reversed .output
      (tapes_inline_RawInitialMachineFinish [] [] [] rev []) [] (rev.reverse.map id ++ [])⟩ at transfer
  rw [frame] at transfer
  have total := trace_trans_inline_RawInitialMachineFinish _ reset transfer
  rw [show 1 + (rev.length + 1) = rev.length + 2 by omega] at total
  change (MachineComposition.advance (TM2.step program))^[rev.length + 2]
    (some ⟨some .reset, state, tapes_inline_RawInitialMachineFinish [] [] [] rev []⟩) =
    some ⟨none, initialState, (haltList machine rev.reverse).stk⟩
  exact total

private theorem update_finish_inline_RawInitialMachineFinish (n m : Nat) (rev word : List Bool) :
    Function.update (finishTapes n m rev) .reversed word = finishTapes n m word :=
  update_reversed_inline_RawInitialMachineFinish _ _ _ _ _ _

private theorem copyFinishTrace_inline_RawInitialMachineFinish (n m r : Nat) (rev : List Bool) (phase : CopyPhase)
    (hsource : finishTapes n m rev (copySource phase) = encodeWord r) (state : State) :
    (MachineComposition.advance (TM2.step program))^[2 * r + 2]
      (some ⟨some (.scan phase), state, finishTapes n m rev⟩) =
      some ⟨some (copyNext phase), (state.1, none),
        finishTapes n m (List.replicate (copyScale phase * r) true ++ rev)⟩ := by
  have h := (copyInTime phase (finishTapes n m rev) r []
    (by simpa only [List.append_nil] using hsource) rfl state).evals_in_steps
  change (MachineComposition.advance (TM2.step program))^[2 * r + 2]
    (some ⟨some (.scan phase), state, finishTapes n m rev⟩) =
    some ⟨some (copyNext phase), (state.1, none),
      Function.update (finishTapes n m rev) .reversed
        (List.replicate (copyScale phase * r) true ++ rev)⟩ at h
  rw [update_finish_inline_RawInitialMachineFinish] at h
  exact h

private theorem closeDummyTailTrace_inline_RawInitialMachineFinish (n m : Nat) (rev : List Bool) (state : State) :
    (MachineComposition.advance (TM2.step program))^[1]
      (some ⟨some .closeDummyTail, state, finishTapes n m rev⟩) =
      some ⟨some (.scan .dummyReverse), state, finishTapes n m (false :: rev)⟩ := by
  change some (TM2.stepAux (program .closeDummyTail) state (finishTapes n m rev)) = _
  simp only [program, TM2.stepAux]
  congr 2
  exact update_finish_inline_RawInitialMachineFinish _ _ _ _

private theorem closeDummyReverseTrace_inline_RawInitialMachineFinish (n m : Nat) (rev : List Bool) (state : State) :
    (MachineComposition.advance (TM2.step program))^[1]
      (some ⟨some .closeDummyReverse, state, finishTapes n m rev⟩) =
      some ⟨some .dummyRelation, state, finishTapes n m (false :: rev)⟩ := by
  change some (TM2.stepAux (program .closeDummyReverse) state (finishTapes n m rev)) = _
  simp only [program, TM2.stepAux]
  congr 2
  exact update_finish_inline_RawInitialMachineFinish _ _ _ _

private theorem dummyRelationTrace_inline_RawInitialMachineFinish (n m : Nat) (rev : List Bool) (state : State) :
    (MachineComposition.advance (TM2.step program))^[1]
      (some ⟨some .dummyRelation, state, finishTapes n m rev⟩) =
      some ⟨some (.cleanupFinal 0), state,
        finishTapes n m ((encodeWords (List.replicate 4096 1)).reverse ++ rev)⟩ := by
  change some (TM2.stepAux (program .dummyRelation) state (finishTapes n m rev)) = _
  rw [program, Reduction.MachineSubstitution.stepAux_pushWord, trueRelationWords]
  simp only [TM2.stepAux]
  congr 2
  exact update_finish_inline_RawInitialMachineFinish _ _ _ _

theorem dummyTrace (n m : Nat) (rev : List Bool) (state : State) :
    (MachineComposition.advance (TM2.step program))^[2 * n + 4 * m + 9]
      (some ⟨some (.scan .dummyVariables), state, finishTapes n m rev⟩) =
      some ⟨some (.cleanupFinal 0), (state.1, none),
        finishTapes n m ((encodeWords (RawInitialRows.dummyWords n m)).reverse ++ rev)⟩ := by
  let a := List.replicate n true ++ rev
  let b := List.replicate m true ++ a
  let c := false :: b
  let d := List.replicate (6 * m) true ++ c
  let e := false :: d
  have h0 := copyFinishTrace_inline_RawInitialMachineFinish n m n rev .dummyVariables rfl state
  simp only [copyScale, copyNext, Nat.one_mul] at h0
  have h1 := copyFinishTrace_inline_RawInitialMachineFinish n m m a .dummyIndex rfl (state.1, none)
  simp only [copyScale, copyNext, Nat.one_mul] at h1
  have h2 := closeDummyTailTrace_inline_RawInitialMachineFinish n m b (state.1, none)
  have h3 := copyFinishTrace_inline_RawInitialMachineFinish n m m c .dummyReverse rfl (state.1, none)
  simp only [copyScale, copyNext] at h3
  have h4 := closeDummyReverseTrace_inline_RawInitialMachineFinish n m d (state.1, none)
  have h5 := dummyRelationTrace_inline_RawInitialMachineFinish n m e (state.1, none)
  have total := trace_trans_inline_RawInitialMachineFinish _ (trace_trans_inline_RawInitialMachineFinish _ (trace_trans_inline_RawInitialMachineFinish _
    (trace_trans_inline_RawInitialMachineFinish _ (trace_trans_inline_RawInitialMachineFinish _ h0 h1) h2) h3) h4) h5
  have output : (encodeWords (List.replicate 4096 1)).reverse ++ e =
      (encodeWords (RawInitialRows.dummyWords n m)).reverse ++ rev := by
    have rep : List.replicate m true ++ (List.replicate n true ++ rev) =
        List.replicate (n + m) true ++ rev := by
      rw [← List.append_assoc, ← List.replicate_add, Nat.add_comm m n]
    simp only [RawInitialRows.dummyWords, encodeWords_append, encodeWords,
      List.append_nil, List.reverse_append,
      encodeWord, List.reverse_cons,
      List.reverse_replicate, List.append_assoc, List.singleton_append,
      a, b, c, d, e]
    rw [rep]
    simp only [List.reverse_nil, List.nil_append, List.cons_append]
  rw [output] at total
  simpa only [show (((((2 * n + 2) + (2 * m + 2)) + 1) + (2 * m + 2)) + 1) + 1 =
    2 * n + 4 * m + 9 by omega] using total

theorem finishTrace (n m : Nat) (rev : List Bool) (state : State) :
    (MachineComposition.advance (TM2.step program))^[
        3 * n + 5 * m + 17 + (encodeWords (RawInitialRows.dummyWords n m)).length + rev.length]
      (some ⟨some (.scan .dummyVariables), state, finishTapes n m rev⟩) =
      some (haltList machine (rev.reverse ++ encodeWords (RawInitialRows.dummyWords n m))) := by
  let emitted := (encodeWords (RawInitialRows.dummyWords n m)).reverse ++ rev
  have total := trace_trans_inline_RawInitialMachineFinish _ (trace_trans_inline_RawInitialMachineFinish _ (dummyTrace n m rev state)
    (cleanupTrace_inline_RawInitialMachineFinish n m emitted (state.1, none)))
    (resetReverseTrace_inline_RawInitialMachineFinish emitted (state.1, none))
  have hout : emitted.reverse = rev.reverse ++ encodeWords (RawInitialRows.dummyWords n m) := by
    simp only [emitted, List.reverse_append, List.reverse_reverse]
  rw [hout] at total
  have htime : (2 * n + 4 * m + 9) + (n + m + 6) + (emitted.length + 2) =
      3 * n + 5 * m + 17 + (encodeWords (RawInitialRows.dummyWords n m)).length + rev.length := by
    simp only [emitted, List.length_append, List.length_reverse]
    omega
  rwa [htime] at total

def finishInTime (n m : Nat) (rev : List Bool) (state : State) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (.scan .dummyVariables), state, finishTapes n m rev⟩
      (some (haltList machine (rev.reverse ++ encodeWords (RawInitialRows.dummyWords n m))))
      (4 * n + 12 * m + 8211 + rev.length) where
  steps := 4 * n + 12 * m + 8211 + rev.length
  evals_in_steps := by
    have h := finishTrace n m rev state
    rw [dummyBits_length] at h
    rw [show 3 * n + 5 * m + 17 + (n + 7 * m + 8194) + rev.length =
      4 * n + 12 * m + 8211 + rev.length by omega] at h
    exact h
  steps_le_m := Nat.le_refl _

end DFVSGames.Foundations.PCP.RawInitialMachineFinish
end

section

namespace DFVSGames.Foundations.PCP.RawInitialMachineLoop

open Turing Target Complexity RawInitialMachineModel RawInitialMachineLoopData
open RawInitialMachineBudget RawInitialMachineBody RawInitialMachineFinish

def finalSigns {n : Nat} (incoming : RawInitialMachineModel.Signs) :
    List (Clause n) → RawInitialMachineModel.Signs
  | [] => incoming
  | c :: cs => finalSigns (RawInitialRows.clauseSigns c) cs

private theorem trace_trans_inline_RawInitialMachineLoop {α : Type*} (f : α → α) {a b : Nat} {x y z : α}
    (first : f^[a] x = y) (second : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

theorem empty_loopTapes (n i : Nat) (rev : List Bool) :
    loopTapes n i 0 [] rev = finishTapes n i rev := by
  funext tape
  cases tape <;> rfl

theorem loopTrace {n : Nat} (i : Nat) (cs : List (Clause n))
    (rev : List Bool) (state : State) :
    (MachineComposition.advance (TM2.step program))^[loopTime i cs]
      (some ⟨some .guard, state, loopTapes n i cs.length (clauseInput cs) rev⟩) =
      some ⟨some (.scan .dummyVariables), (finalSigns state.1 cs, none),
        finishTapes n (i + cs.length) ((encodeWords (clauseOutput n i cs)).reverse ++ rev)⟩ := by
  induction cs generalizing i rev state with
  | nil =>
      have h := RawInitialMachineBody.guardTrace_zero n i [] rev state
      rw [empty_loopTapes] at h
      simpa only [loopTime, List.length_nil, clauseInput_nil, clauseOutput_nil,
        finalSigns, encodeWords, List.reverse_nil, List.nil_append, Nat.add_zero,
        empty_loopTapes] using h
  | cons c cs ih =>
      have first := bodyTrace i cs.length c (clauseInput cs) rev state
      have rest := ih (i + 1)
        ((encodeWords (RawInitialRows.clauseWords n i
          (RawInitialRows.clauseNames c) (RawInitialRows.clauseSigns c))).reverse ++ rev)
        (RawInitialRows.clauseSigns c, none)
      have total := trace_trans_inline_RawInitialMachineLoop _ first rest
      have hi : i + 1 + cs.length = i + (cs.length + 1) := by omega
      simpa only [loopTime, List.length_cons, clauseInput_cons, clauseOutput_cons,
        encodeWords_append, List.reverse_append, List.append_assoc, finalSigns, hi] using total

def loopInTime {n : Nat} (i : Nat) (cs : List (Clause n))
    (rev : List Bool) (state : State) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some .guard, state, loopTapes n i cs.length (clauseInput cs) rev⟩
      (some ⟨some (.scan .dummyVariables), (finalSigns state.1 cs, none),
        finishTapes n (i + cs.length) ((encodeWords (clauseOutput n i cs)).reverse ++ rev)⟩)
      (loopTime i cs) where
  steps := loopTime i cs
  evals_in_steps := loopTrace i cs rev state
  steps_le_m := Nat.le_refl _

end DFVSGames.Foundations.PCP.RawInitialMachineLoop
end

section

namespace DFVSGames.Foundations.PCP.MachineRawInitialTable

open Turing Target Complexity RawInitialMachineModel RawInitialMachineLoopData
open RawInitialMachineBudget RawInitialMachineLoop

private theorem trace_trans_inline_MachineRawInitialTable {α : Type*} (f : α → α) {a b : Nat} {x y z : α}
    (first : f^[a] x = y) (second : f^[b] y = z) : f^[a + b] x = z := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

def prefixBits (F : Formula) : List Bool :=
  encodeWords ([F.«variables» + F.clauses.length + 1, 6 * F.clauses.length + 1] ++
    clauseOutput F.«variables» 0 F.clauses)

theorem outputBits (F : Formula) :
    GraphTables.tableBits (RawInitialTables.table F) = prefixBits F ++
      encodeWords (RawInitialRows.dummyWords F.«variables» F.clauses.length) := by
  change encodeWords (GraphTables.tableWords (RawInitialTables.table F)) = _
  rw [tableWords_decomposition, encodeWords_append]
  rfl

theorem machineTrace (F : Formula) :
    (MachineComposition.advance (TM2.step program))^[fullBudget F]
      (some (initList machine (formulaBits F))) =
      some (haltList machine (GraphTables.tableBits (RawInitialTables.table F))) := by
  have startup := RawInitialMachineStart.formulaStartTrace F
  rw [startTapes_eq] at startup
  have loop := loopTrace 0 F.clauses
    (encodeWords [F.«variables» + F.clauses.length + 1, 6 * F.clauses.length + 1]).reverse
    initialState
  have hprefix : (encodeWords (clauseOutput F.«variables» 0 F.clauses)).reverse ++
      (encodeWords [F.«variables» + F.clauses.length + 1, 6 * F.clauses.length + 1]).reverse =
      (prefixBits F).reverse := by
    simp only [prefixBits, encodeWords_append, List.reverse_append]
  rw [hprefix, Nat.zero_add] at loop
  have finish := RawInitialMachineFinish.finishTrace F.«variables» F.clauses.length
    (prefixBits F).reverse (finalSigns initialState.1 F.clauses, none)
  rw [List.reverse_reverse, ← outputBits F] at finish
  have total := trace_trans_inline_MachineRawInitialTable _ (trace_trans_inline_MachineRawInitialTable _ startup loop) finish
  have time : (3 * F.«variables» + 5 * F.clauses.length + 13 + loopTime 0 F.clauses) +
      (3 * F.«variables» + 5 * F.clauses.length + 17 +
        (encodeWords (RawInitialRows.dummyWords F.«variables» F.clauses.length)).length +
        (prefixBits F).reverse.length) = fullBudget F := by
    rw [fullBudget, outputBits, List.length_append, List.length_reverse]
    omega
  simpa only [time] using total

def outputsInTime (F : Formula) :
    TM2OutputsInTime machine (formulaBits F)
      (some (GraphTables.tableBits (RawInitialTables.table F)))
      (timePolynomial.eval (formulaBits F).length) where
  steps := fullBudget F
  evals_in_steps := machineTrace F
  steps_le_m := fullBudget_le F

noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime formulaEncoding.encode GraphTables.encoding.encode
      RawInitialTables.table where
  tm := machine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := timePolynomial
  outputsFun F := by
    change TM2OutputsInTime machine ((formulaBits F).map id)
      (some ((GraphTables.tableBits (RawInitialTables.table F)).map id))
      (timePolynomial.eval (formulaBits F).length)
    have hi := @List.map_id (machine.Γ machine.k₀) (formulaBits F)
    have ho := @List.map_id (machine.Γ machine.k₁)
      (GraphTables.tableBits (RawInitialTables.table F))
    rw [hi, ho]
    exact outputsInTime F

end DFVSGames.Foundations.PCP.MachineRawInitialTable

end

section

namespace DFVSGames.Foundations.Complexity.FinalCNFMachine

open Turing
open PCP

abbrev Buffer (N : Nat) := MachineFixedBlockMap.Buffer N

section RelationReader

variable {K Λ σ : Type} {N : Nat}

def readUnarySlots (source : K) : List (Fin N) →
    TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N) →
    TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N)
  | [], next => next
  | i :: slots, next =>
      .pop source (fun state head =>
        (state.1, Function.update state.2 i (head.getD false)))
        (.branch (fun state => state.2 i)
          (.pop source (fun state _ => state) (readUnarySlots source slots next))
          (readUnarySlots source slots next))

def unaryBits (slots : List (Fin N)) (bits : Buffer N) : List Bool :=
  slots.flatMap fun i => encodeWord (GraphTables.bitWord (bits i))

theorem unaryBits_eq_encodeWords (slots : List (Fin N)) (bits : Buffer N) :
    unaryBits slots bits = encodeWords (slots.map fun i => GraphTables.bitWord (bits i)) := by
  induction slots with
  | nil => rfl
  | cons i slots ih => simpa only [unaryBits, List.flatMap_cons, List.map_cons,
      encodeWords] using congrArg (encodeWord (GraphTables.bitWord (bits i)) ++ ·) ih

theorem unaryBits_length_le (slots : List (Fin N)) (bits : Buffer N) :
    (unaryBits slots bits).length ≤ 2 * slots.length := by
  induction slots with
  | nil => simp [unaryBits]
  | cons i slots ih =>
      have hi : (encodeWord (GraphTables.bitWord (bits i))).length ≤ 2 := by
        cases bits i <;> simp [GraphTables.bitWord, encodeWord_length]
      simp only [unaryBits, List.flatMap_cons, List.length_append, List.length_cons] at *
      omega

theorem statementPushBound_readUnarySlots (source : K) (slots : List (Fin N))
    (next : TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N)) :
    Runtime.statementPushBound (readUnarySlots source slots next) =
      Runtime.statementPushBound next := by
  induction slots with
  | nil => rfl
  | cons i slots ih =>
      simp only [readUnarySlots, Runtime.statementPushBound, ih, max_self]

variable [DecidableEq K]

theorem stepAux_readUnarySlots (source : K) (slots : List (Fin N))
    (next : TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N))
    (ambient : σ) (bits buffer : Buffer N) (tapes : K → List Bool)
    (suffix : List Bool) :
    TM2.stepAux (readUnarySlots source slots next) (ambient, buffer)
        (Function.update tapes source (unaryBits slots bits ++ suffix)) =
      TM2.stepAux next (ambient, MachineFixedBlockMap.fill slots bits buffer)
        (Function.update tapes source suffix) := by
  induction slots generalizing buffer tapes with
  | nil => simp [readUnarySlots, unaryBits, MachineFixedBlockMap.fill]
  | cons i slots ih =>
      cases hi : bits i <;>
        simp only [readUnarySlots, unaryBits, List.flatMap_cons, hi,
          GraphTables.bitWord, Bool.false_eq_true, ite_false, ite_true, encodeWord,
          List.replicate_zero, List.replicate_succ, List.nil_append,
          List.cons_append,
          TM2.stepAux, Function.update_self, List.head?_cons, Option.getD_some,
          List.tail_cons, Function.update_idem, MachineFixedBlockMap.fill,
          List.foldl_cons]
      · simpa [unaryBits, MachineFixedBlockMap.fill, hi, encodeWord, GraphTables.bitWord] using
          ih (Function.update buffer i false) tapes
      · simpa [unaryBits, MachineFixedBlockMap.fill, hi, encodeWord, GraphTables.bitWord] using
          ih (Function.update buffer i true) tapes

theorem stepAux_readUnaryAll (source : K)
    (next : TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N))
    (state : σ × Buffer N) (bits : Buffer N) (tapes : K → List Bool)
    (suffix : List Bool)
    (hinput : tapes source = unaryBits (List.ofFn id) bits ++ suffix) :
    TM2.stepAux (readUnarySlots source (List.ofFn id) next) state tapes =
      TM2.stepAux next (state.1, bits) (Function.update tapes source suffix) := by
  have h := stepAux_readUnarySlots source (List.ofFn id) next state.1 bits state.2 tapes suffix
  have hin : Function.update tapes source (unaryBits (List.ofFn id) bits ++ suffix) = tapes := by
    simpa only [← hinput] using Function.update_eq_self source tapes
  rw [hin, MachineFixedBlockMap.fill_all] at h
  exact h

def unaryBlockMapAt {M : Nat} (source destination : K) (F : Buffer N → Buffer M)
    (exit : Option Λ) : TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N) :=
  readUnarySlots source (List.ofFn id)
    (MachineFixedBlockMap.writeSlots destination (fun state => F state.2)
      (List.ofFn id).reverse
      (.load (fun state => (state.1, MachineFixedBlockMap.emptyBuffer N))
        (MachineFixedBlockMap.finishAt exit)))

theorem stepAux_unaryBlockMapAt {M : Nat} (source destination : K)
    (F : Buffer N → Buffer M) (exit : Option Λ) (hne : source ≠ destination)
    (state : σ × Buffer N) (bits : Buffer N) (tapes : K → List Bool) (suffix : List Bool)
    (hinput : tapes source = unaryBits (List.ofFn id) bits ++ suffix) :
    TM2.stepAux (unaryBlockMapAt source destination F exit) state tapes =
      { l := exit, var := (state.1, MachineFixedBlockMap.emptyBuffer N),
        stk := Function.update (Function.update tapes source suffix) destination
          (List.ofFn (F bits) ++ tapes destination) } := by
  unfold unaryBlockMapAt
  rw [stepAux_readUnaryAll source _ state bits tapes suffix hinput,
    MachineFixedBlockMap.stepAux_writeSlots]
  simp only [List.map_reverse, List.map_ofFn, Function.comp_id, List.reverse_reverse,
    Function.update_of_ne (Ne.symm hne), TM2.stepAux]
  cases exit <;> rfl

theorem step_unaryBlockMapAt {M : Nat} (source destination : K)
    (F : Buffer N → Buffer M) (exit : Option Λ) (hne : source ≠ destination)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N))
    (label : Λ) (atLabel : program label = unaryBlockMapAt source destination F exit)
    (state : σ × Buffer N) (bits : Buffer N) (tapes : K → List Bool) (suffix : List Bool)
    (hinput : tapes source = unaryBits (List.ofFn id) bits ++ suffix) :
    TM2.step program ⟨some label, state, tapes⟩ =
      some ⟨exit, (state.1, MachineFixedBlockMap.emptyBuffer N),
        Function.update (Function.update tapes source suffix) destination
          (List.ofFn (F bits) ++ tapes destination)⟩ := by
  simp only [TM2.step, atLabel,
    stepAux_unaryBlockMapAt source destination F exit hne state bits tapes suffix hinput]

def unaryBlockInTime {M : Nat} (source destination : K)
    (F : Buffer N → Buffer M) (exit : Option Λ) (hne : source ≠ destination)
    (program : Λ → TM2.Stmt (fun _ : K => Bool) Λ (σ × Buffer N))
    (label : Λ) (atLabel : program label = unaryBlockMapAt source destination F exit)
    (state : σ × Buffer N) (bits : Buffer N) (tapes : K → List Bool) (suffix : List Bool)
    (hinput : tapes source = unaryBits (List.ofFn id) bits ++ suffix) :
    StateTransition.EvalsToInTime (TM2.step program) ⟨some label, state, tapes⟩
      (some ⟨exit, (state.1, MachineFixedBlockMap.emptyBuffer N),
        Function.update (Function.update tapes source suffix) destination
          (List.ofFn (F bits) ++ tapes destination)⟩) 1 where
  steps := 1
  evals_in_steps := step_unaryBlockMapAt source destination F exit hne program label
    atLabel state bits tapes suffix hinput
  steps_le_m := Nat.le_refl _

end RelationReader

theorem unaryBits_relation (relation : GraphTables.RelationTable) :
    unaryBits (List.ofFn id) (fun i => relation[i]) =
      encodeWords (GraphTables.relationWords relation) := by
  have h : List.ofFn (fun i : Fin 4096 => relation[i]) = relation.toList := by
    change List.ofFn (fun i : Fin 4096 => relation[i.val]) = relation.toList
    rw [← Vector.toList_ofFn, Vector.ofFn_getElem]
  rw [unaryBits_eq_encodeWords]
  unfold GraphTables.relationWords
  rw [← h]
  simp only [List.map_ofFn, Function.comp_def, id_eq]

def readerStateEquiv (σ : Type) (N : Nat) :
    (((σ × Unit) × Option Bool) × Buffer N) ≃ (((σ × Buffer N) × Unit) × Option Bool) where
  toFun state := (((state.1.1.1, state.2), state.1.1.2), state.1.2)
  invFun state := (((state.1.1.1, state.1.2), state.2), state.1.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

section AmbientRelation

variable {K Λ σ : Type} [DecidableEq K]

abbrev State (σ : Type) := ((σ × Buffer 4096) × Unit) × Option Bool

def readRelationAt (source : K) (exit : Λ) :
    TM2.Stmt (fun _ : K => Bool) Λ (State σ) :=
  MachineControl.statement id (readerStateEquiv σ 4096)
    (readUnarySlots source (List.ofFn id) (.goto fun _ => exit))

theorem stepAux_readRelationAt (source : K) (exit : Λ) (ambient : σ)
    (buffer : Buffer 4096) (unitState : Unit) (register : Option Bool)
    (relation : GraphTables.RelationTable) (tapes : K → List Bool) (suffix : List Bool)
    (hinput : tapes source = encodeWords (GraphTables.relationWords relation) ++ suffix) :
    TM2.stepAux (readRelationAt source exit) (((ambient, buffer), unitState), register) tapes =
      ⟨some exit, (((ambient, fun i => relation[i]), unitState), register),
        Function.update tapes source suffix⟩ := by
  change TM2.stepAux (MachineControl.statement id (readerStateEquiv σ 4096)
    (readUnarySlots source (List.ofFn id) (.goto fun _ => exit)))
    ((readerStateEquiv σ 4096) (((ambient, unitState), register), buffer)) tapes = _
  rw [MachineControl.stepAux_simulation]
  rw [stepAux_readUnaryAll source _ _ (fun i => relation[i]) tapes suffix
    (by simpa only [unaryBits_relation] using hinput)]
  rfl

end AmbientRelation

namespace Program

open PCP.AlphabetTable

inductive Tape
  | input | output | accumulator | scratch | vertices | darts | tail | head | rowIndex
  | archive | reverseIndex | scanWork | indexWork
  deriving DecidableEq

instance : Fintype Tape := derive_fintype% Tape

abbrev Ambient := Unit × Buffer 4096
abbrev Plan := List (Emitter.Command 5 Ambient 36864)

def values (vertices darts tail head row : Nat) : Fin 5 → Nat :=
  Fin.cases vertices (Fin.cases darts (Fin.cases tail (Fin.cases head (fun _ => row))))

def headerPlan : Plan :=
  Emitter.affineCommands [(0, 6), (1, 36864)] (fun _ => 0) ++
    Emitter.affineCommands [(1, 40960)] (fun _ => 0)

theorem headerPlan_length : headerPlan.length = 7 := by
  simp [headerPlan]

theorem headerPlan_bits (vertices darts tail head row : Nat) (ambient : Ambient) :
    headerPlan.flatMap (Emitter.commandBits (values vertices darts tail head row) ambient) =
      encodeWords [6 * vertices + 36864 * darts, 40960 * darts] := by
  rw [headerPlan, List.flatMap_append, Emitter.affineCommands_bits,
    Emitter.affineCommands_bits]
  simp [Emitter.affineValue, values, encodeWords]
  rfl

def source : Fin 5 → Tape :=
  Fin.cases .vertices (Fin.cases .darts (Fin.cases .tail (Fin.cases .head (fun _ => .rowIndex))))

inductive Label (headerCount rowCount : Nat)
  | copyFirst | copySecond | startVertices | readVertices | startDarts | readDarts | seedIndex
  | header (label : Emitter.Label headerCount 36864)
  | headerClearTail | headerClearHead
  | guard | startTail | readTail | startReverse | readReverse
  | headTableFirst | headTableSecond | headIndexFirst | headIndexSecond
  | headHeaderVertices | headHeaderDarts | headLookup (label : Lookup.Label)
  | readRelation
  | row (label : Emitter.Label rowCount 36864)
  | clearTail | clearHead | clearReverse | nextRow | reverseOutput
  deriving DecidableEq, Fintype

def guard {hc rc : Nat} (again finish : Label hc rc) :
    TM2.Stmt (fun _ : Tape => Bool) (Label hc rc) (State Unit) :=
  .peek .input (fun state head => (state.1, head))
    (.branch (fun state => state.2.isSome)
      (.load (fun state => (state.1, none)) (.goto fun _ => again))
      (.load (fun state => (state.1, none)) (.goto fun _ => finish)))

def program (headerPlan rowPlan : Plan) :
    Label headerPlan.length rowPlan.length →
      TM2.Stmt (fun _ : Tape => Bool) (Label headerPlan.length rowPlan.length) (State Unit)
  | .copyFirst => Reduction.MachineTransfer.loopAt .input .scratch id false .copyFirst
      (some .copySecond)
  | .copySecond => MachineCopy.forkLoop .scratch .input .archive false .copySecond
      (some .startVertices)
  | .startVertices => Hastad.SourceMachine.fieldStart .vertices .readVertices
  | .readVertices => Hastad.SourceMachine.fieldLoop .input .vertices .readVertices (some .startDarts)
  | .startDarts => Hastad.SourceMachine.fieldStart .darts .readDarts
  | .readDarts => Hastad.SourceMachine.fieldLoop .input .darts .readDarts (some .seedIndex)
  | .seedIndex => .push .rowIndex (fun _ => false)
      (.push .tail (fun _ => false) (.push .head (fun _ => false)
        (.goto fun _ => .header (Emitter.labelAt headerPlan.length 36864 0 .entry))))
  | .header label => Emitter.statement (Emitter.listCommands headerPlan)
      source .scratch .accumulator Label.header (some .headerClearTail) label
  | .headerClearTail => MachineLookup.discard .tail .headerClearTail .headerClearHead
  | .headerClearHead => MachineLookup.discard .head .headerClearHead .guard
  | .guard => guard .startTail .reverseOutput
  | .startTail => Hastad.SourceMachine.fieldStart .tail .readTail
  | .readTail => Hastad.SourceMachine.fieldLoop .input .tail .readTail (some .startReverse)
  | .startReverse => Hastad.SourceMachine.fieldStart .reverseIndex .readReverse
  | .readReverse => Hastad.SourceMachine.fieldLoop .input .reverseIndex .readReverse
      (some .headTableFirst)
  | .headTableFirst => Reduction.MachineTransfer.loopAt .archive .scratch id false
      .headTableFirst (some .headTableSecond)
  | .headTableSecond => MachineCopy.forkLoop .scratch .archive .scanWork false
      .headTableSecond (some .headIndexFirst)
  | .headIndexFirst => Reduction.MachineTransfer.loopAt .reverseIndex .scratch id false
      .headIndexFirst (some .headIndexSecond)
  | .headIndexSecond => MachineCopy.forkLoop .scratch .reverseIndex .indexWork false
      .headIndexSecond (some .headHeaderVertices)
  | .headHeaderVertices => MachineLookup.discard .scanWork .headHeaderVertices .headHeaderDarts
  | .headHeaderDarts => MachineLookup.discard .scanWork .headHeaderDarts (.headLookup .guard)
  | .headLookup label => Lookup.statement 64 .indexWork .scanWork .head Label.headLookup
      (some .readRelation) label
  | .readRelation => readRelationAt .input
      (.row (Emitter.labelAt rowPlan.length 36864 0 .entry))
  | .row label => Emitter.statement (Emitter.listCommands rowPlan)
      source .scratch .accumulator Label.row (some .clearTail) label
  | .clearTail => MachineLookup.discard .tail .clearTail .clearHead
  | .clearHead => MachineLookup.discard .head .clearHead .clearReverse
  | .clearReverse => MachineLookup.discard .reverseIndex .clearReverse .nextRow
  | .nextRow => .push .rowIndex (fun _ => true) (.goto fun _ => .guard)
  | .reverseOutput => Reduction.MachineTransfer.loopAt .accumulator .output id false
      .reverseOutput none

def machine (headerPlan rowPlan : Plan) : FinTM2 where
  K := Tape
  k₀ := .input
  k₁ := .output
  Γ _ := Bool
  Λ := Label headerPlan.length rowPlan.length
  main := .copyFirst
  σ := State Unit
  initialState := ((((), fun _ => false), ()), none)
  m := program headerPlan rowPlan

def headRoles : Fin 6 → Tape :=
  Fin.cases .archive (Fin.cases .reverseIndex (Fin.cases .scanWork
    (Fin.cases .indexWork (Fin.cases .head (fun _ => .scratch)))))

theorem headRoles_injective : Function.Injective headRoles := by
  decide

def headPhaseInTime (headerPlan rowPlan : Plan) (base : Tape → List Bool)
    (table : GenericGraphTables.Table 64) (e : Fin table.darts)
    (hTable : base .archive = GenericGraphTables.tableBits table)
    (hReverse : base .reverseIndex = encodeWord (Lookup.headIndex table e).val)
    (hHead : base .head = []) (hScratch : base .scratch = []) (ambient : Ambient) :
    StateTransition.EvalsToInTime (TM2.step (program headerPlan rowPlan))
      ⟨some .headTableFirst, ((ambient, ()), none), base⟩
      (some ⟨some .readRelation, ((ambient, ()), none),
        Lookup.headLookupTapes headRoles base table e⟩)
      (Lookup.headTimePolynomial.eval (GenericGraphTables.tableBits table).length) :=
  Lookup.headLookupInTime headRoles headRoles_injective
    .headTableFirst .headTableSecond .headIndexFirst .headIndexSecond
    .headHeaderVertices .headHeaderDarts Label.headLookup (some .readRelation)
    (program headerPlan rowPlan) rfl rfl rfl rfl rfl rfl (fun _ => rfl)
    base table e hTable hReverse hHead hScratch (ambient, ()) none

def workingTapes (vertices darts row : Nat) (input tail head accumulator : List Bool) :
    Tape → List Bool
  | .input => input
  | .output => []
  | .accumulator => accumulator
  | .scratch => []
  | .vertices => encodeWord vertices
  | .darts => encodeWord darts
  | .tail => tail
  | .head => head
  | .rowIndex => encodeWord row
  | .archive | .reverseIndex | .scanWork | .indexWork => []

theorem workingTapes_operands (vertices darts row tail head : Nat)
    (input accumulator : List Bool) :
    ∀ i, workingTapes vertices darts row input (encodeWord tail) (encodeWord head)
      accumulator (source i) = encodeWord (values vertices darts tail head row i) := by
  intro i
  fin_cases i <;> rfl

theorem update_working_input (vertices darts row : Nat)
    (input tail head accumulator replacement : List Bool) :
    Function.update (workingTapes vertices darts row input tail head accumulator) Tape.input
      replacement = workingTapes vertices darts row replacement tail head accumulator := by
  funext tape
  cases tape <;> simp [workingTapes, Function.update]

theorem update_working_tail (vertices darts row : Nat)
    (input tail head accumulator replacement : List Bool) :
    Function.update (workingTapes vertices darts row input tail head accumulator) Tape.tail
      replacement = workingTapes vertices darts row input replacement head accumulator := by
  funext tape
  cases tape <;> simp [workingTapes, Function.update]

theorem update_working_head (vertices darts row : Nat)
    (input tail head accumulator replacement : List Bool) :
    Function.update (workingTapes vertices darts row input tail head accumulator) Tape.head
      replacement = workingTapes vertices darts row input tail replacement accumulator := by
  funext tape
  cases tape <;> simp [workingTapes, Function.update]

theorem update_working_accumulator (vertices darts row : Nat)
    (input tail head accumulator replacement : List Bool) :
    Function.update (workingTapes vertices darts row input tail head accumulator) Tape.accumulator
      replacement = workingTapes vertices darts row input tail head replacement := by
  funext tape
  cases tape <;> simp [workingTapes, Function.update]

theorem update_working_rowIndex (vertices darts row : Nat)
    (input tail head accumulator : List Bool) :
    Function.update (workingTapes vertices darts row input tail head accumulator) Tape.rowIndex
      (true :: encodeWord row) =
      workingTapes vertices darts (row + 1) input tail head accumulator := by
  funext tape
  cases tape <;> simp [workingTapes, Function.update, encodeWord, List.replicate_succ]

theorem source_ne_scratch (i : Fin 5) : source i ≠ Tape.scratch := by
  fin_cases i <;> decide

theorem source_ne_accumulator (i : Fin 5) : source i ≠ Tape.accumulator := by
  fin_cases i <;> decide

end Program

end DFVSGames.Foundations.Complexity.FinalCNFMachine
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
