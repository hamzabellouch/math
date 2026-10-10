import OAI.Computability.UniqueGames.PCP.RawInitialMachinePhases
import OAI.Computability.UniqueGames.PCP.RawInitialTablesLemmas

namespace OAI

section

/-! Exact execution of the dummy-row and final cleanup/reversal phases. -/

namespace UniqueGamesTheorem.Foundations.PCP.RawInitialMachineFinish

open Turing Complexity RawInitialMachineModel RawInitialMachinePhases

private def tapes (varsWord counter index reversed output : List Bool) : Tape → List Bool
  | .variables => varsWord
  | .counter => counter
  | .index => index
  | .reversed => reversed
  | .output => output
  | _ => []

def finishTapes (n m : Nat) (rev : List Bool) : Tape → List Bool :=
  tapes (encodeWord n) [false] (encodeWord m) rev []

private theorem trace_trans {α : Type*} (f : α → α) {a b : Nat} {x y z : α}
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

private theorem update_reversed (varsWord counter index rev out word : List Bool) :
    Function.update (tapes varsWord counter index rev out) .reversed word =
      tapes varsWord counter index word out := by
  funext k
  cases k <;> simp [tapes]

private theorem cleanupTrace (n m : Nat) (rev : List Bool) (state : State) :
    (MachineComposition.advance (TM2.step program))^[n + m + 6]
      (some ⟨some (.cleanupFinal 0), state, finishTapes n m rev⟩) =
      some ⟨some .reset, (state.1, none), tapes [] [] [] rev []⟩ := by
  have h0 := (cleanupFinalInTime 0 (finishTapes n m rev) state).evals_in_steps
  change (MachineComposition.advance (TM2.step program))^[(encodeWord n).length + 1]
    (some ⟨some (.cleanupFinal 0), state, finishTapes n m rev⟩) = _ at h0
  rw [encodeWord_length] at h0
  have f0 : Function.update (finishTapes n m rev) .variables [] =
      tapes [] [false] (encodeWord m) rev [] := by
    funext k
    cases k <;> simp [finishTapes, tapes]
  change (MachineComposition.advance (TM2.step program))^[n + 2]
    (some ⟨some (.cleanupFinal 0), state, finishTapes n m rev⟩) =
    some ⟨some (.cleanupFinal 1), (state.1, none),
      Function.update (finishTapes n m rev) .variables []⟩ at h0
  rw [f0] at h0
  have h1 := (cleanupFinalInTime 1 (tapes [] [false] (encodeWord m) rev [])
    (state.1, none)).evals_in_steps
  change (MachineComposition.advance (TM2.step program))^[2]
    (some ⟨some (.cleanupFinal 1), (state.1, none),
      tapes [] [false] (encodeWord m) rev []⟩) = _ at h1
  have f1 : Function.update (tapes [] [false] (encodeWord m) rev []) .counter [] =
      tapes [] [] (encodeWord m) rev [] := by
    funext k
    cases k <;> simp [tapes]
  change (MachineComposition.advance (TM2.step program))^[2]
    (some ⟨some (.cleanupFinal 1), (state.1, none), tapes [] [false] (encodeWord m) rev []⟩) =
    some ⟨some (.cleanupFinal 2), (state.1, none),
      Function.update (tapes [] [false] (encodeWord m) rev []) .counter []⟩ at h1
  rw [f1] at h1
  have h2 := (cleanupFinalInTime 2 (tapes [] [] (encodeWord m) rev [])
    (state.1, none)).evals_in_steps
  change (MachineComposition.advance (TM2.step program))^[(encodeWord m).length + 1]
    (some ⟨some (.cleanupFinal 2), (state.1, none),
      tapes [] [] (encodeWord m) rev []⟩) = _ at h2
  rw [encodeWord_length] at h2
  have f2 : Function.update (tapes [] [] (encodeWord m) rev []) .index [] =
      tapes [] [] [] rev [] := by
    funext k
    cases k <;> simp [tapes]
  change (MachineComposition.advance (TM2.step program))^[m + 2]
    (some ⟨some (.cleanupFinal 2), (state.1, none), tapes [] [] (encodeWord m) rev []⟩) =
    some ⟨some .reset, (state.1, none),
      Function.update (tapes [] [] (encodeWord m) rev []) .index []⟩ at h2
  rw [f2] at h2
  have total := trace_trans _ (trace_trans _ h0 h1) h2
  simpa only [show (n + 2) + 2 + (m + 2) = n + m + 6 by omega] using total

private theorem resetReverseTrace (rev : List Bool) (state : State) :
    (MachineComposition.advance (TM2.step program))^[rev.length + 2]
      (some ⟨some .reset, state, tapes [] [] [] rev []⟩) =
      some (haltList machine rev.reverse) := by
  have reset : (MachineComposition.advance (TM2.step program))^[1]
      (some ⟨some .reset, state, tapes [] [] [] rev []⟩) =
      some ⟨some .finalReverse, initialState, tapes [] [] [] rev []⟩ := rfl
  have transfer := (Reduction.MachineTransfer.transferAtInTime
    .reversed .output (by decide) id false .finalReverse none program rfl
    (tapes [] [] [] rev []) (false, false, false) none).evals_in_steps
  change (MachineComposition.advance (TM2.step program))^[rev.length + 1]
    (some ⟨some .finalReverse, initialState, tapes [] [] [] rev []⟩) = _ at transfer
  have frame : Reduction.MachineTransfer.tapesAt .reversed .output
      (tapes [] [] [] rev []) [] (rev.reverse.map id ++ []) =
      (haltList machine rev.reverse).stk := by
    funext k
    change Tape at k
    cases k <;> simp [Reduction.MachineTransfer.tapesAt, tapes, haltList, machine]
    rfl
  change (MachineComposition.advance (TM2.step program))^[rev.length + 1]
    (some ⟨some .finalReverse, initialState, tapes [] [] [] rev []⟩) =
    some ⟨none, initialState, Reduction.MachineTransfer.tapesAt .reversed .output
      (tapes [] [] [] rev []) [] (rev.reverse.map id ++ [])⟩ at transfer
  rw [frame] at transfer
  have total := trace_trans _ reset transfer
  rw [show 1 + (rev.length + 1) = rev.length + 2 by omega] at total
  change (MachineComposition.advance (TM2.step program))^[rev.length + 2]
    (some ⟨some .reset, state, tapes [] [] [] rev []⟩) =
    some ⟨none, initialState, (haltList machine rev.reverse).stk⟩
  exact total

private theorem update_finish (n m : Nat) (rev word : List Bool) :
    Function.update (finishTapes n m rev) .reversed word = finishTapes n m word :=
  update_reversed _ _ _ _ _ _

private theorem copyFinishTrace (n m r : Nat) (rev : List Bool) (phase : CopyPhase)
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
  rw [update_finish] at h
  exact h

private theorem closeDummyTailTrace (n m : Nat) (rev : List Bool) (state : State) :
    (MachineComposition.advance (TM2.step program))^[1]
      (some ⟨some .closeDummyTail, state, finishTapes n m rev⟩) =
      some ⟨some (.scan .dummyReverse), state, finishTapes n m (false :: rev)⟩ := by
  change some (TM2.stepAux (program .closeDummyTail) state (finishTapes n m rev)) = _
  simp only [program, TM2.stepAux]
  congr 2
  exact update_finish _ _ _ _

private theorem closeDummyReverseTrace (n m : Nat) (rev : List Bool) (state : State) :
    (MachineComposition.advance (TM2.step program))^[1]
      (some ⟨some .closeDummyReverse, state, finishTapes n m rev⟩) =
      some ⟨some .dummyRelation, state, finishTapes n m (false :: rev)⟩ := by
  change some (TM2.stepAux (program .closeDummyReverse) state (finishTapes n m rev)) = _
  simp only [program, TM2.stepAux]
  congr 2
  exact update_finish _ _ _ _

private theorem dummyRelationTrace (n m : Nat) (rev : List Bool) (state : State) :
    (MachineComposition.advance (TM2.step program))^[1]
      (some ⟨some .dummyRelation, state, finishTapes n m rev⟩) =
      some ⟨some (.cleanupFinal 0), state,
        finishTapes n m ((encodeWords (List.replicate 4096 1)).reverse ++ rev)⟩ := by
  change some (TM2.stepAux (program .dummyRelation) state (finishTapes n m rev)) = _
  rw [program, Reduction.MachineSubstitution.stepAux_pushWord, trueRelationWords]
  simp only [TM2.stepAux]
  congr 2
  exact update_finish _ _ _ _

/-- The three actual prefix scans and three emitting transitions append the complete dummy row. -/
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
  have h0 := copyFinishTrace n m n rev .dummyVariables rfl state
  simp only [copyScale, copyNext, Nat.one_mul] at h0
  have h1 := copyFinishTrace n m m a .dummyIndex rfl (state.1, none)
  simp only [copyScale, copyNext, Nat.one_mul] at h1
  have h2 := closeDummyTailTrace n m b (state.1, none)
  have h3 := copyFinishTrace n m m c .dummyReverse rfl (state.1, none)
  simp only [copyScale, copyNext] at h3
  have h4 := closeDummyReverseTrace n m d (state.1, none)
  have h5 := dummyRelationTrace n m e (state.1, none)
  have total := trace_trans _ (trace_trans _ (trace_trans _
    (trace_trans _ (trace_trans _ h0 h1) h2) h3) h4) h5
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

/-- Exact final execution, including all tape cleanup and the canonical halt state. -/
theorem finishTrace (n m : Nat) (rev : List Bool) (state : State) :
    (MachineComposition.advance (TM2.step program))^[
        3 * n + 5 * m + 17 + (encodeWords (RawInitialRows.dummyWords n m)).length + rev.length]
      (some ⟨some (.scan .dummyVariables), state, finishTapes n m rev⟩) =
      some (haltList machine (rev.reverse ++ encodeWords (RawInitialRows.dummyWords n m))) := by
  let emitted := (encodeWords (RawInitialRows.dummyWords n m)).reverse ++ rev
  have total := trace_trans _ (trace_trans _ (dummyTrace n m rev state)
    (cleanupTrace n m emitted (state.1, none)))
    (resetReverseTrace emitted (state.1, none))
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

end UniqueGamesTheorem.Foundations.PCP.RawInitialMachineFinish

end

end OAI
