import Mathlib
import OAI.Computability.MaxCut.Encoding.GameEncodingSize
import OAI.Computability.MaxCut.Machines.RuntimeSpace
import OAI.Computability.MaxCut.Machines.MachineSubdivisionEmission

namespace OAI

/-!
Actual execution of the subdivision controller's full-table reader.
The reader consumes exactly the fixed number of zero-delimited table entries,
retains the unread input suffix, and reverses the saved table into forward order.
No table entry is stored in finite control; only the number of delimiters is.
-/

namespace MaxCutGames.Explicit.MachineSubdivisionTableRead

open Turing
open MaxCutGames.Foundations MaxCutGames.Foundations.Complexity
open MaxCutGames.Reduction
open MachineSubdivisionProgram

def tapes (base : Tape → List Bool) (input reversed : List Bool) : Tape → List Bool :=
  Function.update (Function.update base Tape.input input) Tape.permutationReverse reversed

@[simp] theorem tapes_input (base : Tape → List Bool) (input reversed : List Bool) :
    tapes base input reversed .input = input := by simp [tapes]

@[simp] theorem tapes_reverse (base : Tape → List Bool) (input reversed : List Bool) :
    tapes base input reversed .permutationReverse = reversed := by simp [tapes]

private theorem update_input_inline_MachineSubdivisionTableRead (base : Tape → List Bool) (input reversed replacement : List Bool) :
    Function.update (tapes base input reversed) .input replacement =
      tapes base replacement reversed := by
  funext k
  cases k <;> simp [tapes]

private theorem update_reverse_inline_MachineSubdivisionTableRead (base : Tape → List Bool) (input reversed replacement : List Bool) :
    Function.update (tapes base input reversed) .permutationReverse replacement =
      tapes base input replacement := by
  funext k
  cases k <;> simp [tapes]

theorem step_true (q : Nat) (completed : Fin (q + 1)) (valid : completed.val < q)
    (base : Tape → List Bool) (input reversed : List Bool)
    (ambient : Unit × Unit) (register : Option Bool) :
    TM2.step (program q)
      ⟨some (.readTable completed), (ambient, register), tapes base (true :: input) reversed⟩ =
      some ⟨some (.readTable completed), (ambient, some true),
        tapes base input (true :: reversed)⟩ := by
  change some (TM2.stepAux (program q (.readTable completed)) _ _) = _
  simp [program, valid, TM2.stepAux, tapes_input, tapes_reverse, update_input_inline_MachineSubdivisionTableRead, update_reverse_inline_MachineSubdivisionTableRead]

theorem step_false (q : Nat) (completed : Fin (q + 1)) (valid : completed.val < q)
    (base : Tape → List Bool) (input reversed : List Bool)
    (ambient : Unit × Unit) (register : Option Bool) :
    TM2.step (program q)
      ⟨some (.readTable completed), (ambient, register), tapes base (false :: input) reversed⟩ =
      some ⟨some (.readTable ⟨completed.val + 1, by omega⟩), (ambient, none),
        tapes base input (false :: reversed)⟩ := by
  change some (TM2.stepAux (program q (.readTable completed)) _ _) = _
  simp [program, valid, TM2.stepAux, tapes_input, tapes_reverse, update_input_inline_MachineSubdivisionTableRead, update_reverse_inline_MachineSubdivisionTableRead]

/-- One encoded entry consumes its final delimiter in the same transition that
increments the finite completed-entry counter. -/
theorem readWordTrace (q : Nat) (completed : Fin (q + 1)) (valid : completed.val < q)
    (base : Tape → List Bool) (value : Nat) (input reversed : List Bool)
    (ambient : Unit × Unit) (register : Option Bool) :
    (MachineComposition.advance (TM2.step (program q)))^[value + 1]
      (some ⟨some (.readTable completed), (ambient, register),
        tapes base (encodeWord value ++ input) reversed⟩) =
      some ⟨some (.readTable ⟨completed.val + 1, by omega⟩), (ambient, none),
        tapes base input ((encodeWord value).reverse ++ reversed)⟩ := by
  induction value generalizing reversed register with
  | zero =>
    simpa [encodeWord, MachineComposition.advance] using
      step_false q completed valid base input reversed ambient register
  | succ value ih =>
    rw [Function.iterate_succ_apply]
    simp only [encodeWord, List.replicate_succ, List.cons_append,
      MachineComposition.advance_some]
    rw [step_true q completed valid]
    have h := ih (true :: reversed) (some true)
    simpa only [encodeWord, List.reverse_cons, List.reverse_append,
      List.append_assoc, List.singleton_append] using h

/-- Read a suffix of the q-entry table, stopping before any following data. -/
theorem readWordsTrace (q : Nat) (words : List Nat) (completed : Fin (q + 1))
    (complete : completed.val + words.length = q) (base : Tape → List Bool)
    (suffix reversed : List Bool) (ambient : Unit × Unit) (register : Option Bool) :
    (MachineComposition.advance (TM2.step (program q)))^[(encodeWords words).length + 1]
      (some ⟨some (.readTable completed), (ambient, register),
        tapes base (encodeWords words ++ suffix) reversed⟩) =
      some ⟨some .reverseTable, (ambient, none),
        tapes base suffix ((encodeWords words).reverse ++ reversed)⟩ := by
  induction words generalizing completed reversed register with
  | nil =>
    have hc : ¬ completed.val < q := by simpa using complete.ge
    simp [encodeWords, MachineComposition.advance, TM2.step, program, hc, TM2.stepAux]
  | cons value words ih =>
    have valid : completed.val < q := by simp only [List.length_cons] at complete; omega
    let next : Fin (q + 1) := ⟨completed.val + 1, by omega⟩
    have hn : next.val + words.length = q := by
      simp only [List.length_cons] at complete
      dsimp [next]
      omega
    have first := readWordTrace q completed valid base value (encodeWords words ++ suffix)
      reversed ambient register
    have second := ih next hn ((encodeWord value).reverse ++ reversed) none
    rw [encodeWords, List.length_append, encodeWord_length,
      show value + 1 + (encodeWords words).length + 1 =
        ((encodeWords words).length + 1) + (value + 1) by omega,
      Function.iterate_add_apply]
    simp only [List.append_assoc]
    rw [first]
    simpa only [next, List.reverse_append, List.append_assoc] using second

def finalTapes (base : Tape → List Bool) (suffix bits : List Bool) : Tape → List Bool :=
  Function.update (tapes base suffix []) .permutation (bits ++ base .permutation)

theorem finalTapes_other (base : Tape → List Bool) (suffix bits : List Bool)
    (k : Tape) (hi : k ≠ .input) (hr : k ≠ .permutationReverse) (hp : k ≠ .permutation) :
    finalTapes base suffix bits k = base k := by
  simp [finalTapes, tapes, hi, hr, hp]

@[simp] theorem finalTapes_input (base : Tape → List Bool) (suffix bits : List Bool) :
    finalTapes base suffix bits .input = suffix := by simp [finalTapes]

@[simp] theorem finalTapes_reverse (base : Tape → List Bool) (suffix bits : List Bool) :
    finalTapes base suffix bits .permutationReverse = [] := by simp [finalTapes]

@[simp] theorem finalTapes_permutation (base : Tape → List Bool) (suffix bits : List Bool) :
    finalTapes base suffix bits .permutation = bits ++ base .permutation := by simp [finalTapes]

/-- Full exact table phase: read q delimited entries and reverse the physical
saved stack, arriving at the actual row-emission label. -/
theorem tableTrace (q : Nat) (words : List Nat) (length : words.length = q)
    (base : Tape → List Bool) (suffix : List Bool)
    (ambient : Unit × Unit) (register : Option Bool) :
    (MachineComposition.advance (TM2.step (program q)))^[2 * (encodeWords words).length + 2]
      (some ⟨some (.readTable 0), (ambient, register),
        tapes base (encodeWords words ++ suffix) []⟩) =
      some ⟨some (rowEntry q), (ambient, none), finalTapes base suffix (encodeWords words)⟩ := by
  have read := readWordsTrace q words 0 (by simpa using length) base suffix [] ambient register
  simp only [List.append_nil] at read
  have reverse := MachineTransfer.transferAt_fromTapes
    Tape.permutationReverse Tape.permutation (by decide) id false
    Label.reverseTable (some (rowEntry q)) (program q) rfl
    (tapes base suffix (encodeWords words).reverse) ambient none
  have finish : MachineTransfer.tapesAt Tape.permutationReverse Tape.permutation
      (tapes base suffix (encodeWords words).reverse) []
      (((tapes base suffix (encodeWords words).reverse) .permutationReverse).reverse.map id ++
        (tapes base suffix (encodeWords words).reverse) .permutation) =
      finalTapes base suffix (encodeWords words) := by
    funext k
    cases k <;> simp [MachineTransfer.tapesAt, tapes, finalTapes]
  rw [finish] at reverse
  simp only [tapes_reverse, List.length_reverse] at reverse
  rw [show 2 * (encodeWords words).length + 2 =
      ((encodeWords words).length + 1) + ((encodeWords words).length + 1) by omega,
    Function.iterate_add_apply, read]
  exact reverse

/-- Timed witness for the actual controller, with a fixed alphabet-dependent
bound on its full forward table. Other row fields and unread input are preserved. -/
def tableInTime {q : Nat} (table : Target.PermutationTable q)
    (base : Tape → List Bool) (suffix : List Bool)
    (ambient : Unit × Unit) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step (program q))
      ⟨some (.readTable 0), (ambient, register),
        tapes base (encodeWords (tableWords table) ++ suffix) []⟩
      (some ⟨some (rowEntry q), (ambient, none),
        finalTapes base suffix (encodeWords (tableWords table))⟩)
      (2 * (q * (q + 1)) + 2) where
  steps := 2 * (encodeWords (tableWords table)).length + 2
  evals_in_steps := tableTrace q (tableWords table) (tableWords_length table)
    base suffix ambient register
  steps_le_m := by
    have h := GameEncodingSize.tableBits_length_le table
    omega

end MaxCutGames.Explicit.MachineSubdivisionTableRead

/-!
One whole occurrence iteration of the actual subdivision controller.
The proved trace includes both endpoint loads, the dynamic full-table reader,
the four-row template, all three local drains, and private-index increments.
-/

namespace MaxCutGames.Explicit.MachineSubdivisionBody

open Turing
open MaxCutGames.Foundations MaxCutGames.Foundations.Complexity
open MaxCutGames.Foundations.Hastad
open MaxCutGames.Reduction
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

private theorem rowField_ne_scratch_inline_MachineSubdivisionBody (j : Fin 6) : rowField j ≠ Tape.copyScratch := by
  fin_cases j <;> decide

private theorem rowField_ne_accumulator_inline_MachineSubdivisionBody (j : Fin 6) : rowField j ≠ Tape.accumulator := by
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
    Tape.copyScratch Tape.accumulator rowField_ne_scratch_inline_MachineSubdivisionBody rowField_ne_accumulator_inline_MachineSubdivisionBody (by decide)
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

end MaxCutGames.Explicit.MachineSubdivisionBody

/-! Concrete frames and literal row words for the subdivision occurrence loop. -/

namespace MaxCutGames.Explicit.MachineSubdivisionLoopFrame

open Turing
open MaxCutGames.Foundations MaxCutGames.Foundations.Target
open MaxCutGames.Foundations.Complexity
open MaxCutGames.Reduction
open MachineSubdivisionProgram

def bodyBits {n q : Nat} (edges : List (Constraint n q)) : List Bool :=
  encodeWords (edges.flatMap constraintWords)

@[simp] theorem bodyBits_nil {n q : Nat} : bodyBits ([] : List (Constraint n q)) = [] := rfl

theorem bodyBits_cons {n q : Nat} (edge : Constraint n q) (edges : List (Constraint n q)) :
    bodyBits (edge :: edges) =
      encodeWord edge.source.val ++ encodeWord edge.target.val ++
        MachineSubdivisionBody.tableBits edge.permutation ++ bodyBits edges := by
  simp [bodyBits, constraintWords, encodeWords, MachineSubdivisionBody.tableBits,
    List.append_assoc]

def identityBits (q : Nat) : List Bool :=
  encodeWords (tableWords (MachineSubdivisionRows.identityTable q))

def rowBits {n q : Nat} (Q e : Nat) (edge : Constraint n q) : List Bool :=
  encodeWords [edge.source.val, n + Q + 2 * e] ++ identityBits q ++
  encodeWords [n + e, n + Q + 2 * e] ++ identityBits q ++
  encodeWords [n + e, n + Q + 2 * e + 1] ++ identityBits q ++
  encodeWords [edge.target.val, n + Q + 2 * e + 1] ++
    MachineSubdivisionBody.tableBits edge.permutation

def outputRows {n q : Nat} (Q : Nat) : Nat → List (Constraint n q) → List Bool
  | _, [] => []
  | e, edge :: edges => rowBits Q e edge ++ outputRows Q (e + 1) edges

def frame {n q : Nat} (Q e : Nat) (edges : List (Constraint n q))
    (emitted : List Bool) : Tape → List Bool :=
  fun tape => match tape with
  | .input => bodyBits edges
  | .remaining => encodeWord edges.length
  | .middle => encodeWord (n + e)
  | .first => encodeWord (n + Q + 2 * e)
  | .last => encodeWord (n + Q + 2 * e + 1)
  | .accumulator => emitted.reverse
  | _ => MachineSubdivisionInit.resultTapes n q Q [] tape

def afterGuard {n q : Nat} (Q e : Nat) (edge : Constraint n q)
    (edges : List (Constraint n q)) (emitted : List Bool) : Tape → List Bool :=
  Function.update (frame Q e (edge :: edges) emitted) .remaining (encodeWord edges.length)

theorem frame_prepared {n q : Nat} (edges : List (Constraint n q)) :
    frame edges.length 0 edges (MachineSubdivisionEmission.headerBits n q edges.length) =
      MachineSubdivisionEmission.resultTapes n q edges.length (bodyBits edges) := by
  funext tape
  cases tape <;> simp [frame, MachineSubdivisionEmission.resultTapes,
    MachineSubdivisionInit.resultTapes]

theorem guard_cons {n q : Nat} (Q e : Nat) (edge : Constraint n q)
    (edges : List (Constraint n q)) (emitted : List Bool) :
    (machine q).step ⟨some .guard, initialState, frame Q e (edge :: edges) emitted⟩ =
      some ⟨some .startU, initialState, afterGuard Q e edge edges emitted⟩ := by
  have before : MachineUnaryCounter.counterTapes Tape.remaining
      (frame Q e (edge :: edges) emitted) (edges.length + 1) [] =
      frame Q e (edge :: edges) emitted := by
    simp only [MachineUnaryCounter.counterTapes, List.append_nil]
    change Function.update (frame Q e (edge :: edges) emitted) Tape.remaining
      ((frame Q e (edge :: edges) emitted) .remaining) = _
    exact Function.update_eq_self _ _
  have after : MachineUnaryCounter.counterTapes Tape.remaining
      (frame Q e (edge :: edges) emitted) edges.length [] =
      afterGuard Q e edge edges emitted := by
    simp [MachineUnaryCounter.counterTapes, afterGuard]
  have run := MachineUnaryCounter.guardStep_succ Tape.remaining
    (.guard : Label q) .startU .finishStart (program q) rfl
    (frame Q e (edge :: edges) emitted) edges.length [] ((), ()) none
  rw [before, after] at run
  simpa only [FinTM2.step, FinTM2.Cfg, machine, initialState] using! run

theorem guard_nil (n q Q e : Nat) (emitted : List Bool) :
    (machine q).step
      ⟨some .guard, initialState, frame Q e ([] : List (Constraint n q)) emitted⟩ =
      some ⟨some .finishStart, initialState, frame Q e ([] : List (Constraint n q)) emitted⟩ := by
  have framed : MachineUnaryCounter.counterTapes Tape.remaining
      (frame Q e ([] : List (Constraint n q)) emitted) 0 [] =
      frame Q e ([] : List (Constraint n q)) emitted := by
    simp only [MachineUnaryCounter.counterTapes, List.append_nil]
    change Function.update (frame Q e ([] : List (Constraint n q)) emitted) Tape.remaining
      ((frame Q e ([] : List (Constraint n q)) emitted) .remaining) = _
    exact Function.update_eq_self _ _
  have run := MachineUnaryCounter.guardStep_zero Tape.remaining
    (.guard : Label q) .startU .finishStart (program q) rfl
    (frame Q e ([] : List (Constraint n q)) emitted) [] ((), ()) none
  rw [framed] at run
  simpa only [FinTM2.step, FinTM2.Cfg, machine, initialState] using! run

theorem ready {n q : Nat} (Q e : Nat) (edge : Constraint n q)
    (edges : List (Constraint n q)) (emitted : List Bool) :
    MachineSubdivisionBody.Ready (afterGuard Q e edge edges emitted)
      edge.source.val edge.target.val edge.permutation (bodyBits edges) := by
  constructor
  · simpa only [afterGuard, Function.update_of_ne (by decide : Tape.input ≠ .remaining),
      frame] using bodyBits_cons edge edges
  · simp [afterGuard, frame, MachineSubdivisionInit.resultTapes]
  · simp [afterGuard, frame, MachineSubdivisionInit.resultTapes]
  · simp [afterGuard, frame, MachineSubdivisionInit.resultTapes]
  · simp [afterGuard, frame, MachineSubdivisionInit.resultTapes]
  · simp [afterGuard, frame, MachineSubdivisionInit.resultTapes]

end MaxCutGames.Explicit.MachineSubdivisionLoopFrame

/-! Exact tape framing, row serialization, and a uniform polynomial bound for
the already constructed whole subdivision-body execution. -/

namespace MaxCutGames.Explicit.MachineSubdivisionBodySpec

open Turing
open MaxCutGames.Foundations MaxCutGames.Foundations.Complexity
open MaxCutGames.Foundations.Hastad
open MaxCutGames.Reduction
open MachineSubdivisionProgram MachineSubdivisionBody

def resultTapes {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool) : Tape → List Bool
  | .input => suffix
  | .u | .v | .permutation | .permutationReverse => []
  | .middle => true :: base .middle
  | .first => true :: true :: base .first
  | .last => true :: true :: base .last
  | .accumulator => (rowPayload base u v table suffix).reverse ++ base .accumulator
  | k => base k

/-- Every tape at the body boundary, including all preserved headers and counters. -/
theorem bodyResult_eq {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool)
    (_ready : Ready base u v table suffix) :
    bodyResult base u v table suffix = resultTapes base u v table suffix := by
  funext k
  cases k <;> simp [bodyResult, incrementTapes, afterDrainTable, afterDrainV,
    afterDrainU, afterRows, MachineFieldTemplate.outputTapes, afterTable,
    MachineSubdivisionTableRead.finalTapes, MachineSubdivisionTableRead.tapes,
    afterV, afterU, SourceMachine.afterField, SourceMachine.fieldTapes, resultTapes]

theorem result_input {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool)
    (ready : Ready base u v table suffix) :
    bodyResult base u v table suffix .input = suffix := by
  rw [bodyResult_eq base u v table suffix ready]
  rfl

theorem result_locals {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool)
    (ready : Ready base u v table suffix) :
    bodyResult base u v table suffix .u = [] ∧
    bodyResult base u v table suffix .v = [] ∧
    bodyResult base u v table suffix .permutation = [] ∧
    bodyResult base u v table suffix .permutationReverse = [] ∧
    bodyResult base u v table suffix .copyScratch = [] := by
  rw [bodyResult_eq base u v table suffix ready]
  simp [resultTapes, ready.scratchEmpty]

theorem result_accumulator {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool)
    (ready : Ready base u v table suffix) :
    bodyResult base u v table suffix .accumulator =
      (rowPayload base u v table suffix).reverse ++ base .accumulator := by
  rw [bodyResult_eq base u v table suffix ready]
  rfl

theorem encodeWord_succ (n : Nat) : encodeWord (n + 1) = true :: encodeWord n := by
  simp [encodeWord, List.replicate_succ]

theorem result_indices {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool)
    (ready : Ready base u v table suffix) (n Q e : Nat)
    (middle : base .middle = encodeWord (n + e))
    (first : base .first = encodeWord (n + Q + 2 * e))
    (last : base .last = encodeWord (n + Q + 2 * e + 1)) :
    bodyResult base u v table suffix .middle = encodeWord (n + (e + 1)) ∧
    bodyResult base u v table suffix .first = encodeWord (n + Q + 2 * (e + 1)) ∧
    bodyResult base u v table suffix .last = encodeWord (n + Q + 2 * (e + 1) + 1) := by
  rw [bodyResult_eq base u v table suffix ready]
  have hm : n + (e + 1) = (n + e) + 1 := by omega
  have hf : n + Q + 2 * (e + 1) = (n + Q + 2 * e) + 1 + 1 := by omega
  have hl : n + Q + 2 * (e + 1) + 1 = (n + Q + 2 * e + 1) + 1 + 1 := by omega
  simp [resultTapes, middle, first, last, hm, hf, encodeWord_succ]

/-- Four whole rows, with the final table already in left-to-right orientation. -/
def rowBits {q : Nat} (u middle first last v : Nat) (table : Target.PermutationTable q) :
    List Bool :=
  encodeWords
    ([u, first] ++ tableWords (MachineSubdivisionRows.identityTable q) ++
      [middle, first] ++ tableWords (MachineSubdivisionRows.identityTable q) ++
      [middle, last] ++ tableWords (MachineSubdivisionRows.identityTable q) ++
      [v, last] ++ tableWords table)

theorem rowPayload_eq {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool)
    (ready : Ready base u v table suffix) (middle first last : Nat)
    (hm : base .middle = encodeWord middle) (hf : base .first = encodeWord first)
    (hl : base .last = encodeWord last) :
    rowPayload base u v table suffix = rowBits u middle first last v table := by
  simp [rowPayload, rowTokens, MachineSubdivisionDynamicRows.tokens,
    MachineFieldTemplate.templateOutput, MachineFieldTemplate.tokenOutput, rowField,
    afterTable, MachineSubdivisionTableRead.finalTapes, MachineSubdivisionTableRead.tapes,
    afterV, afterU, SourceMachine.afterField, SourceMachine.fieldTapes,
    ready.uEmpty, ready.vEmpty, ready.permutationEmpty, hm, hf, hl,
    rowBits, tableBits, encodeWords, List.append_assoc]

/-- The natural-word description is literally the established finite-target
constraint codec, rather than an alternative encoding. -/
theorem rowBits_eq_dynamic {N q : Nat} (vertices : Fin 5 → Fin N)
    (table : Target.PermutationTable q) :
    rowBits (vertices 0).val (vertices 2).val (vertices 1).val (vertices 3).val
      (vertices 4).val table = MachineSubdivisionDynamicRows.rowBits vertices table := by
  simp [rowBits, MachineSubdivisionDynamicRows.rowBits, MachineSubdivisionDynamicRows.rows,
    constraintWords, List.append_assoc]

/-- One conservative bound uniform over all occurrences in this output.
Only the fixed alphabet and the runtime header sizes appear in the polynomial. -/
theorem bodyBudget_le {q : Nat} (base : Tape → List Bool) (u v : Nat)
    (table : Target.PermutationTable q) (suffix : List Bool)
    (ready : Ready base u v table suffix) (n Q e : Nat)
    (hu : u < n) (hv : v < n) (he : e ≤ Q)
    (middle : base .middle = encodeWord (n + e))
    (first : base .first = encodeWord (n + Q + 2 * e))
    (last : base .last = encodeWord (n + Q + 2 * e + 1)) :
    bodyBudget base u v table suffix ≤ 100 * (n + 3 * Q + q * (q + 1) + 1) := by
  have ht : (tableBits table).length ≤ q * (q + 1) :=
    GameEncodingSize.tableBits_length_le table
  simp [bodyBudget, rowTokens, MachineSubdivisionDynamicRows.tokens,
    MachineFieldTemplate.copiedLength, rowField,
    afterDrainV, afterDrainU, afterRows, MachineFieldTemplate.outputTapes,
    afterTable, MachineSubdivisionTableRead.finalTapes, MachineSubdivisionTableRead.tapes,
    afterV, afterU, SourceMachine.afterField, SourceMachine.fieldTapes,
    ready.uEmpty, ready.vEmpty, ready.permutationEmpty, middle, first, last] at *
  omega

end MaxCutGames.Explicit.MachineSubdivisionBodySpec

/-! Complete physical occurrence traversal of the subdivision program. -/

namespace MaxCutGames.Explicit.MachineSubdivisionLoop

open Turing
open MaxCutGames.Foundations MaxCutGames.Foundations.Target
open MaxCutGames.Foundations.Complexity
open MachineSubdivisionProgram MachineSubdivisionLoopFrame

theorem rowPayload_eq {n q : Nat} (Q e : Nat) (edge : Constraint n q)
    (edges : List (Constraint n q)) (emitted : List Bool) :
    MachineSubdivisionBody.rowPayload (afterGuard Q e edge edges emitted)
      edge.source.val edge.target.val edge.permutation (bodyBits edges) = rowBits Q e edge := by
  rw [MachineSubdivisionBodySpec.rowPayload_eq _ _ _ _ _ (ready Q e edge edges emitted)
    (n + e) (n + Q + 2 * e) (n + Q + 2 * e + 1) rfl rfl rfl]
  simp only [MachineSubdivisionBodySpec.rowBits, rowBits, identityBits,
    MachineSubdivisionBody.tableBits, encodeWords_append, List.append_assoc]

theorem bodyResult_eq_frame {n q : Nat} (Q e : Nat) (edge : Constraint n q)
    (edges : List (Constraint n q)) (emitted : List Bool) :
    MachineSubdivisionBody.bodyResult (afterGuard Q e edge edges emitted)
      edge.source.val edge.target.val edge.permutation (bodyBits edges) =
      frame Q (e + 1) edges (emitted ++ rowBits Q e edge) := by
  have indices := MachineSubdivisionBodySpec.result_indices
    (afterGuard Q e edge edges emitted) edge.source.val edge.target.val edge.permutation
    (bodyBits edges) (ready Q e edge edges emitted) n Q e rfl rfl rfl
  funext tape
  cases tape with
  | middle => exact indices.1
  | first => exact indices.2.1
  | last => exact indices.2.2
  | input => exact MachineSubdivisionBodySpec.result_input _ _ _ _ _ (ready Q e edge edges emitted)
  | accumulator =>
    rw [MachineSubdivisionBodySpec.result_accumulator _ _ _ _ _ (ready Q e edge edges emitted),
      rowPayload_eq]
    simp [afterGuard, frame, List.reverse_append]
  | _ =>
    rw [MachineSubdivisionBodySpec.bodyResult_eq _ _ _ _ _ (ready Q e edge edges emitted)]
    simp [MachineSubdivisionBodySpec.resultTapes, afterGuard, frame,
      MachineSubdivisionInit.resultTapes]

def bodyBound (n q Q : Nat) : Nat := 100 * (n + 3 * Q + q * (q + 1) + 1)

def bodyInTime {n q : Nat} (Q e : Nat) (edge : Constraint n q)
    (edges : List (Constraint n q)) (emitted : List Bool) (he : e ≤ Q) :
    StateTransition.EvalsToInTime (machine q).step
      ⟨some .startU, initialState, afterGuard Q e edge edges emitted⟩
      (some ⟨some .guard, initialState, frame Q (e + 1) edges (emitted ++ rowBits Q e edge)⟩)
      (bodyBound n q Q) := by
  have run := MachineSubdivisionBody.bodyInTime (afterGuard Q e edge edges emitted)
    edge.source.val edge.target.val edge.permutation (bodyBits edges) (ready Q e edge edges emitted)
  rw [bodyResult_eq_frame] at run
  have bound := MachineSubdivisionBodySpec.bodyBudget_le (afterGuard Q e edge edges emitted)
    edge.source.val edge.target.val edge.permutation (bodyBits edges) (ready Q e edge edges emitted)
    n Q e edge.source.isLt edge.target.isLt he rfl rfl rfl
  exact { toEvalsTo := run.toEvalsTo, steps_le_m := run.steps_le_m.trans bound }

/-- Every list occurrence is read once, emits exactly its four rows, and advances
the three private numeric names. The loop includes its final zero-counter test. -/
def loopInTime {n q : Nat} (Q e : Nat) (edges : List (Constraint n q))
    (emitted : List Bool) (fit : e + edges.length ≤ Q) :
    StateTransition.EvalsToInTime (machine q).step
      ⟨some .guard, initialState, frame Q e edges emitted⟩
      (some ⟨some .finishStart, initialState,
        frame Q (e + edges.length) ([] : List (Constraint n q))
          (emitted ++ outputRows Q e edges)⟩)
      (edges.length * (bodyBound n q Q + 1) + 1) := by
  induction edges generalizing e emitted with
  | nil =>
    refine { steps := 1, evals_in_steps := ?_, steps_le_m := by simp }
    change (machine q).step ⟨some .guard, initialState, frame Q e [] emitted⟩ = _
    simpa only [List.length_nil, Nat.add_zero, outputRows, List.append_nil]
      using guard_nil n q Q e emitted
  | cons edge edges ih =>
    have he : e ≤ Q := by simp only [List.length_cons] at fit; omega
    have remainingFit : (e + 1) + edges.length ≤ Q := by
      simp only [List.length_cons] at fit
      omega
    have guard : StateTransition.EvalsToInTime (machine q).step
        ⟨some .guard, initialState, frame Q e (edge :: edges) emitted⟩
        (some ⟨some .startU, initialState, afterGuard Q e edge edges emitted⟩) 1 := {
      steps := 1
      evals_in_steps := by
        change (machine q).step
          ⟨some .guard, initialState, frame Q e (edge :: edges) emitted⟩ = _
        exact guard_cons Q e edge edges emitted
      steps_le_m := Nat.le_refl _ }
    have body := bodyInTime Q e edge edges emitted he
    have tail := ih (e + 1) (emitted ++ rowBits Q e edge) remainingFit
    have first := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ guard body
    have whole := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ first tail
    have index_eq : (e + 1) + edges.length = e + (edge :: edges).length := by simp; omega
    have words_eq : (emitted ++ rowBits Q e edge) ++ outputRows Q (e + 1) edges =
        emitted ++ outputRows Q e (edge :: edges) := by
      simp only [outputRows, List.append_assoc]
    rw [index_eq, words_eq] at whole
    exact {
      toEvalsTo := whole.toEvalsTo
      steps_le_m := by
        have bound := whole.steps_le_m
        simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
        omega }

end MaxCutGames.Explicit.MachineSubdivisionLoop

/-! Actual cleanup, output reversal, and polynomial finishing overhead. -/

namespace MaxCutGames.Explicit.MachineSubdivisionFinish

open Turing
open MaxCutGames.Foundations.Complexity
open MaxCutGames.Foundations.Hastad
open MachineSubdivisionProgram

noncomputable def timePolynomial (q : Nat) (prefixTime : Polynomial Nat) : Polynomial Nat :=
  SourceRuntimeSpace.completedTime (machine q) clearKeys.length (prefixTime + 1)

theorem haltList_eq (q : Nat) (bits : List Bool) :
    haltList (machine q) bits =
      ⟨none, initialState, SourceRuntimeFinish.canonicalTapes Tape.output bits⟩ := by
  unfold haltList
  congr 1
  funext k
  cases k <;> simp [machine, SourceRuntimeFinish.canonicalTapes, Function.update]
  rfl

def finishStartInTime (q : Nat) (base : Tape → List Bool) :
    StateTransition.EvalsToInTime (machine q).step
      ⟨some .finishStart, initialState, base⟩
      (some ⟨SourceRuntimeFinish.entry clearKeys (Label.finish (q := q)), initialState, base⟩)
      1 where
  steps := 1
  evals_in_steps := by
    change some (TM2.stepAux (program q .finishStart) initialState base) = _
    simp only [program, TM2.stepAux]
    rfl
  steps_le_m := Nat.le_refl _

theorem covers (k : Tape) (ha : k ≠ .accumulator) (ho : k ≠ .output) :
    k ∈ clearKeys := by
  rcases clearKeys_covers k with h | h | h
  · exact h
  · exact False.elim (ha h)
  · exact False.elim (ho h)

noncomputable def completePrefix (q : Nat) (input : List Bool) (prefixTime : Polynomial Nat)
    (base : Tape → List Bool)
    (execution : StateTransition.EvalsToInTime (machine q).step
      (initList (machine q) input)
      (some ⟨some .finishStart, initialState, base⟩) (prefixTime.eval input.length))
    (outputEmpty : base .output = []) :
    TM2OutputsInTime (machine q) input (some (base .accumulator).reverse)
      ((timePolynomial q prefixTime).eval input.length) := by
  let bridge := finishStartInTime q base
  let joined := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ execution bridge
  let prefixRun : StateTransition.EvalsToInTime (machine q).step
      (initList (machine q) input)
      (some ⟨SourceRuntimeFinish.entry clearKeys (Label.finish (q := q)), initialState, base⟩)
      ((prefixTime + 1).eval input.length) := {
    toEvalsTo := joined.toEvalsTo
    steps_le_m := by
      simpa only [Polynomial.eval_add, Polynomial.eval_one, Nat.add_comm] using joined.steps_le_m }
  let finishRun := SourceRuntimeFinish.finishInTime clearKeys Tape.accumulator Tape.output
    (by decide) accumulator_not_mem_clearKeys output_not_mem_clearKeys covers
    ((), ()) (Label.finish (q := q)) none (program q) (fun _ => rfl)
    base outputEmpty ((), ()) none
  let run := SourceRuntimeSpace.prefixAndFinishInTime (machine q)
    input (prefixTime + 1) prefixRun clearKeys Tape.accumulator Tape.output
    accumulator_not_mem_clearKeys output_not_mem_clearKeys covers base outputEmpty
    (fun _ => rfl) finishRun
  change StateTransition.EvalsToInTime (machine q).step
    (initList (machine q) input)
    (some (haltList (machine q) (base .accumulator).reverse)) _
  rw [haltList_eq]
  exact run

end MaxCutGames.Explicit.MachineSubdivisionFinish

end OAI
