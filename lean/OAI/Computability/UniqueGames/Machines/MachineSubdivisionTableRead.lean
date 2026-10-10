import OAI.Computability.UniqueGames.Machines.MachineSubdivisionDynamicRowsLemmas
import OAI.Computability.UniqueGames.Reduction.GameEncodingSizeLemmas

namespace OAI

section

/-!
Actual execution of the subdivision controller's full-table reader.
The reader consumes exactly the fixed number of zero-delimited table entries,
retains the unread input suffix, and reverses the saved table into forward order.
No table entry is stored in finite control; only the number of delimiters is.
-/

namespace UniqueGamesTheorem.Explicit.MachineSubdivisionTableRead

open Turing
open UniqueGamesTheorem.Foundations UniqueGamesTheorem.Foundations.Complexity
open UniqueGamesTheorem.Reduction
open MachineSubdivisionProgram

def tapes (base : Tape → List Bool) (input reversed : List Bool) : Tape → List Bool :=
  Function.update (Function.update base Tape.input input) Tape.permutationReverse reversed

@[simp] theorem tapes_input (base : Tape → List Bool) (input reversed : List Bool) :
    tapes base input reversed .input = input := by simp [tapes]

@[simp] theorem tapes_reverse (base : Tape → List Bool) (input reversed : List Bool) :
    tapes base input reversed .permutationReverse = reversed := by simp [tapes]

private theorem update_input (base : Tape → List Bool) (input reversed replacement : List Bool) :
    Function.update (tapes base input reversed) .input replacement =
      tapes base replacement reversed := by
  funext k
  cases k <;> simp [tapes]

private theorem update_reverse (base : Tape → List Bool) (input reversed replacement : List Bool) :
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
  simp [program, valid, TM2.stepAux, tapes_input, tapes_reverse, update_input, update_reverse]

theorem step_false (q : Nat) (completed : Fin (q + 1)) (valid : completed.val < q)
    (base : Tape → List Bool) (input reversed : List Bool)
    (ambient : Unit × Unit) (register : Option Bool) :
    TM2.step (program q)
      ⟨some (.readTable completed), (ambient, register), tapes base (false :: input) reversed⟩ =
      some ⟨some (.readTable ⟨completed.val + 1, by omega⟩), (ambient, none),
        tapes base input (false :: reversed)⟩ := by
  change some (TM2.stepAux (program q (.readTable completed)) _ _) = _
  simp [program, valid, TM2.stepAux, tapes_input, tapes_reverse, update_input, update_reverse]

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

end UniqueGamesTheorem.Explicit.MachineSubdivisionTableRead

end

end OAI
