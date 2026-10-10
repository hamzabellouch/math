import Mathlib.Algebra.BigOperators.Fin
import OAI.Computability.UniqueGames.Machines.MachineCompare
import OAI.Computability.UniqueGames.Machines.MachineCompositionLemmas
import OAI.Computability.UniqueGames.Machines.MachineCopy
import OAI.Computability.UniqueGames.Machines.MachineDrain
import OAI.Computability.UniqueGames.Machines.MachineLookupLemmas
import OAI.Computability.UniqueGames.PCP.InputLemmas

namespace OAI

/-! Actual finite-stack cleanup. Each selected stack is drained using the
checked pop loop, followed by one transition resetting the finite state.
Repeated selections are allowed; they only reduce the cost upper bound. -/

namespace UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Cleanup

open Turing
open Complexity
open scoped BigOperators

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

/-- Reset both the ambient finite state and the drain register before exiting. -/
def finish (initial : σ) (exit : Option Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  .load (fun _ => (initial, none))
    (match exit with | none => .halt | some label => .goto fun _ => label)

/-- A concrete instruction for each of the n drain phases and the final reset. -/
def instruction {n : Nat} (selected : Fin n → K) (labels : Fin (n + 1) → Λ)
    (initial : σ) (exit : Option Λ) (phase : Fin (n + 1)) :
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  if h : phase.val < n then
    MachineDrain.drain (selected ⟨phase.val, h⟩) (labels phase)
      (some (labels ⟨phase.val + 1, Nat.succ_lt_succ h⟩))
  else finish initial exit

omit [DecidableEq K] in
@[simp] theorem instruction_drain {n : Nat} (selected : Fin n → K)
    (labels : Fin (n + 1) → Λ) (initial : σ) (exit : Option Λ) (i : Fin n) :
    instruction selected labels initial exit i.castSucc =
      MachineDrain.drain (selected i) (labels i.castSucc) (some (labels i.succ)) := by
  simp [instruction, i.isLt]
  rfl

omit [DecidableEq K] in
@[simp] theorem instruction_finish {n : Nat} (selected : Fin n → K)
    (labels : Fin (n + 1) → Λ) (initial : σ) (exit : Option Λ) :
    instruction selected labels initial exit (Fin.last n) = finish initial exit := by
  simp [instruction]

/-- Actual tape family after the selected stacks have been drained in order. -/
def clearTapes : {n : Nat} → (Fin n → K) → (K → List Bool) → K → List Bool
  | 0, _, base => base
  | n + 1, selected, base =>
      clearTapes (fun i : Fin n => selected i.succ) (Function.update base (selected 0) [])

/-- Exact number of transitions, including the final state-reset transition. -/
def actualCost : {n : Nat} → (Fin n → K) → (K → List Bool) → Nat
  | 0, _, _ => 1
  | n + 1, selected, base =>
      actualCost (fun i : Fin n => selected i.succ) (Function.update base (selected 0) []) +
        ((base (selected 0)).length + 1)

theorem clearTapes_apply {n : Nat} (selected : Fin n → K) (base : K → List Bool) (k : K) :
    clearTapes selected base k = if ∃ i, selected i = k then [] else base k := by
  induction n generalizing base with
  | zero => simp [clearTapes]
  | succ n ih =>
      rw [clearTapes, ih]
      by_cases first : selected 0 = k
      · subst k
        simp [Function.update]
      · have notFirst : k ≠ selected 0 := Ne.symm first
        by_cases later : ∃ i : Fin n, selected i.succ = k <;>
          simp [Fin.exists_fin_succ, first, later, Function.update, notFirst]

@[simp] theorem clearTapes_selected {n : Nat} (selected : Fin n → K)
    (base : K → List Bool) (i : Fin n) : clearTapes selected base (selected i) = [] := by
  rw [clearTapes_apply, ite_eq_left ⟨i, rfl⟩]

theorem clearTapes_unselected {n : Nat} (selected : Fin n → K)
    (base : K → List Bool) (k : K) (notSelected : ∀ i, selected i ≠ k) :
    clearTapes selected base k = base k := by
  rw [clearTapes_apply]
  simp [notSelected]

theorem actualCost_le {n : Nat} (selected : Fin n → K) (base : K → List Bool) :
    actualCost selected base ≤ (∑ i, (base (selected i)).length) + n + 1 := by
  induction n generalizing base with
  | zero => simp [actualCost]
  | succ n ih =>
      have tailBound := ih (fun i : Fin n => selected i.succ)
        (Function.update base (selected 0) [])
      have sumBound :
          (∑ i : Fin n, ((Function.update base (selected 0) []) (selected i.succ)).length) ≤
            ∑ i : Fin n, (base (selected i.succ)).length := by
        apply Finset.sum_le_sum
        intro i _
        by_cases h : selected i.succ = selected 0 <;> simp [h]
      rw [actualCost, Fin.sum_univ_succ]
      omega

/-- The trace is derived solely from the actual drain instructions and final
reset instruction. No execution of the entire cleanup is assumed. -/
theorem cleanupTrace {n : Nat} (selected : Fin n → K) (labels : Fin (n + 1) → Λ)
    (initial : σ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atDrain : ∀ i : Fin n, program (labels i.castSucc) =
      MachineDrain.drain (selected i) (labels i.castSucc) (some (labels i.succ)))
    (atFinish : program (labels (Fin.last n)) = finish initial exit)
    (base : K → List Bool) (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[actualCost selected base]
      (some ⟨some (labels 0), (ambient, register), base⟩) =
      some ⟨exit, (initial, none), clearTapes selected base⟩ := by
  induction n generalizing base ambient register with
  | zero =>
      change some (TM2.stepAux (program (labels 0)) (ambient, register) base) = _
      rw [show program (labels 0) = finish initial exit from atFinish]
      cases exit <;> rfl
  | succ n ih =>
      rw [actualCost, Function.iterate_add_apply]
      have first := MachineDrain.drainTrace (selected 0) (labels (0 : Fin (n + 1)).castSucc)
        (some (labels (0 : Fin (n + 1)).succ)) program (atDrain 0)
        base (base (selected 0)) ambient register
      simp only [Function.update_eq_self, Fin.castSucc_zero] at first
      rw [first]
      exact ih (fun i : Fin n => selected i.succ) (fun i => labels i.succ)
        (fun i => atDrain i.succ) atFinish (Function.update base (selected 0) []) ambient none

/-- Actual cleanup execution, bounded using the original selected-stack lengths. -/
def cleanupInTime {n : Nat} (selected : Fin n → K) (labels : Fin (n + 1) → Λ)
    (initial : σ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atDrain : ∀ i : Fin n, program (labels i.castSucc) =
      MachineDrain.drain (selected i) (labels i.castSucc) (some (labels i.succ)))
    (atFinish : program (labels (Fin.last n)) = finish initial exit)
    (base : K → List Bool) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels 0), (ambient, register), base⟩
      (some ⟨exit, (initial, none), clearTapes selected base⟩)
      ((∑ i, (base (selected i)).length) + n + 1) where
  steps := actualCost selected base
  evals_in_steps := cleanupTrace selected labels initial exit program atDrain atFinish
    base ambient register
  steps_le_m := actualCost_le selected base

/-- Concrete n+1-label program, terminating after resetting the finite state. -/
def program {n : Nat} (selected : Fin n → K) (initial : σ) :
    Fin (n + 1) → TM2.Stmt (Alphabet (K := K)) (Fin (n + 1)) (σ × Option Bool) :=
  instruction selected id initial none

/-- A bundled finite machine. Its input/output tapes are designated explicitly. -/
def machine [Fintype K] [Fintype σ] {n : Nat} (selected : Fin n → K)
    (input output : K) (initial : σ) : FinTM2 where
  K := K
  k₀ := input
  k₁ := output
  Γ := Alphabet
  Λ := Fin (n + 1)
  main := 0
  σ := σ × Option Bool
  initialState := (initial, none)
  m := program selected initial

def machineInTime [Fintype K] [Fintype σ] {n : Nat} (selected : Fin n → K)
    (input output : K) (initial : σ) (base : K → List Bool)
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (machine selected input output initial).step
      ⟨some (0 : Fin (n + 1)), (ambient, register), base⟩
      (some ⟨none, (initial, none), clearTapes selected base⟩)
      ((∑ i, (base (selected i)).length) + n + 1) :=
  cleanupInTime selected id initial none (program selected initial)
    (fun i => instruction_drain selected id initial none i)
    (instruction_finish selected id initial none) base ambient register

/-- Enumerating exactly the nonoutput stacks yields the standard final tape
family. Repeated selected stacks are permitted. -/
theorem clearTapes_outputOnly {n : Nat} (selected : Fin n → K)
    (output : K) (base : K → List Bool)
    (excludesOutput : ∀ i, selected i ≠ output)
    (coversOther : ∀ k, k ≠ output → ∃ i, selected i = k) :
    clearTapes selected base = fun k => if k = output then base output else [] := by
  funext k
  by_cases h : k = output
  · subst k
    simp [clearTapes_unselected selected base output excludesOutput]
  · rw [clearTapes_apply]
    simp [h, coversOther k h]

/-- Full cleanup reaches `haltList`, with all nonoutput stacks empty and the
machine's actual initial finite state restored. -/
def machineHaltInTime [Fintype K] [Fintype σ] {n : Nat} (selected : Fin n → K)
    (input output : K) (initial : σ) (base : K → List Bool)
    (ambient : σ) (register : Option Bool)
    (excludesOutput : ∀ i, selected i ≠ output)
    (coversOther : ∀ k, k ≠ output → ∃ i, selected i = k) :
    StateTransition.EvalsToInTime (machine selected input output initial).step
      ⟨some (0 : Fin (n + 1)), (ambient, register), base⟩
      (some (haltList (machine selected input output initial) (base output)))
      ((∑ i, (base (selected i)).length) + n + 1) := by
  have tapeEq := clearTapes_outputOnly selected output base excludesOutput coversOther
  have haltEq : (⟨none, (initial, none), clearTapes selected base⟩ :
      (machine selected input output initial).Cfg) =
      haltList (machine selected input output initial) (base output) := by
    congr 1
  rw [← haltEq]
  exact machineInTime selected input output initial base ambient register

end UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Cleanup

namespace UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Lookup

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open MachineComposition GenericGraphTables

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

/-- A fixed finite chain skips Boolean unary words. A true head causes one
additional delimiter pop; a false head is already the complete zero word.
Only the one-bit head register is examined. -/
def skipBits (source : K) : Nat →
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) →
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool)
  | 0, next => .load (fun state => (state.1, none)) next
  | count + 1, next =>
      let rest := skipBits source count next
      .pop source (fun state head => (state.1, head))
        (.branch (fun state => state.2.getD false)
          (.pop source (fun state _ => (state.1, none)) rest)
          (.load (fun state => (state.1, none)) rest))

theorem stepAux_skipBits (source : K) (bits : List Bool)
    (next : TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (base : K → List Bool) (suffix : List Bool) (ambient : σ) (register : Option Bool) :
    TM2.stepAux (skipBits source bits.length next) (ambient, register)
        (Function.update base source (encodeWords (bits.map bitWord) ++ suffix)) =
      TM2.stepAux next (ambient, none) (Function.update base source suffix) := by
  induction bits generalizing register with
  | nil => simp [skipBits, encodeWords, TM2.stepAux]
  | cons bit bits ih =>
    cases bit <;>
      simpa only [List.length_cons, skipBits, List.map_cons, bitWord, Bool.false_eq_true,
        ite_false, ite_true, encodeWords, encodeWord, List.replicate_zero,
        List.replicate_succ, List.nil_append, List.cons_append, List.singleton_append,
        TM2.stepAux, Function.update_self, List.head?_cons, List.tail_cons,
        Option.getD_some, Bool.cond_false, Bool.cond_true, Function.update_idem] using
          ih none

theorem stepAux_skipBits_fromTapes (source : K) (bits : List Bool)
    (next : TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (base : K → List Bool) (suffix : List Bool)
    (hinput : base source = encodeWords (bits.map bitWord) ++ suffix)
    (ambient : σ) (register : Option Bool) :
    TM2.stepAux (skipBits source bits.length next) (ambient, register) base =
      TM2.stepAux next (ambient, none) (Function.update base source suffix) := by
  have h := stepAux_skipBits source bits next base suffix ambient register
  have hbase : Function.update base source (encodeWords (bits.map bitWord) ++ suffix) =
      base := by rw [← hinput]; exact Function.update_eq_self source base
  rw [hbase] at h
  exact h

omit [DecidableEq K] in
theorem skipBits_pushBound (source : K) (count : Nat)
    (next : TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool)) :
    Runtime.statementPushBound (skipBits source count next) =
      Runtime.statementPushBound next := by
  induction count with
  | zero => rfl
  | succ count ih => simp only [skipBits, Runtime.statementPushBound, ih, max_self]

inductive Label
  | guard | skipTail | skipReverse | skipPredicate | select | copy
  deriving DecidableEq

protected abbrev Label.enumList : List Label := [.guard, .skipTail, .skipReverse, .skipPredicate,
  .select, .copy]

protected theorem Label.enumList_getElem?_ctorIdx_eq (x : Label) :
    Label.enumList[x.ctorIdx]? = some x := by
  cases x <;> rfl

protected theorem Label.enumList_nodup : Label.enumList.Nodup := by decide

instance : Fintype Label where
  elems := ⟨Label.enumList, Label.enumList_nodup⟩
  complete x := by cases x <;> decide

/-- Six fixed control labels implement row selection. `q` fixes the finite
predicate parser; no data-dependent number is placed in the program syntax. -/
def statement (q : Nat) (counter source destination : K) (labels : Label → Λ)
    (exit : Option Λ) : Label → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool)
  | .guard => MachineUnaryCounter.guard counter (labels .skipTail) (labels .select)
  | .skipTail => MachineLookup.discard source (labels .skipTail) (labels .skipReverse)
  | .skipReverse => MachineLookup.discard source (labels .skipReverse) (labels .skipPredicate)
  | .skipPredicate => skipBits source (q * q) (.goto fun _ => labels .guard)
  | .select => Hastad.SourceMachine.fieldStart destination (labels .copy)
  | .copy => Hastad.SourceMachine.fieldLoop source destination (labels .copy) exit

def program (q : Nat) (counter source destination : K) :
    Label → TM2.Stmt (Alphabet (K := K)) Label (σ × Option Bool) :=
  statement q counter source destination id none

def rowBits {q n m : Nat} (row : DartRow q n m) : List Bool := encodeWords (rowWords row)

theorem rowBits_eq {q n m : Nat} (row : DartRow q n m) :
    rowBits row = encodeWord row.tail.val ++
      (encodeWord row.reverseIndex.val ++ encodeWords (relationWords row.relation)) := by
  simp [rowBits, rowWords, encodeWords]

def rowsBits {q n m : Nat} (rows : List (DartRow q n m)) : List Bool :=
  encodeWords (rows.flatMap rowWords)

@[simp] theorem rowsBits_nil {q n m : Nat} : rowsBits ([] : List (DartRow q n m)) = [] := rfl

@[simp] theorem rowsBits_cons {q n m : Nat} (row : DartRow q n m)
    (rows : List (DartRow q n m)) : rowsBits (row :: rows) = rowBits row ++ rowsBits rows := by
  simp only [rowsBits, List.flatMap_cons, encodeWords_append, rowBits]

def skipCost {q n m : Nat} (row : DartRow q n m) : Nat :=
  row.tail.val + row.reverseIndex.val + 4

def prefixCost {q n m : Nat} (rows : List (DartRow q n m)) : Nat :=
  (rows.map skipCost).sum

def lookupCost {q n m : Nat} (prior : List (DartRow q n m)) (row : DartRow q n m) : Nat :=
  prefixCost prior + row.tail.val + 3

section Ambient

variable {q n m : Nat} (counter source destination : K) (labels : Label → Λ)
  (exit : Option Λ)
  (P : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
  (atStatement : ∀ label, P (labels label) = statement q counter source destination labels exit label)

include atStatement

/-- One skipped row: two actual unary scans followed by one finite predicate
statement. All registers are reset and every other tape is untouched. -/
theorem skipRowTrace (base : K → List Bool) (row : DartRow q n m) (suffix : List Bool)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step P))^[row.tail.val + row.reverseIndex.val + 3]
      (some ⟨some (labels .skipTail), (ambient, register),
        Function.update base source (rowBits row ++ suffix)⟩) =
      some ⟨some (labels .guard), (ambient, none), Function.update base source suffix⟩ := by
  have ht := MachineLookup.discardTrace_update source (labels .skipTail) (labels .skipReverse)
    P (atStatement .skipTail) base row.tail.val
    (encodeWord row.reverseIndex.val ++ (encodeWords (relationWords row.relation) ++ suffix))
    ambient register
  have hr := MachineLookup.discardTrace_update source (labels .skipReverse) (labels .skipPredicate)
    P (atStatement .skipReverse) base row.reverseIndex.val
    (encodeWords (relationWords row.relation) ++ suffix) ambient none
  have hp : TM2.step P
      ⟨some (labels .skipPredicate), (ambient, none), Function.update base source
        (encodeWords (relationWords row.relation) ++ suffix)⟩ =
      some ⟨some (labels .guard), (ambient, none), Function.update base source suffix⟩ := by
    change some (TM2.stepAux (P (labels .skipPredicate)) _ _) = _
    rw [atStatement .skipPredicate]
    have h := congrArg some (stepAux_skipBits source row.relation.toList
      (.goto fun _ => labels .guard) base suffix ambient none)
    simpa only [statement, Vector.length_toList, relationWords, TM2.stepAux] using h
  rw [rowBits_eq]
  simp only [List.append_assoc]
  rw [show row.tail.val + row.reverseIndex.val + 3 =
    1 + ((row.reverseIndex.val + 1) + (row.tail.val + 1)) by omega,
    Function.iterate_add_apply, Function.iterate_add_apply, ht, hr,
    Function.iterate_one, advance_some, hp]

theorem skipRowTrace_fromTapes (base : K → List Bool) (row : DartRow q n m)
    (suffix : List Bool) (hinput : base source = rowBits row ++ suffix)
    (ambient : σ) (register : Option Bool) :
    (advance (TM2.step P))^[row.tail.val + row.reverseIndex.val + 3]
      (some ⟨some (labels .skipTail), (ambient, register), base⟩) =
      some ⟨some (labels .guard), (ambient, none), Function.update base source suffix⟩ := by
  have h := skipRowTrace counter source destination labels exit P atStatement
    base row suffix ambient register
  have hb : Function.update base source (rowBits row ++ suffix) = base := by
    rw [← hinput]
    exact Function.update_eq_self source base
  rw [hb] at h
  exact h

theorem selectTrace (hsd : source ≠ destination) (base : K → List Bool)
    (row : DartRow q n m) (suffix : List Bool)
    (hinput : base source = rowBits row ++ suffix) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step P))^[row.tail.val + 2]
      (some ⟨some (labels .select), (ambient, register), base⟩) =
      some ⟨exit, (ambient, none), Hastad.SourceMachine.fieldTapes source destination base
        (encodeWord row.reverseIndex.val ++ (encodeWords (relationWords row.relation) ++ suffix))
        (encodeWord row.tail.val ++ base destination)⟩ := by
  let ht := Hastad.SourceMachine.fieldInTime source destination hsd
    (labels .select) (labels .copy) exit P (atStatement .select) (atStatement .copy)
    base row.tail.val
    (encodeWord row.reverseIndex.val ++ (encodeWords (relationWords row.relation) ++ suffix))
    (by simpa only [rowBits_eq, List.append_assoc] using hinput) ambient register
  have hsteps : ht.steps = row.tail.val + 2 := rfl
  have htrace := ht.evals_in_steps
  rw [hsteps] at htrace
  exact htrace

/-- Exact successful row lookup. The only data premise is the literal table
prefix; no lookup result or whole execution is postulated. -/
theorem lookupTailTrace
    (hcs : counter ≠ source) (hcd : counter ≠ destination) (hsd : source ≠ destination)
    (base : K → List Bool) (prior : List (DartRow q n m)) (row : DartRow q n m)
    (counterSuffix suffix output : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step P))^[lookupCost prior row]
      (some ⟨some (labels .guard), (ambient, register),
        MachineLookup.tapes counter source destination base
          (encodeWord prior.length ++ counterSuffix)
          (rowsBits prior ++ (rowBits row ++ suffix)) output⟩) =
      some ⟨exit, (ambient, none),
        MachineLookup.tapes counter source destination base
          (encodeWord 0 ++ counterSuffix)
          (encodeWord row.reverseIndex.val ++ (encodeWords (relationWords row.relation) ++ suffix))
          (encodeWord row.tail.val ++ output)⟩ := by
  induction prior generalizing register with
  | nil =>
    simp only [lookupCost, prefixCost, List.map_nil, List.sum_nil, Nat.zero_add,
      List.length_nil, rowsBits_nil, List.nil_append]
    rw [show row.tail.val + 3 = (row.tail.val + 2) + 1 by omega,
      Function.iterate_succ_apply]
    have hg := MachineUnaryCounter.guardStep_zero counter (labels .guard)
      (labels .skipTail) (labels .select) P (atStatement .guard)
      (MachineLookup.tapes counter source destination base
        (encodeWord 0 ++ counterSuffix) (rowBits row ++ suffix) output)
      counterSuffix ambient register
    have hcounter : MachineUnaryCounter.counterTapes counter
        (MachineLookup.tapes counter source destination base
          (encodeWord 0 ++ counterSuffix) (rowBits row ++ suffix) output) 0 counterSuffix =
        MachineLookup.tapes counter source destination base
          (encodeWord 0 ++ counterSuffix) (rowBits row ++ suffix) output := by
      simp only [MachineUnaryCounter.counterTapes, MachineLookup.update_index _ _ _ hcs hcd]
    rw [hcounter] at hg
    simp only [advance_some]
    rw [hg]
    have hs := selectTrace counter source destination labels exit P atStatement hsd
      (MachineLookup.tapes counter source destination base
        (encodeWord 0 ++ counterSuffix) (rowBits row ++ suffix) output)
      row suffix (by simp [hsd]) ambient none
    simpa only [MachineLookup.tapes_destination,
      MachineLookup.fieldTapes_eq _ _ _ hsd] using hs
  | cons first prior ih =>
    simp only [lookupCost, prefixCost, List.map_cons, List.sum_cons, List.length_cons,
      rowsBits_cons, List.append_assoc]
    rw [show skipCost first + (prior.map skipCost).sum + row.tail.val + 3 =
      ((prior.map skipCost).sum + row.tail.val + 3) +
        (first.tail.val + first.reverseIndex.val + 3) + 1 by simp only [skipCost]; omega,
      Function.iterate_succ_apply]
    have hg := MachineUnaryCounter.guardStep_succ counter (labels .guard)
      (labels .skipTail) (labels .select) P (atStatement .guard)
      (MachineLookup.tapes counter source destination base
        (encodeWord prior.length ++ counterSuffix)
        (rowBits first ++ (rowsBits prior ++ (rowBits row ++ suffix))) output)
      prior.length counterSuffix ambient register
    simp only [MachineUnaryCounter.counterTapes,
      MachineLookup.update_index _ _ _ hcs hcd] at hg
    simp only [advance_some]
    rw [hg, Function.iterate_add_apply]
    have hs := skipRowTrace_fromTapes counter source destination labels exit P atStatement
      (MachineLookup.tapes counter source destination base
        (encodeWord prior.length ++ counterSuffix)
        (rowBits first ++ (rowsBits prior ++ (rowBits row ++ suffix))) output)
      first (rowsBits prior ++ (rowBits row ++ suffix)) (by simp [hsd]) ambient none
    rw [hs]
    simp only [MachineLookup.update_source _ _ _ hsd]
    exact ih none

end Ambient

/-- The number of actual transitions is linear in the scanned encoding and
the unary row index. Fixed predicate statements contribute one transition. -/
theorem lookupCost_le {q n m : Nat} (prior : List (DartRow q n m)) (row : DartRow q n m) :
    lookupCost prior row ≤ (rowsBits prior ++ rowBits row).length +
      2 * (encodeWord prior.length).length + 1 := by
  have hp : prefixCost prior ≤ (rowsBits prior).length + 2 * prior.length := by
    induction prior with
    | nil => simp [prefixCost]
    | cons first prior ih =>
      have hb : skipCost first ≤ (rowBits first).length + 2 := by
        simp only [skipCost, rowBits_eq, List.length_append, encodeWord_length]
        omega
      simp only [prefixCost, List.map_cons, List.sum_cons, rowsBits_cons,
        List.length_append, List.length_cons] at *
      omega
  have hr : row.tail.val + 1 ≤ (rowBits row).length := by
    simp only [rowBits_eq, List.length_append, encodeWord_length]
    omega
  simp only [lookupCost, List.length_append, encodeWord_length]
  omega

/-- The exact row-selection trace packaged with its linear transition budget. -/
def lookupTailInTime {q n m : Nat}
    (counter source destination : K) (labels : Label → Λ) (exit : Option Λ)
    (P : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atStatement : ∀ label, P (labels label) = statement q counter source destination labels exit label)
    (hcs : counter ≠ source) (hcd : counter ≠ destination) (hsd : source ≠ destination)
    (base : K → List Bool) (prior : List (DartRow q n m)) (row : DartRow q n m)
    (counterSuffix suffix output : List Bool) (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step P)
      ⟨some (labels .guard), (ambient, register),
        MachineLookup.tapes counter source destination base
          (encodeWord prior.length ++ counterSuffix)
          (rowsBits prior ++ (rowBits row ++ suffix)) output⟩
      (some ⟨exit, (ambient, none),
        MachineLookup.tapes counter source destination base
          (encodeWord 0 ++ counterSuffix)
          (encodeWord row.reverseIndex.val ++ (encodeWords (relationWords row.relation) ++ suffix))
          (encodeWord row.tail.val ++ output)⟩)
      ((rowsBits prior ++ rowBits row).length + 2 * (encodeWord prior.length).length + 1) where
  steps := lookupCost prior row
  evals_in_steps := lookupTailTrace counter source destination labels exit P atStatement
    hcs hcd hsd base prior row counterSuffix suffix output ambient register
  steps_le_m := lookupCost_le prior row

/-- The input's actual stored row vector determines the selected row. This
specialization derives the literal lookup prefix from the checked codec. -/
theorem tableTailTrace {q : Nat}
    (counter source destination : K) (labels : Label → Λ) (exit : Option Λ)
    (P : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atStatement : ∀ label, P (labels label) = statement q counter source destination labels exit label)
    (hcs : counter ≠ source) (hcd : counter ≠ destination) (hsd : source ≠ destination)
    (base : K → List Bool) (table : Table q) (e : Fin table.darts)
    (counterSuffix suffix output : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step P))^[lookupCost ((rowList table).take e.val) table.rows[e]]
      (some ⟨some (labels .guard), (ambient, register),
        MachineLookup.tapes counter source destination base
          (encodeWord e.val ++ counterSuffix) (rowsBits (rowList table) ++ suffix) output⟩) =
      some ⟨exit, (ambient, none),
        MachineLookup.tapes counter source destination base
          (encodeWord 0 ++ counterSuffix)
          (encodeWord table.rows[e].reverseIndex.val ++
            (encodeWords (relationWords table.rows[e].relation) ++
              (rowsBits ((rowList table).drop (e.val + 1)) ++ suffix)))
          (encodeWord table.rows[e].tail.val ++ output)⟩ := by
  have h := lookupTailTrace counter source destination labels exit P atStatement
    hcs hcd hsd base ((rowList table).take e.val) table.rows[e] counterSuffix
    (rowsBits ((rowList table).drop (e.val + 1)) ++ suffix) output ambient register
  have hlength : ((rowList table).take e.val).length = e.val := by
    simp only [List.length_take, rowList_length, Nat.min_eq_left (Nat.le_of_lt e.isLt)]
  have hsplit : rowsBits (rowList table) ++ suffix =
      rowsBits ((rowList table).take e.val) ++
        (rowBits table.rows[e] ++ (rowsBits ((rowList table).drop (e.val + 1)) ++ suffix)) := by
    have hrow : table.rows[e.val] = table.rows[e] := rfl
    simpa only [rowsBits, rowBits, rowList, Vector.getElem_toList, hrow] using
      Input.rowsBits_append_split (rowList table) e.val (by simp) suffix
  rw [hlength, ← hsplit] at h
  exact h

/-- Two real delimiter-scanning loops remove the header of the copied table
before the row counter starts. The protected original table can occupy any
other tape in `base` and is unchanged. -/
theorem fullTableTailTrace {q : Nat}
    (counter source destination : K) (labels : Label → Λ) (exit : Option Λ)
    (headerVertices headerDarts : Λ)
    (P : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atStatement : ∀ label, P (labels label) = statement q counter source destination labels exit label)
    (atVertices : P headerVertices = MachineLookup.discard source headerVertices headerDarts)
    (atDarts : P headerDarts = MachineLookup.discard source headerDarts (labels .guard))
    (hcs : counter ≠ source) (hcd : counter ≠ destination) (hsd : source ≠ destination)
    (base : K → List Bool) (table : Table q) (e : Fin table.darts)
    (counterSuffix suffix output : List Bool) (ambient : σ) (register : Option Bool) :
    (advance (TM2.step P))^[lookupCost ((rowList table).take e.val) table.rows[e] +
        (table.darts + 1) + (table.vertices + 1)]
      (some ⟨some headerVertices, (ambient, register),
        MachineLookup.tapes counter source destination base
          (encodeWord e.val ++ counterSuffix) (tableBits table ++ suffix) output⟩) =
      some ⟨exit, (ambient, none),
        MachineLookup.tapes counter source destination base
          (encodeWord 0 ++ counterSuffix)
          (encodeWord table.rows[e].reverseIndex.val ++
            (encodeWords (relationWords table.rows[e].relation) ++
              (rowsBits ((rowList table).drop (e.val + 1)) ++ suffix)))
          (encodeWord table.rows[e].tail.val ++ output)⟩ := by
  have hv := MachineLookup.discardTrace source headerVertices headerDarts P atVertices
    (MachineLookup.tapes counter source destination base
      (encodeWord e.val ++ counterSuffix) (tableBits table ++ suffix) output)
    table.vertices (encodeWord table.darts ++ (rowsBits (rowList table) ++ suffix))
    (by simp only [MachineLookup.tapes_source _ _ _ hsd, Input.tableBits_header,
      rowsBits, List.append_assoc]) ambient register
  rw [Function.iterate_add_apply, hv]
  simp only [MachineLookup.update_source _ _ _ hsd]
  have hd := MachineLookup.discardTrace source headerDarts (labels .guard) P atDarts
    (MachineLookup.tapes counter source destination base
      (encodeWord e.val ++ counterSuffix)
      (encodeWord table.darts ++ (rowsBits (rowList table) ++ suffix)) output)
    table.darts (rowsBits (rowList table) ++ suffix) (by simp [hsd]) ambient none
  rw [Function.iterate_add_apply, hd]
  simp only [MachineLookup.update_source _ _ _ hsd]
  exact tableTailTrace counter source destination labels exit P atStatement hcs hcd hsd
    base table e counterSuffix suffix output ambient none

theorem lookup_frame (counter source destination other : K)
    (hc : other ≠ counter) (hs : other ≠ source) (hd : other ≠ destination)
    (base : K → List Bool) (counterBits input output : List Bool) :
    MachineLookup.tapes counter source destination base counterBits input output other = base other :=
  MachineLookup.tapes_other counter source destination other hc hs hd base counterBits input output

def tableTailCost {q : Nat} (table : Table q) (e : Fin table.darts) : Nat :=
  lookupCost ((rowList table).take e.val) table.rows[e] +
    (table.darts + 1) + (table.vertices + 1)

theorem tableTailCost_le {q : Nat} (table : Table q) (e : Fin table.darts) :
    tableTailCost table e ≤ (tableBits table).length + 2 * (encodeWord e.val).length + 1 := by
  have htake : ((rowList table).take e.val).length = e.val := by
    simp only [List.length_take, rowList_length, Nat.min_eq_left (Nat.le_of_lt e.isLt)]
  have hrow : table.rows[e.val] = table.rows[e] := rfl
  have hsplit : rowsBits (rowList table) = rowsBits ((rowList table).take e.val) ++
      (rowBits table.rows[e] ++ rowsBits ((rowList table).drop (e.val + 1))) := by
    simpa only [rowsBits, rowBits, rowList, Vector.getElem_toList, hrow] using
      Input.rowsBits_split (rowList table) e.val (by simp)
  have hp : (rowsBits ((rowList table).take e.val) ++ rowBits table.rows[e]).length ≤
      (rowsBits (rowList table)).length := by
    rw [hsplit]
    simp only [List.length_append]
    omega
  have hb := lookupCost_le ((rowList table).take e.val) table.rows[e]
  rw [htake] at hb
  have hh := congrArg List.length (Input.tableBits_header table)
  change (tableBits table).length =
    (encodeWord table.vertices ++ (encodeWord table.darts ++ rowsBits (rowList table))).length at hh
  simp only [List.length_append, encodeWord_length] at hh
  unfold tableTailCost
  omega

def headIndex {q : Nat} (table : Table q) (e : Fin table.darts) : Fin table.darts :=
  table.rows[e].reverseIndex

def headValue {q : Nat} (table : Table q) (e : Fin table.darts) : Nat :=
  table.rows[headIndex table e].tail.val

/-- The looked-up endpoint is the head of the actual graph semantics, including
paired loop darts whose reverse index differs from their own index. -/
theorem headValue_eq_semantics {q : Nat} (table : Table q) (e : Fin table.darts) :
    headValue table e = ((semantics table).head e).val := rfl

abbrev HeadTapes (K : Type) := Fin 6 → K

def headLookupTapes {q : Nat} (tape : HeadTapes K) (base : K → List Bool)
    (table : Table q) (e : Fin table.darts) : K → List Bool :=
  MachineLookup.tapes (tape 3) (tape 2) (tape 4) base
    (encodeWord 0 ++ base (tape 3))
    (encodeWord table.rows[headIndex table e].reverseIndex.val ++
      (encodeWords (relationWords table.rows[headIndex table e].relation) ++
        (rowsBits ((rowList table).drop ((headIndex table e).val + 1)) ++ base (tape 2))))
    (encodeWord (headValue table e))

def headLookupCost {q : Nat} (table : Table q) (e : Fin table.darts) : Nat :=
  2 * ((tableBits table).length + 1) +
    2 * ((encodeWord (headIndex table e).val).length + 1) + tableTailCost table (headIndex table e)

theorem headLookupCost_le {q : Nat} (table : Table q) (e : Fin table.darts) :
    headLookupCost table e ≤ 7 * (tableBits table).length + 5 := by
  have hi : (encodeWord (headIndex table e).val).length ≤ (tableBits table).length := by
    rw [encodeWord_length]
    exact (Nat.succ_le_of_lt (headIndex table e).isLt).trans (darts_le_tableBits_length table)
  have hl := tableTailCost_le table (headIndex table e)
  unfold headLookupCost
  omega

noncomputable def headTimePolynomial : Polynomial Nat :=
  Polynomial.C 7 * Polynomial.X + Polynomial.C 5

def headLookupInTime {q : Nat}
    (tape : HeadTapes K) (hinj : Function.Injective tape)
    (tableFirst tableSecond indexFirst indexSecond headerVertices headerDarts : Λ)
    (labels : Label → Λ) (exit : Option Λ)
    (P : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atTableFirst : P tableFirst = Reduction.MachineTransfer.loopAt
      (tape 0) (tape 5) id false tableFirst (some tableSecond))
    (atTableSecond : P tableSecond = MachineCopy.forkLoop
      (tape 5) (tape 0) (tape 2) false tableSecond (some indexFirst))
    (atIndexFirst : P indexFirst = Reduction.MachineTransfer.loopAt
      (tape 1) (tape 5) id false indexFirst (some indexSecond))
    (atIndexSecond : P indexSecond = MachineCopy.forkLoop
      (tape 5) (tape 1) (tape 3) false indexSecond (some headerVertices))
    (atVertices : P headerVertices = MachineLookup.discard (tape 2) headerVertices headerDarts)
    (atDarts : P headerDarts = MachineLookup.discard (tape 2) headerDarts (labels .guard))
    (atStatement : ∀ label,
      P (labels label) = statement q (tape 3) (tape 2) (tape 4) labels exit label)
    (base : K → List Bool) (table : Table q) (e : Fin table.darts)
    (hTable : base (tape 0) = tableBits table)
    (hReverse : base (tape 1) = encodeWord (headIndex table e).val)
    (hHead : base (tape 4) = []) (hScratch : base (tape 5) = [])
    (ambient : σ) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step P)
      ⟨some tableFirst, (ambient, register), base⟩
      (some ⟨exit, (ambient, none), headLookupTapes tape base table e⟩)
      (headTimePolynomial.eval (tableBits table).length) := by
  have hne (i j : Fin 6) (h : i ≠ j) : tape i ≠ tape j := fun heq => h (hinj heq)
  let t₁ := Function.update base (tape 2) (tableBits table ++ base (tape 2))
  let t₂ := Function.update t₁ (tape 3) (encodeWord (headIndex table e).val ++ base (tape 3))
  have run₁ : StateTransition.EvalsToInTime (TM2.step P)
      ⟨some tableFirst, (ambient, register), base⟩
      (some ⟨some indexFirst, (ambient, none), t₁⟩)
      (2 * ((tableBits table).length + 1)) := by
    simpa only [hTable, t₁] using MachineCopy.copyInTime (tape 0) (tape 2) (tape 5)
      (hne 0 2 (by decide)) (hne 0 5 (by decide)) (hne 2 5 (by decide)) false
      tableFirst tableSecond (some indexFirst) P atTableFirst atTableSecond
      base hScratch ambient register
  have hsrc : t₁ (tape 1) = encodeWord (headIndex table e).val := by
    simp only [t₁, Function.update_of_ne (hne 1 2 (by decide)), hReverse]
  have hdst : t₁ (tape 3) = base (tape 3) := by
    simp only [t₁, Function.update_of_ne (hne 3 2 (by decide))]
  have hscratch₁ : t₁ (tape 5) = [] := by
    simp only [t₁, Function.update_of_ne (hne 5 2 (by decide)), hScratch]
  have run₂ : StateTransition.EvalsToInTime (TM2.step P)
      ⟨some indexFirst, (ambient, none), t₁⟩
      (some ⟨some headerVertices, (ambient, none), t₂⟩)
      (2 * ((encodeWord (headIndex table e).val).length + 1)) := by
    simpa only [hsrc, hdst, t₂] using MachineCopy.copyInTime (tape 1) (tape 3) (tape 5)
      (hne 1 3 (by decide)) (hne 1 5 (by decide)) (hne 3 5 (by decide)) false
      indexFirst indexSecond (some headerVertices) P atIndexFirst atIndexSecond
      t₁ hscratch₁ ambient none
  have ht₂ : t₂ = MachineLookup.tapes (tape 3) (tape 2) (tape 4) base
      (encodeWord (headIndex table e).val ++ base (tape 3))
      (tableBits table ++ base (tape 2)) [] := by
    funext k
    by_cases hi : k = tape 3
    · subst k
      simp [t₂, MachineLookup.tapes, hne 3 2 (by decide), hne 3 4 (by decide)]
    · by_cases hs : k = tape 2
      · subst k
        simp [t₂, t₁, MachineLookup.tapes, hne 2 3 (by decide), hne 2 4 (by decide)]
      · by_cases hh : k = tape 4
        · subst k
          simp [t₂, t₁, MachineLookup.tapes, hne 4 3 (by decide),
            hne 4 2 (by decide), hHead]
        · simp [t₂, t₁, MachineLookup.tapes, hi, hs, hh]
  let run₃ : StateTransition.EvalsToInTime (TM2.step P)
      ⟨some headerVertices, (ambient, none), t₂⟩
      (some ⟨exit, (ambient, none), headLookupTapes tape base table e⟩)
      (tableTailCost table (headIndex table e)) := {
    steps := tableTailCost table (headIndex table e)
    evals_in_steps := by
      change (advance (TM2.step P))^[tableTailCost table (headIndex table e)]
        (some ⟨some headerVertices, (ambient, none), t₂⟩) =
          some ⟨exit, (ambient, none), headLookupTapes tape base table e⟩
      rw [ht₂]
      simpa only [headLookupTapes, headValue, tableTailCost, List.append_nil] using
        fullTableTailTrace (tape 3) (tape 2) (tape 4) labels exit
          headerVertices headerDarts P atStatement atVertices atDarts
          (hne 3 2 (by decide)) (hne 3 4 (by decide)) (hne 2 4 (by decide))
          base table (headIndex table e) (base (tape 3)) (base (tape 2)) [] ambient none
    steps_le_m := Nat.le_refl _ }
  let run₁₂ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ run₁ run₂
  let run := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ run₁₂ run₃
  refine { toEvalsTo := run.toEvalsTo, steps_le_m := ?_ }
  have ht := run.steps_le_m
  have hb := headLookupCost_le table e
  simp only [headTimePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X]
  unfold headLookupCost at hb
  omega

theorem headLookupTapes_head {q : Nat} (tape : HeadTapes K) (base : K → List Bool)
    (table : Table q) (e : Fin table.darts) :
    headLookupTapes tape base table e (tape 4) = encodeWord (headValue table e) := by
  simp [headLookupTapes]

theorem headLookupTapes_frame {q : Nat} (tape : HeadTapes K) (base : K → List Bool)
    (table : Table q) (e : Fin table.darts) (other : K)
    (hc : other ≠ tape 3) (hs : other ≠ tape 2) (hh : other ≠ tape 4) :
    headLookupTapes tape base table e other = base other :=
  lookup_frame (tape 3) (tape 2) (tape 4) other hc hs hh base _ _ _

def readRowTapes {q n m : Nat} (source tail reverse : K) (base : K → List Bool)
    (row : DartRow q n m) (suffix : List Bool) : K → List Bool :=
  Function.update (Function.update (Function.update base source suffix)
    tail (encodeWord row.tail.val)) reverse (encodeWord row.reverseIndex.val)

theorem readRowTapes_source {q n m : Nat} (source tail reverse : K)
    (hst : source ≠ tail) (hsr : source ≠ reverse)
    (base : K → List Bool) (row : DartRow q n m) (suffix : List Bool) :
    readRowTapes source tail reverse base row suffix source = suffix := by
  simp [readRowTapes, hst, hsr]

theorem readRowTapes_tail {q n m : Nat} (source tail reverse : K)
    (htr : tail ≠ reverse) (base : K → List Bool)
    (row : DartRow q n m) (suffix : List Bool) :
    readRowTapes source tail reverse base row suffix tail = encodeWord row.tail.val := by
  simp [readRowTapes, htr]

theorem readRowTapes_reverse {q n m : Nat} (source tail reverse : K)
    (base : K → List Bool) (row : DartRow q n m) (suffix : List Bool) :
    readRowTapes source tail reverse base row suffix reverse =
      encodeWord row.reverseIndex.val := by
  simp [readRowTapes]

theorem readRowTapes_frame {q n m : Nat} (source tail reverse other : K)
    (hs : other ≠ source) (ht : other ≠ tail) (hr : other ≠ reverse)
    (base : K → List Bool) (row : DartRow q n m) (suffix : List Bool) :
    readRowTapes source tail reverse base row suffix other = base other := by
  simp [readRowTapes, hs, ht, hr]

def readRowCost {q n m : Nat} (row : DartRow q n m) : Nat :=
  row.tail.val + row.reverseIndex.val + 5

theorem readRowCost_le {q n m : Nat} (row : DartRow q n m) :
    readRowCost row ≤ (rowBits row).length + 3 := by
  rw [rowBits_eq]
  simp only [List.length_append, encodeWord_length]
  unfold readRowCost
  omega

theorem readRowCost_table_le {q : Nat} (table : Table q) (e : Fin table.darts) :
    readRowCost table.rows[e] ≤ 2 * (tableBits table).length + 5 := by
  have ht := (Nat.le_of_lt table.rows[e].tail.isLt).trans
    (vertices_le_tableBits_length table)
  have hr := (Nat.le_of_lt table.rows[e].reverseIndex.isLt).trans
    (darts_le_tableBits_length table)
  unfold readRowCost
  omega

/-- Read both unary fields using actual copy loops, then execute the checked
fixed predicate parser. Only the two field destinations must initially be
empty; the cursor suffix and every unrelated tape are retained exactly. -/
def readRowInTime {q n m : Nat} (source tail reverse : K)
    (hst : source ≠ tail) (hsr : source ≠ reverse) (htr : tail ≠ reverse)
    (tailStart tailLoop reverseStart reverseLoop readLabel exitLabel : Λ)
    (P : Λ → TM2.Stmt (Alphabet (K := K)) Λ (ReadRelation.State σ q))
    (atTailStart : P tailStart = Hastad.SourceMachine.fieldStart tail tailLoop)
    (atTailLoop : P tailLoop =
      Hastad.SourceMachine.fieldLoop source tail tailLoop (some reverseStart))
    (atReverseStart : P reverseStart = Hastad.SourceMachine.fieldStart reverse reverseLoop)
    (atReverseLoop : P reverseLoop =
      Hastad.SourceMachine.fieldLoop source reverse reverseLoop (some readLabel))
    (atRead : P readLabel = ReadRelation.parser source exitLabel)
    (base : K → List Bool) (row : DartRow q n m) (suffix : List Bool)
    (hinput : base source = rowBits row ++ suffix)
    (hTail : base tail = []) (hReverse : base reverse = [])
    (ambient : σ) (initial : RelationTable q) (register : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step P)
      ⟨some tailStart, ((ambient, initial), register), base⟩
      (some ⟨some exitLabel, ((ambient, row.relation), none),
        readRowTapes source tail reverse base row suffix⟩)
      (readRowCost row) := by
  let relationInput := encodeWords (relationWords row.relation) ++ suffix
  let reverseInput := encodeWord row.reverseIndex.val ++ relationInput
  let t₁ := Hastad.SourceMachine.fieldTapes source tail base reverseInput
    (encodeWord row.tail.val)
  let t₂ := Hastad.SourceMachine.fieldTapes source reverse t₁ relationInput
    (encodeWord row.reverseIndex.val)
  have hinput₁ : base source = encodeWord row.tail.val ++ reverseInput := by
    simpa only [rowBits_eq, List.append_assoc, reverseInput, relationInput] using hinput
  have run₁ : StateTransition.EvalsToInTime (TM2.step P)
      ⟨some tailStart, ((ambient, initial), register), base⟩
      (some ⟨some reverseStart, ((ambient, initial), none), t₁⟩)
      (row.tail.val + 2) := by
    simpa only [hTail, List.append_nil, t₁] using
      Hastad.SourceMachine.fieldInTime source tail hst tailStart tailLoop
        (some reverseStart) P atTailStart atTailLoop base row.tail.val reverseInput
        hinput₁ (ambient, initial) register
  have hinput₂ : t₁ source = encodeWord row.reverseIndex.val ++ relationInput := by
    simp only [t₁, Hastad.SourceMachine.fieldTapes_source source tail hst, reverseInput]
  have hreverse₁ : t₁ reverse = [] := by
    simp [t₁, Hastad.SourceMachine.fieldTapes, Ne.symm hsr, Ne.symm htr, hReverse]
  have run₂ : StateTransition.EvalsToInTime (TM2.step P)
      ⟨some reverseStart, ((ambient, initial), none), t₁⟩
      (some ⟨some readLabel, ((ambient, initial), none), t₂⟩)
      (row.reverseIndex.val + 2) := by
    simpa only [hreverse₁, List.append_nil, t₂] using
      Hastad.SourceMachine.fieldInTime source reverse hsr reverseStart reverseLoop
        (some readLabel) P atReverseStart atReverseLoop t₁ row.reverseIndex.val relationInput
        hinput₂ (ambient, initial) none
  have hinput₃ : t₂ source = encodeWords (relationWords row.relation) ++ suffix := by
    simp only [t₂, Hastad.SourceMachine.fieldTapes_source source reverse hsr, relationInput]
  have hrestore : Function.update t₂ source
      (encodeWords (relationWords row.relation) ++ suffix) = t₂ := by
    rw [← hinput₃]
    exact Function.update_eq_self source t₂
  have hfinal : Function.update t₂ source suffix =
      readRowTapes source tail reverse base row suffix := by
    funext k
    by_cases hs : k = source
    · subst k
      simp [readRowTapes, hst, hsr]
    · by_cases ht : k = tail
      · subst k
        simp [t₂, t₁, Hastad.SourceMachine.fieldTapes, readRowTapes, hs, htr]
      · by_cases hr : k = reverse
        · subst k
          simp [t₂, Hastad.SourceMachine.fieldTapes, readRowTapes, hs]
        · simp [t₂, t₁, Hastad.SourceMachine.fieldTapes, readRowTapes, hs, ht, hr]
  have run₃ : StateTransition.EvalsToInTime (TM2.step P)
      ⟨some readLabel, ((ambient, initial), none), t₂⟩
      (some ⟨some exitLabel, ((ambient, row.relation), none),
        readRowTapes source tail reverse base row suffix⟩) 1 := {
    steps := 1
    evals_in_steps := by
      change (advance (TM2.step P))^[1] _ = _
      simpa only [hrestore, hfinal] using ReadRelation.parserTrace source readLabel exitLabel
        P atRead t₂ row.relation suffix ambient initial none
    steps_le_m := Nat.le_refl _ }
  let run₁₂ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ run₁ run₂
  let run := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ run₁₂ run₃
  refine { toEvalsTo := run.toEvalsTo, steps_le_m := ?_ }
  have ht := run.steps_le_m
  unfold readRowCost
  omega

/-- A concrete finite machine instance, with input-dependent unary values
located only on its three tapes. -/
def machine (q : Nat) : FinTM2 where
  K := Fin 3
  k₀ := 1
  k₁ := 2
  Γ _ := Bool
  Λ := Label
  main := .guard
  σ := Unit × Option Bool
  initialState := ((), none)
  m := program q 0 1 2

end UniqueGamesTheorem.Foundations.PCP.AlphabetTable.Lookup

end OAI
