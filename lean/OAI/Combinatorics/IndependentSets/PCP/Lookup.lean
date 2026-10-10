import Mathlib
import OAI.Combinatorics.IndependentSets.Machines.MachineLookupCore

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.AlphabetTable.Lookup

open Turing
open IndependentSetsGames.Foundations.Complexity
open MachineComposition GenericGraphTables

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

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

instance : Fintype Label where
  elems := {.guard, .skipTail, .skipReverse, .skipPredicate, .select, .copy}
  complete label := by cases label <;> simp

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

end IndependentSetsGames.Foundations.PCP.AlphabetTable.Lookup

end OAI
