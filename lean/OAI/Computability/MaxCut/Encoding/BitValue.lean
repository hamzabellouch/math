import Mathlib
import OAI.Computability.MaxCut.Estimates.Rename

namespace OAI

noncomputable section
namespace OptimalMaxCut.CounterMachine.Expr
open scoped BigOperators
open Finset

def bitValue (input : List Bool) (i : ℕ) : ℕ := if (input[i]?).getD false then 1 else 0

def zeroPrefix (input : List Bool) (i : ℕ) : ℕ :=
  ∑ j ∈ range i, (1-bitValue input j)

def wordValue (input : List Bool) (k : ℕ) : ℕ :=
  ∑ i ∈ range input.length, bitValue input i * (if zeroPrefix input i = k then 1 else 0)

def prefixZeros (i : Expr) : Expr := .sum i (.zero (.bit (.arg 0)))
def word (k : Expr) : Expr := .sum .length
  (.mul (.bit (.arg 0)) (equal (prefixZeros (.arg 0)) (k.rename Nat.succ)))

@[simp] theorem prefixZeros_eval (i : Expr) (input : List Bool) (args : ℕ → ℕ) :
    (prefixZeros i).eval input args = zeroPrefix input (i.eval input args) := by
  simp only [prefixZeros, eval, bind, zeroPrefix, bitValue]
  apply sum_congr rfl
  intro j hj
  by_cases h : (input[j]?).getD false = true <;> simp [h]

@[simp] theorem word_eval (k : Expr) (input : List Bool) (args : ℕ → ℕ) :
    (word k).eval input args = wordValue input (k.eval input args) := by
  simp [word, eval, prefixZeros_eval, equal_eval, wordValue, bitValue, bind]
  rfl

@[simp] theorem bitValue_cons_zero (a : Bool) (s : List Bool) :
    bitValue (a::s) 0 = if a then 1 else 0 := by simp [bitValue]
@[simp] theorem bitValue_cons_succ (a : Bool) (s : List Bool) (i : ℕ) :
    bitValue (a::s) (i+1) = bitValue s i := by simp [bitValue]
@[simp] theorem zeroPrefix_zero (input : List Bool) : zeroPrefix input 0 = 0 := by simp [zeroPrefix]
@[simp] theorem zeroPrefix_cons_succ (a : Bool) (s : List Bool) (i : ℕ) :
    zeroPrefix (a::s) (i+1) = (if a then 0 else 1)+zeroPrefix s i := by
  rw [zeroPrefix, sum_range_succ']
  simp only [bitValue_cons_zero, bitValue_cons_succ, zeroPrefix]
  cases a <;> simp [add_comm]

@[simp] theorem wordValue_nil (k : ℕ) : wordValue [] k = 0 := by simp [wordValue]

 theorem wordValue_true (s : List Bool) (k : ℕ) :
    wordValue (true::s) k = (if k=0 then 1 else 0)+wordValue s k := by
  rw [wordValue, List.length_cons, sum_range_succ']
  simp [wordValue, eq_comm, add_comm]

@[simp] theorem wordValue_false_zero (s : List Bool) : wordValue (false::s) 0 = 0 := by
  rw [wordValue, List.length_cons, sum_range_succ']
  simp

 theorem wordValue_false_succ (s : List Bool) (k : ℕ) :
    wordValue (false::s) (k+1) = wordValue s k := by
  rw [wordValue, List.length_cons, sum_range_succ']
  simp [wordValue, Nat.add_comm 1]

 theorem wordValue_block_zero (n : ℕ) (s : List Bool) :
    wordValue (List.replicate n true ++ false::s) 0 = n := by
  induction n with
  | zero => simp
  | succ n ih => simp only [List.replicate_succ, List.cons_append, wordValue_true, ↓reduceIte, ih]; omega

 theorem wordValue_block_succ (n k : ℕ) (s : List Bool) :
    wordValue (List.replicate n true ++ false::s) (k+1) = wordValue s k := by
  induction n with
  | zero => simpa using wordValue_false_succ s k
  | succ n ih => simp [List.replicate_succ, wordValue_true, ih]

def unaryWords (words : List ℕ) : List Bool := words.flatMap (fun n => List.replicate n true ++ [false])

 theorem wordValue_encoded (words : List ℕ) (k : ℕ) :
    wordValue (unaryWords words) k = (words[k]?).getD 0 := by
  induction words generalizing k with
  | nil => simp [unaryWords]
  | cons n words ih =>
    cases k with
    | zero => simpa [unaryWords, List.append_assoc] using wordValue_block_zero n (unaryWords words)
    | succ k =>
      simp only [unaryWords, List.flatMap_cons, List.append_assoc, List.singleton_append]
      change wordValue (List.replicate n true ++ false :: unaryWords words) (k+1) = _
      rw [wordValue_block_succ, ih]
      simp

end OptimalMaxCut.CounterMachine.Expr

end

end OAI
