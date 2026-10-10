import Mathlib
import OAI.Computability.QuantumFactoring.FactorVerifier
import OAI.Computability.QuantumFactoring.FactorController
import OAI.Computability.QuantumFactoring.SplitCandidate
import OAI.Computability.QuantumFactoring.BoundedStack

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork FactorController

def properOn {k w : ℕ} (m d : BooleanNetwork k w) : BooleanNetwork k 1 :=
  ((wordLt (wordConstant (BitVec.ofNat w 1)) d).band (wordLt d m)).band
    (zeroWord ((m.pair d).comp (mod w)))

lemma properOn_value {k w : ℕ} (hw : 0<w) (m d : BooleanNetwork k w) (x : Basis k) :
    (properOn m d).eval x 0=true ↔ ProperDivisor (bitsValue (m.eval x)).toNat
      (bitsValue (d.eval x)).toNat := by
  have h1 : 1<2^w := Nat.one_lt_pow (by omega) (by decide)
  rw [properOn,eval_band,Bool.and_eq_true,eval_band,Bool.and_eq_true,
    wordLt_eval,wordLt_eval,decide_eq_true_eq,decide_eq_true_eq,wordConstant_eval,
    BitVec.toNat_ofNat,Nat.mod_eq_of_lt h1,zeroWord_value,eval_comp,eval_pair,
    mod_word,BitVec.toNat_umod,←Nat.dvd_iff_mod_eq_zero]
  exact and_assoc

namespace NodeCircuit

abbrev width (s w : ℕ) := (s+1)*w+w

def pending (s w : ℕ) : BooleanNetwork (width s w) ((s+1)*w) := select (Fin.castAdd w)
def divisor (s w : ℕ) : BooleanNetwork (width s w) w := select (Fin.natAdd ((s+1)*w))
def top (s w : ℕ) : BooleanNetwork (width s w) w :=
  (pending s w).comp (blockNet (s+1) w 0)
def popped (s w : ℕ) : BooleanNetwork (width s w) ((s+1)*w) :=
  (pending s w).comp (stackPop (s+1) w)
def quotient (s w : ℕ) : BooleanNetwork (width s w) w :=
  ((top s w).pair (divisor s w)).comp (div w)
def isPrime (s w : ℕ) : BooleanNetwork (width s w) 1 := (top s w).comp (primeWord w)
def isDone (s w : ℕ) : BooleanNetwork (width s w) 1 := zeroWord (top s w)
def isProper (s w : ℕ) : BooleanNetwork (width s w) 1 := properOn (top s w) (divisor s w)
def split (s w : ℕ) : BooleanNetwork (width s w) ((s+1)*w) :=
  stackPush (divisor s w) (stackPush (quotient s w) (popped s w))

def next (s w : ℕ) : BooleanNetwork (width s w) ((s+1)*w) :=
  wordMux (isDone s w) (pending s w)
    (wordMux (isPrime s w) (popped s w) (wordMux (isProper s w) (split s w) (pending s w)))
def emitted (s w : ℕ) : BooleanNetwork (width s w) w :=
  wordMux (isPrime s w) (top s w) (wordConstant 0)
def failed (s w : ℕ) : BooleanNetwork (width s w) 1 :=
  ((isDone s w).bnot.band (isPrime s w).bnot).band (isProper s w).bnot

def step (s w : ℕ) : BooleanNetwork (width s w) (width s w+1) :=
  ((next s w).pair (emitted s w)).pair (failed s w)

def pack {s w : ℕ} (xs : List (Basis w)) (d : Basis w) : Basis (width s w) :=
  Fin.append (stackEncoding (s+1) w xs) d

@[simp] lemma pending_pack {s w : ℕ} (xs : List (Basis w)) (d : Basis w) :
    (pending s w).eval (pack xs d)=stackEncoding (s+1) w xs := by
  funext i
  exact Fin.append_left _ _ i
@[simp] lemma divisor_pack {s w : ℕ} (xs : List (Basis w)) (d : Basis w) :
    (divisor s w).eval (pack xs d)=d := by
  funext i
  exact Fin.append_right _ _ i
@[simp] lemma top_pack {s w : ℕ} (xs : List (Basis w)) (d : Basis w) :
    (top s w).eval (pack xs d)=xs.head?.getD (fun _=>false) := by
  rw [top,eval_comp,pending_pack,blockNet_eval,block_stackEncoding]
  cases xs <;> rfl

lemma popped_pack {s w : ℕ} (xs : List (Basis w)) (d : Basis w) (h : xs.length ≤ s+1) :
    (popped s w).eval (pack xs d)=stackEncoding (s+1) w xs.tail := by
  rw [popped,eval_comp,pending_pack,stackPop_encoding xs h]

lemma quotient_pack {s w : ℕ} (a d : Basis w) (xs : List (Basis w)) :
    (bitsValue ((quotient s w).eval (pack (a::xs) d))).toNat =
      (bitsValue a).toNat/(bitsValue d).toNat := by
  rw [quotient,eval_comp,eval_pair,div_word,top_pack,divisor_pack]
  rfl

lemma split_pack {s w : ℕ} (a d : Basis w) (xs : List (Basis w)) (h : xs.length ≤ s) :
    (split s w).eval (pack (a::xs) d)=stackEncoding (s+1) w
      (d::(quotient s w).eval (pack (a::xs) d)::xs) := by
  rw [split,stackPush_encoding _ _ _ _
    (stackPush_encoding _ _ _ _ (popped_pack (a::xs) d (by simp;omega))),divisor_pack]
  rfl

lemma isPrime_pack {s w : ℕ} (hw : 128 ≤ w) (a d : Basis w) (xs : List (Basis w)) :
    (isPrime s w).eval (pack (a::xs) d) 0=true ↔ (bitsValue a).toNat.Prime := by
  rw [isPrime,eval_comp,top_pack]
  exact primeWord_value hw _

lemma isProper_pack {s w : ℕ} (hw : 0<w) (a d : Basis w) (xs : List (Basis w)) :
    (isProper s w).eval (pack (a::xs) d) 0=true ↔
      ProperDivisor (bitsValue a).toNat (bitsValue d).toNat := by
  rw [isProper,properOn_value hw,top_pack,divisor_pack]
  rfl

lemma isDone_pack {s w : ℕ} (xs : List (Basis w)) (d : Basis w) :
    (isDone s w).eval (pack xs d) 0=true ↔
      (bitsValue (xs.head?.getD (fun _=>false))).toNat=0 := by
  rw [isDone,zeroWord_value,top_pack]

/-- Literal guarded stack update for one node of the recursive producer.
The source primality test is the Boolean AKS circuit, and division is a full
word division circuit. No semantic factorization operation is used here. -/
lemma next_pack_cons {s w : ℕ} (hw : 128 ≤ w) (a d : Basis w) (xs : List (Basis w))
    (h : xs.length ≤ s) (ha : 2 ≤ (bitsValue a).toNat) :
    (next s w).eval (pack (a::xs) d)=
      if (bitsValue a).toNat.Prime then stackEncoding (s+1) w xs
      else if ProperDivisor (bitsValue a).toNat (bitsValue d).toNat then
        stackEncoding (s+1) w (d::(quotient s w).eval (pack (a::xs) d)::xs)
      else stackEncoding (s+1) w (a::xs) := by
  rw [next,wordMux_eval,ite_eq_right (by
    rw [isDone_pack]
    simp only [List.head?_cons,Option.getD_some]
    omega),wordMux_eval,wordMux_eval,pending_pack,
    popped_pack (a::xs) d (by simp;omega),split_pack a d xs h]
  simp only [List.tail_cons]
  simp only [isPrime_pack hw,isProper_pack (by omega : 0<w)]

lemma emitted_pack_cons {s w : ℕ} (hw : 128 ≤ w) (a d : Basis w) (xs : List (Basis w)) :
    (emitted s w).eval (pack (a::xs) d)=
      if (bitsValue a).toNat.Prime then a else (fun _=>false) := by
  rw [emitted,wordMux_eval,top_pack]
  simp only [List.head?_cons,Option.getD_some,isPrime_pack hw]
  split_ifs
  · rfl
  · funext i
    simp [wordConstant]

lemma failed_pack_cons {s w : ℕ} (hw : 128 ≤ w) (a d : Basis w) (xs : List (Basis w))
    (ha : 2 ≤ (bitsValue a).toNat) :
    (failed s w).eval (pack (a::xs) d) 0=true ↔
      ¬(bitsValue a).toNat.Prime ∧ ¬ProperDivisor (bitsValue a).toNat (bitsValue d).toNat := by
  rw [failed,eval_band,Bool.and_eq_true,eval_band,Bool.and_eq_true,bnot_value,bnot_value,
    bnot_value,isDone_pack,isPrime_pack hw,isProper_pack (by omega : 0<w)]
  simp only [List.head?_cons,Option.getD_some]
  have h0 : (bitsValue a).toNat≠0 := by omega
  simp only [h0,not_false_eq_true,true_and]

end NodeCircuit
end ExactQuantumFactoring.BitArithmetic


end

end OAI
