import Mathlib
import OAI.Combinatorics.UniformKServer.WrapperAlgebra

namespace OAI

noncomputable section

namespace UniformKServer.UniformWrapper
open Turing Turing.PartrecToTM2 TypedStack
open scoped Classical
variable {qc qa : ℕ}
variable (C : StackCompiler.Processor qc (Fintype.card K') g)
  (A : StackCompiler.Processor qa (Fintype.card K') g)

theorem push_main (q exit : Control qc qa) (a : Fin g)
    (h : ∀inp hd coin,(processor C A).transition q inp hd coin=write exit main a)
    (i : BitTape) (m p b : List (Fin g)) (out : List Bool) (coin : Bool) :
    TypedStack.step (processor C A) (wordState q i m p b out) coin=
      wordState exit i (a::m) p b out := by
  unfold TypedStack.step
  simp only [wordState,Bool.false_eq_true,↓reduceIte,h,write,BitTape.shift]
  apply wordState_ext <;> try rfl
  intro k;cases k with
  | base k=>cases k <;> rfl
  | pay=>rfl
  | buf=>rfl

theorem pop_main (q exit : Control qc qa) (y : Bool)
    (h : ∀inp hd coin,(processor C A).transition q inp hd coin=pop exit main y)
    (i : BitTape) (a : Fin g) (m p b : List (Fin g)) (out : List Bool) (coin : Bool) :
    TypedStack.step (processor C A) (wordState q i (a::m) p b out) coin=
      wordState exit i m p b out y := by
  unfold TypedStack.step
  simp only [wordState,Bool.false_eq_true,↓reduceIte,h,pop,BitTape.shift]
  apply wordState_ext <;> try rfl
  intro k;cases k with
  | base k=>cases k <;> rfl
  | pay=>rfl
  | buf=>rfl

theorem save_step (i : BitTape) (a : Bool) (m p b : List (Fin g)) (out : List Bool) (coin : Bool) :
    TypedStack.step (processor C A) (wordState .savePayload i (digit a::m) p b out) coin=
      wordState .savePayload i m (digit a::p) b out := by
  unfold TypedStack.step
  simp only [wordState,Bool.false_eq_true,↓reduceIte,processor,List.head?_cons,
    Option.some.injEq,digit_ne_sep,↓reduceIte,move,BitTape.shift]
  apply wordState_ext <;> try rfl
  intro k;cases k with
  | base k=>cases k <;> rfl
  | pay=>rfl
  | buf=>rfl

theorem save_end (i : BitTape) (p b : List (Fin g)) (out : List Bool) (coin : Bool) :
    TypedStack.step (processor C A) (wordState .savePayload i [sep] p b out) coin=
      wordState .randomCons i [] p b out := by
  unfold TypedStack.step
  simp only [wordState,Bool.false_eq_true,↓reduceIte,processor,List.head?_cons,↓reduceIte,pop,BitTape.shift]
  apply wordState_ext <;> try rfl
  intro k;cases k with
  | base k=>cases k <;> rfl
  | pay=>rfl
  | buf=>rfl

theorem save_run (i : BitTape) (w : List Bool) (p b : List (Fin g)) (out : List Bool) :
    UniformRun (processor C A) (wordState .savePayload i (w.map digit++[sep]) p b out) (w.length+1)
      (wordState .randomCons i [] ((w.map digit).reverse++p) b out) := by
  induction w generalizing p with
  | nil=>simpa only [List.length_nil,Nat.zero_add,List.map_nil,List.nil_append,List.reverse_nil] using
      uniform_step _ _ _ (save_end C A i p b out)
  | cons a w ih=>
    have hs:=uniform_step _ _ _ (save_step C A i a (w.map digit++[sep]) p b out)
    convert hs.trans (ih (digit a::p)) using 1 <;>
      simp only [List.length_cons,List.map_cons,List.reverse_cons,List.cons_append,List.append_assoc,
        List.nil_append]
    omega

theorem sample_step (i : BitTape) (m p b : List (Fin g)) (out : List Bool) (coin : Bool) :
    TypedStack.step (processor C A) (wordState .sample i (digit false::m) p b out) coin=
      wordState .sample i m p (digit coin::b) out := by
  unfold TypedStack.step
  simp only [wordState,Bool.false_eq_true,↓reduceIte,processor,List.head?_cons,↓reduceIte,move,BitTape.shift]
  apply wordState_ext <;> try rfl
  intro k;cases k with
  | base k=>cases k <;> rfl
  | pay=>rfl
  | buf=>rfl

theorem sample_run (i : BitTape) (bs : List Bool) (m p b : List (Fin g)) (out : List Bool) :
    TypedStack.run (processor C A)
      (wordState .sample i (List.replicate bs.length (digit false)++m) p b out) bs=
      wordState .sample i m p ((bs.map digit).reverse++b) out := by
  induction bs generalizing b with
  | nil=>simp only [List.length_nil,List.replicate_zero,List.nil_append,TypedStack.run,List.foldl_nil,
      List.map_nil,List.reverse_nil]
  | cons a bs ih=>
    simp only [List.length_cons,List.replicate_succ,List.cons_append,TypedStack.run_cons,sample_step,ih,
      List.map_cons,List.reverse_cons,List.append_assoc,List.nil_append]

theorem sample_end (i : BitTape) (m p b : List (Fin g)) (out : List Bool) (coin : Bool) :
    TypedStack.step (processor C A) (wordState .sample i (digit true::m) p b out) coin=
      wordState .sampleSep i m p b out := by
  unfold TypedStack.step
  simp only [wordState,Bool.false_eq_true,↓reduceIte,processor,List.head?_cons,
    Option.some.injEq,digit_eq_digit,Bool.true_eq_false,↓reduceIte,pop,BitTape.shift]
  apply wordState_ext <;> try rfl
  intro k;cases k with
  | base k=>cases k <;> rfl
  | pay=>rfl
  | buf=>rfl

 theorem pow_bits (b : ℕ) : (2^b).bits=List.replicate b false++[true] := by
  induction b with
  | zero=>rfl
  | succ b ih=>
    rw [pow_succ,show 2^b*2=Nat.bit false (2^b) from by simp [Nat.bit_val,Nat.mul_comm]]
    rw [Nat.bits_append_bit _ _ (fun hn=>False.elim ((pow_ne_zero b (by decide : (2:ℕ)≠0)) hn)),ih]
    simp only [List.replicate_succ,List.cons_append]

 theorem encodedNat (u : ℕ) : (trNat u).map FlatTM2.letters=u.bits.map digit := by
  rw [RawBits.trNat_bits,List.map_map]
  rfl
 theorem encodedList (u : ℕ) (xs : List ℕ) :
    (trList (u::xs)).map FlatTM2.letters=u.bits.map digit++sep::(trList xs).map FlatTM2.letters := by
  simp only [trList,List.map_append,List.map_cons,encodedNat]

end UniformKServer.UniformWrapper

end

end OAI
