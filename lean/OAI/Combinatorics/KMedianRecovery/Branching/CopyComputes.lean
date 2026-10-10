import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.Op

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace UnaryResources
noncomputable def copy_computes {f g : List Bool → List Bool} (hf : PolyComputes f) (hg : PolyComputes g) :
    PolyComputes (fun x=>RepeatedAppend.copies (f x).length (g x)) := by
  have hh := (hf.pair hg).comp RepeatedAppend.run_computes
  simpa only [Function.comp_def,RepeatedAppend.run_pair] using hh
lemma copies_replicate (a b : ℕ) (v : Bool) :
    RepeatedAppend.copies a (List.replicate b v)=List.replicate (a*b) v := by
  induction a with
  | zero => simp only [RepeatedAppend.copies,Nat.zero_mul,List.replicate_zero]
  | succ a ih => rw [RepeatedAppend.copies,ih,←List.replicate_add]; congr 1; ring

noncomputable def cap : PolynomialCounter (2*Polynomial.X+2) := PolynomialCounter.choose _
lemma cap_length (x : List Bool) : (cap.word x).length=2*x.length+2 := by
  rw [cap.word_length]
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X]
def inc (x : List Bool) : List Bool := (value x+1).bits
noncomputable def inc_computes : PolyComputes inc := by
  change PolyComputes (fun x=>(value x+1).bits)
  have hh := NatOps.add id_computes (const_computes (1:ℕ).bits)
  simpa only [inc,Function.comp_def,id_eq,value_bits] using hh
lemma inc_iter (j : ℕ) : inc^[j] (0:ℕ).bits=j.bits := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply',ih]; simp only [inc,value_bits]
noncomputable def lengthBits (x : List Bool) : List Bool :=
  BoundedIteration.run inc (pairBits (x,pairBits (cap.word x,(0:ℕ).bits)))
noncomputable def lengthBits_computes : PolyComputes lengthBits :=
  (id_computes.pair (cap.computes.pair (const_computes (0:ℕ).bits))).comp
    (BoundedIteration.run_computes inc_computes)
lemma lengthBits_eq (x : List Bool) : lengthBits x=x.length.bits := by
  unfold lengthBits
  rw [BoundedIteration.run_eq,inc_iter]
  intro j hj
  rw [inc_iter,cap_length]
  exact (WordList.Indices.bits_length_le j).trans (by omega)

def triple (x : List Bool) : List Bool := (3*value x).bits
noncomputable def triple_computes : PolyComputes triple := by
  change PolyComputes (fun x=>(3*value x).bits)
  have hh := NatOps.mul (const_computes (3:ℕ).bits) id_computes
  simpa only [triple,Function.comp_def,id_eq,value_bits] using hh
lemma triple_iter (j : ℕ) : triple^[j] (1:ℕ).bits=(3^j).bits := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply',ih]; simp only [triple,value_bits,pow_succ']
lemma three_power_length (j : ℕ) : (3^j).bits.length≤2*j+1 := by
  rw [Nat.size_eq_bits_len]
  apply Nat.size_le.mpr
  calc
    3^j ≤ (2^2)^j := Nat.pow_le_pow_left (by norm_num) j
    _ = 2^(2*j) := by rw [pow_mul]
    _ < 2^(2*j+1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
noncomputable def threePower (x : List Bool) : List Bool :=
  BoundedIteration.run triple (pairBits (x,pairBits (cap.word x,(1:ℕ).bits)))
noncomputable def threePower_computes : PolyComputes threePower :=
  (id_computes.pair (cap.computes.pair (const_computes (1:ℕ).bits))).comp
    (BoundedIteration.run_computes triple_computes)
lemma threePower_eq (x : List Bool) : threePower x=(3^x.length).bits := by
  unfold threePower
  rw [BoundedIteration.run_eq,triple_iter]
  intro j hj
  rw [triple_iter,cap_length]
  exact (three_power_length j).trans (by omega)
end UnaryResources
namespace WordList
lemma encode_append (ws vs : List (List Bool)) : encode (ws++vs)=encode ws++encode vs := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp only [List.cons_append,encode,cons,pairBits,ih,List.cons_append,List.append_assoc]
lemma copies_encode (n : ℕ) (w : List Bool) :
    RepeatedAppend.copies n (encode [w])=encode (List.replicate n w) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [RepeatedAppend.copies,ih,←encode_append,←List.replicate_succ']

def repeatWords (x : List Bool) : List Bool :=
  RepeatedAppend.copies (extractPrefix x).length (encode [discardPrefix x])
noncomputable def repeatWords_computes : PolyComputes repeatWords :=
  UnaryResources.copy_computes extractPrefix_computes
    (cons_computes discardPrefix_computes (const_computes []))
lemma repeatWords_pair (u w : List Bool) : repeatWords (pairBits (u,w))=
    encode (List.replicate u.length w) := by
  simp only [repeatWords,extractPrefix_pairBits,discardPrefix_pairBits,copies_encode]
lemma repeatWords_ofFn (n : ℕ) (w : List Bool) : repeatWords (pairBits (List.replicate n true,w))=
    encode (List.ofFn (fun _ : Fin n=>w)) := by
  rw [repeatWords_pair,List.length_replicate,List.ofFn_const]
end WordList
end MetricKMedianRecovery.BitMachine

end OAI
