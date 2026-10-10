import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.Pack7

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace NaturalArray
open WordList
def encode (xs : List ℕ) : List Bool := WordList.encode (xs.map Nat.bits)
lemma product_le (xs : List ℕ) : xs.prod≤2^(xs.map (fun n=>n.bits.length)).sum := by
  induction xs with
  | nil => simp only [List.prod_nil,List.map_nil,List.sum_nil,pow_zero,Nat.le_refl]
  | cons x xs ih =>
    simp only [List.prod_cons,List.map_cons,List.sum_cons,pow_add]
    apply Nat.mul_le_mul _ ih
    have hh := BinarySubtraction.value_lt x.bits
    rw [value_bits] at hh
    exact hh.le
lemma product_length (xs : List ℕ) : xs.prod.bits.length≤(xs.map (fun n=>n.bits.length)).sum+1 := by
  rw [Nat.size_eq_bits_len]
  apply Nat.size_le.mpr
  apply (product_le xs).trans_lt
  exact Nat.pow_lt_pow_right (by norm_num) (by omega)
def mulOp (x : List Bool) : List Bool :=
  (value (extractPrefix (discardPrefix x))*value (discardPrefix (discardPrefix x))).bits
noncomputable def mulOp_computes : PolyComputes mulOp :=
  NatOps.mul (discardPrefix_computes.comp extractPrefix_computes) (discardPrefix_computes.comp discardPrefix_computes)
lemma fold_mul (xs : List ℕ) (a : ℕ) (ctx : List Bool) :
    (xs.map Nat.bits).foldl (Fold.operation mulOp ctx) a.bits=(a*xs.prod).bits := by
  induction xs generalizing a with
  | nil => simp only [List.map_nil,List.foldl_nil,List.prod_nil,mul_one]
  | cons x xs ih =>
    simp only [List.map_cons,List.foldl_cons,Fold.operation,mulOp,
      extractPrefix_pairBits,discardPrefix_pairBits,value_bits,ih,List.prod_cons]
    congr 1
    ring
noncomputable def productWords (x : List Bool) : List Bool :=
  Fold.run mulOp (4*Polynomial.X+4) (Fold.pack x [] (1:ℕ).bits)
noncomputable def productWords_computes : PolyComputes productWords :=
  (Fold.pack_computes id_computes (const_computes []) (const_computes (1:ℕ).bits)).comp
    (Fold.run_computes mulOp_computes (4*Polynomial.X+4))
lemma productWords_encode (xs : List ℕ) : productWords (encode xs)=xs.prod.bits := by
  unfold productWords encode
  rw [Fold.run_encode mulOp (4*Polynomial.X+4) [] (1:ℕ).bits (xs.map Nat.bits)
    (1+(WordList.encode (xs.map Nat.bits)).length)]
  · simp only [fold_mul,one_mul]
  · intro n
    rw [←List.map_take,fold_mul,one_mul]
    have hp := product_length (xs.take n)
    have hl := WordList.length_encode (xs.take n |>.map Nat.bits)
    have ht := WordList.length_encode_take (xs.map Nat.bits) n
    rw [←List.map_take] at ht
    simp only [List.map_map,Function.comp_def] at hl
    omega
  · simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,
      Fold.length_pack,List.length_nil,Nat.mul_zero,Nat.add_zero]
    omega

noncomputable def exponentiate (x : List Bool) : List Bool := productWords (repeatWords x)
noncomputable def exponentiate_computes : PolyComputes exponentiate := repeatWords_computes.comp productWords_computes
lemma exponentiate_pair (u : List Bool) (a : ℕ) : exponentiate (pairBits (u,a.bits))=(a^u.length).bits := by
  rw [exponentiate,repeatWords_pair]
  have he : WordList.encode (List.replicate u.length a.bits)=encode (List.replicate u.length a) := by
    simp only [encode,List.map_replicate]
  rw [he,productWords_encode,List.prod_replicate]

def nextOp : List Bool → List Bool := UnaryResources.inc ∘ discardPrefix
noncomputable def nextOp_computes : PolyComputes nextOp := discardPrefix_computes.comp UnaryResources.inc_computes
noncomputable def factorialWords (u : List Bool) : List Bool :=
  productWords (mapWith nextOp (pairBits ([],BinaryEllipsoidInitial.indices u)))
noncomputable def factorialWords_computes : PolyComputes factorialWords := by
  unfold factorialWords
  simpa only [Function.comp_def] using
    (PolyComputes.comp (f:=fun input=>pairBits ([],BinaryEllipsoidInitial.indices input))
      (g:=productWords ∘ mapWith nextOp)
      ((const_computes []).pair BinaryEllipsoidInitial.indices_computes)
      (PolyComputes.comp (f:=mapWith nextOp) (g:=productWords)
        (mapWith_computes nextOp_computes) productWords_computes))
lemma factorial_list (n : ℕ) : ((List.range n).map (fun i=>i+1)).prod=n.factorial := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.range_succ,List.map_append,List.prod_append,ih]; simp [Nat.factorial_succ,mul_comm]
lemma factorialWords_replicate (n : ℕ) : factorialWords (List.replicate n true)=n.factorial.bits := by
  simp only [factorialWords,BinaryEllipsoidInitial.indices,BinaryEllipsoidInitial.dummy,
    Function.comp_apply,repeatWords_pair,List.length_replicate,Indices.run_encode,List.length_replicate]
  rw [mapWith_encode]
  simp only [List.map_map,Function.comp_def,nextOp,discardPrefix_pairBits,UnaryResources.inc,value_bits]
  simpa only [encode,List.map_map,Function.comp_def,factorial_list] using
    productWords_encode ((List.range n).map (fun i=>i+1))

lemma bits_length_log (n : ℕ) (hn : n≠0) : n.bits.length=n.log2+1 := by
  rw [Nat.size_eq_bits_len]
  have hl := Nat.size_le.mpr (Nat.lt_log2_self (n:=n))
  have hh := (Nat.log2_lt hn).mpr (Nat.lt_size_self n)
  omega
noncomputable def unaryLog (x : List Bool) : List Bool :=
  if value x=0 then [true] else RepeatedAppend.copies (BinaryArithmetic.normalize x).length [true]
noncomputable def unaryLog_computes : PolyComputes unaryLog := by
  unfold unaryLog
  have hh := (NatOps.zero id_computes).cond (const_computes [true])
    (UnaryResources.copy_computes BinaryArithmetic.normalize_computes (const_computes [true]))
  simpa only [id_eq,decide_eq_true_eq] using hh
lemma unaryLog_bits (n : ℕ) : unaryLog n.bits=List.replicate (n.log2+1) true := by
  simp only [unaryLog,value_bits,BinaryArithmetic.normalize_eq_bits]
  by_cases hn : n=0
  · subst n; rfl
  · rw [ite_eq_right hn]
    change RepeatedAppend.copies n.bits.length (List.replicate 1 true)=_
    rw [UnaryResources.copies_replicate,Nat.mul_one,bits_length_log n hn]
end NaturalArray
end MetricKMedianRecovery.BitMachine

end OAI
