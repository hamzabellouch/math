import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.Step2

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace Signed
lemma encode_length (z : ℤ) : (encode z).length=z.natAbs.size+1 := by
  simp only [encode,List.length_cons,Nat.size_eq_bits_len]
lemma natSize_add (a b : ℕ) : (a+b).size ≤ a.size+b.size+1 := by
  apply Nat.size_le.mpr
  have ha : a<2^(a.size+b.size) := (Nat.lt_size_self a).trans_le
    (Nat.pow_le_pow_right (by decide) (Nat.le_add_right _ _))
  have hb : b<2^(a.size+b.size) := (Nat.lt_size_self b).trans_le
    (Nat.pow_le_pow_right (by decide) (Nat.le_add_left _ _))
  calc
    a+b < 2^(a.size+b.size)+2^(a.size+b.size) := Nat.add_lt_add ha hb
    _ = 2^(a.size+b.size+1) := by rw [pow_succ]; omega
lemma encode_add_length (a b : ℤ) :
    (encode (a+b)).length ≤ (encode a).length+(encode b).length := by
  simp only [encode_length]
  have h := (Nat.size_le_size (Int.natAbs_add_le a b)).trans (natSize_add a.natAbs b.natAbs)
  omega
lemma encode_sum_length (xs : List ℤ) :
    (encode xs.sum).length ≤ 1+((xs.map encode).map List.length).sum := by
  induction xs with
  | nil => decide
  | cons x xs ih =>
    simp only [List.sum_cons,List.map_cons]
    have h := encode_add_length x xs.sum
    omega
end Signed
namespace WordList
lemma length_encode_take (xs : List (List Bool)) (n : ℕ) :
    (encode (xs.take n)).length ≤ (encode xs).length := by
  have h := length_encode_append (xs.take n) (xs.drop n)
  rw [List.take_append_drop] at h
  omega
end WordList
namespace IntegerArray

def encode (xs : List ℤ) : List Bool := WordList.encode (xs.map Signed.encode)
def addOp (x : List Bool) : List Bool := Signed.encode
  (Signed.decode (extractPrefix (discardPrefix x))+Signed.decode (discardPrefix (discardPrefix x)))
noncomputable def addOp_computes : PolyComputes addOp := discardPrefix_computes.comp Signed.add_computes
lemma fold_add (xs : List ℤ) (a : ℤ) (ctx : List Bool) :
    (xs.map Signed.encode).foldl (WordList.Fold.operation addOp ctx) (Signed.encode a)=
      Signed.encode (a+xs.sum) := by
  induction xs generalizing a with
  | nil => simp only [List.map_nil,List.foldl_nil,List.sum_nil,add_zero]
  | cons x xs ih =>
    simp only [List.map_cons,List.foldl_cons,WordList.Fold.operation,addOp,
      extractPrefix_pairBits,discardPrefix_pairBits,Signed.encode_decode,ih,List.sum_cons]
    congr 1
    ring

noncomputable def sumWords (x : List Bool) : List Bool :=
  WordList.Fold.run addOp (4*Polynomial.X+4) (WordList.Fold.pack x [] (Signed.encode 0))
noncomputable def sumWords_computes : PolyComputes sumWords :=
  (WordList.Fold.pack_computes id_computes (const_computes []) (const_computes (Signed.encode 0))).comp
    (WordList.Fold.run_computes addOp_computes (4*Polynomial.X+4))
lemma sumWords_encode (xs : List ℤ) : sumWords (encode xs)=Signed.encode xs.sum := by
  unfold sumWords encode
  rw [WordList.Fold.run_encode addOp (4*Polynomial.X+4) [] (Signed.encode 0)
    (xs.map Signed.encode) (1+(WordList.encode (xs.map Signed.encode)).length)]
  · simpa only [zero_add] using fold_add xs 0 []
  · intro n
    rw [←List.map_take,fold_add,zero_add]
    have hs := Signed.encode_sum_length (xs.take n)
    have hl := WordList.length_encode (xs.take n |>.map Signed.encode)
    have ht := WordList.length_encode_take (xs.map Signed.encode) n
    rw [←List.map_take] at ht
    omega
  · simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,
      WordList.Fold.length_pack,List.length_nil,Nat.mul_zero,Nat.add_zero]
    omega
noncomputable def sum : Turing.TM2ComputableInPolyTime encode Signed.encode List.sum :=
  sumWords_computes.reencode _ _ sumWords_encode

def encodePairs (xs : List (ℤ×ℤ)) : List Bool :=
  WordList.encode (xs.map (fun p=>pairBits (Signed.encode p.1,Signed.encode p.2)))
def mulOp (x : List Bool) : List Bool := Signed.encode
  (Signed.decode (extractPrefix (discardPrefix x))*Signed.decode (discardPrefix (discardPrefix x)))
noncomputable def mulOp_computes : PolyComputes mulOp := discardPrefix_computes.comp Signed.mul_computes

noncomputable def dotWords : List Bool → List Bool :=
  sumWords ∘ ((WordList.mapWith mulOp) ∘ (fun x=>pairBits ([],x)))
noncomputable def mappedProducts_computes : PolyComputes (WordList.mapWith mulOp) :=
  WordList.mapWith_computes (f:=mulOp) mulOp_computes
noncomputable def prefixEmpty_computes : PolyComputes (fun x=>pairBits ([],x)) :=
  PolyComputes.pair (f:=fun _=>[]) (g:=id) (const_computes []) id_computes
noncomputable def productsWords_computes :
    PolyComputes ((WordList.mapWith mulOp) ∘ (fun x=>pairBits ([],x))) :=
  PolyComputes.comp (f:=fun x=>pairBits ([],x)) (g:=WordList.mapWith mulOp)
    prefixEmpty_computes mappedProducts_computes
noncomputable def dotWords_computes : PolyComputes dotWords :=
  PolyComputes.comp (f:=((WordList.mapWith mulOp) ∘ (fun x=>pairBits ([],x))))
    (g:=sumWords) productsWords_computes sumWords_computes
lemma dotWords_encode (xs : List (ℤ×ℤ)) :
    dotWords (encodePairs xs)=Signed.encode (xs.map (fun p=>p.1*p.2)).sum := by
  simp only [dotWords,Function.comp_apply,encodePairs,WordList.mapWith_encode,List.map_map,Function.comp_def,mulOp,
    discardPrefix_pairBits,extractPrefix_pairBits,Signed.encode_decode]
  simpa only [encode,List.map_map,Function.comp_def] using sumWords_encode (xs.map (fun p=>p.1*p.2))
noncomputable def dot : Turing.TM2ComputableInPolyTime encodePairs Signed.encode
    (fun xs=>(xs.map (fun p=>p.1*p.2)).sum) :=
  dotWords_computes.reencode _ _ dotWords_encode
end IntegerArray
end MetricKMedianRecovery.BitMachine

end OAI
