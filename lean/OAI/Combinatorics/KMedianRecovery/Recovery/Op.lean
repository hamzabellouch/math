import Mathlib
import OAI.Combinatorics.KMedianRecovery.Encoding.Encode

namespace OAI

namespace MetricKMedianRecovery.BitMachine

section
open WordOperations
namespace WordList
lemma length_encode_reverse (xs : List (List Bool)) : (encode xs.reverse).length=(encode xs).length := by
  simp only [length_encode,List.map_reverse,List.sum_reverse,List.length_reverse]
lemma length_encode_zip (xs ys : List (List Bool)) :
    (encode ((xs.zip ys).map pairBits)).length ≤ 2*(encode xs).length+(encode ys).length := by
  induction xs generalizing ys with
  | nil => simp only [List.zip_nil_left,List.map_nil,encode,List.length_nil,Nat.zero_le]
  | cons x xs ih =>
    cases ys with
    | nil => simp only [List.zip_nil_right,List.map_nil,encode,List.length_nil,Nat.zero_le]
    | cons y ys =>
      simp only [List.zip_cons_cons,List.map_cons,encode,length_cons,pairBits_length]
      have h := ih ys
      omega
namespace Zip

def op (x : List Bool) : List Bool :=
  let a := discardPrefix (discardPrefix x)
  let ys := extractPrefix a
  let os := discardPrefix a
  if ys=[] then a else pairBits (WordList.tail ys,cons (pairBits (extractPrefix (discardPrefix x),head ys)) os)
noncomputable def op_computes : PolyComputes op := by
  let a : PolyComputes (fun x=>discardPrefix (discardPrefix x)) := discardPrefix_computes.comp discardPrefix_computes
  let ys : PolyComputes (fun x=>extractPrefix (discardPrefix (discardPrefix x))) := a.comp extractPrefix_computes
  let os : PolyComputes (fun x=>discardPrefix (discardPrefix (discardPrefix x))) := a.comp discardPrefix_computes
  have hh := ys.comp isEmpty_computes
  have hv := (discardPrefix_computes.comp extractPrefix_computes).pair (ys.comp head_computes)
  have ht := (ys.comp tail_computes).pair (cons_computes hv os)
  unfold op
  simpa only [Function.comp_def,decide_eq_true_eq] using hh.cond a ht
lemma op_nil (w : List Bool) (os : List (List Bool)) :
    Fold.operation op [] (pairBits (encode [],encode os)) w=pairBits (encode [],encode os) := by
  simp only [Fold.operation,op,extractPrefix_pairBits,discardPrefix_pairBits,encode,ite_true]
lemma op_cons (w y : List Bool) (ys os : List (List Bool)) :
    Fold.operation op [] (pairBits (encode (y::ys),encode os)) w=
      pairBits (encode ys,encode (pairBits (w,y)::os)) := by
  simp only [Fold.operation,op,extractPrefix_pairBits,discardPrefix_pairBits,encode,cons_ne_nil,ite_false,
    tail_cons,head_cons]
lemma fold_eq (xs ys os : List (List Bool)) :
    xs.foldl (Fold.operation op []) (pairBits (encode ys,encode os))=
      pairBits (encode (ys.drop xs.length),encode (((xs.zip ys).map pairBits).reverse++os)) := by
  induction xs generalizing ys os with
  | nil => simp only [List.foldl_nil,List.length_nil,List.drop_zero,List.zip_nil_left,List.map_nil,
      List.reverse_nil,List.nil_append]
  | cons x xs ih =>
    rw [List.foldl_cons]
    cases ys with
    | nil =>
      rw [op_nil,ih]
      simp only [List.drop_nil,List.zip_nil_right,List.map_nil,List.reverse_nil,List.nil_append]
    | cons y ys =>
      rw [op_cons,ih]
      simp only [List.length_cons,List.drop_succ_cons,List.zip_cons_cons,List.map_cons,List.reverse_cons,
        List.append_assoc,List.singleton_append]

noncomputable def run (x : List Bool) : List Bool := reverse (discardPrefix
  (Fold.run op (4*Polynomial.X+4) (Fold.pack (extractPrefix x) [] (pairBits (discardPrefix x,[])))))
noncomputable def run_computes : PolyComputes run := by
  have ha : PolyComputes (fun x=>pairBits (discardPrefix x,[])) := discardPrefix_computes.pair (const_computes [])
  have hi := Fold.pack_computes extractPrefix_computes (const_computes []) ha
  have hf := hi.comp (Fold.run_computes op_computes (4*Polynomial.X+4))
  exact (hf.comp discardPrefix_computes).comp reverse_computes
lemma run_encode (xs ys : List (List Bool)) :
    run (pairBits (encode xs,encode ys))=encode ((xs.zip ys).map pairBits) := by
  unfold run
  rw [extractPrefix_pairBits,discardPrefix_pairBits]
  change reverse (discardPrefix (Fold.run op _ (Fold.pack (encode xs) [] (pairBits (encode ys,encode [])))))=_
  rw [Fold.run_encode op (4*Polynomial.X+4) [] (pairBits (encode ys,encode [])) xs
    (2*(encode xs).length+3*(encode ys).length+1)]
  · rw [fold_eq,discardPrefix_pairBits,List.append_nil,reverse_encode,List.reverse_reverse]
  · intro n
    rw [fold_eq,List.append_nil,pairBits_length]
    dsimp only
    have hd := length_encode_drop ys (xs.take n).length
    have hz := length_encode_zip (xs.take n) ys
    have ht := length_encode_take xs n
    rw [length_encode_reverse]
    omega
  · simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,
      Fold.length_pack,List.length_nil,Nat.mul_zero,Nat.add_zero,pairBits_length,encode]
    omega
end Zip
end WordList
namespace IntegerArray
noncomputable def dotListsWords : List Bool → List Bool := dotWords ∘ WordList.Zip.run
noncomputable def dotListsWords_computes : PolyComputes dotListsWords := WordList.Zip.run_computes.comp dotWords_computes
lemma dotListsWords_encode (xs ys : List ℤ) :
    dotListsWords (pairBits (encode xs,encode ys))=Signed.encode ((xs.zip ys).map (fun p=>p.1*p.2)).sum := by
  simp only [dotListsWords,Function.comp_apply,encode,WordList.Zip.run_encode,List.zip_map,List.map_map,Function.comp_def]
  exact dotWords_encode _
noncomputable def dotLists : Turing.TM2ComputableInPolyTime
    (fun p : List ℤ×List ℤ=>pairBits (encode p.1,encode p.2)) Signed.encode
    (fun p=>((p.1.zip p.2).map (fun q=>q.1*q.2)).sum) :=
  dotListsWords_computes.reencode _ _ (fun p=>dotListsWords_encode p.1 p.2)
end IntegerArray
end
open WordOperations BinaryArithmetic
namespace WordList
lemma encode_le_bound (ws : List (List Bool)) (B : ℕ) (hB : ∀ w∈ws,w.length ≤ B) :
    (encode ws).length ≤ ws.length*(2*B+2) := by
  induction ws with
  | nil => simp only [encode,List.length_nil,Nat.zero_mul,Nat.le_refl]
  | cons w ws ih =>
    have hw := hB w (List.mem_cons_self ..)
    have ht := ih (fun x hx=>hB x (List.mem_cons_of_mem _ hx))
    simp only [encode,length_cons,List.length_cons]
    nlinarith
namespace Indices

def op (x : List Bool) : List Bool :=
  let a := discardPrefix (discardPrefix x)
  pairBits ((value (extractPrefix a)+1).bits,cons (extractPrefix a) (discardPrefix a))
noncomputable def op_computes : PolyComputes op := by
  let a : PolyComputes (fun x=>discardPrefix (discardPrefix x)) := discardPrefix_computes.comp discardPrefix_computes
  let l := a.comp extractPrefix_computes
  let r := a.comp discardPrefix_computes
  have hi := NatOps.add l (const_computes [true])
  have hh := hi.pair (cons_computes l r)
  unfold op
  simpa only [Function.comp_def,value,Bool.toNat_true,Nat.mul_zero,Nat.add_zero] using hh
lemma op_pair (w : List Bool) (a : ℕ) (os : List (List Bool)) :
    Fold.operation op [] (pairBits (a.bits,encode os)) w=
      pairBits ((a+1).bits,encode (a.bits::os)) := by
  simp only [Fold.operation,op,discardPrefix_pairBits,extractPrefix_pairBits,value_bits,encode]
lemma fold_eq (ws os : List (List Bool)) (a : ℕ) :
    ws.foldl (Fold.operation op []) (pairBits (a.bits,encode os))=
      pairBits ((a+ws.length).bits,encode ((List.range' a ws.length |>.map Nat.bits).reverse++os)) := by
  induction ws generalizing a os with
  | nil => simp only [List.foldl_nil,List.length_nil,Nat.add_zero,List.range'_zero,List.map_nil,
      List.reverse_nil,List.nil_append]
  | cons w ws ih =>
    rw [List.foldl_cons,op_pair,ih]
    simp only [List.length_cons,List.range'_succ,List.map_cons,List.reverse_cons,List.append_assoc,
      List.singleton_append,Nat.add_assoc,Nat.add_comm 1]
lemma bits_length_le (n : ℕ) : n.bits.length ≤ n := by
  rw [Nat.size_eq_bits_len]
  exact Nat.size_le.mpr Nat.lt_two_pow_self
lemma range_length (n : ℕ) : (encode ((List.range' 0 n).map Nat.bits)).length ≤ n*(2*n+2) := by
  have hh := encode_le_bound ((List.range' 0 n).map Nat.bits) n (by
    intro w hw
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hw
    have hh := (List.mem_range'_1.mp hi).2
    exact (bits_length_le i).trans (by omega))
  simpa only [List.length_map,List.length_range'] using hh

noncomputable def run (x : List Bool) : List Bool := reverse (discardPrefix
  (Fold.run op (20*(Polynomial.X+1)^2) (Fold.pack x [] (pairBits (Nat.bits 0,encode [])))))
noncomputable def run_computes : PolyComputes run := by
  have hi := Fold.pack_computes id_computes (const_computes [])
    (const_computes (pairBits (Nat.bits 0,encode [])))
  have hf := hi.comp (Fold.run_computes op_computes (20*(Polynomial.X+1)^2))
  exact (hf.comp discardPrefix_computes).comp reverse_computes
lemma run_encode (ws : List (List Bool)) : run (encode ws)=encode ((List.range ws.length).map Nat.bits) := by
  unfold run
  rw [Fold.run_encode op (20*(Polynomial.X+1)^2) [] (pairBits (Nat.bits 0,encode [])) ws
    (2*ws.length+1+ws.length*(2*ws.length+2))]
  · rw [fold_eq,discardPrefix_pairBits,List.append_nil,reverse_encode,List.reverse_reverse,List.range_eq_range']
  · intro n
    rw [fold_eq,Nat.zero_add,List.append_nil,pairBits_length]
    dsimp only
    rw [length_encode_reverse]
    have hb := bits_length_le (ws.take n).length
    have hr := range_length (ws.take n).length
    have hl : (ws.take n).length ≤ ws.length := by simp only [List.length_take]; omega
    nlinarith
  · simp only [Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_pow,Polynomial.eval_add,
      Polynomial.eval_X,Polynomial.eval_one,Fold.length_pack,List.length_nil,Nat.mul_zero,Nat.add_zero]
    have hw := length_le_encode ws
    have hsq := Nat.mul_le_mul hw hw
    nlinarith [Nat.zero_le ((pairBits (Nat.bits 0, encode [])).length)]
end Indices
end WordList
end MetricKMedianRecovery.BitMachine

end OAI
