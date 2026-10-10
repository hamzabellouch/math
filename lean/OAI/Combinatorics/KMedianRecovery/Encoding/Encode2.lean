import Mathlib
import OAI.Combinatorics.KMedianRecovery.Machines.LoopInput
import OAI.Combinatorics.KMedianRecovery.Recovery.Iterate

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace BinaryRational
lemma encode_length (q : ℚ) : (encode q).length=2*(q.num.natAbs.size+1)+1+q.den.size := by
  simp only [encode,pairBits_length,Signed.encode_length,←Nat.size_eq_bits_len]
lemma encode_height {q : ℚ} {b : ℕ} (hq : RationalHeight.Height q b) :
    (encode q).length≤3*b+6 := by
  have hn := Nat.size_le_size hq.1
  have hd := Nat.size_le_size hq.2
  rw [Nat.size_pow] at hn hd
  rw [encode_length]
  omega
lemma input_height (q : ℚ) : RationalHeight.Height q (encode q).length := by
  rw [encode_length]
  constructor
  · apply Nat.le_of_lt
    apply Nat.size_le.mp
    omega
  · apply Nat.le_of_lt
    apply Nat.size_le.mp
    omega
end BinaryRational
namespace RationalArray
open RationalHeight
def encode (xs : List ℚ) : List Bool := WordList.encode (xs.map BinaryRational.encode)
lemma input_height (xs : List ℚ) (q : ℚ) (hq : q∈xs) : Height q (encode xs).length := by
  exact (BinaryRational.input_height q).mono
    (WordList.length_member_le_encode (List.mem_map.mpr ⟨q,hq,rfl⟩))
noncomputable def addOp : List Bool → List Bool := BinaryRational.addWords ∘ discardPrefix
noncomputable def addOp_computes : PolyComputes addOp := discardPrefix_computes.comp BinaryRational.addWords_computes
lemma fold_add (xs : List ℚ) (a : ℚ) (ctx : List Bool) :
    (xs.map BinaryRational.encode).foldl (WordList.Fold.operation addOp ctx) (BinaryRational.encode a)=
      BinaryRational.encode (a+xs.sum) := by
  induction xs generalizing a with
  | nil => simp only [List.map_nil,List.foldl_nil,List.sum_nil,add_zero]
  | cons x xs ih =>
    have hop : WordList.Fold.operation addOp ctx (BinaryRational.encode a) (BinaryRational.encode x)=
        BinaryRational.encode (a+x) := by
      simp only [WordList.Fold.operation,addOp,Function.comp_apply,discardPrefix_pairBits,BinaryRational.addWords_pair]
      rw [add_comm]
    rw [List.map_cons,List.foldl_cons,hop,ih,List.sum_cons,add_assoc]
noncomputable def sumInput (x : List Bool) : List Bool :=
  WordList.Fold.pack x [] (BinaryRational.encode 0)
noncomputable def sumInput_computes : PolyComputes sumInput :=
  WordList.Fold.pack_computes id_computes (const_computes []) (const_computes (BinaryRational.encode 0))
noncomputable def sumWords : List Bool → List Bool :=
  (WordList.Fold.run addOp (20*(Polynomial.X+1)^2)) ∘ sumInput
noncomputable def sumWords_computes : PolyComputes sumWords := sumInput_computes.comp
  (WordList.Fold.run_computes addOp_computes (20*(Polynomial.X+1)^2))
lemma sumWords_encode (xs : List ℚ) : sumWords (encode xs)=BinaryRational.encode xs.sum := by
  let L := (encode xs).length
  have hn : xs.length≤L := by
    simpa only [List.length_map,L,encode] using WordList.length_le_encode (xs.map BinaryRational.encode)
  unfold sumWords
  simp only [Function.comp_apply,sumInput,encode]
  rw [WordList.Fold.run_encode addOp (20*(Polynomial.X+1)^2) [] (BinaryRational.encode 0)
    (xs.map BinaryRational.encode) (3*(L*(L+1))+6)]
  · simpa only [zero_add] using fold_add xs 0 []
  · intro n
    rw [←List.map_take,fold_add,zero_add]
    have hh := list_sum (xs.take n) L (fun q hq=>input_height xs q (List.mem_of_mem_take hq))
    have ht : (xs.take n).length≤L := by simp only [List.length_take]; omega
    exact (BinaryRational.encode_height hh).trans (by gcongr)
  · have hs : L≤(WordList.Fold.pack (WordList.encode (xs.map BinaryRational.encode)) []
        (BinaryRational.encode 0)).length := by
      rw [WordList.Fold.length_pack]
      change L≤2*L+2*[].length+(BinaryRational.encode 0).length+2
      omega
    have hp := Nat.pow_le_pow_left (Nat.add_le_add_right hs 1) 2
    simp only [Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_pow,Polynomial.eval_add,
      Polynomial.eval_X,Polynomial.eval_one,List.length_nil,Nat.mul_zero,Nat.add_zero]
    change 2*L+3*(L*(L+1))+6+2≤_
    nlinarith
noncomputable def sum : Turing.TM2ComputableInPolyTime encode BinaryRational.encode List.sum :=
  sumWords_computes.reencode _ _ sumWords_encode

noncomputable def mulOp : List Bool → List Bool := BinaryRational.mulWords ∘ discardPrefix
noncomputable def mulOp_computes : PolyComputes mulOp := discardPrefix_computes.comp BinaryRational.mulWords_computes
def encodePairs (xs : List (ℚ×ℚ)) : List Bool :=
  WordList.encode (xs.map (fun p=>pairBits (BinaryRational.encode p.1,BinaryRational.encode p.2)))
noncomputable def dotWords : List Bool → List Bool :=
  sumWords ∘ ((WordList.mapWith mulOp) ∘ (fun x=>pairBits ([],x)))
noncomputable def dotWords_computes : PolyComputes dotWords :=
  (IntegerArray.prefixEmpty_computes.comp (WordList.mapWith_computes mulOp_computes)).comp sumWords_computes
lemma dotWords_encode (xs : List (ℚ×ℚ)) :
    dotWords (encodePairs xs)=BinaryRational.encode (xs.map (fun p=>p.1*p.2)).sum := by
  simp only [dotWords,Function.comp_apply,encodePairs,WordList.mapWith_encode,List.map_map,
    Function.comp_def,mulOp,discardPrefix_pairBits,BinaryRational.mulWords_pair]
  simpa only [encode,List.map_map,Function.comp_def] using sumWords_encode (xs.map (fun p=>p.1*p.2))
noncomputable def dotListsWords : List Bool → List Bool := dotWords ∘ WordList.Zip.run
noncomputable def dotListsWords_computes : PolyComputes dotListsWords := WordList.Zip.run_computes.comp dotWords_computes
lemma dotListsWords_encode (xs ys : List ℚ) :
    dotListsWords (pairBits (encode xs,encode ys))=BinaryRational.encode ((xs.zip ys).map (fun p=>p.1*p.2)).sum := by
  simp only [dotListsWords,Function.comp_apply,encode,WordList.Zip.run_encode,List.zip_map]
  simpa only [encodePairs,List.map_map,Function.comp_def,Prod.map] using dotWords_encode (xs.zip ys)
end RationalArray
attribute [irreducible] RationalArray.sumWords RationalArray.dotWords RationalArray.dotListsWords
namespace RationalMatrix
open WordList

def rowEncode {n : ℕ} (v : Fin n → ℚ) : List Bool := RationalArray.encode (List.ofFn v)
def encode {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) : List Bool :=
  WordList.encode (List.ofFn (fun i=>rowEncode (A i)))
lemma rowEncode_eq {n : ℕ} (v : Fin n → ℚ) :
    rowEncode v=WordList.encode (List.ofFn (fun i=>BinaryRational.encode (v i))) := by
  simp only [rowEncode,RationalArray.encode,List.map_ofFn,Function.comp_def]

def swapWords (x : List Bool) : List Bool := pairBits (discardPrefix x,extractPrefix x)
noncomputable def swapWords_computes : PolyComputes swapWords :=
  discardPrefix_computes.pair extractPrefix_computes
def columnOp : List Bool → List Bool := (WordList.mapWith Lookup.run) ∘ swapWords
noncomputable def columnMap_computes : PolyComputes (WordList.mapWith Lookup.run) :=
  mapWith_computes Lookup.run_computes
noncomputable def columnOp_computes : PolyComputes columnOp :=
  PolyComputes.comp (f:=swapWords) (g:=WordList.mapWith Lookup.run) swapWords_computes columnMap_computes
lemma columnOp_encode {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (j : Fin n) :
    columnOp (pairBits (encode A,j.val.bits))=rowEncode (fun i=>A i j) := by
  simp only [columnOp,Function.comp_apply,swapWords,discardPrefix_pairBits,extractPrefix_pairBits,encode,mapWith_ofFn,rowEncode_eq,
    lookup_ofFn]

noncomputable def matrixIndices (x : List Bool) : List Bool := pairBits (x,Indices.run x)
noncomputable def matrixIndices_computes : PolyComputes matrixIndices := id_computes.pair Indices.run_computes
noncomputable def transposeWords : List Bool → List Bool := (mapWith columnOp) ∘ matrixIndices
noncomputable def transposeMap_computes : PolyComputes (mapWith columnOp) := mapWith_computes columnOp_computes
noncomputable def transposeWords_computes : PolyComputes transposeWords :=
  PolyComputes.comp (f:=matrixIndices) (g:=mapWith columnOp) matrixIndices_computes transposeMap_computes
lemma transposeWords_encode {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) :
    transposeWords (encode A)=encode A.transpose := by
  simp only [transposeWords,Function.comp_apply,matrixIndices]
  have hi := indices_ofFn (fun i=>rowEncode (A i))
  change Indices.run (encode A)=_ at hi
  rw [hi,mapWith_ofFn]
  simp only [columnOp_encode]
  rfl

noncomputable def rightRowOp : List Bool → List Bool := (mapWith RationalArray.dotListsWords) ∘ swapWords
noncomputable def rightRowMap_computes : PolyComputes (mapWith RationalArray.dotListsWords) :=
  mapWith_computes RationalArray.dotListsWords_computes
noncomputable def rightRowOp_computes : PolyComputes rightRowOp :=
  PolyComputes.comp (f:=swapWords) (g:=mapWith RationalArray.dotListsWords)
    swapWords_computes rightRowMap_computes
lemma dotListsWords_ofFn {n : ℕ} (u v : Fin n → ℚ) :
    RationalArray.dotListsWords (pairBits (rowEncode u,rowEncode v))=BinaryRational.encode (∑ i,u i*v i) := by
  rw [rowEncode,rowEncode,RationalArray.dotListsWords_encode]
  congr 1
  have hz : ((List.ofFn u).zip (List.ofFn v)).map (fun p=>p.1*p.2)=List.ofFn (fun i=>u i*v i) := by
    apply List.ext_getElem
    · simp
    · intro i h₁ h₂
      simp only [List.getElem_map,List.getElem_zip,List.getElem_ofFn]
  rw [hz,List.sum_ofFn]
lemma rightRowOp_encode {n : ℕ} (B : Matrix (Fin n) (Fin n) ℚ) (u : Fin n → ℚ) :
    rightRowOp (pairBits (encode B.transpose,rowEncode u))=
      rowEncode (fun j=>∑ i,u i*B i j) := by
  simp only [rightRowOp,Function.comp_apply,swapWords,extractPrefix_pairBits,discardPrefix_pairBits]
  rw [encode,mapWith_ofFn]
  change WordList.encode (List.ofFn (fun j=>RationalArray.dotListsWords
    (pairBits (rowEncode u,rowEncode (fun i=>B i j)))))=_
  simp only [dotListsWords_ofFn]
  exact (rowEncode_eq _).symm
noncomputable def mulInput (x : List Bool) : List Bool :=
  pairBits (transposeWords (discardPrefix x),extractPrefix x)
noncomputable def mulInput_computes : PolyComputes mulInput := by
  unfold mulInput
  simpa only [Function.comp_def] using
    (PolyComputes.pair (f:=transposeWords ∘ discardPrefix) (g:=extractPrefix)
    (PolyComputes.comp (f:=discardPrefix) (g:=transposeWords)
      discardPrefix_computes transposeWords_computes) extractPrefix_computes)
noncomputable def mulWords : List Bool → List Bool := (mapWith rightRowOp) ∘ mulInput
noncomputable def mulMap_computes : PolyComputes (mapWith rightRowOp) := mapWith_computes rightRowOp_computes
noncomputable def mulWords_computes : PolyComputes mulWords :=
  PolyComputes.comp (f:=mulInput) (g:=mapWith rightRowOp) mulInput_computes mulMap_computes
lemma mulWords_encode {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℚ) :
    mulWords (pairBits (encode A,encode B))=encode (A*B) := by
  simp only [mulWords,Function.comp_apply,mulInput,extractPrefix_pairBits,discardPrefix_pairBits,transposeWords_encode]
  unfold encode
  rw [mapWith_ofFn]
  change WordList.encode (List.ofFn (fun i=>rightRowOp (pairBits (encode B.transpose,rowEncode (A i)))) )=_
  simp only [rightRowOp_encode]
  rfl
noncomputable def multiplication {n : ℕ} : Turing.TM2ComputableInPolyTime
    (fun p : Matrix (Fin n) (Fin n) ℚ × Matrix (Fin n) (Fin n) ℚ=>pairBits (encode p.1,encode p.2))
    encode (fun p=>p.1*p.2) :=
  mulWords_computes.reencode _ _ (fun p=>mulWords_encode p.1 p.2)
end RationalMatrix
end MetricKMedianRecovery.BitMachine

end OAI
