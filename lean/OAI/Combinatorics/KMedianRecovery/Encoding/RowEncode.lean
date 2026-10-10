import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.Op

namespace OAI

namespace MetricKMedianRecovery.BitMachine

attribute [local irreducible] WordList.mapWith WordList.Indices.run WordList.Lookup.run
  WordList.Fold.run IntegerArray.sumWords IntegerArray.dotWords IntegerArray.dotListsWords
open WordOperations BinaryArithmetic
namespace WordList
lemma lookup_ofFn {n : ℕ} (i : Fin n) (f : Fin n → List Bool) :
    Lookup.run (pairBits (i.val.bits,encode (List.ofFn f)))=f i := by
  rw [Lookup.run_encode]
  simp only [List.getElem?_ofFn,i.isLt,dite_eq_left,Option.getD_some]
lemma mapWith_ofFn {n : ℕ} (f : List Bool → List Bool) (d : List Bool) (g : Fin n → List Bool) :
    mapWith f (pairBits (d,encode (List.ofFn g)))=encode (List.ofFn (fun i=>f (pairBits (d,g i)))) := by
  rw [mapWith_encode,List.map_ofFn]
  rfl
lemma indices_ofFn {n : ℕ} (f : Fin n → List Bool) :
    Indices.run (encode (List.ofFn f))=encode (List.ofFn (fun i : Fin n=>i.val.bits)) := by
  rw [Indices.run_encode,List.length_ofFn]
  congr 1
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]
end WordList
namespace IntegerMatrix
open WordList

def rowEncode {n : ℕ} (v : Fin n → ℤ) : List Bool := IntegerArray.encode (List.ofFn v)
def encode {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : List Bool :=
  WordList.encode (List.ofFn (fun i=>rowEncode (A i)))
lemma rowEncode_eq {n : ℕ} (v : Fin n → ℤ) :
    rowEncode v=WordList.encode (List.ofFn (fun i=>Signed.encode (v i))) := by
  simp only [rowEncode,IntegerArray.encode,List.map_ofFn,Function.comp_def]

def swapWords (x : List Bool) : List Bool := pairBits (discardPrefix x,extractPrefix x)
noncomputable def swapWords_computes : PolyComputes swapWords :=
  discardPrefix_computes.pair extractPrefix_computes
def columnOp : List Bool → List Bool := (WordList.mapWith Lookup.run) ∘ swapWords
noncomputable def columnMap_computes : PolyComputes (WordList.mapWith Lookup.run) :=
  mapWith_computes Lookup.run_computes
noncomputable def columnOp_computes : PolyComputes columnOp :=
  PolyComputes.comp (f:=swapWords) (g:=WordList.mapWith Lookup.run) swapWords_computes columnMap_computes
lemma columnOp_encode {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (j : Fin n) :
    columnOp (pairBits (encode A,j.val.bits))=rowEncode (fun i=>A i j) := by
  simp only [columnOp,Function.comp_apply,swapWords,discardPrefix_pairBits,extractPrefix_pairBits,encode,mapWith_ofFn,rowEncode_eq,
    lookup_ofFn]

noncomputable def matrixIndices (x : List Bool) : List Bool := pairBits (x,Indices.run x)
noncomputable def matrixIndices_computes : PolyComputes matrixIndices := id_computes.pair Indices.run_computes
noncomputable def transposeWords : List Bool → List Bool := (mapWith columnOp) ∘ matrixIndices
noncomputable def transposeMap_computes : PolyComputes (mapWith columnOp) := mapWith_computes columnOp_computes
noncomputable def transposeWords_computes : PolyComputes transposeWords :=
  PolyComputes.comp (f:=matrixIndices) (g:=mapWith columnOp) matrixIndices_computes transposeMap_computes
lemma transposeWords_encode {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) :
    transposeWords (encode A)=encode A.transpose := by
  simp only [transposeWords,Function.comp_apply,matrixIndices]
  have hi := indices_ofFn (fun i=>rowEncode (A i))
  change Indices.run (encode A)=_ at hi
  rw [hi,mapWith_ofFn]
  simp only [columnOp_encode]
  rfl

noncomputable def rightRowOp : List Bool → List Bool := (mapWith IntegerArray.dotListsWords) ∘ swapWords
noncomputable def rightRowMap_computes : PolyComputes (mapWith IntegerArray.dotListsWords) :=
  mapWith_computes IntegerArray.dotListsWords_computes
noncomputable def rightRowOp_computes : PolyComputes rightRowOp :=
  PolyComputes.comp (f:=swapWords) (g:=mapWith IntegerArray.dotListsWords)
    swapWords_computes rightRowMap_computes
lemma dotListsWords_ofFn {n : ℕ} (u v : Fin n → ℤ) :
    IntegerArray.dotListsWords (pairBits (rowEncode u,rowEncode v))=Signed.encode (∑ i,u i*v i) := by
  rw [rowEncode,rowEncode,IntegerArray.dotListsWords_encode]
  congr 1
  have hz : ((List.ofFn u).zip (List.ofFn v)).map (fun p=>p.1*p.2)=List.ofFn (fun i=>u i*v i) := by
    apply List.ext_getElem
    · simp
    · intro i h₁ h₂
      simp only [List.getElem_map,List.getElem_zip,List.getElem_ofFn]
  rw [hz,List.sum_ofFn]
lemma rightRowOp_encode {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (u : Fin n → ℤ) :
    rightRowOp (pairBits (encode B.transpose,rowEncode u))=
      rowEncode (fun j=>∑ i,u i*B i j) := by
  simp only [rightRowOp,Function.comp_apply,swapWords,extractPrefix_pairBits,discardPrefix_pairBits]
  rw [encode,mapWith_ofFn]
  change WordList.encode (List.ofFn (fun j=>IntegerArray.dotListsWords
    (pairBits (rowEncode u,rowEncode (fun i=>B i j)))))=_
  simp only [dotListsWords_ofFn]
  exact (rowEncode_eq _).symm
noncomputable def mulInput (x : List Bool) : List Bool :=
  pairBits (transposeWords (discardPrefix x),extractPrefix x)
noncomputable def mulInput_computes : PolyComputes mulInput :=
  (discardPrefix_computes.comp transposeWords_computes).pair extractPrefix_computes
noncomputable def mulWords : List Bool → List Bool := (mapWith rightRowOp) ∘ mulInput
noncomputable def mulMap_computes : PolyComputes (mapWith rightRowOp) := mapWith_computes rightRowOp_computes
noncomputable def mulWords_computes : PolyComputes mulWords :=
  PolyComputes.comp (f:=mulInput) (g:=mapWith rightRowOp) mulInput_computes mulMap_computes
lemma mulWords_encode {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℤ) :
    mulWords (pairBits (encode A,encode B))=encode (A*B) := by
  simp only [mulWords,Function.comp_apply,mulInput,extractPrefix_pairBits,discardPrefix_pairBits,transposeWords_encode]
  unfold encode
  rw [mapWith_ofFn]
  change WordList.encode (List.ofFn (fun i=>rightRowOp (pairBits (encode B.transpose,rowEncode (A i)))) )=_
  simp only [rightRowOp_encode]
  rfl
noncomputable def multiplication {n : ℕ} : Turing.TM2ComputableInPolyTime
    (fun p : Matrix (Fin n) (Fin n) ℤ × Matrix (Fin n) (Fin n) ℤ=>pairBits (encode p.1,encode p.2))
    encode (fun p=>p.1*p.2) :=
  mulWords_computes.reencode _ _ (fun p=>mulWords_encode p.1 p.2)
end IntegerMatrix
end MetricKMedianRecovery.BitMachine

end OAI
