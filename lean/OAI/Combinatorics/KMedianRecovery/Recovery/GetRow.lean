import Mathlib
import OAI.Combinatorics.KMedianRecovery.Encoding.RowEncode

namespace OAI

namespace MetricKMedianRecovery.BitMachine
attribute [local irreducible] WordList.mapWith WordList.Indices.run WordList.Lookup.run
  WordList.Fold.run IntegerArray.sumWords IntegerArray.dotWords IntegerArray.dotListsWords
open WordOperations BinaryArithmetic
namespace IntegerMatrix
open WordList

def getRow : List Bool → List Bool := Lookup.run ∘ swapWords
noncomputable def getRow_computes : PolyComputes getRow := swapWords_computes.comp Lookup.run_computes
lemma getRow_encode {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) :
    getRow (pairBits (encode A,i.val.bits))=rowEncode (A i) := by
  simp only [getRow,Function.comp_apply,swapWords,extractPrefix_pairBits,discardPrefix_pairBits,
    encode,lookup_ofFn]

def entryInput (x : List Bool) : List Bool := pairBits (discardPrefix x,getRow (extractPrefix x))
noncomputable def entryInput_computes : PolyComputes entryInput :=
  discardPrefix_computes.pair (extractPrefix_computes.comp getRow_computes)
def getEntry : List Bool → List Bool := Lookup.run ∘ entryInput
noncomputable def getEntry_computes : PolyComputes getEntry := entryInput_computes.comp Lookup.run_computes
lemma getEntry_encode {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (i j : Fin n) :
    getEntry (pairBits (pairBits (encode A,i.val.bits),j.val.bits))=Signed.encode (A i j) := by
  simp only [getEntry,Function.comp_apply,entryInput,extractPrefix_pairBits,discardPrefix_pairBits,
    getRow_encode,rowEncode_eq,lookup_ofFn]

def diagInput (x : List Bool) : List Bool := pairBits (x,discardPrefix x)
noncomputable def diagInput_computes : PolyComputes diagInput := id_computes.pair discardPrefix_computes
def diagAt : List Bool → List Bool := getEntry ∘ diagInput
noncomputable def diagAt_computes : PolyComputes diagAt := diagInput_computes.comp getEntry_computes
lemma diagAt_encode {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) :
    diagAt (pairBits (encode A,i.val.bits))=Signed.encode (A i i) := by
  simp only [diagAt,Function.comp_apply,diagInput,discardPrefix_pairBits,getEntry_encode]

def contextMatrix (x : List Bool) : List Bool := extractPrefix (extractPrefix x)
def contextIndex (x : List Bool) : List Bool := discardPrefix (extractPrefix x)
noncomputable def contextMatrix_computes : PolyComputes contextMatrix := extractPrefix_computes.comp extractPrefix_computes
noncomputable def contextIndex_computes : PolyComputes contextIndex := extractPrefix_computes.comp discardPrefix_computes
def tailDiagInput (x : List Bool) : List Bool := pairBits (contextMatrix x,discardPrefix x)
noncomputable def tailDiagInput_computes : PolyComputes tailDiagInput := contextMatrix_computes.pair discardPrefix_computes
def tailDiagValue : List Bool → List Bool := diagAt ∘ tailDiagInput
noncomputable def tailDiagValue_computes : PolyComputes tailDiagValue := tailDiagInput_computes.comp diagAt_computes

def tailDiagOp (x : List Bool) : List Bool :=
  if value (discardPrefix x)≤value (contextIndex x) then Signed.encode 0 else tailDiagValue x
noncomputable def tailDiagOp_computes : PolyComputes tailDiagOp := by
  have hh := (NatOps.le discardPrefix_computes contextIndex_computes).cond
    (const_computes (Signed.encode 0)) tailDiagValue_computes
  unfold tailDiagOp
  simpa only [decide_eq_true_eq] using hh
lemma tailDiagOp_encode {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (i k : Fin n) :
    tailDiagOp (pairBits (pairBits (encode A,i.val.bits),k.val.bits))=
      Signed.encode (if i<k then A k k else 0) := by
  simp only [tailDiagOp,contextIndex,extractPrefix_pairBits,discardPrefix_pairBits,value_bits,
    tailDiagValue,Function.comp_apply,tailDiagInput,contextMatrix,diagAt_encode]
  split_ifs <;> try rfl
  all_goals omega

noncomputable def tailDiagMapInput (x : List Bool) : List Bool :=
  pairBits (x,Indices.run (extractPrefix x))
noncomputable def tailDiagMapInput_computes : PolyComputes tailDiagMapInput :=
  id_computes.pair (extractPrefix_computes.comp Indices.run_computes)
noncomputable def tailDiagMap : List Bool → List Bool := (mapWith tailDiagOp) ∘ tailDiagMapInput
noncomputable def tailDiagMap_computes : PolyComputes tailDiagMap :=
  tailDiagMapInput_computes.comp (mapWith_computes tailDiagOp_computes)
noncomputable def tailDiag : List Bool → List Bool := IntegerArray.sumWords ∘ tailDiagMap
noncomputable def tailDiag_computes : PolyComputes tailDiag := tailDiagMap_computes.comp IntegerArray.sumWords_computes
lemma tailDiag_encode {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) :
    tailDiag (pairBits (encode A,i.val.bits))=Signed.encode (∑ k∈Finset.Ioi i,A k k) := by
  have hi := indices_ofFn (fun i=>rowEncode (A i))
  change Indices.run (encode A)=_ at hi
  simp only [tailDiag,Function.comp_apply,tailDiagMap,tailDiagMapInput,extractPrefix_pairBits,hi,
    mapWith_ofFn,tailDiagOp_encode]
  have he := IntegerArray.sumWords_encode (List.ofFn (fun k : Fin n=>if i<k then A k k else 0))
  simp only [IntegerArray.encode,List.map_ofFn,Function.comp_def,List.sum_ofFn] at he
  rw [he]
  congr 1
  rw [←Finset.sum_filter]
  simp only [Finset.filter_lt_eq_Ioi]

noncomputable def negDiag : List Bool → List Bool :=
  (fun x=>Signed.encode (-Signed.decode x)) ∘ tailDiag ∘ extractPrefix
noncomputable def negDiag_computes : PolyComputes negDiag :=
  (extractPrefix_computes.comp tailDiag_computes).comp Signed.neg_computes
noncomputable def muEntry (x : List Bool) : List Bool :=
  if value (discardPrefix x)≤value (contextIndex x) then
    if value (contextIndex x)≤value (discardPrefix x) then negDiag x else Signed.encode 0
  else getEntry x
noncomputable def muEntry_computes : PolyComputes muEntry := by
  have hl := NatOps.le discardPrefix_computes contextIndex_computes
  have hr := NatOps.le contextIndex_computes discardPrefix_computes
  have hh := hl.cond (hr.cond negDiag_computes (const_computes (Signed.encode 0))) getEntry_computes
  unfold muEntry
  simpa only [decide_eq_true_eq] using hh

def mu {n : ℕ} (F : Matrix (Fin n) (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j=>if i<j then F i j else if i=j then -(∑ k∈Finset.Ioi i,F k k) else 0
lemma muEntry_encode {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (i j : Fin n) :
    muEntry (pairBits (pairBits (encode A,i.val.bits),j.val.bits))=Signed.encode (mu A i j) := by
  simp only [muEntry,contextIndex,extractPrefix_pairBits,discardPrefix_pairBits,value_bits,
    negDiag,Function.comp_apply,tailDiag_encode,Signed.encode_decode,getEntry_encode,mu]
  split_ifs <;> try rfl
  all_goals omega

noncomputable def muRow : List Bool → List Bool := (mapWith muEntry) ∘ tailDiagMapInput
noncomputable def muRow_computes : PolyComputes muRow :=
  tailDiagMapInput_computes.comp (mapWith_computes muEntry_computes)
lemma muRow_encode {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) :
    muRow (pairBits (encode A,i.val.bits))=rowEncode (mu A i) := by
  have hi := indices_ofFn (fun i=>rowEncode (A i))
  change Indices.run (encode A)=_ at hi
  simp only [muRow,Function.comp_apply,tailDiagMapInput,extractPrefix_pairBits,hi,mapWith_ofFn,muEntry_encode]
  exact (rowEncode_eq _).symm
noncomputable def muWords : List Bool → List Bool := (mapWith muRow) ∘ matrixIndices
noncomputable def muWords_computes : PolyComputes muWords := matrixIndices_computes.comp (mapWith_computes muRow_computes)
lemma muWords_encode {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : muWords (encode A)=encode (mu A) := by
  have hi := indices_ofFn (fun i=>rowEncode (A i))
  change Indices.run (encode A)=_ at hi
  simp only [muWords,Function.comp_apply,matrixIndices,hi,mapWith_ofFn,muRow_encode]
  rfl

lemma mu_mul {n : ℕ} (A F : Matrix (Fin n) (Fin n) ℤ) :
    mu F*A=BirdDet.Spec.stepEntry A F := by
  ext i j
  rw [Matrix.mul_apply,BirdDet.Spec.stepEntry_eq,Matrix.of_apply]
  simp only [mu,ite_mul,zero_mul]
  rw [Finset.sum_ite,Finset.sum_ite]
  have hn : (Finset.univ.filter fun k : Fin n=>i<k)=Finset.Ioi i := by ext k; simp
  rw [hn]
  have he : (Finset.univ.filter fun k : Fin n=>¬i<k).filter (fun k=>i=k)={i} := by
    ext k
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton]
    constructor
    · exact fun h=>h.2.symm
    · intro h
      subst k
      simp
  rw [he,Finset.sum_singleton,Finset.sum_const_zero,add_zero]
  exact add_comm _ _
noncomputable def stepInput (x : List Bool) : List Bool := pairBits (muWords (discardPrefix x),extractPrefix x)
noncomputable def stepInput_computes : PolyComputes stepInput :=
  (discardPrefix_computes.comp muWords_computes).pair extractPrefix_computes
noncomputable def stepWords (x : List Bool) : List Bool := mulWords (stepInput x)
noncomputable def stepWords_computes : PolyComputes stepWords := stepInput_computes.comp mulWords_computes
lemma stepWords_apply (x : List Bool) : stepWords x=mulWords (stepInput x) := rfl
lemma stepInput_pair (a f : List Bool) : stepInput (pairBits (a,f))=pairBits (muWords f,a) := by
  simp only [stepInput,discardPrefix_pairBits,extractPrefix_pairBits]
lemma stepWords_encode {n : ℕ} (A F : Matrix (Fin n) (Fin n) ℤ) :
    stepWords (pairBits (encode A,encode F))=encode (BirdDet.Spec.stepEntry A F) := by
  rw [stepWords_apply,stepInput_pair,muWords_encode,mulWords_encode,mu_mul]

end IntegerMatrix
end MetricKMedianRecovery.BitMachine

end OAI
