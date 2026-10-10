import Mathlib
import OAI.Combinatorics.KMedianRecovery.Encoding.CoupledEncode

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryLabel
open WordOperations WordList BinaryArithmetic RationalLeaves
open BinaryOpeningPayment (field field_computes field_encode)
noncomputable def makeLeaf (x : List Bool) : List Bool :=
  pairBits ((value (field 0 x)+1).bits,pairBits (parentWords (field 1 x),field 2 x))
noncomputable def makeLeaf_computes : PolyComputes makeLeaf := by
  have hi : PolyComputes (fun x=>(value (field 0 x)+1).bits) := by
    simpa only [value_bits] using NatOps.add (field_computes 0) (const_computes (1:ℕ).bits)
  exact hi.pair (((field_computes 1).comp parentWords_computes).pair (field_computes 2))
lemma makeLeaf_pack {m : ℕ} (key : ℕ) (i : Label (Fin m)) (s : ℚ) :
    makeLeaf (WordList.encode [key.bits,encode i,BinaryRational.encode s])=encode (leaf key (parent i) s) := by
  simp only [makeLeaf,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,value_bits,parentWords_encode]
  rfl
end MetricKMedianRecovery.BitMachine.BinaryLabel

namespace MetricKMedianRecovery.BitMachine.BinaryCoupled
open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge
open BinaryOpeningPayment (field field_computes field_encode)
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
noncomputable def advance (x : List Bool) : List Bool :=
  encode [field 0 (field 0 x),field 1 (field 0 x)++cons (field 1 x) [],field 2 (field 0 x),
    field 3 (field 0 x),field 4 (field 0 x),field 2 x,field 3 x]
noncomputable def advance_computes : PolyComputes advance :=
  list_computes [field 0 ∘ field 0,(fun x=>field 1 (field 0 x)++cons (field 1 x) []),field 2 ∘ field 0,
    field 3 ∘ field 0,field 4 ∘ field 0,field 2,field 3] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact ⟨(field_computes 0).comp (field_computes 0)⟩
    · exact ⟨((field_computes 0).comp (field_computes 1)).append (cons_computes (field_computes 1) (const_computes []))⟩
    · exact ⟨(field_computes 0).comp (field_computes 2)⟩
    · exact ⟨(field_computes 0).comp (field_computes 3)⟩
    · exact ⟨(field_computes 0).comp (field_computes 4)⟩
    · exact ⟨field_computes _⟩
    · exact ⟨field_computes _⟩)
lemma advance_pack {m : ℕ} (s : State (Fin m)) (G : List (Label (Fin m))) (T U : List (List (Label (Fin m)))) :
    advance (encode [stateBits s,labels G,historyBits T,historyBits U])=stateBits (advanceState s G T U) := by
  simp only [advance,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    stateBits,advanceState,historyBits_append,historyBits_cons]
  rfl

def leafPack {m : ℕ} (B : Finset (Label (Fin m))) (P : List (List (Label (Fin m)))) (lam : ℚ)
    (key : ℕ) (i : Label (Fin m)) (C : List (Label (Fin m))) (l u : ℚ) (T U : List (List (Label (Fin m)))) : List Bool :=
  encode [setBits B,historyBits P,BinaryRational.encode lam,key.bits,BinaryLabel.encode i,labels C,
    BinaryRational.encode l,BinaryRational.encode u,historyBits T,historyBits U]
noncomputable def endLeaf (j : ℕ) (x : List Bool) : List Bool := BinaryLabel.makeLeaf (encode [field 3 x,field 4 x,field j x])
noncomputable def endLeaf_computes (j : ℕ) : PolyComputes (endLeaf j) :=
  (cons_computes (field_computes 3) (cons_computes (field_computes 4) (cons_computes (field_computes j) (const_computes [])))).comp BinaryLabel.makeLeaf_computes
lemma endLeaf_pack {m : ℕ} (B : Finset (Label (Fin m))) (P : List (List (Label (Fin m)))) (lam : ℚ)
    (key : ℕ) (i : Label (Fin m)) (C : List (Label (Fin m))) (l u : ℚ) (T U : List (List (Label (Fin m)))) :
    endLeaf 6 (leafPack B P lam key i C l u T U)=BinaryLabel.encode (leaf key (parent i) l) ∧
    endLeaf 7 (leafPack B P lam key i C l u T U)=BinaryLabel.encode (leaf key (parent i) u) := by
  simp only [endLeaf,leafPack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,BinaryLabel.makeLeaf_pack,and_self]
noncomputable def leafBank (x : List Bool) : List Bool := BinaryFiniteContext.union (pairBits (field 0 x,cons (endLeaf 7 x) []))
noncomputable def leafBank_computes : PolyComputes leafBank := ((field_computes 0).pair (cons_computes (endLeaf_computes 7) (const_computes []))).comp BinaryFiniteContext.union_computes
noncomputable def leafPrefix (x : List Bool) : List Bool := field 1 x++cons (field 5 x++cons (endLeaf 7 x) []) []
noncomputable def leafPrefix_computes : PolyComputes leafPrefix := (field_computes 1).append
  (cons_computes ((field_computes 5).append (cons_computes (endLeaf_computes 7) (const_computes []))) (const_computes []))
noncomputable def leafResult (x : List Bool) : List Bool :=
  encode [leafBank x,leafPrefix x,pairBits (endLeaf 7 x,endLeaf 6 x),field 2 x,field 2 x,field 8 x,field 9 x]
noncomputable def leafResult_computes : PolyComputes leafResult :=
  list_computes [leafBank,leafPrefix,(fun x=>pairBits (endLeaf 7 x,endLeaf 6 x)),field 2,field 2,field 8,field 9] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact ⟨leafBank_computes⟩
    · exact ⟨leafPrefix_computes⟩
    · exact ⟨(endLeaf_computes 7).pair (endLeaf_computes 6)⟩
    all_goals exact ⟨field_computes _⟩)
lemma leafResult_pack {m : ℕ} (B : Finset (Label (Fin m))) (P : List (List (Label (Fin m)))) (lam : ℚ)
    (key : ℕ) (i : Label (Fin m)) (C : List (Label (Fin m))) (l u : ℚ) (T U : List (List (Label (Fin m)))) :
    leafResult (leafPack B P lam key i C l u T U)=stateBits (leafState B P lam key (parent i) C l u T U) := by
  obtain ⟨hl,hu⟩:=endLeaf_pack B P lam key i C l u T U
  unfold leafResult leafBank leafPrefix
  rw [hl,hu]
  simp only [leafPack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  change encode [BinaryFiniteContext.union (pairBits (setBits B,labels [leaf key (parent i) u])),_,_,_,_,_,_]=_
  rw [BinaryFiniteContext.union_list_pack]
  simp only [List.toFinset_cons,List.toFinset_nil,Finset.union_insert,Finset.union_empty,
    stateBits,leafState,historyBits_append,historyBits_cons,BinaryFiniteContext.labels_append,
    BinaryCorrection.encode]
  rfl
end MetricKMedianRecovery.BitMachine.BinaryCoupled

end OAI
