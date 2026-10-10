import Mathlib
import OAI.Combinatorics.KMedianRecovery.Machines.SuffixMachine
import OAI.Combinatorics.KMedianRecovery.Encoding.WordExtras

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryFiniteContext
open WordOperations WordList RationalLeaves BinaryArithmetic
noncomputable def containsItem (x : List Bool) : Bool := BinaryLabel.contains (pairBits (discardPrefix x,extractPrefix x))
noncomputable def containsItem_computes : PolyComputes (fun x=>[containsItem x]) :=
  (discardPrefix_computes.pair extractPrefix_computes).comp BinaryLabel.contains_computes
noncomputable def inter (x : List Bool) : List Bool :=
  BinaryLabel.sort (filterWith containsItem (pairBits (discardPrefix x,extractPrefix x)))
noncomputable def inter_computes : PolyComputes inter :=
  ((discardPrefix_computes.pair extractPrefix_computes).comp (filterWith_computes containsItem_computes)).comp BinaryLabel.sort_computes
lemma inter_pack {m : ℕ} (S T : Finset (Label (Fin m))) :
    inter (pairBits (setBits S,setBits T))=setBits (S∩T) := by
  simp only [inter,discardPrefix_pairBits,extractPrefix_pairBits,setBits,labels,filterWith_encode,List.filter_map,
    Function.comp_def,containsItem,discardPrefix_pairBits,extractPrefix_pairBits,BinaryLabel.contains_encode,
    BinaryLabel.sort_encode]
  apply congrArg (fun S : Finset (Label (Fin m))=>labels (BinaryLabel.orderedSort S))
  ext a
  simp only [List.mem_toFinset,List.mem_filter,decide_eq_true_eq,BinaryLabel.orderedSort,Finset.mem_sort,Finset.mem_inter]
lemma lengthBits_setBits {m : ℕ} (S : Finset (Label (Fin m))) : lengthBits (setBits S)=S.card.bits := by
  simp only [setBits,labels,lengthBits_encode,List.length_map,BinaryLabel.orderedSort,Finset.length_sort]
noncomputable def countInter : List Bool → List Bool := lengthBits ∘ inter
noncomputable def countInter_computes : PolyComputes countInter := inter_computes.comp lengthBits_computes
lemma countInter_pack {m : ℕ} (S T : Finset (Label (Fin m))) :
    countInter (pairBits (setBits S,setBits T))=(S∩T).card.bits := by
  simp only [countInter,Function.comp_apply,inter_pack,lengthBits_setBits]
end MetricKMedianRecovery.BitMachine.BinaryFiniteContext

namespace MetricKMedianRecovery.BitMachine.BinaryCross
open WordOperations WordList RationalLeaves BinaryArithmetic
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field field_computes field_encode)

def ctxBits {m : ℕ} (F Q : Finset (Label (Fin m))) (k : ℕ) : List Bool := encode [setBits F,setBits Q,k.bits]
def nodeBits {m : ℕ} (P : List (Label (Fin m)) × List (List (Label (Fin m)))) : List Bool :=
  pairBits (labels P.1,historyBits P.2)
def cf (n : ℕ) : List Bool → List Bool := field n ∘ extractPrefix
noncomputable def cf_computes (n : ℕ) : PolyComputes (cf n) := extractPrefix_computes.comp (field_computes n)
noncomputable def opened (x : List Bool) : List Bool := BinaryFiniteContext.union
  (pairBits (cf 1 x,extractPrefix (discardPrefix x)))
noncomputable def opened_computes : PolyComputes opened :=
  ((cf_computes 1).pair (discardPrefix_computes.comp extractPrefix_computes)).comp BinaryFiniteContext.union_computes
lemma opened_pack {m : ℕ} (F Q : Finset (Label (Fin m))) (k : ℕ)
    (H : List (Label (Fin m))) (T : List (List (Label (Fin m)))) :
    opened (pairBits (ctxBits F Q k,nodeBits (H,T)))=setBits (Q∪H.toFinset) := by
  simp only [opened,cf,Function.comp_apply,ctxBits,nodeBits,field_encode,extractPrefix_pairBits,discardPrefix_pairBits,
    List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,BinaryFiniteContext.union_list_pack]
noncomputable def paid (x : List Bool) : List Bool := BinaryFiniteContext.countInter (pairBits (opened x,cf 0 x))
noncomputable def paid_computes : PolyComputes paid :=
  (opened_computes.pair (cf_computes 0)).comp BinaryFiniteContext.countInter_computes
lemma paid_pack {m : ℕ} (F Q : Finset (Label (Fin m))) (k : ℕ)
    (H : List (Label (Fin m))) (T : List (List (Label (Fin m)))) :
    paid (pairBits (ctxBits F Q k,nodeBits (H,T)))=(CanonicalMergeCrossing.paid F Q H).bits := by
  rw [paid,opened_pack]
  simp only [cf,Function.comp_apply,ctxBits,field_encode,extractPrefix_pairBits,
    List.getElem?_cons_zero,Option.getD_some,BinaryFiniteContext.countInter_pack,CanonicalMergeCrossing.paid]
noncomputable def finalOpened (x : List Bool) : List Bool :=
  BinaryFiniteMachine.after (pairBits (opened x,discardPrefix (discardPrefix x)))
noncomputable def finalOpened_computes : PolyComputes finalOpened :=
  (opened_computes.pair (discardPrefix_computes.comp discardPrefix_computes)).comp BinaryFiniteMachine.after_computes
noncomputable def finalCount (x : List Bool) : List Bool := BinaryFiniteContext.countInter (pairBits (finalOpened x,cf 0 x))
noncomputable def finalCount_computes : PolyComputes finalCount :=
  (finalOpened_computes.pair (cf_computes 0)).comp BinaryFiniteContext.countInter_computes
lemma finalCount_pack {m : ℕ} (F Q : Finset (Label (Fin m))) (k : ℕ)
    (H : List (Label (Fin m))) (T : List (List (Label (Fin m)))) :
    finalCount (pairBits (ctxBits F Q k,nodeBits (H,T)))=(CanonicalMergeCrossing.finalCount F Q H T).bits := by
  rw [finalCount,finalOpened,opened_pack]
  simp only [nodeBits,discardPrefix_pairBits,cf,Function.comp_apply,ctxBits,
    field_encode,extractPrefix_pairBits,List.getElem?_cons_zero,Option.getD_some,
    BinaryFiniteMachine.after_pack,BinaryFiniteContext.countInter_pack,CanonicalMergeCrossing.finalCount]
end MetricKMedianRecovery.BitMachine.BinaryCross

namespace MetricKMedianRecovery.BitMachine.BinaryJump
open WordOperations WordList RationalLeaves CanonicalMergeRefinement BinaryArithmetic
open BinaryFiniteContext (labels setBits)
open BinaryOpeningPayment (field field_computes field_encode)
noncomputable def removedTail (x : List Bool) : List Bool :=
  Drop.run (pairBits ((value (lengthBits (field 3 x))-1).bits,field 4 x))
noncomputable def removedTail_computes : PolyComputes removedTail := by
  unfold removedTail
  have h:=NatOps.sub ((field_computes 3).comp lengthBits_computes) (const_computes (1:ℕ).bits)
  simpa only [Function.comp_def,value_bits] using (h.pair (field_computes 4)).comp Drop.run_computes
lemma removedTail_pack {m : ℕ} (F : Finset (Label (Fin m))) (R : List (Label (Fin m))) (key : ℕ)
    (H G : List (Label (Fin m))) : removedTail (ctxBits F R key H G)=labels (G.drop (H.length-1)) := by
  simp only [removedTail,ctxBits,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    labels,lengthBits_encode,List.length_map,value_bits,Drop.run_encode,←List.map_drop]
attribute [local irreducible] removedTail
noncomputable def addOp (x : List Bool) : List Bool := encode [(0:ℕ).bits,[],[],[],discardPrefix x]
noncomputable def addOp_computes : PolyComputes addOp := list_computes [fun _=>(0:ℕ).bits,fun _=>[],fun _=>[],fun _=>[],discardPrefix] (by
  intro f hf; refine Classical.choice ?_
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
  rcases hf with rfl|rfl|rfl|rfl|rfl
  · exact ⟨const_computes _⟩
  · exact ⟨const_computes _⟩
  · exact ⟨const_computes _⟩
  · exact ⟨const_computes _⟩
  · exact ⟨discardPrefix_computes⟩)
noncomputable def removeOp (x : List Bool) : List Bool :=
  encode [(1:ℕ).bits,jf 0 x,jf 2 x,removedTail (extractPrefix x),jf 1 x]
noncomputable def removeOp_computes : PolyComputes removeOp :=
  list_computes [fun _=>(1:ℕ).bits,jf 0,jf 2,removedTail ∘ extractPrefix,jf 1] (by
    intro f hf; refine Classical.choice ?_
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl|rfl
    · exact ⟨const_computes _⟩
    · exact ⟨jf_computes _⟩
    · exact ⟨jf_computes _⟩
    · exact ⟨extractPrefix_computes.comp removedTail_computes⟩
    · exact ⟨jf_computes _⟩)
noncomputable def replaceOp (x : List Bool) : List Bool := encode [(2:ℕ).bits,jf 0 x,jf 2 x,[],jf 1 x]
noncomputable def replaceOp_computes : PolyComputes replaceOp := list_computes [fun _=>(2:ℕ).bits,jf 0,jf 2,fun _=>[],jf 1] (by
  intro f hf; refine Classical.choice ?_
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
  rcases hf with rfl|rfl|rfl|rfl|rfl
  · exact ⟨const_computes _⟩
  · exact ⟨jf_computes _⟩
  · exact ⟨jf_computes _⟩
  · exact ⟨const_computes _⟩
  · exact ⟨jf_computes _⟩)
noncomputable def adds (x : List Bool) : List Bool := mapWith addOp (pairBits (x,field 1 x))
noncomputable def adds_computes : PolyComputes adds := by
  have addsComputes := (id_computes.pair (field_computes 1)).comp (mapWith_computes addOp_computes)
  unfold adds
  simpa only [Function.comp_def, id_eq] using addsComputes
noncomputable def removes (x : List Bool) : List Bool := mapWith removeOp (pairBits (x,Slices.run (field 3 x)))
noncomputable def removes_computes : PolyComputes removes := by
  have removesComputes :=
    (id_computes.pair ((field_computes 3).comp Slices.run_computes)).comp (mapWith_computes removeOp_computes)
  unfold removes
  simpa only [Function.comp_def, id_eq] using removesComputes
noncomputable def replaces (x : List Bool) : List Bool := mapWith replaceOp (pairBits (x,Slices.run (field 4 x)))
noncomputable def replaces_computes : PolyComputes replaces := by
  have replacesComputes :=
    (id_computes.pair ((field_computes 4).comp Slices.run_computes)).comp (mapWith_computes replaceOp_computes)
  unfold replaces
  simpa only [Function.comp_def, id_eq] using replacesComputes
noncomputable def candidates (x : List Bool) : List Bool := (adds x++removes x)++replaces x
noncomputable def candidates_computes : PolyComputes candidates := (adds_computes.append removes_computes).append replaces_computes
lemma adds_pack {m : ℕ} (F : Finset (Label (Fin m))) (R : List (Label (Fin m))) (key : ℕ)
    (H G : List (Label (Fin m))) : adds (ctxBits F R key H G)=encode ((R.map Jump.add).map jumpBits) := by
  simp only [adds,ctxBits,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    labels,mapWith_encode,List.map_map,addOp,Function.comp_def,discardPrefix_pairBits,jumpBits]
lemma removes_pack {m : ℕ} (F : Finset (Label (Fin m))) (R : List (Label (Fin m))) (key : ℕ)
    (H G : List (Label (Fin m))) : removes (ctxBits F R key H G)=
      encode (((cuts H).map (fun p=>Jump.remove p.1 p.2.2 (G.drop (H.length-1)) p.2.1)).map jumpBits) := by
  have hc : field 3 (ctxBits F R key H G)=labels H := by
    simp only [ctxBits,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  simp only [removes,hc,BinarySuffix.slices_labels,Slices.outBits,mapWith_encode,List.map_map,Function.comp_def,
    removeOp,jf,extractPrefix_pairBits,discardPrefix_pairBits,removedTail_pack,
    (BinarySuffix.cut_fields _).1,(BinarySuffix.cut_fields _).2.1,(BinarySuffix.cut_fields _).2.2,jumpBits]
lemma replaces_pack {m : ℕ} (F : Finset (Label (Fin m))) (R : List (Label (Fin m))) (key : ℕ)
    (H G : List (Label (Fin m))) : replaces (ctxBits F R key H G)=
      encode (((cuts G).map (fun p=>Jump.replace p.1 p.2.2 p.2.1)).map jumpBits) := by
  have hc : field 4 (ctxBits F R key H G)=labels G := by
    simp only [ctxBits,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  simp only [replaces,hc,BinarySuffix.slices_labels,Slices.outBits,mapWith_encode,List.map_map,Function.comp_def,
    replaceOp,jf,discardPrefix_pairBits,
    (BinarySuffix.cut_fields _).1,(BinarySuffix.cut_fields _).2.1,(BinarySuffix.cut_fields _).2.2,jumpBits]
lemma candidates_pack {m : ℕ} (F : Finset (Label (Fin m))) (R : List (Label (Fin m))) (key : ℕ)
    (H G : List (Label (Fin m))) : candidates (ctxBits F R key H G)=
      encode ((CanonicalMergeRefinement.candidates R H G).map jumpBits) := by
  simp only [candidates,adds_pack,removes_pack,replaces_pack,CanonicalMergeRefinement.candidates,List.map_append,encode_append]
noncomputable def view (x : List Bool) : List Bool := Find.run accepts (pairBits (x,candidates x))
noncomputable def view_computes : PolyComputes view := (id_computes.pair candidates_computes).comp (Find.run_computes accepts_computes)
lemma view_pack {m : ℕ} (F : Finset (Label (Fin m))) (R : List (Label (Fin m))) (key : ℕ)
    (H G : List (Label (Fin m))) : view (ctxBits F R key H G)=
      Find.optionEncode ((CanonicalMergeRefinement.view F R (copy key) H G).map jumpBits) := by
  simp only [view,candidates_pack,Find.run_encode,List.find?_map,Function.comp_def,accepts_pack,CanonicalMergeRefinement.view]
end MetricKMedianRecovery.BitMachine.BinaryJump

end OAI
