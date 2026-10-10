import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.RegularChain
import OAI.Combinatorics.KMedianRecovery.Recovery.CrossEdge

namespace OAI

namespace MetricKMedianRecovery.BitMachine.WordList.FirstPresent
open WordOperations
open CanonicalMergeCrossing
noncomputable def present (x : List Bool) : Bool := !decide (discardPrefix x=[])
noncomputable def present_computes : PolyComputes (fun x=>[present x]) :=
  (discardPrefix_computes.comp isEmpty_computes).not
noncomputable def found (x : List Bool) : List Bool := Find.run present (pairBits ([],discardPrefix x))
noncomputable def found_computes : PolyComputes found :=
  ((const_computes []).pair discardPrefix_computes).comp (Find.run_computes present_computes)
noncomputable def run (x : List Bool) : List Bool := if found x=[] then extractPrefix x else (found x).tail.tail
noncomputable def run_computes : PolyComputes run := by
  unfold run
  simpa only [Function.comp_def,decide_eq_true_eq] using
    (found_computes.comp isEmpty_computes).cond extractPrefix_computes
      ((found_computes.comp WordOperations.tail_computes).comp WordOperations.tail_computes)
def marker {A : Type*} (enc : A → List Bool) (o : Option A) : List Bool := Find.optionEncode (o.map enc)
lemma find_markers {A : Type*} (enc : A → List Bool) (os : List (Option A)) :
    ((os.map (marker enc)).find? (fun b=>!decide (b=[])))=
      (firstPresent os).map (fun a=>true::enc a) := by
  induction os with
  | nil=>rfl
  | cons o os ih=>
    cases o <;> simp only [List.map_cons,marker,Option.map_none,Option.map_some,Find.optionEncode,
      List.find?_cons,List.cons_ne_nil,decide_false,decide_true,Bool.not_false,Bool.not_true,
      firstPresent,ih]
lemma run_pack {A : Type*} (enc : A → List Bool) (fallback : A) (os : List (Option A)) :
    run (pairBits (enc fallback,encode (os.map (marker enc))))=
      enc ((firstPresent os).getD fallback) := by
  have hf : found (pairBits (enc fallback,encode (os.map (marker enc))))=
      Find.optionEncode ((firstPresent os).map (fun a=>true::enc a)) := by
    simp only [found,discardPrefix_pairBits,Find.run_encode,present,find_markers]
  rw [run,hf,extractPrefix_pairBits]
  cases firstPresent os <;> rfl
end MetricKMedianRecovery.BitMachine.WordList.FirstPresent

namespace MetricKMedianRecovery.BitMachine.BinaryCross
open WordOperations WordList RationalLeaves BinaryArithmetic
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field field_computes field_encode)
attribute [local irreducible] finalCount paid edge
noncomputable def leftCount : List Bool → List Bool := finalCount ∘ leftData
noncomputable def rightCount : List Bool → List Bool := finalCount ∘ rightData
noncomputable def leftCount_computes : PolyComputes leftCount := leftData_computes.comp finalCount_computes
noncomputable def rightCount_computes : PolyComputes rightCount := rightData_computes.comp finalCount_computes
lemma leftCount_pack {m : ℕ} (F Q : Finset (Label (Fin m))) (k : ℕ)
    (P R : List (Label (Fin m)) × List (List (Label (Fin m)))) :
    leftCount (pack F Q k P R)=(CanonicalMergeCrossing.finalCount F Q P.1 P.2).bits := by
  rcases P with ⟨H,T⟩
  simp only [leftCount,leftData,leftNode,pack,Function.comp_apply,extractPrefix_pairBits,discardPrefix_pairBits,finalCount_pack]
lemma rightCount_pack {m : ℕ} (F Q : Finset (Label (Fin m))) (k : ℕ)
    (P R : List (Label (Fin m)) × List (List (Label (Fin m)))) :
    rightCount (pack F Q k P R)=(CanonicalMergeCrossing.finalCount F Q R.1 R.2).bits := by
  rcases R with ⟨G,U⟩
  simp only [rightCount,rightData,rightNode,pack,Function.comp_apply,extractPrefix_pairBits,discardPrefix_pairBits,finalCount_pack]
lemma key_pack {m : ℕ} (F Q : Finset (Label (Fin m))) (k : ℕ)
    (P R : List (Label (Fin m)) × List (List (Label (Fin m)))) : cf 2 (pack F Q k P R)=k.bits := by
  simp only [cf,pack,Function.comp_apply,extractPrefix_pairBits,ctxBits,field_encode,
    List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
noncomputable def sandwiched (x : List Bool) : Bool :=
  (decide (value (leftCount x)<value (cf 2 x)) && decide (value (cf 2 x)<value (rightCount x))) ||
  (decide (value (rightCount x)<value (cf 2 x)) && decide (value (cf 2 x)<value (leftCount x)))
noncomputable def sandwiched_computes : PolyComputes (fun x=>[sandwiched x]) :=
  ((NatOps.lt leftCount_computes (cf_computes 2)).and (NatOps.lt (cf_computes 2) rightCount_computes)).or
    ((NatOps.lt rightCount_computes (cf_computes 2)).and (NatOps.lt (cf_computes 2) leftCount_computes))
lemma sandwiched_pack {m : ℕ} (F Q : Finset (Label (Fin m))) (k : ℕ)
    (P R : List (Label (Fin m)) × List (List (Label (Fin m)))) :
    sandwiched (pack F Q k P R)=decide (PhaseCountCrossing.Sandwich k
      (CanonicalMergeCrossing.finalCount F Q P.1 P.2) (CanonicalMergeCrossing.finalCount F Q R.1 R.2)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [sandwiched,leftCount_pack,rightCount_pack,key_pack,value_bits,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq]
  unfold PhaseCountCrossing.Sandwich
  rfl
noncomputable def transition (x : List Bool) : List Bool :=
  if decide (value (rightCount x)=value (cf 2 x)) then true::successNode (rightNode x)
  else if sandwiched x then true::edge x else []
noncomputable def transition_computes : PolyComputes transition :=
  (NatOps.eq rightCount_computes (cf_computes 2)).cond
    ((const_computes [true]).append (rightNode_computes.comp successNode_computes))
    (sandwiched_computes.cond ((const_computes [true]).append edge_computes) (const_computes []))
lemma transition_pack {m : ℕ} (F Q : Finset (Label (Fin m))) (k : ℕ)
    (P R : List (Label (Fin m)) × List (List (Label (Fin m)))) :
    transition (pack F Q k P R)=FirstPresent.marker resultBits (CanonicalMergeCrossing.transition F Q k P R) := by
  rcases P with ⟨H,T⟩
  rcases R with ⟨G,U⟩
  rw [transition,rightCount_pack,key_pack,sandwiched_pack]
  simp only [value_bits,decide_eq_true_eq,CanonicalMergeCrossing.transition]
  split_ifs <;> simp only [FirstPresent.marker,Option.map_some,Option.map_none,Find.optionEncode,edge_pack]
  simp only [rightNode,pack,Function.comp_apply,discardPrefix_pairBits,successNode,resultBits]
end MetricKMedianRecovery.BitMachine.BinaryCross

namespace MetricKMedianRecovery.BitMachine.BinaryNodeScan
open WordOperations WordList RationalLeaves CanonicalMergeRefinement CanonicalMergeCrossing
open BinaryCross (ctxBits nodeBits resultBits)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field field_computes field_encode)
attribute [local irreducible] BinaryCross.transition
noncomputable def suffix (x : List Bool) : List Bool := field 2 (discardPrefix x)
noncomputable def suffix_computes : PolyComputes suffix := discardPrefix_computes.comp (field_computes 2)
noncomputable def current (x : List Bool) : List Bool := field 1 (discardPrefix x)
noncomputable def current_computes : PolyComputes current := discardPrefix_computes.comp (field_computes 1)
noncomputable def transitionInput (x : List Bool) : List Bool :=
  pairBits (extractPrefix x,pairBits (current x,head (suffix x)))
noncomputable def transitionInput_computes : PolyComputes transitionInput :=
  extractPrefix_computes.pair (current_computes.pair (suffix_computes.comp WordList.head_computes))
noncomputable def cutOp (x : List Bool) : List Bool :=
  if suffix x=[] then [] else BinaryCross.transition (transitionInput x)
noncomputable def cutOp_computes : PolyComputes cutOp := by
  unfold cutOp
  simpa only [Function.comp_def,decide_eq_true_eq] using
    (suffix_computes.comp isEmpty_computes).cond (const_computes [])
      (transitionInput_computes.comp BinaryCross.transition_computes)
lemma cutOp_pack {m : ℕ} (F Q : Finset (Label (Fin m))) (k : ℕ)
    (p : List (List (Label (Fin m)) × List (List (Label (Fin m)))) ×
      (List (Label (Fin m)) × List (List (Label (Fin m)))) ×
      List (List (Label (Fin m)) × List (List (Label (Fin m))))) :
    cutOp (pairBits (ctxBits F Q k,Slices.cutBits nodeBits p))=
      FirstPresent.marker resultBits (match p.2.2 with | []=>none | b::_=>transition F Q k p.2.1 b) := by
  rcases p with ⟨C,a,T⟩
  simp only [cutOp,suffix,Slices.cutBits,discardPrefix_pairBits,field_encode,List.getElem?_cons_zero,
    List.getElem?_cons_succ,Option.getD_some]
  cases T with
  | nil=>rfl
  | cons b T=>
    have hn : Slices.itemsBits nodeBits (b::T)≠[] := WordList.cons_ne_nil _ _
    rw [ite_eq_right hn]
    simp only [transitionInput,current,suffix,extractPrefix_pairBits,discardPrefix_pairBits,
      field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,Slices.itemsBits_cons,head_cons]
    exact BinaryCross.transition_pack F Q k a b
noncomputable def scanInput (x : List Bool) : List Bool := pairBits (field 0 x,Slices.run (field 2 x))
noncomputable def scanInput_computes : PolyComputes scanInput :=
  (field_computes 0).pair ((field_computes 2).comp Slices.run_computes)
noncomputable def markers : List Bool → List Bool := mapWith cutOp ∘ scanInput
noncomputable def markers_computes : PolyComputes markers := scanInput_computes.comp (mapWith_computes cutOp_computes)
noncomputable def lastNode : List Bool → List Bool := head ∘ WordList.reverse ∘ field 2
noncomputable def lastNode_computes : PolyComputes lastNode :=
  ((field_computes 2).comp WordList.reverse_computes).comp WordList.head_computes
noncomputable def fallback (x : List Bool) : List Bool := encode [(1:ℕ).bits,lastNode x,field 1 x]
noncomputable def fallback_computes : PolyComputes fallback := list_computes [fun _=>(1:ℕ).bits,lastNode,field 1] (by
  intro f hf; refine Classical.choice ?_
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
  rcases hf with rfl|rfl|rfl
  · exact ⟨const_computes _⟩
  · exact ⟨lastNode_computes⟩
  · exact ⟨field_computes _⟩)
noncomputable def run (x : List Bool) : List Bool := FirstPresent.run (pairBits (fallback x,markers x))
noncomputable def run_computes : PolyComputes run := (fallback_computes.pair markers_computes).comp FirstPresent.run_computes
lemma head_encode_of_head {A : Type*} (enc : A → List Bool) (xs : List A) (a : A) (h : xs.head?=some a) :
    head (encode (xs.map enc))=enc a := by
  cases xs with
  | nil=>simp only [List.head?_nil,reduceCtorEq] at h
  | cons b T=>
    simp only [List.head?_cons,Option.some.injEq] at h
    subst b
    exact head_cons _ _
def pack {m : ℕ} (F Q : Finset (Label (Fin m))) (k : ℕ) (U : List (List (Label (Fin m))))
    (nodes : List (List (Label (Fin m)) × List (List (Label (Fin m))))) : List Bool :=
  encode [ctxBits F Q k,historyBits U,encode (nodes.map nodeBits)]
lemma markers_pack {m : ℕ} (F Q : Finset (Label (Fin m))) (k : ℕ) (U : List (List (Label (Fin m))))
    (a : List (Label (Fin m)) × List (List (Label (Fin m))))
    (T : List (List (Label (Fin m)) × List (List (Label (Fin m))))) :
    markers (pack F Q k U (a::T))=encode ((slots (transition F Q k) a T++[none]).map (FirstPresent.marker resultBits)) := by
  simp only [markers,Function.comp_apply,scanInput,pack,field_encode,List.getElem?_cons_zero,
    List.getElem?_cons_succ,Option.getD_some]
  rw [show encode ((a::T).map nodeBits)=Slices.itemsBits nodeBits (a::T) from rfl]
  simp only [Slices.run_items,Slices.outBits,mapWith_encode,List.map_map]
  have hcuts:=cuts_slots (transition F Q k) a T
  simp only [←hcuts,List.map_map,Function.comp_def]
  apply congrArg encode
  apply List.map_congr_left
  rintro ⟨previousNodes,node,remainingNodes⟩ _
  cases remainingNodes with
  | nil=>exact cutOp_pack F Q k (previousNodes,node,[])
  | cons nextNode rest=>exact cutOp_pack F Q k (previousNodes,node,nextNode::rest)
lemma fallback_pack {m : ℕ} (F Q : Finset (Label (Fin m))) (k : ℕ) (U : List (List (Label (Fin m))))
    (a : List (Label (Fin m)) × List (List (Label (Fin m))))
    (T : List (List (Label (Fin m)) × List (List (Label (Fin m))))) :
    fallback (pack F Q k U (a::T))=resultBits (.common (finalNode a T).1 (finalNode a T).2 U) := by
  simp only [fallback,lastNode,Function.comp_apply,pack,field_encode,List.getElem?_cons_zero,
    List.getElem?_cons_succ,Option.getD_some,reverse_encode,←List.map_reverse]
  rw [head_encode_of_head nodeBits _ _ (finalNode_reverse a T)]
  rfl
lemma run_pack {m : ℕ} (F Q : Finset (Label (Fin m))) (k : ℕ) (U : List (List (Label (Fin m))))
    (a : List (Label (Fin m)) × List (List (Label (Fin m))))
    (T : List (List (Label (Fin m)) × List (List (Label (Fin m))))) :
    run (pack F Q k U (a::T))=resultBits (walk (transition F Q k) (fun p=>.common p.1 p.2 U) a T) := by
  rw [run,fallback_pack,markers_pack,FirstPresent.run_pack,firstPresent_append_none,walk_slots]
end MetricKMedianRecovery.BitMachine.BinaryNodeScan

end OAI
