import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.RefineMath

namespace OAI

namespace MetricKMedianRecovery.BitMachine.WordList
open WordOperations
lemma flatMapWith_typed {A B : Type*} (encA : A → List Bool) (encB : B → List Bool)
    (f : List Bool → List Bool) (ctx : List Bool) (g : A → List B) (xs : List A)
    (h : ∀ a∈xs,f (pairBits (ctx,encA a))=encode ((g a).map encB)) :
    flatMapWith f (pairBits (ctx,encode (xs.map encA)))=encode ((xs.flatMap g).map encB) := by
  simp only [flatMapWith,Function.comp_apply,mapWith_encode,Flatten.run_encode,List.map_map,
    List.map_flatMap,Flatten.encode_flatMap]
  congr 1
  apply List.map_congr_left
  exact h
end MetricKMedianRecovery.BitMachine.WordList
namespace MetricKMedianRecovery.BitMachine.BinaryRefine
open WordOperations WordList RationalLeaves CanonicalMergeRefinement
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field field_computes field_encode)
def ctxBits {m : ℕ} (F : Finset (Label (Fin m))) (R : List (Label (Fin m))) (key spare : ℕ) : List Bool :=
  encode [setBits F,labels R,key.bits,spare.bits]
noncomputable def cutTail (x : List Bool) : List Bool := field 2 (discardPrefix x)
noncomputable def cutTail_computes : PolyComputes cutTail := discardPrefix_computes.comp (field_computes 2)
noncomputable def source (x : List Bool) : List Bool := field 1 (discardPrefix x)
noncomputable def source_computes : PolyComputes source := discardPrefix_computes.comp (field_computes 1)
noncomputable def target : List Bool → List Bool := head ∘ cutTail
noncomputable def target_computes : PolyComputes target := cutTail_computes.comp WordList.head_computes
noncomputable def cf (n : ℕ) : List Bool → List Bool := field n ∘ extractPrefix
noncomputable def cf_computes (n : ℕ) : PolyComputes (cf n) := extractPrefix_computes.comp (field_computes n)
noncomputable def jumpContext (x : List Bool) : List Bool := encode [cf 0 x,cf 1 x,cf 2 x,source x,target x]
noncomputable def jumpContext_computes : PolyComputes jumpContext := list_computes [cf 0,cf 1,cf 2,source,target] (by
  intro f hf; refine Classical.choice ?_
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
  rcases hf with rfl|rfl|rfl|rfl|rfl
  · exact ⟨cf_computes _⟩
  · exact ⟨cf_computes _⟩
  · exact ⟨cf_computes _⟩
  · exact ⟨source_computes⟩
  · exact ⟨target_computes⟩)
noncomputable def edgeInput (x : List Bool) : List Bool := encode [jumpContext x,cf 3 x]
noncomputable def edgeInput_computes : PolyComputes edgeInput := list_computes [jumpContext,cf 3] (by
  intro f hf; refine Classical.choice ?_
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
  rcases hf with rfl|rfl
  · exact ⟨jumpContext_computes⟩
  · exact ⟨cf_computes _⟩)
noncomputable def cutOp (x : List Bool) : List Bool := if cutTail x=[] then [] else BinaryJump.edge (edgeInput x)
noncomputable def cutOp_computes : PolyComputes cutOp := by
  unfold cutOp
  simpa only [Function.comp_def,decide_eq_true_eq] using
    (cutTail_computes.comp isEmpty_computes).cond (const_computes []) (edgeInput_computes.comp BinaryJump.edge_computes)
lemma cutOp_pack {m : ℕ} (F : Finset (Label (Fin m))) (R : List (Label (Fin m))) (key spare : ℕ)
    (p : List (List (Label (Fin m))) × List (Label (Fin m)) × List (List (Label (Fin m)))) :
    cutOp (pairBits (ctxBits F R key spare,Slices.cutBits labels p))=
      historyBits (match p.2.2 with | []=>[] | G::_=>refinedEdge F R (copy key) (copy spare) p.2.1 G) := by
  rcases p with ⟨C,H,T⟩
  simp only [cutOp,cutTail,Slices.cutBits,discardPrefix_pairBits,field_encode,List.getElem?_cons_zero,
    List.getElem?_cons_succ,Option.getD_some]
  cases T with
  | nil=>rfl
  | cons G T=>
    have hn : Slices.itemsBits labels (G::T)≠[] := WordList.cons_ne_nil _ _
    rw [ite_eq_right hn]
    simp only [edgeInput,jumpContext,source,target,cutTail,cf,Function.comp_apply,extractPrefix_pairBits,
      discardPrefix_pairBits,field_encode,List.getElem?_cons_zero,
      List.getElem?_cons_succ,Option.getD_some,Slices.itemsBits_cons,head_cons,ctxBits]
    exact BinaryJump.edge_pack F R key spare H G
noncomputable def runInput (x : List Bool) : List Bool := pairBits (extractPrefix x,Slices.run (discardPrefix x))
noncomputable def runInput_computes : PolyComputes runInput := extractPrefix_computes.pair (discardPrefix_computes.comp Slices.run_computes)
noncomputable def run : List Bool → List Bool := flatMapWith cutOp ∘ runInput
noncomputable def run_computes : PolyComputes run := runInput_computes.comp (flatMapWith_computes cutOp_computes)
lemma run_pack {m : ℕ} (F : Finset (Label (Fin m))) (R : List (Label (Fin m))) (key spare : ℕ)
    (H : List (Label (Fin m))) (T : List (List (Label (Fin m)))) :
    run (pairBits (ctxBits F R key spare,historyBits (H::T)))=
      historyBits (refinePath F R (copy key) (copy spare) H T) := by
  have hs : Slices.run (historyBits (H::T))=Slices.outBits labels (cuts (H::T)) := Slices.run_items labels (H::T)
  simp only [run,Function.comp_apply,runInput,extractPrefix_pairBits,discardPrefix_pairBits,hs,Slices.outBits]
  rw [flatMapWith_typed (Slices.cutBits labels) labels cutOp (ctxBits F R key spare)
    (fun p=>match p.2.2 with | []=>[] | G::_=>refinedEdge F R (copy key) (copy spare) p.2.1 G)
    (cuts (H::T)) (fun p _=>cutOp_pack F R key spare p)]
  apply congrArg historyBits
  convert (cuts_adjacent (refinedEdge F R (copy key) (copy spare)) (H::T)).trans
    (refinePath_adjacent F R (copy key) (copy spare) H T).symm using 1
  congr 1
  funext p
  cases p.2.2 <;> rfl
end MetricKMedianRecovery.BitMachine.BinaryRefine

end OAI
