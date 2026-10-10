import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.CrossCount

namespace OAI

namespace MetricKMedianRecovery.CanonicalMergeRefinement
variable {X Y : Type*}
def adjacent (f : X → X → List Y) : List X → List Y
  | []=>[]
  | a::T=>match T with | []=>[] | b::_=>f a b++adjacent f T
lemma cuts_adjacent (f : X → X → List Y) (U : List X) :
    (cuts U).flatMap (fun p=>match p.2.2 with | []=>[] | b::_=>f p.2.1 b)=adjacent f U := by
  induction U with
  | nil=>rfl
  | cons a U ih=>
    simp only [cuts,List.flatMap_cons,List.flatMap_map,ih]
    cases U with
    | nil=>rfl
    | cons b U=>rfl
variable [DecidableEq X]
def refinedEdge (F : Finset X) (R : List X) (copy spare : X → X) (H G : List X) : List (List X) :=
  match view F R copy H G with
  | none=>[G]
  | some J=>J.expand spare G
lemma refinePath_adjacent (F : Finset X) (R : List X) (copy spare : X → X) (H : List X) (T : List (List X)) :
    refinePath F R copy spare H T=adjacent (refinedEdge F R copy spare) (H::T) := by
  induction T generalizing H with
  | nil=>rfl
  | cons G T ih=>
    change refinePath F R copy spare H (G::T)=refinedEdge F R copy spare H G ++ adjacent (refinedEdge F R copy spare) (G::T)
    simp only [refinePath]
    cases he : view F R copy H G <;> simp only [he,refinedEdge,ih,List.singleton_append]
end MetricKMedianRecovery.CanonicalMergeRefinement

namespace MetricKMedianRecovery.BitMachine.BinaryJump
open WordOperations WordList RationalLeaves CanonicalMergeRefinement
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field field_computes field_encode)
noncomputable def spareWord (x : List Bool) : List Bool := BinaryLabel.copied (pairBits (cf 0 x,jf 4 x))
noncomputable def spareWord_computes : PolyComputes spareWord := by
  have spareWordComputes := ((cf_computes 0).pair (jf_computes 4)).comp BinaryLabel.copied_computes
  unfold spareWord
  simpa only [Function.comp_def] using spareWordComputes
noncomputable def ct (x : List Bool) : List Bool := jf 1 x++jf 2 x
noncomputable def ct_computes : PolyComputes ct := (jf_computes 1).append (jf_computes 2)
noncomputable def ctSpare (x : List Bool) : List Bool := ct x++cons (spareWord x) []
noncomputable def ctSpare_computes : PolyComputes ctSpare := ct_computes.append (cons_computes spareWord_computes (const_computes []))
noncomputable def grown (x : List Bool) : List Bool := BinarySuffix.grow (pairBits (pairBits (ct x,spareWord x),jf 3 x))
noncomputable def grown_computes : PolyComputes grown := by
  have grownComputes :=
    ((ct_computes.pair spareWord_computes).pair (jf_computes 3)).comp BinarySuffix.grow_computes
  unfold grown
  simpa only [Function.comp_def] using grownComputes
noncomputable def removeOut (x : List Bool) : List Bool := cons (ctSpare x) (grown x++cons (ct x++jf 3 x) [])
noncomputable def removeOut_computes : PolyComputes removeOut :=
  cons_computes ctSpare_computes (grown_computes.append (cons_computes (ct_computes.append (jf_computes 3)) (const_computes [])))
noncomputable def expand (x : List Bool) : List Bool := if tagIs 1 x then removeOut x else cons (cf 1 x) []
noncomputable def expand_computes : PolyComputes expand :=
  (tagIs_computes 1).cond removeOut_computes (cons_computes (cf_computes 1) (const_computes []))
lemma expand_pack {m : ℕ} (spare : ℕ) (G : List (Label (Fin m))) (J : Jump (Label (Fin m))) :
    expand (pairBits (encode [spare.bits,labels G],jumpBits J))=historyBits (J.expand (copy spare) G) := by
  cases J with
  | add i=>
    simp only [expand,tagIs,jf,cf,Function.comp_apply,discardPrefix_pairBits,extractPrefix_pairBits,jumpBits,
      field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,BinaryArithmetic.value_bits,
      Jump.expand]
    rfl
  | replace C T i=>
    simp only [expand,tagIs,jf,cf,Function.comp_apply,discardPrefix_pairBits,extractPrefix_pairBits,jumpBits,
      field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,BinaryArithmetic.value_bits,
      Jump.expand]
    rfl
  | remove C T A i=>
    simp only [expand,tagIs,removeOut,ctSpare,ct,grown,spareWord,jf,cf,Function.comp_apply,
      discardPrefix_pairBits,extractPrefix_pairBits,jumpBits,field_encode,List.getElem?_cons_zero,
      List.getElem?_cons_succ,Option.getD_some,BinaryArithmetic.value_bits,decide_true,ite_true,BinaryLabel.copied_pack]
    rw [←BinaryFiniteContext.labels_append,BinarySuffix.grow_pack]
    simp only [Jump.expand,removeVertices,historyBits,List.map_cons,List.map_append,List.map_nil,
      encode,encode_append,BinaryFiniteContext.labels_append,BinaryFiniteContext.labels_cons,BinaryFiniteContext.labels_nil]
noncomputable def edgeG (x : List Bool) : List Bool := field 4 (field 0 x)
noncomputable def edgeG_computes : PolyComputes edgeG := (field_computes 0).comp (field_computes 4)
noncomputable def edgeView : List Bool → List Bool := view ∘ field 0
noncomputable def edgeView_computes : PolyComputes edgeView := (field_computes 0).comp view_computes
noncomputable def edgeData (x : List Bool) : List Bool := encode [field 1 x,edgeG x]
noncomputable def edgeData_computes : PolyComputes edgeData := list_computes [field 1,edgeG] (by
  intro f hf; refine Classical.choice ?_
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hf
  rcases hf with rfl|rfl
  · exact ⟨field_computes _⟩
  · exact ⟨edgeG_computes⟩)
noncomputable def edge (x : List Bool) : List Bool :=
  if edgeView x=[] then cons (edgeG x) [] else expand (pairBits (edgeData x,(edgeView x).tail))
noncomputable def edge_computes : PolyComputes edge := by
  unfold edge
  simpa only [Function.comp_def,decide_eq_true_eq] using
    ((edgeView_computes.comp isEmpty_computes).cond (cons_computes edgeG_computes (const_computes []))
    ((edgeData_computes.pair (edgeView_computes.comp WordOperations.tail_computes)).comp expand_computes))
lemma edge_pack {m : ℕ} (F : Finset (Label (Fin m))) (R : List (Label (Fin m))) (key spare : ℕ)
    (H G : List (Label (Fin m))) : edge (encode [ctxBits F R key H G,spare.bits])=
      historyBits (refinedEdge F R (copy key) (copy spare) H G) := by
  have hg : edgeG (encode [ctxBits F R key H G,spare.bits])=labels G := by
    simp only [edgeG,ctxBits,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  have hv : edgeView (encode [ctxBits F R key H G,spare.bits])=
      Find.optionEncode ((CanonicalMergeRefinement.view F R (copy key) H G).map jumpBits) := by
    simp only [edgeView,Function.comp_apply,field_encode,List.getElem?_cons_zero,Option.getD_some,view_pack]
  simp only [edge,hv,hg,edgeData,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  cases hh : CanonicalMergeRefinement.view F R (copy key) H G with
  | none=>simp only [Option.map_none,Find.optionEncode,ite_true,refinedEdge,hh]; rfl
  | some J=>
    simp only [Option.map_some,Find.optionEncode,List.cons_ne_nil,ite_false,List.tail_cons,expand_pack,refinedEdge,hh]
end MetricKMedianRecovery.BitMachine.BinaryJump

end OAI
