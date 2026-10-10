import Mathlib
import OAI.Combinatorics.KMedian.Machines.Ordered

namespace OAI

section Inline_PCPOrderedLists
namespace MetricKMedian.PCP.Compiler.Ordered
open scoped Classical

variable {A B : Type} [DecidableEq A] [DecidableEq B]
def sigma (o : Ordered A) {B : A → Type} (s : ∀ a, Ordered (B a)) : Ordered (Sigma B) where
  entries := o.entries.sigma (fun a => (s a).entries)
  nodup := o.nodup.sigma (fun a => (s a).nodup)
  all a := List.mem_sigma.mpr ⟨o.all a.1,(s a.1).all a.2⟩
def prod (o : Ordered A) (s : Ordered B) : Ordered (A × B) where
  entries := o.entries.product s.entries
  nodup := o.nodup.product s.nodup
  all a := List.mem_product.mpr ⟨o.all a.1,s.all a.2⟩
omit [DecidableEq A] in
lemma filter_val (o : Ordered A) (p : A → Prop) [DecidablePred p] :
    ((o.filter p).entries.map Subtype.val)=o.entries.filter (fun a => decide (p a)) := by
  unfold filter
  rw [List.map_filterMap]
  have hf : (fun a : {a // a∈o.entries} =>
    Option.map Subtype.val (if h : p a.val then some (⟨a.val,h⟩ : {a // p a}) else none))=
      (fun a : {a // a∈o.entries} => Option.guard (fun x => decide (p x)) a.val) := by
    funext a
    by_cases h : p a.val <;> simp [h,Option.guard]
  rw [hf]
  change List.filterMap ((Option.guard (fun x => decide (p x))) ∘ Subtype.val) o.entries.attach = _
  rw [← List.filterMap_map,List.attach_map_subtype_val,List.filterMap_eq_filter]
lemma index_coded (o : Ordered A) (f : A → B) (hf : Function.Injective f) (a : A) :
    (o.equiv a).val=(o.entries.map f).findIdx (fun b => decide (b=f a)) := by
  rw [equiv_val,List.idxOf,List.findIdx_map]
  congr 1
  funext x
  simp only [Function.comp_def,hf.eq_iff,Bool.beq_eq_decide_eq]
omit [DecidableEq B] in
lemma get_coded (o : Ordered A) (f : A → B) (a : A) :
    (o.entries.map f)[(o.equiv a).val]?=some (f a) := by
  rw [List.getElem?_map,List.getElem?_eq_getElem (o.equiv a).isLt,get_equiv]
  rfl
end MetricKMedian.PCP.Compiler.Ordered

end Inline_PCPOrderedLists

end OAI
