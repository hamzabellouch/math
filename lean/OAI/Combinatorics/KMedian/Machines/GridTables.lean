import Mathlib
import OAI.Combinatorics.KMedian.Machines.OrderedLists
import OAI.Combinatorics.KMedian.Machines.TableBuilders

namespace OAI

section Inline_PCPGridTables
namespace MetricKMedian.PCP.Compiler
open Binary Binary.Automatic
open scoped Classical

namespace Ordered
variable {V W : Type} [DecidableEq V] [DecidableEq W]
lemma map_index (o : Ordered V) (e : V ≃ W) (v : V) :
    ((o.map e).equiv (e v)).val=(o.equiv v).val := by
  change (o.entries.map e).idxOf (e v)=o.entries.idxOf v
  simp only [List.idxOf,List.findIdx_map]
  congr 1
  funext x
  simp only [Function.comp_def,Bool.beq_eq_decide_eq,e.injective.eq_iff]
lemma fin_index (n : ℕ) (v : Fin n) : ((fin n).equiv v).val=v.val := by
  change (List.finRange n).idxOf v=v.val
  exact List.idxOf_finRange v
def indexed {n : ℕ} (e : V ≃ Fin n) : Ordered V := (fin n).map e.symm
lemma indexed_index {n : ℕ} (e : V ≃ Fin n) (v : V) :
    ((indexed e).equiv v).val=(e v).val := by
  change ((List.finRange n).map e.symm).idxOf v=(e v).val
  rw [show v=e.symm (e v) from (e.symm_apply_apply v).symm]
  simp only [List.idxOf,List.findIdx_map]
  have hh : (fun x : Fin n => e.symm x == e.symm (e v))=(fun x : Fin n => x == e v) := by
    funext x
    simp only [Bool.beq_eq_decide_eq,e.symm.injective.eq_iff]
  change (List.finRange n).findIdx (fun x => e.symm x == e.symm (e v))=_
  rw [hh]
  simpa only [Equiv.apply_symm_apply,List.idxOf] using List.idxOf_finRange (e v)
omit [DecidableEq V] in
lemma indexed_codes {n : ℕ} (e : V ≃ Fin n) :
    (indexed e).entries.map (fun v => (e v).val)=List.range n := by
  simp only [indexed,map,fin,List.map_map,Function.comp_def,Equiv.apply_symm_apply]
  apply List.ext_getElem
  · simp
  · intros; simp
omit [DecidableEq V] in
lemma indexed_length {n : ℕ} (e : V ≃ Fin n) : (indexed e).entries.length=n := by
  simp only [indexed,map,fin,List.length_map,List.length_finRange]
end Ordered
namespace CSPTable
variable {A T B : Type} [Fintype A] [Coding T] [Coding B]
noncomputable def grid (seeds : List Unit) (tags : List B) (row : ℕ → B → CSPRow A) : CSPTable A :=
  (seeds,(List.range seeds.length).flatMap (fun v => tags.map (row v)))
lemma poly_grid [Inhabited B] (seeds : T → List Unit) (tags : List B) (row : T → ℕ → B → CSPRow A)
    (hs : Poly seeds) (hr : Poly (fun p : (T × ℕ) × B => row p.1.1 p.1.2 p.2)) :
    Poly (fun t => grid (seeds t) tags (row t)) := by
  unfold grid
  apply Poly.pair hs
  apply Poly.list_flatMap
  · apply Poly.list_map hr (Automatic.Poly.const tags)
  · exact Poly.list_indices.comp hs
variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  [DecidableEq A] [DecidableEq B]
omit [Fintype A] [Coding B] [Fintype V] [Fintype E]
  [DecidableEq E] [DecidableEq A] [DecidableEq B] in
lemma grid_build (C : BinaryCSP V E A) (seeds : List Unit) (ve : V ≃ Fin seeds.length)
    (tags : Ordered B) (ee : V × B ≃ E) (row : ℕ → B → CSPRow A)
    (hr : ∀ v b, row (ve v).val b=((ve (C.left (ee (v,b)))).val,
      (ve (C.right (ee (v,b)))).val,C.allowed (ee (v,b)))) :
    grid seeds tags.entries row=build C (Ordered.indexed ve)
      (((Ordered.indexed ve).prod tags).map ee) := by
  unfold grid build
  apply Prod.ext
  · have h : (Ordered.indexed ve).entries.map (fun _ => ())=seeds := by
      apply List.ext_getElem
      · simp only [List.length_map,Ordered.indexed_length]
      · intros; exact Subsingleton.elim _ _
    exact h.symm
  · rw [← Ordered.indexed_codes ve]
    simp only [Ordered.map,Ordered.prod,List.map_map,List.product, List.flatMap_map,
      List.map_flatMap,Function.comp_def]
    apply congrArg (fun f : V → List (CSPRow A) => (Ordered.indexed ve).entries.flatMap f)
    funext v
    apply List.map_congr_left
    intro b hb
    simp only [Ordered.indexed_index]
    exact hr v b
end CSPTable
end MetricKMedian.PCP.Compiler

end Inline_PCPGridTables

end OAI
