import Mathlib
import OAI.Combinatorics.KMedian.Machines.GridTables

namespace OAI

section Inline_PCPRectTables
namespace MetricKMedian.PCP.Compiler.CSPTable
open Binary Binary.Automatic
open scoped Classical

variable {A T B : Type} [Fintype A] [Coding T] [Coding B]
noncomputable def rect (seeds roots : List Unit) (tags : List B) (row : ℕ → B → CSPRow A) : CSPTable A :=
  (seeds,(List.range roots.length).flatMap (fun v => tags.map (row v)))
lemma poly_rect [Inhabited B] (seeds roots : T → List Unit) (tags : List B) (row : T → ℕ → B → CSPRow A)
    (hs : Poly seeds) (hx : Poly roots) (hr : Poly (fun p : (T × ℕ) × B => row p.1.1 p.1.2 p.2)) :
    Poly (fun t => rect (seeds t) (roots t) tags (row t)) := by
  unfold rect
  apply Poly.pair hs
  apply Poly.list_flatMap
  · apply Poly.list_map hr (Automatic.Poly.const tags)
  · exact Poly.list_indices.comp hx
variable {V E R : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  [DecidableEq A] [DecidableEq B] [DecidableEq R]
omit [Fintype A] [Coding B] [Fintype V] [Fintype E] [DecidableEq E]
  [DecidableEq A] [DecidableEq B] [DecidableEq R] in
lemma rect_build (C : BinaryCSP V E A) (seeds roots : List Unit) (ve : V ≃ Fin seeds.length)
    (re : R ≃ Fin roots.length) (tags : Ordered B) (ee : R × B ≃ E) (row : ℕ → B → CSPRow A)
    (hr : ∀ v b, row (re v).val b=((ve (C.left (ee (v,b)))).val,
      (ve (C.right (ee (v,b)))).val,C.allowed (ee (v,b)))) :
    rect seeds roots tags.entries row=build C (Ordered.indexed ve)
      (((Ordered.indexed re).prod tags).map ee) := by
  unfold rect build
  apply Prod.ext
  · have h : (Ordered.indexed ve).entries.map (fun _ => ())=seeds := by
      apply List.ext_getElem
      · simp only [List.length_map,Ordered.indexed_length]
      · intros; exact Subsingleton.elim _ _
    exact h.symm
  · rw [← Ordered.indexed_codes re]
    simp only [Ordered.map,Ordered.prod,List.map_map,List.product,List.flatMap_map,
      List.map_flatMap,Function.comp_def]
    apply congrArg (fun f : R → List (CSPRow A) => (Ordered.indexed re).entries.flatMap f)
    funext v
    apply List.map_congr_left
    intro b hb
    simp only [Ordered.indexed_index]
    exact hr v b
end MetricKMedian.PCP.Compiler.CSPTable

end Inline_PCPRectTables

end OAI
