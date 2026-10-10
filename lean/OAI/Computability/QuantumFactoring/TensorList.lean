import Mathlib
import OAI.Computability.QuantumFactoring.SortingCircuit

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic.SortedWords

lemma layout_ofFn (w r : ℕ) (f : Fin r→Basis w) :
    layout w r (List.ofFn f)=tensorLayout w r f := by
  induction r with
  | zero=>rfl
  | succ r ih=>
    rw [List.ofFn_succ,layout,tensorLayout_succ]
    simp only [List.head?_cons,Option.getD_some,List.tail_cons]
    rw [ih]
    rfl

lemma ofFn_getD_pad {α : Type} (xs : List α) (d : α) (r : ℕ) (hlen : xs.length ≤ r) :
    List.ofFn (fun i : Fin r=>xs[i.val]?.getD d)=xs++List.replicate (r-xs.length) d := by
  apply List.ext_getElem
  · simp only [List.length_ofFn,List.length_append,List.length_replicate]
    omega
  · intro i hi hj
    rw [List.getElem_ofFn]
    by_cases hx : i<xs.length
    · rw [List.getElem?_eq_getElem hx,Option.getD_some,List.getElem_append_left hx]
    · have hle : xs.length ≤ i := by omega
      rw [List.getElem?_eq_none hle,Option.getD_none,List.getElem_append_right hle,List.getElem_replicate]

lemma ofFn_map_getD_pad {α β : Type} (xs : List α) (d : α) (r : ℕ) (hlen : xs.length ≤ r) (f : α→β) :
    List.ofFn (fun i : Fin r=>f (xs[i.val]?.getD d))=
      xs.map f++List.replicate (r-xs.length) (f d) := by
  have h := congrArg (List.map f) (ofFn_getD_pad xs d r hlen)
  simpa only [List.map_ofFn,List.map_append,List.map_replicate,Function.comp_def] using h

end ExactQuantumFactoring.BitArithmetic.SortedWords


end

end OAI
