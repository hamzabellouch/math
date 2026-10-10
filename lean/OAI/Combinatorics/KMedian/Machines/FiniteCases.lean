import Mathlib
import OAI.Combinatorics.KMedian.Machines.Hardcoded

namespace OAI

section Inline_PCPFiniteCases
namespace MetricKMedian.PCP.Compiler
open Binary Binary.Automatic
open scoped Classical

lemma poly_finite_cases {I X Y : Type} [Fintype I] [Coding I] [Hardcoded I]
    [Coding X] [Coding Y] [Inhabited Y] (f : I → X → Y)
    (h : ∀ i, Poly (f i)) : Poly (fun p : I × X => f p.1 p.2) := by
  let lookup : List I → I × X → Y := fun xs =>
    xs.foldr (fun i g p => if p.1=i then f i p.2 else g p) (fun _ => default)
  have hp : ∀ xs, Poly (lookup xs) := by
    intro xs
    induction xs with
    | nil => exact Automatic.Poly.const _
    | cons i xs ih =>
      change Poly (fun p : I × X => if p.1=i then f i p.2 else lookup xs p)
      exact Poly.ite_prop ((hardcoded (fun j : I => decide (j=i))).comp Poly.fst)
        ((h i).comp Poly.snd) ih
  have he : ∀ xs (i:I) (x:X), i∈xs → lookup xs (i,x)=f i x := by
    intro xs
    induction xs with
    | nil => simp
    | cons j xs ih =>
      intro i x hi
      change (if i=j then f j x else lookup xs (i,x))=f i x
      by_cases hij : i=j
      · simp [hij]
      · rw [ite_eq_right hij]
        exact ih i x ((List.mem_cons.mp hi).resolve_left hij)
  apply poly_congr (hp (Finset.univ.toList))
  intro p
  exact he _ p.1 p.2 (by simp)
lemma poly_fixedList {I X Y : Type} [Coding X] [Coding Y] (xs : List I)
    (f : I → X → Y) (h : ∀ i∈xs, Poly (f i)) : Poly (fun x => xs.map (fun i => f i x)) := by
  induction xs with
  | nil => exact Automatic.Poly.const []
  | cons i xs ih =>
    have hf := h i (by simp)
    have ht := ih (fun i hi => h i (by simp [hi]))
    change Poly (fun x => f i x :: xs.map (fun i => f i x))
    fun_prop
end MetricKMedian.PCP.Compiler

end Inline_PCPFiniteCases

end OAI
