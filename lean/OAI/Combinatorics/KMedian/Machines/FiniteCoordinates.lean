import Mathlib
import OAI.Combinatorics.KMedian.Machines.Hardcoded

namespace OAI

section Inline_PCPFiniteCoordinates

namespace MetricKMedian.PCP.Compiler
open Binary Binary.Automatic
open scoped Classical

noncomputable instance functionCoding {I A : Type} [Fintype I] [Fintype A] : Coding (I → A) := finiteCoding _
noncomputable instance functionHardcoded {I A : Type} [Fintype I] [Fintype A] : Hardcoded (I → A) :=
  ⟨fun _ _ _ f => finite_function f⟩
lemma poly_finCoordinates {X A : Type} [Coding X] [Fintype A] [Coding A] [Hardcoded A] [Inhabited A]
    (n : ℕ) (f : X → Fin n → A) (h : ∀ i, Poly (fun x => f x i)) : Poly f := by
  induction n with
  | zero =>
    apply poly_congr (Automatic.Poly.const (fun i : Fin 0 => Fin.elim0 i))
    intro x; funext i; exact Fin.elim0 i
  | succ n ih =>
    have ht := ih (fun x i => f x i.succ) (fun i => h i.succ)
    have hc : Poly (fun p : A × (Fin n → A) => Fin.cons p.1 p.2) := hardcoded _
    apply poly_congr (hc.comp (Poly.pair (h 0) ht))
    intro x; exact Fin.cons_self_tail (f x)
lemma poly_coordinates {X I A : Type} [Coding X] [Fintype I] [Fintype A]
    [Coding A] [Hardcoded A] [Inhabited A] (f : X → I → A)
    (h : ∀ i, Poly (fun x => f x i)) : Poly f := by
  have hf := poly_finCoordinates (Fintype.card I)
    (fun x i => f x ((Fintype.equivFin I).symm i)) (fun i => h _)
  have hc : Poly (fun g : Fin (Fintype.card I) → A => fun i => g (Fintype.equivFin I i)) := hardcoded _
  apply poly_congr (hc.comp hf)
  intro x; funext i; exact congrArg (f x) ((Fintype.equivFin I).symm_apply_apply i)
end MetricKMedian.PCP.Compiler

end Inline_PCPFiniteCoordinates

end OAI
