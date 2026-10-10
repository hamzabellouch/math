import Mathlib
import OAI.Combinatorics.KMedian.Machines.FiniteCompiler

namespace OAI

section Inline_PCPHardcoded
namespace MetricKMedian.PCP.Compiler
open Binary Binary.Automatic
open scoped Classical

class Hardcoded (A : Type) [Coding A] : Prop where
  all : ∀ (B : Type) [Coding B] [Inhabited B] (f : A → B), Poly f
lemma hardcoded {A B : Type} [Coding A] [Hardcoded A] [Coding B] [Inhabited B]
    (f : A → B) : Poly f := Hardcoded.all B f
noncomputable instance finCoding (n : ℕ) : Coding (Fin n) := finiteCoding _
noncomputable instance finHardcoded (n : ℕ) : Hardcoded (Fin n) := ⟨fun _ _ _ f => finite_function f⟩
noncomputable instance prodHardcoded {A B : Type} [Coding A] [Coding B]
    [Hardcoded A] [Hardcoded B] [Fintype B] : Hardcoded (A × B) where
  all C _ _ f := by
    let table : A → List C := fun a => List.ofFn (fun i => f (a,(Fintype.equivFin B).symm i))
    have ht : Poly table := hardcoded _
    have hi : Poly (fun b : B => (Fintype.equivFin B b).val) := hardcoded _
    have hp : Poly (fun p : A × B => (table p.1)[(Fintype.equivFin B p.2).val]?.getD default) :=
      Poly.list_getD_comp default (ht.comp Poly.fst) (hi.comp Poly.snd)
    apply poly_congr hp
    intro p
    simp only [table,List.getElem?_ofFn,Fin.isLt,↓reduceDIte,Option.getD_some,Fin.eta,Equiv.symm_apply_apply]
end MetricKMedian.PCP.Compiler

end Inline_PCPHardcoded

end OAI
