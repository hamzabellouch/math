import Mathlib
import OAI.Combinatorics.KMedian.Binary.BinaryAutomatic

namespace OAI

section Inline_PCPFiniteCompiler

namespace MetricKMedian.PCP.Compiler
open Binary Binary.Automatic
open scoped Classical

@[instance_reducible]
noncomputable def finiteCoding (A : Type) [Fintype A] : Coding A :=
  ⟨fun a => Nat.bits (Fintype.equivFin A a).val⟩
noncomputable def finiteIndexProgram (A : Type) [Fintype A] :
    PolyProgram (finiteCoding A).encode Nat.bits (fun a => (Fintype.equivFin A a).val) where
  machine := (PolyProgram.identity Nat.bits).machine
  time := (PolyProgram.identity Nat.bits).time
  outputs a := (PolyProgram.identity Nat.bits).outputs (Fintype.equivFin A a).val
lemma finite_function {A B : Type} [Fintype A] [Coding B] [Inhabited B] (f : A → B) :
    @Poly A B (finiteCoding A) _ f := by
  let table := List.ofFn (fun i => f ((Fintype.equivFin A).symm i))
  let P := ((PolyProgram.constant (finiteCoding A).encode (Binary.encodeList enc) table).fanout
    (finiteIndexProgram A)).comp (PolyProgram.listGetD enc (default : B))
  refine ⟨P.congr f ?_⟩
  intro a
  simp only [Function.comp_def,table,List.getElem?_ofFn,Fin.isLt,↓reduceDIte,
    Option.getD_some,Fin.eta,Equiv.symm_apply_apply]
lemma poly_congr {A B : Type} [Coding A] [Coding B] {f g : A → B}
    (h : Poly f) (he : ∀ a, f a=g a) : Poly g := ⟨h.program.congr g he⟩
end MetricKMedian.PCP.Compiler

end Inline_PCPFiniteCompiler

end OAI
