import Mathlib

namespace OAI

noncomputable section

/-! Finite arrays represented by ordinary lists, including sparse integer keys.
This is an existence lemma used to show that exhaustive certificate search halts;
it is not nonuniform advice to the online machine. -/
namespace UniformKServer.FiniteRepresentation
open scoped Classical

theorem represents {α β : Type*} [Fintype α] (key : α→ℕ) (hk : Function.Injective key)
    (f : α→β) (default : β) : ∃xs : List β,∀a,(xs.getD (key a) default)=f a := by
  let B := Finset.univ.sup key+1
  let g (i : Fin B) : β := if h : ∃a,key a=i.val then f (Classical.choose h) else default
  refine ⟨List.ofFn g,?_⟩
  intro a
  have hbound : key a<B := by
    exact Nat.lt_succ_of_le (Finset.le_sup (f:=key) (Finset.mem_univ a))
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using hbound)]
  simp only [List.getElem_ofFn,g]
  have h : ∃b,key b=(⟨key a,hbound⟩:Fin B).val := ⟨a,rfl⟩
  rw [dite_eq_left h]
  congr 1
  exact hk (Classical.choose_spec h)

theorem represents_on {α β : Type*} (as : Finset α) (key : α→ℕ) (hk : Function.Injective key)
    (f : α→β) (default : β) : ∃xs : List β,∀a∈as,(xs.getD (key a) default)=f a := by
  obtain ⟨xs,hxs⟩ := represents (fun a : as=>key a.val)
    (fun a b h=>Subtype.ext (hk h)) (fun a=>f a.val) default
  exact ⟨xs,fun a ha=>hxs ⟨a,ha⟩⟩

end UniformKServer.FiniteRepresentation

end

end OAI
