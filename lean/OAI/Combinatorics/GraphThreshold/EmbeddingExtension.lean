import Mathlib.Logic.Equiv.Fintype

namespace OAI

/-! Two placements of the same finite graph differ by an ambient permutation.
The statement is about arbitrary embeddings and therefore preserves isolated
vertices as well as vertices incident to edges. -/

namespace LeanBlast.SecondKahnKalai

theorem exists_perm_comp_embedding {α β : Type*} [Finite β]
    (f g : α ↪ β) : ∃ σ : Equiv.Perm β, ∀ a, σ (f a) = g a := by
  classical
  let : Finite α := Finite.of_injective f f.injective
  let : Fintype α := Fintype.ofFinite α
  let e : Set.range f ≃ Set.range g := f.toEquivRange.symm.trans g.toEquivRange
  refine ⟨e.extendSubtype, ?_⟩
  intro a
  rw [e.extendSubtype_apply_of_mem (f a) ⟨a, rfl⟩]
  change (e (f.toEquivRange a) : β) = g a
  simp [e]

end LeanBlast.SecondKahnKalai

end OAI
