import OAI.RepresentationTheory.FoulkesHowe.FlattenedForm
import OAI.RepresentationTheory.FoulkesHowe.RowSwap

namespace OAI

noncomputable section

namespace Problem346

/-- Flattened monomial forms are invariant under any transposition whose slots have the same row. -/
theorem flattenedSymmetricForm_swap_same_row {a b : ℕ} {V : Type*}
    [AddCommGroup V] [Module ℂ V] (T : SymmetricMultilinearForm a b V)
    (p q : Fin a × Fin b) (hpq : p.1 = q.1) (v : Fin a × Fin b → V) :
    flattenedSymmetricForm T (v ∘ Equiv.swap p q) = flattenedSymmetricForm T v := by
  rcases p with ⟨i, j⟩
  rcases q with ⟨i', k⟩
  dsimp at hpq
  subst i'
  exact rowwise_invariant_swap (flattenedSymmetricForm T)
    (flattenedSymmetricForm_inner_permute T) i j k v

/-- Coefficient arrays of flattened forms satisfy exactly the row-swap condition
required to collapse a directional derivative to a multiplicity times one term. -/
theorem flattenedSymmetricForm_coeff_swap_same_row {a b : ℕ} {V I : Type*}
    [AddCommGroup V] [Module ℂ V] (T : SymmetricMultilinearForm a b V)
    (e : I → V) (p q : Fin a × Fin b) (hpq : p.1 = q.1)
    (k : Fin a × Fin b → I) :
    flattenedSymmetricForm T (e ∘ (k ∘ Equiv.swap p q)) =
      flattenedSymmetricForm T (e ∘ k) := by
  exact flattenedSymmetricForm_swap_same_row T p q hpq (e ∘ k)

end Problem346

end

end OAI
