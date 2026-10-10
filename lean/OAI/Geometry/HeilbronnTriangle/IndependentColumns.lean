import Mathlib

namespace OAI


namespace Problem355.IndependentColumns

variable {F V ι : Type*} [Field F] [AddCommGroup V] [Module F V]

theorem exists_independent_subfamily [Finite ι] (v : ι → V) (r : ℕ)
    (hr : r ≤ Module.finrank F (Submodule.span F (Set.range v))) :
    ∃ e : Fin r ↪ ι, LinearIndependent F (v ∘ e) := by
  classical
  obtain ⟨κ, a, ha, hspan, hlin⟩ := exists_linearIndependent' F v
  let : Finite κ := Finite.of_injective a ha
  let : Fintype κ := Fintype.ofFinite κ
  have hc : Fintype.card κ =
      Module.finrank F (Submodule.span F (Set.range v)) := by
    rw [← hspan]
    exact (finrank_span_eq_card hlin).symm
  have hr' : Fintype.card (Fin r) ≤ Fintype.card κ := by
    simpa only [Fintype.card_fin, hc] using hr
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hr'
  refine ⟨e.trans ⟨a, ha⟩, ?_⟩
  exact hlin.comp e e.injective

theorem exists_independent_columns {m n : Type*} [Fintype n]
    (A : Matrix m n F) (r : ℕ) (hr : r ≤ A.rank) :
    ∃ e : Fin r ↪ n, LinearIndependent F (A.col ∘ e) := by
  apply exists_independent_subfamily A.col r
  simpa only [Matrix.rank_eq_finrank_span_cols] using hr

theorem exists_independent_column_pair {m n : Type*} [Fintype n]
    (A : Matrix m n F) (hr : 2 ≤ A.rank) :
    ∃ i j : n, i ≠ j ∧ LinearIndependent F ![A.col i, A.col j] := by
  obtain ⟨e, he⟩ := exists_independent_columns A 2 hr
  refine ⟨e 0, e 1, e.injective.ne (by decide), ?_⟩
  convert he using 1
  funext i
  fin_cases i <;> rfl

end Problem355.IndependentColumns

end OAI
