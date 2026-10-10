import OAI.Analysis.LipschitzHilbert.Estimates.FiniteVariation

namespace OAI

/-! Sampling partial sums at increasing times cannot increase variation. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

theorem finiteCubicVariation_comp_le {E : Type*} [NormedAddCommGroup E]
    (F : ℕ → E) (N : ℕ) (q : ℕ → ℕ) (hq : Monotone q) (hN : q N ≤ N) :
    finiteCubicVariation (fun n => F (q n)) N ≤ finiteCubicVariation F N := by
  classical
  unfold finiteCubicVariation
  apply Finset.sup'_le
  intro p _
  by_cases hp : Monotone p
  · rw [ite_eq_left hp]
    let r : Fin (N + 1) → Fin (N + 1) := fun k =>
      ⟨q (p k).val, by have := (hq (show (p k).val ≤ N by omega)).trans hN; omega⟩
    have hr : Monotone r := by
      intro i j hij
      exact hq (hp hij)
    exact partition_le_finiteCubicVariation F N r hr
  · rw [ite_eq_right hp]
    exact finiteCubicVariation_nonneg F N

theorem finiteCubicVariation_congr {E : Type*} [NormedAddCommGroup E]
    (F G : ℕ → E) (N : ℕ) (h : ∀ i, i ≤ N → F i = G i) :
    finiteCubicVariation F N = finiteCubicVariation G N := by
  classical
  unfold finiteCubicVariation
  congr 1
  funext p
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [h (p i.succ) (by have := (p i.succ).isLt; omega),
    h (p i.castSucc) (by have := (p i.castSucc).isLt; omega)]

end LipschitzHilbert

end

end OAI
