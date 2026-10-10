import Mathlib

namespace OAI

open scoped BigOperators

namespace Problem346

/-- Reverse induction over a finite rectangular grid.  A zero at its upper corner
propagates to every point when a one-coordinate upward step can be cancelled. -/
theorem zero_of_upward_grid {ι M : Type*} [Fintype ι] [DecidableEq ι] [Zero M]
    (r : ℕ) (F : (ι → ℕ) → M)
    (hend : F (fun _ => r) = 0)
    (hstep : ∀ (c : ι → ℕ), (∀ i, c i ≤ r) → ∀ i, c i < r →
      F (Function.update c i (c i + 1)) = 0 → F c = 0)
    (c : ι → ℕ) (hc : ∀ i, c i ≤ r) : F c = 0 := by
  classical
  have aux : ∀ n : ℕ, ∀ c : ι → ℕ, (∀ i, c i ≤ r) →
      (∑ i, (r - c i)) = n → F c = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro c hc hn
      by_cases htop : ∀ i, c i = r
      · have heq : c = fun _ => r := funext htop
        simpa only [heq] using hend
      · push Not at htop
        obtain ⟨i, hi⟩ := htop
        have hir : c i < r := lt_of_le_of_ne (hc i) hi
        apply hstep c hc i hir
        let c' := Function.update c i (c i + 1)
        have hc' : ∀ j, c' j ≤ r := by
          intro j
          by_cases hji : j = i
          · subst j
            simp only [c', Function.update_self]
            omega
          · simpa only [c', Function.update_of_ne hji] using hc j
        have hlt : (∑ j, (r - c' j)) < n := by
          rw [← hn]
          apply Finset.sum_lt_sum
          · intro j hj
            by_cases hji : j = i
            · subst j
              simp only [c', Function.update_self]
              omega
            · simp only [c', Function.update_of_ne hji, le_refl]
          · refine ⟨i, Finset.mem_univ i, ?_⟩
            simp only [c', Function.update_self]
            omega
        exact ih _ hlt c' hc' rfl
  exact aux _ c hc rfl

end Problem346

end OAI
