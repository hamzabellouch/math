import OAI.MeasureTheory.Falconer.Estimates.ScalarLogAverages

namespace OAI

/-! Finite iteration of the actual weighted child inequalities. The
 coefficient is shared by all levels and all branches. -/
namespace Falconer

 theorem scalar_tree_log_growth {α β : Type*} (N : ℕ)
    (B : Finset β) (hB : B.Nonempty) (nodes : ℕ → Finset α)
    (children : ℕ → α → Finset α) (m : ℕ → ℕ) (ell : ℕ → ℝ)
    (q : ℕ → α → β → ℝ) (w : ℕ → α → β → ℝ)
    (hq : ∀ n ≤ N, ∀ x ∈ nodes n, ∀ b ∈ B, 0 < q n x b)
    (hleaf : ∀ x ∈ nodes 0, ∀ b ∈ B, 1 ≤ q 0 x b)
    (hchildren : ∀ n < N, ∀ x ∈ nodes (n+1), children n x ⊆ nodes n)
    (hchildne : ∀ n < N, ∀ x ∈ nodes (n+1), (children n x).Nonempty)
    (hcard : ∀ n < N, ∀ x ∈ nodes (n+1), (children n x).card = m n)
    (hw : ∀ n < N, ∀ x ∈ nodes (n+1), ∀ b ∈ B, 0 < w n x b)
    (hwlog : ∀ n < N, ∀ x ∈ nodes (n+1),
      ell n ≤ scalarAverage B (fun b => Real.log (w n x b)))
    (hstep : ∀ n < N, ∀ x ∈ nodes (n+1), ∀ b ∈ B,
      w n x b*(∑ y ∈ children n x, q n y b) ≤ q (n+1) x b) :
    ∀ n ≤ N, ∀ x ∈ nodes n,
      (∑ j ∈ Finset.range n, (ell j+Real.log (m j : ℝ))) ≤
        scalarAverage B (fun b => Real.log (q n x b)) := by
  intro n hn
  induction n with
  | zero =>
    intro x hx
    simp only [Finset.range_zero,Finset.sum_empty]
    have hh := scalarAverage_mono B (fun b hb => Real.log_nonneg (hleaf x hx b hb))
    rw [scalarAverage_const B hB 0] at hh
    exact hh
  | succ n ih =>
    intro x hx
    have hnN : n < N := by omega
    have hh := scalar_average_weighted_branch (children n x) B
      (hchildne n hnN x hx) hB (q n) (w n x) (q (n+1) x)
      (fun y hy b hb => hq n (by omega) y (hchildren n hnN x hx hy) b hb)
      (hw n hnN x hx) (hstep n hnN x hx)
      (fun y hy => ih (by omega) y (hchildren n hnN x hx hy)) (hwlog n hnN x hx)
    rw [hcard n hnN x hx] at hh
    rw [Finset.sum_range_succ]
    linarith

 theorem scalar_tree_average_growth {α β : Type*} (N : ℕ)
    (B : Finset β) (hB : B.Nonempty) (nodes : ℕ → Finset α)
    (children : ℕ → α → Finset α) (m : ℕ → ℕ) (ell : ℕ → ℝ)
    (q : ℕ → α → β → ℝ) (w : ℕ → α → β → ℝ)
    (hq : ∀ n ≤ N, ∀ x ∈ nodes n, ∀ b ∈ B, 0 < q n x b)
    (hleaf : ∀ x ∈ nodes 0, ∀ b ∈ B, 1 ≤ q 0 x b)
    (hchildren : ∀ n < N, ∀ x ∈ nodes (n+1), children n x ⊆ nodes n)
    (hchildne : ∀ n < N, ∀ x ∈ nodes (n+1), (children n x).Nonempty)
    (hcard : ∀ n < N, ∀ x ∈ nodes (n+1), (children n x).card = m n)
    (hw : ∀ n < N, ∀ x ∈ nodes (n+1), ∀ b ∈ B, 0 < w n x b)
    (hwlog : ∀ n < N, ∀ x ∈ nodes (n+1),
      ell n ≤ scalarAverage B (fun b => Real.log (w n x b)))
    (hstep : ∀ n < N, ∀ x ∈ nodes (n+1), ∀ b ∈ B,
      w n x b*(∑ y ∈ children n x, q n y b) ≤ q (n+1) x b)
    (x : α) (hx : x ∈ nodes N) :
    Real.exp (∑ j ∈ Finset.range N, (ell j+Real.log (m j : ℝ))) ≤
      scalarAverage B (q N x) := by
  have h := scalar_tree_log_growth N B hB nodes children m ell q w hq hleaf
    hchildren hchildne hcard hw hwlog hstep N le_rfl x hx
  exact (Real.exp_le_exp.mpr h).trans (scalar_exp_average_log_le B hB (q N x) (hq N le_rfl x hx))

end Falconer

end OAI
