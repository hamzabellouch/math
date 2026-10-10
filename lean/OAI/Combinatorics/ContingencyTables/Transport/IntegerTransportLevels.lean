import OAI.Combinatorics.ContingencyTables.Transport.IntegerPairRecursion

namespace OAI

/-! # Summing the actual integer-branch recursion by exposure level

The branches are the U+1 balanced profiles of each ordinary slot.
Local potential increments and future-form monotonicity telescope to the
root bound used before the softened limit. No positivity of future forms
or signature property of their weighted sums is assumed.
-/

namespace ContingencyTables.IntegerWeightedTransport

open scoped BigOperators Classical

abbrev BranchPath (U k : ℕ) := Fin k → Fin (U+1)

noncomputable def levelSum {U k : ℕ} (f : BranchPath U k → ℝ) : ℝ := ∑ s, f s

lemma levelSum_succ {U k : ℕ} (f : BranchPath U (k+1) → ℝ) :
    levelSum f = ∑ s : BranchPath U k, ∑ j : Fin (U+1),
      f (Fin.snoc (α := fun _ : Fin (k+1) => Fin (U+1)) s j) := by
  unfold levelSum
  rw [← (Fin.snocEquiv (fun _ : Fin (k+1) => Fin (U+1))).sum_comp]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  rfl

/-- A future slot's total quadratic form increases up to the level at
which that slot is processed. -/
theorem level_future_lower (U : ℕ)
    (Q : ∀ k, BranchPath U k → ℕ → ℝ)
    (hfuture : ∀ k t, k < t → ∀ s : BranchPath U k,
      Q k s t ≤ ∑ j : Fin (U+1),
        Q (k+1) (Fin.snoc (α := fun _ : Fin (k+1) => Fin (U+1)) s j) t)
    (k t : ℕ) (hkt : k ≤ t) :
    levelSum (fun s => Q 0 s t) ≤ levelSum (fun s => Q k s t) := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    apply (ih (by omega)).trans
    rw [levelSum_succ]
    apply Finset.sum_le_sum
    intro s _
    exact hfuture k t (by omega) s

/-- The sum of all leaf potentials is at most the root potential minus
the root's future corrections. This is the manuscript's recursion-level
telescoping step for U+1 ordinary integer branches. -/
theorem integer_leaf_potential_bound (U : ℕ)
    (P : ∀ k, BranchPath U k → ℝ) (Q : ∀ k, BranchPath U k → ℕ → ℝ)
    (hsplit : ∀ k, ∀ s : BranchPath U k,
      (∑ j : Fin (U+1), P (k+1)
        (Fin.snoc (α := fun _ : Fin (k+1) => Fin (U+1)) s j)) ≤ P k s - Q k s k)
    (hfuture : ∀ k t, k < t → ∀ s : BranchPath U k,
      Q k s t ≤ ∑ j : Fin (U+1),
        Q (k+1) (Fin.snoc (α := fun _ : Fin (k+1) => Fin (U+1)) s j) t)
    (n : ℕ) :
    levelSum (P n) ≤ levelSum (P 0) -
      ∑ t ∈ Finset.range n, levelSum (fun s => Q 0 s t) := by
  induction n with
  | zero => simp [levelSum]
  | succ n ih =>
    have hs : levelSum (P (n+1)) ≤ levelSum (P n) - levelSum (fun s => Q n s n) := by
      rw [levelSum_succ]
      unfold levelSum
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_le_sum (fun s _ => hsplit n s)
    have hq := level_future_lower U Q hfuture n n le_rfl
    rw [Finset.sum_range_succ]
    linarith

end ContingencyTables.IntegerWeightedTransport

end OAI
